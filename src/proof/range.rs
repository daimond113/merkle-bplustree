//! Range queries.

use std::{
    borrow::Borrow,
    collections::VecDeque,
    marker::PhantomData,
    ops::{Bound, RangeBounds},
    task::Poll,
};

use derive_where::derive_where;
use futures_util::{
    FutureExt as _, Stream, StreamExt as _,
    future::{BoxFuture, Either, try_join},
};

use crate::{
    ExactIterExt as _, HasherOutput, TreeConfig,
    hasher::Hasher as _,
    merkle_tree::merkle_root_in_place,
    node::{LeafSearchPath, NodeOwner, RootTreeNode, TreeInternalNode, TreeLeafNode, TreeNode},
    proof::InvalidProofError,
    storage::ReadNodeStorage,
};

pin_project_lite::pin_project! {
    #[project = RangeQueryContextPin]
    enum RangeQueryContext<
        'a,
        FutRes: Future,
        C: TreeConfig,
        O,
        S,
    >
    where
        O: NodeOwner<C>,
        O: 'a,
        S: ReadNodeStorage<C>,
        S: 'a,
    {
        Resolving {
            #[pin]
            fut: FutRes,
        },
        RootOnly {
            leaf: O::Leaf,
            current_item: usize,
        },
        ResolvedMultilevel {
            path: Vec<(usize, O::Internal)>,
            // TODO: this should be generic, but we are not able to name get_node's return type
            current_leaf: Either<
                (Option<S>, O::Leaf),
                BoxFuture<'a, Result<(S, usize, O::Internal, TreeNode<C>), S::Error>>,
            >,
            current_item: usize,

            upper: Option<LeafSearchPath<C, O>>,
        },
        Dead,
    }
}

pin_project_lite::pin_project! {
    #[project = RangeQueryStreamPin]
    struct RangeQueryStreamImpl<
        'a,
        Q: ?Sized,
        B: RangeBounds<Q>,
        FutRes: Future<Output = ResolvingOutput<'a, B, C, O, S>>,
        R,
        F,
        C: TreeConfig,
        O,
        S,
        W,
    >
    where
        O: NodeOwner<C>,
        O: 'a,
        S: ReadNodeStorage<C>,
        S: 'a,
        W: RangeQueryWitness<C, R>,
    {
        bounds: Option<B>,
        #[pin]
        context: RangeQueryContext<'a, FutRes, C, O, S>,
        map: F,
        witness: W,
        _phantom: PhantomData<(R, Q)>,
    }
}

pub(crate) trait RangeQueryWitness<C: TreeConfig, R> {
    type Item;

    fn witness_internal(&mut self, node: &TreeInternalNode<C>);

    fn witness_leaf(&mut self, leaf: &TreeLeafNode<C>, start: usize, end: usize, last: bool);

    fn witness_entry(&mut self, entry: R);

    fn next_item(&mut self) -> Option<Self::Item>;
}

pub(crate) struct Plain<R>(Option<R>);

impl<R> Plain<R> {
    pub(crate) fn new() -> Self {
        Self(None)
    }
}

impl<C: TreeConfig, R> RangeQueryWitness<C, R> for Plain<R> {
    type Item = R;

    fn witness_internal(&mut self, _node: &TreeInternalNode<C>) {}

    fn witness_leaf(&mut self, _leaf: &TreeLeafNode<C>, _start: usize, _end: usize, _last: bool) {}

    fn witness_entry(&mut self, entry: R) {
        self.0 = Some(entry);
    }

    fn next_item(&mut self) -> Option<R> {
        self.0.take()
    }
}

type ResolvingOutput<'a, B, C, O, S> =
    Result<(B, S, LeafSearchPath<C, O>, LeafSearchPath<C, O>), <S as ReadNodeStorage<C>>::Error>;

impl<
    'a,
    Q: Ord + ?Sized,
    B: RangeBounds<Q>,
    FutRes: Future<Output = ResolvingOutput<'a, B, C, O, S>>,
    R,
    F: Fn(&C::Key, &C::Value) -> R,
    C: TreeConfig,
    O: NodeOwner<C> + 'a,
    S: ReadNodeStorage<C> + Send + Sync + 'a,
    W: RangeQueryWitness<C, R>,
> Stream for RangeQueryStreamImpl<'a, Q, B, FutRes, R, F, C, O, S, W>
where
    O::Internal: Send,
    C::Key: Borrow<Q>,
{
    type Item = Result<W::Item, S::Error>;

    fn poll_next(
        self: std::pin::Pin<&mut Self>,
        cx: &mut std::task::Context<'_>,
    ) -> Poll<Option<Self::Item>> {
        let RangeQueryStreamPin {
            bounds,
            mut context,
            map,
            witness,
            ..
        } = self.project();

        if let RangeQueryContextPin::Resolving { fut } = context.as_mut().project() {
            let (got_bounds, storage, mut lower, mut upper) = match std::task::ready!(fut.poll(cx))
            {
                Ok(r) => r,
                Err(e) => {
                    context.set(RangeQueryContext::Dead);
                    return Poll::Ready(Some(Err(e)));
                }
            };

            let bounds = bounds.insert(got_bounds);

            let shared_ancestor = lower
                .path
                .iter()
                .map(|(idx, n)| &n.children.as_ref()[*idx])
                .zip(upper.path.iter().map(|(idx, n)| &n.children.as_ref()[*idx]))
                .enumerate()
                .rev()
                .find_map(|(idx, (lower, upper))| (lower == upper).then_some(idx + 1))
                .unwrap_or(0);

            debug_assert!(
                lower.path[..shared_ancestor]
                    .iter()
                    .zip(&upper.path[..shared_ancestor])
                    .all(|((l_idx, l_node), (u_idx, u_node))| {
                        l_idx == u_idx
                            && l_node.keys.as_ref() == u_node.keys.as_ref()
                            && l_node.children.as_ref() == u_node.children.as_ref()
                    })
            );

            for (_, node) in &lower.path {
                witness.witness_internal(node);
            }

            lower.path.drain(..shared_ancestor);
            upper.path.drain(..shared_ancestor);

            let current_item = leaf_start(&lower.leaf, bounds.start_bound());

            witness.witness_leaf(
                &lower.leaf,
                current_item,
                leaf_end(&lower.leaf, bounds.end_bound()),
                lower.path.is_empty(),
            );

            // by construction, lower.path.len() == upper.path.len(). equality means they are the same node.
            if lower.path.is_empty() {
                context.set(RangeQueryContext::RootOnly {
                    current_item,
                    leaf: lower.leaf,
                });
            } else {
                context.set(RangeQueryContext::ResolvedMultilevel {
                    path: lower.path,
                    current_item,
                    current_leaf: Either::Left((Some(storage), lower.leaf)),
                    upper: Some(upper),
                });
            }
        }

        let bounds = bounds.as_ref().unwrap();

        'poll: loop {
            if let Some(item) = witness.next_item() {
                return Poll::Ready(Some(Ok(item)));
            }

            let (path, current_leaf, current_item, upper) = match context.as_mut().project() {
                RangeQueryContextPin::ResolvedMultilevel {
                    path,
                    current_leaf,
                    current_item,
                    upper,
                } => (path, current_leaf, current_item, upper),
                RangeQueryContextPin::RootOnly { leaf, current_item } => {
                    let idx = *current_item;
                    *current_item += 1;
                    if let Some(key) = leaf.keys.as_ref().get(idx)
                        && bounds.contains(key.borrow())
                    {
                        let item = map(key, &leaf.values.as_ref()[idx]);
                        witness.witness_entry(item);
                    } else {
                        context.set(RangeQueryContext::Dead);
                    }

                    continue 'poll;
                }
                RangeQueryContextPin::Resolving { .. } => unreachable!(),
                RangeQueryContextPin::Dead => return Poll::Ready(None),
            };

            loop {
                if let Either::Right(future) = current_leaf {
                    let node = std::task::ready!(future.poll_unpin(cx));
                    *current_item = 0;
                    *current_leaf = match node {
                        Ok((storage, idx, node, child)) => {
                            path.push((idx, node));
                            match child {
                                TreeNode::Internal(child) => {
                                    witness.witness_internal(&child);

                                    Either::Right(
                                        async move {
                                            storage.get_node(&child.children.as_ref()[0]).await.map(
                                                |new_child| {
                                                    (storage, 0, O::internal(child), new_child)
                                                },
                                            )
                                        }
                                        .boxed(),
                                    )
                                }
                                TreeNode::Leaf(child) => {
                                    witness.witness_leaf(
                                        &child,
                                        leaf_start(&child, bounds.start_bound()),
                                        leaf_end(&child, bounds.end_bound()),
                                        upper.as_ref().is_some_and(|u| {
                                            u.path.len() == path.len()
                                                && u.path
                                                    .iter()
                                                    .zip(path.iter())
                                                    .all(|(u, p)| u.0 == p.0)
                                        }),
                                    );

                                    Either::Left((Some(storage), O::leaf(child)))
                                }
                            }
                        }
                        Err(e) => {
                            context.set(RangeQueryContext::Dead);
                            return Poll::Ready(Some(Err(e)));
                        }
                    };
                    continue;
                }

                let Either::Left((storage, leaf)) = current_leaf else {
                    continue;
                };

                let Some(key) = leaf.keys.as_ref().get(*current_item) else {
                    while let Some((idx, node)) = path.last_mut() {
                        *idx += 1;
                        if node.children.as_ref().get(*idx).is_some() {
                            break;
                        }
                        path.pop();
                    }

                    *current_item = 0;

                    let took_upper = upper.take_if(|u| {
                        u.path.len() == path.len()
                            && u.path
                                .iter()
                                .map(|(idx, n)| &n.children.as_ref()[*idx])
                                .zip(path.iter().map(|(idx, n)| &n.children.as_ref()[*idx]))
                                .all(|(u, p)| u == p)
                    });

                    if let Some(u) = took_upper {
                        witness.witness_leaf(
                            &u.leaf,
                            leaf_start(&u.leaf, bounds.start_bound()),
                            leaf_end(&u.leaf, bounds.end_bound()),
                            true,
                        );

                        *path = u.path;
                        *current_leaf = Either::Left((storage.take(), u.leaf));
                    } else if let Some((idx, node)) = path.pop() {
                        let storage = storage.take().unwrap();
                        *current_leaf = Either::Right(
                            async move {
                                storage
                                    .get_node(&node.children.as_ref()[idx])
                                    .await
                                    .map(|child| (storage, idx, node, child))
                            }
                            .boxed(),
                        );
                    } else {
                        context.set(RangeQueryContext::Dead);
                        continue 'poll;
                    }

                    continue;
                };

                if !bounds.contains(key.borrow()) {
                    context.set(RangeQueryContext::Dead);
                    continue 'poll;
                }

                let item = map(key, &leaf.values.as_ref()[*current_item]);
                *current_item += 1;
                witness.witness_entry(item);
                continue 'poll;
            }
        }
    }
}

/// An item of a proven range, that is either an entry or a proof node.
#[derive_where(Debug; R, RangeProofNode<C>)]
#[derive_where(Clone; R)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(
    feature = "serde",
    serde(bound(
        serialize = "R: serde::Serialize, RangeProofNode<C>: serde::Serialize",
        deserialize = "R: serde::Deserialize<'de>, RangeProofNode<C>: serde::Deserialize<'de>"
    ))
)]
pub enum RangeItem<C: TreeConfig, R> {
    /// An entry within a leaf,
    Entry(R),
    /// A proof node.
    Node(RangeProofNode<C>),
}

/// A range proof's node.
#[derive_where(Debug; C::Key, HasherOutput<C>)]
#[derive_where(Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(
    feature = "serde",
    serde(bound(
        serialize = "C::Key: serde::Serialize, HasherOutput<C>: serde::Serialize",
        deserialize = "C::Key: serde::Deserialize<'de>, HasherOutput<C>: serde::Deserialize<'de>"
    ))
)]
pub enum RangeProofNode<C: TreeConfig> {
    /// An internal node.
    Internal {
        /// The separator keys.
        keys: Box<[C::Key]>,
        /// The hashes of the children.
        children: Box<[HasherOutput<C>]>,
    },
    /// A leaf node. Entries inside of the range are not present, they are provided by the queried stream.
    Leaf {
        /// The entries preceding the range, as key and value hash pairs.
        before: Box<[(C::Key, HasherOutput<C>)]>,
        /// The amount of entries of this leaf that lie within the range.
        inside: usize,
        /// The entries following the range, as key and value hash pairs.
        after: Box<[(C::Key, HasherOutput<C>)]>,
    },
}

pub(crate) struct RangeProofEmitter<C: TreeConfig, R> {
    queue: VecDeque<RangeItem<C, R>>,
    finished: bool,
}

impl<C: TreeConfig, R> RangeProofEmitter<C, R> {
    pub(crate) fn new() -> Self {
        Self {
            queue: VecDeque::new(),
            finished: false,
        }
    }
}

impl<C: TreeConfig, R> RangeQueryWitness<C, R> for RangeProofEmitter<C, R> {
    type Item = RangeItem<C, R>;

    fn witness_internal(&mut self, node: &TreeInternalNode<C>) {
        if !self.finished {
            self.queue
                .push_back(RangeItem::Node(RangeProofNode::Internal {
                    keys: node.keys.as_ref().into(),
                    children: node.children.as_ref().into(),
                }));
        }
    }

    fn witness_leaf(&mut self, leaf: &TreeLeafNode<C>, start: usize, end: usize, last: bool) {
        if self.finished {
            return;
        }

        let keys = leaf.keys.as_ref();
        let values = leaf.values.as_ref();
        let end = end.max(start);

        let hashed = |from: usize, to: usize| {
            keys[from..to]
                .iter()
                .zip(&values[from..to])
                .map(|(k, v)| (k.clone(), C::Hasher::hash_value(v)))
                .into_boxed_slice()
        };

        self.queue.push_back(RangeItem::Node(RangeProofNode::Leaf {
            before: hashed(0, start),
            inside: end - start,
            after: hashed(end, keys.len()),
        }));
        self.finished = last;
    }

    fn witness_entry(&mut self, entry: R) {
        self.queue.push_back(RangeItem::Entry(entry));
    }

    fn next_item(&mut self) -> Option<Self::Item> {
        self.queue.pop_front()
    }
}

fn is_empty_range<Q: Ord + ?Sized>(range: &impl RangeBounds<Q>) -> bool {
    match (range.start_bound(), range.end_bound()) {
        (Bound::Included(start), Bound::Included(end)) => start > end,
        #[expect(clippy::unnested_or_patterns)]
        (Bound::Included(start), Bound::Excluded(end))
        | (Bound::Excluded(start), Bound::Included(end))
        | (Bound::Excluded(start), Bound::Excluded(end)) => start >= end,
        _ => false,
    }
}

struct VerifyFrame<C: TreeConfig> {
    keys: Box<[C::Key]>,
    children: Box<[HasherOutput<C>]>,
    lower: Option<C::Key>,
    upper: Option<C::Key>,
    next: usize,
    base: usize,
}

/// Verifies that `entries` are exactly the entries within `range` of the tree `expected_root` represents.
///
/// The entries must be provided in ascending key order and are consumed as they arrive.
pub async fn verify_range<C: TreeConfig, Q: Ord + ?Sized, K: Borrow<C::Key>, V: Borrow<C::Value>>(
    expected_root: &HasherOutput<C>,
    range: impl RangeBounds<Q>,
    items: impl Stream<Item = RangeItem<C, (K, V)>>,
) -> Result<(), InvalidProofError>
where
    C::Key: Borrow<Q>,
{
    let mut items = std::pin::pin!(items);

    if is_empty_range(&range) {
        return match items.next().await {
            None => Ok(()),
            Some(_) => Err(InvalidProofError),
        };
    }

    let mut stack = vec![];
    let mut buf = vec![];
    let mut bounds = (None, None);
    let mut done = None;

    while let Some(item) = items.next().await {
        if done.is_some() {
            return Err(InvalidProofError);
        }

        let RangeItem::Node(node) = item else {
            return Err(InvalidProofError);
        };

        match node {
            RangeProofNode::Internal { keys, children } => {
                if keys.len() + 1 != children.len() {
                    return Err(InvalidProofError);
                }

                stack.push(VerifyFrame::<C> {
                    keys,
                    children,
                    lower: bounds.0.take(),
                    upper: bounds.1.take(),
                    next: 0,
                    base: buf.len(),
                });
            }
            RangeProofNode::Leaf {
                before,
                inside,
                after,
            } => {
                let base = buf.len();

                for (key, value_hash) in &before {
                    if (range.start_bound(), Bound::Unbounded).contains(key.borrow()) {
                        return Err(InvalidProofError);
                    }
                    buf.push(C::Hasher::hash_key(key));
                    buf.push(value_hash.clone());
                }

                for _ in 0..inside {
                    let Some(RangeItem::Entry((key, value))) = items.next().await else {
                        return Err(InvalidProofError);
                    };

                    let key = key.borrow();
                    let value = value.borrow();
                    if !range.contains(key.borrow()) {
                        return Err(InvalidProofError);
                    }

                    buf.push(C::Hasher::hash_key(key));
                    buf.push(C::Hasher::hash_value(value));
                }

                for (key, value_hash) in &after {
                    if (Bound::Unbounded, range.end_bound()).contains(key.borrow()) {
                        return Err(InvalidProofError);
                    }

                    buf.push(C::Hasher::hash_key(key));
                    buf.push(value_hash.clone());
                }

                let count = (buf.len() - base) >> 1usize;
                let entries_root = merkle_root_in_place::<C>(&mut buf, base);
                done = Some(C::Hasher::hash_leaf(count, &entries_root));
            }
        }

        while let Some(frame) = stack.last_mut() {
            if let Some(hash) = done.take() {
                if hash != frame.children[frame.next] {
                    return Err(InvalidProofError);
                }

                buf.push(if frame.next == 0 {
                    hash
                } else {
                    C::Hasher::hash_slot(&frame.keys[frame.next - 1], &hash)
                });
                frame.next += 1;
            }

            while frame.next < frame.children.len() {
                let lower = if let Some(idx) = frame.next.checked_sub(1) {
                    Some(&frame.keys[idx])
                } else {
                    frame.lower.as_ref()
                };
                let upper = frame.keys.get(frame.next).or(frame.upper.as_ref());

                let below = matches!(
                    (upper, range.start_bound()),
                    (Some(upper), Bound::Included(start) | Bound::Excluded(start))
                        if upper.borrow() <= start
                );
                let above = match (lower, range.end_bound()) {
                    (Some(lower), Bound::Included(end)) => lower.borrow() > end,
                    (Some(lower), Bound::Excluded(end)) => lower.borrow() >= end,
                    _ => false,
                };

                if !below && !above {
                    bounds = (lower.cloned(), upper.cloned());
                    break;
                }

                buf.push(if frame.next == 0 {
                    frame.children[0].clone()
                } else {
                    C::Hasher::hash_slot(&frame.keys[frame.next - 1], &frame.children[frame.next])
                });

                frame.next += 1;
            }

            if frame.next < frame.children.len() {
                break;
            }

            let frame = stack.pop().unwrap();
            let slots_root = merkle_root_in_place::<C>(&mut buf, frame.base);
            done = Some(C::Hasher::hash_internal(frame.children.len(), &slots_root));
        }
    }

    let root = done.ok_or(InvalidProofError)?;
    if root != *expected_root {
        return Err(InvalidProofError);
    }

    Ok(())
}

fn leaf_start<C: TreeConfig, Q: Ord + ?Sized>(leaf: &TreeLeafNode<C>, lower: Bound<&Q>) -> usize
where
    C::Key: Borrow<Q>,
{
    let keys = leaf.keys.as_ref();
    match lower {
        Bound::Included(key) => keys.partition_point(|k| k.borrow() < key),
        Bound::Excluded(key) => keys.partition_point(|k| k.borrow() <= key),
        Bound::Unbounded => 0,
    }
}

fn leaf_end<C: TreeConfig, Q: Ord + ?Sized>(leaf: &TreeLeafNode<C>, upper: Bound<&Q>) -> usize
where
    C::Key: Borrow<Q>,
{
    let keys = leaf.keys.as_ref();
    match upper {
        Bound::Included(key) => keys.partition_point(|k| k.borrow() <= key),
        Bound::Excluded(key) => keys.partition_point(|k| k.borrow() < key),
        Bound::Unbounded => keys.len(),
    }
}

pub(crate) fn range_impl<
    'a,
    C: TreeConfig,
    O: NodeOwner<C> + 'a,
    S: ReadNodeStorage<C> + Send + Sync + 'a,
    Q: Ord + ?Sized + 'a,
    B: RangeBounds<Q>,
    R,
    M: Fn(&C::Key, &C::Value) -> R,
    W: RangeQueryWitness<C, R>,
>(
    storage: S,
    root: RootTreeNode<C, O>,
    range: B,
    map: M,
    mut witness: W,
) -> impl Stream<Item = Result<W::Item, S::Error>>
where
    O::Internal: Clone + Send,
    C::Key: Borrow<Q>,
{
    if is_empty_range(&range) {
        return RangeQueryStreamImpl {
            context: RangeQueryContext::Dead,
            bounds: Some(range),
            map,
            witness,
            _phantom: PhantomData,
        };
    }

    let root = match root {
        RootTreeNode::Internal(root) => root,
        RootTreeNode::Leaf(node) => {
            let current_item = leaf_start(&node, range.start_bound());

            witness.witness_leaf(
                &node,
                current_item,
                leaf_end(&node, range.end_bound()),
                true,
            );

            return RangeQueryStreamImpl {
                context: RangeQueryContext::RootOnly {
                    current_item,
                    leaf: node,
                },
                bounds: Some(range),
                map,
                witness,
                _phantom: PhantomData,
            };
        }
    };

    macro_rules! bound {
        ($root:expr, $bound:expr, $included:ident, $excluded:ident, $unbounded:literal) => {
            match $bound {
                Bound::Included(key) => {
                    Either::Left(bound!(search $root, | k | k.borrow().$included(key)))
                }
                Bound::Excluded(key) => {
                    Either::Right(Either::Left(bound!(search $root, | k | k.borrow().$excluded(key))))
                }
                Bound::Unbounded => Either::Right(Either::Right(bound!(search $root, | _ | $unbounded))),
            }
        };
        (search $root:expr, $expr:expr) => {
            TreeInternalNode::leaf_search::<true, _, O>($root, &storage, $expr)
        };
    }

    RangeQueryStreamImpl {
        bounds: None,
        context: RangeQueryContext::Resolving {
            fut: async move {
                let lower = bound!(root.clone(), range.start_bound(), le, le, false);
                let upper = bound!(root, range.end_bound(), le, lt, true);

                try_join(lower, upper)
                    .await
                    .map(|(l, u)| (range, storage, l, u))
            },
        },
        map,
        witness,
        _phantom: PhantomData,
    }
}

#[cfg(test)]
mod tests {
    use std::ops::{Bound, RangeBounds as _};

    use futures_util::{TryStreamExt as _, stream};

    use super::{RangeItem, RangeProofNode, verify_range};
    use crate::hasher::Hasher as _;
    use crate::tests::{
        Blake3Hasher, TestConfig, TestTree, all_test_shapers, corrupt, filled_tree,
        filled_tree_with_shaper, insert_orders, new_tree, value_for,
    };

    type Item = RangeItem<TestConfig, (u64, String)>;
    type Bounds = (Bound<u64>, Bound<u64>);

    async fn collect_range<Q>(
        tree: &TestTree,
        range: impl std::ops::RangeBounds<Q>,
    ) -> Vec<(u64, String)>
    where
        Q: Ord + ?Sized,
        u64: std::borrow::Borrow<Q>,
    {
        tree.range(range).try_collect().await.unwrap()
    }

    #[tokio::test]
    async fn range_on_empty_tree_is_empty() {
        let tree = new_tree(5, 4);
        let out = collect_range(&tree, 0u64..100).await;
        assert!(out.is_empty());
    }

    #[tokio::test]
    async fn range_on_single_leaf_tree_matches_oracle() {
        let tree = filled_tree(5, 4, 0..3u64).await;

        let out = collect_range(&tree, 0u64..3).await;
        assert_eq!(
            out,
            vec![
                (0, "v0".to_string()),
                (1, "v1".to_string()),
                (2, "v2".to_string()),
            ]
        );
    }

    #[tokio::test]
    async fn range_respects_inclusive_and_exclusive_bounds() {
        let tree = filled_tree(4, 3, 0..20u64).await;

        let inclusive = collect_range(&tree, 5u64..=10).await;
        assert_eq!(
            inclusive.iter().map(|(k, _)| *k).collect::<Vec<_>>(),
            (5..=10).collect::<Vec<_>>()
        );

        let exclusive_start =
            collect_range(&tree, (Bound::Excluded(5u64), Bound::Included(10u64))).await;
        assert_eq!(
            exclusive_start.iter().map(|(k, _)| *k).collect::<Vec<_>>(),
            (6..=10).collect::<Vec<_>>()
        );

        let exclusive_end = collect_range(&tree, 5u64..10).await;
        assert_eq!(
            exclusive_end.iter().map(|(k, _)| *k).collect::<Vec<_>>(),
            (5..10).collect::<Vec<_>>()
        );
    }

    #[tokio::test]
    async fn range_with_unbounded_start_or_end_matches_oracle() {
        let tree = filled_tree(4, 3, 0..30u64).await;

        let from_start = collect_range(&tree, ..15u64).await;
        assert_eq!(
            from_start.iter().map(|(k, _)| *k).collect::<Vec<_>>(),
            (0..15).collect::<Vec<_>>()
        );

        let to_end = collect_range(&tree, 15u64..).await;
        assert_eq!(
            to_end.iter().map(|(k, _)| *k).collect::<Vec<_>>(),
            (15..30).collect::<Vec<_>>()
        );

        let full = collect_range(&tree, ..).await;
        assert_eq!(full.len(), 30);
    }

    #[tokio::test]
    async fn range_returns_empty_when_bounds_exclude_everything() {
        let tree = filled_tree(4, 3, 0..10u64).await;

        let below = collect_range(&tree, 100u64..200).await;
        assert!(below.is_empty());

        let above = collect_range(&tree, ..0u64).await;
        assert!(above.is_empty());

        let empty = collect_range(&tree, 5u64..5).await;
        assert!(empty.is_empty());
    }

    #[tokio::test]
    async fn range_spanning_multiple_leaves_matches_oracle_across_shapers_and_sizes() {
        for s in all_test_shapers() {
            for n in [1u64, 2, 3, 5, 8, 13, 50] {
                let tree = filled_tree_with_shaper(s, 0..n).await;

                let out = collect_range(&tree, ..).await;
                let expected: Vec<_> = (0..n).map(|k| (k, value_for(k))).collect();
                assert_eq!(out, expected, "shaper={s:?} n={n}: full range mismatch");

                if n >= 2 {
                    #[expect(clippy::integer_division)]
                    let lo = n / 4;
                    #[expect(clippy::integer_division)]
                    let hi = (3 * n / 4).max(lo + 1).min(n);
                    let out = collect_range(&tree, lo..hi).await;
                    let expected: Vec<_> = (lo..hi).map(|k| (k, value_for(k))).collect();
                    assert_eq!(
                        out, expected,
                        "shaper={s:?} n={n}: partial range [{lo}, {hi}) mismatch",
                    );
                }
            }
        }
    }

    #[tokio::test]
    async fn range_matches_oracle_regardless_of_insertion_order() {
        const N: u64 = 100;
        for (label, order) in insert_orders(N) {
            let tree = filled_tree(4, 3, order).await;

            let out = collect_range(&tree, 10u64..90).await;
            let expected: Vec<_> = (10..90).map(|k| (k, value_for(k))).collect();
            assert_eq!(out, expected, "insert_order={label}: range mismatch");
        }
    }

    #[tokio::test]
    async fn range_after_deletes_reflects_current_state() {
        let mut tree = filled_tree(4, 3, 0..40u64).await;
        for k in (0..40u64).step_by(3) {
            tree.delete(&k).await.unwrap();
        }

        let out = collect_range(&tree, ..).await;
        let expected: Vec<_> = (0..40u64)
            .filter(|k| k % 3 != 0)
            .map(|k| (k, value_for(k)))
            .collect();
        assert_eq!(out, expected);
    }

    #[tokio::test]
    async fn range_single_key_bounds_selects_exactly_one_or_none() {
        let tree = filled_tree(4, 3, 0..20u64).await;

        let hit = collect_range(&tree, 7u64..=7).await;
        assert_eq!(hit, vec![(7, "v7".to_string())]);

        let miss_excluded =
            collect_range(&tree, (Bound::Excluded(7u64), Bound::Included(7u64))).await;
        assert!(miss_excluded.is_empty());
    }

    async fn proven(tree: &TestTree, range: Bounds) -> Vec<Item> {
        tree.proven_range(range).try_collect().await.unwrap()
    }

    fn entries_of(items: &[Item]) -> Vec<(u64, String)> {
        items
            .iter()
            .filter_map(|i| match i {
                RangeItem::Entry(e) => Some(e.clone()),
                RangeItem::Node(_) => None,
            })
            .collect()
    }

    fn entry_positions(items: &[Item]) -> Vec<usize> {
        items
            .iter()
            .enumerate()
            .filter_map(|(i, it)| matches!(it, RangeItem::Entry(_)).then_some(i))
            .collect()
    }

    async fn verifies(items: &[Item], root: &[u8; 32], range: Bounds) -> bool {
        verify_range(root, range, stream::iter(items.iter().cloned()))
            .await
            .is_ok()
    }

    fn bounds_for(n: u64) -> Vec<Bounds> {
        let lo = n >> 2u64;
        let hi = n - (n >> 2u64);
        vec![
            (Bound::Unbounded, Bound::Unbounded),
            (Bound::Included(lo), Bound::Unbounded),
            (Bound::Excluded(lo), Bound::Unbounded),
            (Bound::Unbounded, Bound::Included(hi)),
            (Bound::Unbounded, Bound::Excluded(hi)),
            (Bound::Included(lo), Bound::Included(hi)),
            (Bound::Included(lo), Bound::Excluded(hi)),
            (Bound::Excluded(lo), Bound::Included(hi)),
            (Bound::Excluded(lo), Bound::Excluded(hi)),
            (Bound::Included(n), Bound::Unbounded),
            (Bound::Included(n + 5), Bound::Included(n + 10)),
            (Bound::Included(hi), Bound::Included(lo)),
        ]
    }

    #[tokio::test]
    async fn range_proof_verifies_across_shapers_sizes_and_bounds() {
        for s in all_test_shapers() {
            for n in [0u64, 1, 2, 3, 5, 8, 13, 50] {
                let tree = filled_tree_with_shaper(s, 0..n).await;
                let root = tree.root_hash();

                for bounds in bounds_for(n) {
                    let items = proven(&tree, bounds).await;
                    let expected: Vec<_> = (0..n)
                        .filter(|k| bounds.contains(k))
                        .map(|k| (k, value_for(k)))
                        .collect();
                    assert_eq!(
                        entries_of(&items),
                        expected,
                        "shaper={s:?} n={n} bounds={bounds:?}: entries mismatch"
                    );
                    assert!(
                        verifies(&items, &root, bounds).await,
                        "shaper={s:?} n={n} bounds={bounds:?}: range proof failed to verify",
                    );
                }
            }
        }
    }

    #[tokio::test]
    async fn range_proof_verifies_after_deletes_regardless_of_insertion_order() {
        const N: u64 = 100;
        for (label, order) in insert_orders(N) {
            let mut tree = filled_tree(4, 3, order).await;
            for k in (0..N).step_by(3) {
                tree.delete(&k).await.unwrap();
            }
            let root = tree.root_hash();

            let bounds = (Bound::Included(10u64), Bound::Excluded(90u64));
            let items = proven(&tree, bounds).await;
            let expected: Vec<_> = (10..90)
                .filter(|k| k % 3 != 0)
                .map(|k| (k, value_for(k)))
                .collect();
            assert_eq!(entries_of(&items), expected, "insert_order={label}");
            assert!(
                verifies(&items, &root, bounds).await,
                "insert_order={label}: range proof failed to verify",
            );
        }
    }

    #[tokio::test]
    async fn range_proof_rejects_tampered_entries() {
        let tree = filled_tree(4, 3, 0..40u64).await;
        let root = tree.root_hash();
        let bounds = (Bound::Included(7u64), Bound::Excluded(31u64));
        let items = proven(&tree, bounds).await;
        assert!(verifies(&items, &root, bounds).await);

        let positions = entry_positions(&items);

        for (n, &pos) in positions.iter().enumerate() {
            let mut dropped = items.clone();
            dropped.remove(pos);
            assert!(
                !verifies(&dropped, &root, bounds).await,
                "dropping entry {n} must invalidate",
            );
        }

        let mut extra = items.clone();
        extra.insert(
            positions[positions.len() - 1] + 1,
            RangeItem::Entry((1000, "extra".to_string())),
        );
        assert!(!verifies(&extra, &root, bounds).await);

        let mut trailing = items.clone();
        trailing.push(RangeItem::Entry((1000, "extra".to_string())));
        assert!(!verifies(&trailing, &root, bounds).await);

        let mut modified = items.clone();
        if let RangeItem::Entry((_, v)) = &mut modified[positions[3]] {
            v.push('x');
        }
        assert!(!verifies(&modified, &root, bounds).await);

        let mut reordered = items.clone();
        reordered.swap(positions[0], positions[1]);
        assert!(!verifies(&reordered, &root, bounds).await);

        let mut all = Vec::new();
        all.extend(
            items
                .iter()
                .filter(|i| matches!(i, RangeItem::Node(_)))
                .cloned(),
        );
        all.extend((0..40u64).map(|k| RangeItem::Entry((k, value_for(k)))));
        assert!(!verifies(&all, &root, bounds).await);
    }

    #[tokio::test]
    async fn range_proof_rejects_wrong_root_and_other_trees() {
        let mut tree_a = new_tree(4, 3);
        let mut tree_b = new_tree(4, 3);
        for k in 0..40u64 {
            tree_a.insert(k, value_for(k)).await.unwrap();
            tree_b.insert(k, format!("other-{k}")).await.unwrap();
        }
        let root_a = tree_a.root_hash();
        let root_b = tree_b.root_hash();
        let bounds = (Bound::Included(7u64), Bound::Excluded(31u64));
        let items = proven(&tree_a, bounds).await;
        assert!(verifies(&items, &root_a, bounds).await);
        assert!(!verifies(&items, &root_b, bounds).await);

        let mut bad_root = root_a;
        corrupt(&mut bad_root);
        assert!(!verifies(&items, &bad_root, bounds).await);
    }

    #[tokio::test]
    async fn range_proof_rejects_tampered_proof() {
        let tree = filled_tree(4, 3, 0..40u64).await;
        let root = tree.root_hash();
        let bounds = (Bound::Included(7u64), Bound::Excluded(31u64));
        let items = proven(&tree, bounds).await;

        let mut corrupted = items.clone();
        for item in &mut corrupted {
            if let RangeItem::Node(RangeProofNode::Internal { children, .. }) = item {
                corrupt(&mut children[0]);
                break;
            }
        }
        assert!(!verifies(&corrupted, &root, bounds).await);

        let mut hidden = items.clone();
        let pos = hidden
            .iter()
            .position(|i| {
                matches!(i, RangeItem::Node(RangeProofNode::Leaf { inside, .. }) if *inside > 0)
            })
            .unwrap();
        let RangeItem::Entry((k, v)) = hidden.remove(pos + 1) else {
            panic!("an entry must directly follow a leaf node with inside > 0");
        };
        if let RangeItem::Node(RangeProofNode::Leaf { before, inside, .. }) = &mut hidden[pos] {
            let mut moved = std::mem::take(before).into_vec();
            moved.push((k, Blake3Hasher::hash_value(&v)));
            *before = moved.into_boxed_slice();
            *inside -= 1;
        }
        assert!(!verifies(&hidden, &root, bounds).await);

        let mut truncated = items.clone();
        let last_node = truncated
            .iter()
            .rposition(|i| matches!(i, RangeItem::Node(_)))
            .unwrap();
        truncated.truncate(last_node);
        assert!(!verifies(&truncated, &root, bounds).await);

        let mut cut_short = items.clone();
        cut_short.pop();
        assert!(!verifies(&cut_short, &root, bounds).await);

        let mut padded = items.clone();
        padded.push(items[0].clone());
        assert!(!verifies(&padded, &root, bounds).await);
    }

    #[tokio::test]
    async fn range_proof_for_empty_range_only_accepts_empty_stream() {
        let tree = filled_tree(4, 3, 0..20u64).await;
        let root = tree.root_hash();
        let bounds = (Bound::Included(5u64), Bound::Excluded(5u64));
        let items = proven(&tree, bounds).await;
        assert!(items.is_empty());
        assert!(verifies(&items, &root, bounds).await);
        assert!(!verifies(&[RangeItem::Entry((5, "v5".to_string()))], &root, bounds).await);
    }
}
