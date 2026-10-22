//! Range queries.

use std::{
    borrow::Borrow,
    marker::PhantomData,
    ops::{Bound, RangeBounds},
    pin::Pin,
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
        W: RangeQueryWitness<C, O>,
    {
        bounds: Option<B>,
        #[pin]
        context: RangeQueryContext<'a, FutRes, C, O, S>,
        map: F,
        witness: W,
        _phantom: PhantomData<(R, Q)>,
    }
}

pub(crate) trait RangeQueryWitness<C: TreeConfig, O: NodeOwner<C>> {
    fn witness_internal(&mut self, node: &TreeInternalNode<C>);

    fn witness_leaf(&mut self, leaf: &TreeLeafNode<C>, start: usize, end: usize, last: bool);

    fn get_proof(&mut self) -> RangeProof<C>;
}

impl<C: TreeConfig, O: NodeOwner<C>> RangeQueryWitness<C, O> for () {
    fn witness_internal(&mut self, _node: &TreeInternalNode<C>) {}

    fn witness_leaf(&mut self, _leaf: &TreeLeafNode<C>, _start: usize, _end: usize, _last: bool) {}

    fn get_proof(&mut self) -> RangeProof<C> {
        // GetRangeProof isn't exposed on unproven queries through the API
        unreachable!()
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
    W: RangeQueryWitness<C, O>,
> Stream for RangeQueryStreamImpl<'a, Q, B, FutRes, R, F, C, O, S, W>
where
    O::Internal: Send,
    C::Key: Borrow<Q>,
{
    type Item = Result<R, S::Error>;

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
                Err(e) => return Poll::Ready(Some(Err(e))),
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

        match context.as_mut().project() {
            RangeQueryContextPin::ResolvedMultilevel {
                path,
                current_leaf,
                current_item,
                upper,
            } => loop {
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
                        Err(e) => return Poll::Ready(Some(Err(e))),
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
                        return Poll::Ready(None);
                    }

                    continue;
                };

                if !bounds.contains(key.borrow()) {
                    context.set(RangeQueryContext::Dead);
                    return Poll::Ready(None);
                }

                let item = map(key, &leaf.values.as_ref()[*current_item]);
                *current_item += 1;
                return Poll::Ready(Some(Ok(item)));
            },
            RangeQueryContextPin::RootOnly { leaf, current_item } => {
                let idx = *current_item;
                *current_item += 1;
                if let Some(key) = leaf.keys.as_ref().get(idx)
                    && bounds.contains(key.borrow())
                {
                    let item = map(key, &leaf.values.as_ref()[idx]);
                    return Poll::Ready(Some(Ok(item)));
                }

                context.set(RangeQueryContext::Dead);
                Poll::Ready(None)
            }
            RangeQueryContextPin::Resolving { .. } => Poll::Pending,
            RangeQueryContextPin::Dead => Poll::Ready(None),
        }
    }
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

/// A proof over a queried range of values.
#[derive_where(Debug; RangeProofNode<C>)]
#[derive_where(Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(
    feature = "serde",
    serde(bound(
        serialize = "RangeProofNode<C>: serde::Serialize",
        deserialize = "RangeProofNode<C>: serde::Deserialize<'de>"
    ))
)]
pub struct RangeProof<C: TreeConfig> {
    /// The nodes of the tree that overlap the range, in depth-first order.
    pub nodes: Box<[RangeProofNode<C>]>,
}

struct VerifyFrame<'a, C: TreeConfig> {
    keys: &'a [C::Key],
    children: &'a [HasherOutput<C>],
    lower: Option<&'a C::Key>,
    upper: Option<&'a C::Key>,
    next: usize,
    base: usize,
}

impl<C: TreeConfig> RangeProof<C> {
    /// Verifies that `entries` are exactly the entries within `range` of the tree `expected_root` represents.
    ///
    /// The entries must be provided in ascending key order and are consumed as they arrive, never retained.
    pub async fn verify<Q, K, V>(
        &self,
        expected_root: &HasherOutput<C>,
        range: impl RangeBounds<Q>,
        entries: impl Stream<Item = (K, V)>,
    ) -> Result<(), InvalidProofError>
    where
        Q: Ord + ?Sized,
        C::Key: Borrow<Q>,
        K: Borrow<C::Key>,
        V: Borrow<C::Value>,
    {
        let mut entries = std::pin::pin!(entries);

        let empty = match (range.start_bound(), range.end_bound()) {
            (Bound::Included(start), Bound::Included(end)) => start > end,
            #[expect(clippy::unnested_or_patterns)]
            (Bound::Included(start), Bound::Excluded(end))
            | (Bound::Excluded(start), Bound::Included(end))
            | (Bound::Excluded(start), Bound::Excluded(end)) => start >= end,
            _ => false,
        };
        if empty {
            return match entries.next().await {
                None => Ok(()),
                Some(_) => Err(InvalidProofError),
            };
        }

        let mut stack: Vec<VerifyFrame<'_, C>> = vec![];
        let mut buf = vec![];
        let mut bounds = (None, None);
        let mut done = None;

        for node in &self.nodes {
            if done.is_some() {
                return Err(InvalidProofError);
            }

            match node {
                RangeProofNode::Internal { keys, children } => {
                    if keys.len() + 1 != children.len() {
                        return Err(InvalidProofError);
                    }

                    stack.push(VerifyFrame {
                        keys,
                        children,
                        lower: bounds.0,
                        upper: bounds.1,
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

                    for (key, value_hash) in before {
                        if (range.start_bound(), Bound::Unbounded).contains(key.borrow()) {
                            return Err(InvalidProofError);
                        }
                        buf.push(C::Hasher::hash_key(key));
                        buf.push(value_hash.clone());
                    }

                    for _ in 0..*inside {
                        let Some((key, value)) = entries.next().await else {
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

                    for (key, value_hash) in after {
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
                        frame.lower
                    };
                    let upper = frame.keys.get(frame.next).or(frame.upper);

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
                        bounds = (lower, upper);
                        break;
                    }

                    buf.push(if frame.next == 0 {
                        frame.children[0].clone()
                    } else {
                        C::Hasher::hash_slot(
                            &frame.keys[frame.next - 1],
                            &frame.children[frame.next],
                        )
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
        if root != *expected_root || entries.next().await.is_some() {
            return Err(InvalidProofError);
        }

        Ok(())
    }
}

/// A trait which allows getting a proof of a range query.
pub trait GetRangeProof<C: TreeConfig> {
    /// Returns the proof built after evaluating the stream's entire contents.
    ///
    /// Must be called after all values have been processed (next returns None),
    /// otherwise it may return invalid values. In debug builds, this will panic.
    /// Calling this more than once returns an empty proof.
    fn get_proof(self: Pin<&mut Self>) -> RangeProof<C>;
}

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
    W: RangeQueryWitness<C, O>,
> GetRangeProof<C> for RangeQueryStreamImpl<'a, Q, B, FutRes, R, F, C, O, S, W>
where
    O::Internal: Send,
    C::Key: Borrow<Q>,
{
    fn get_proof(self: Pin<&mut Self>) -> RangeProof<C> {
        let RangeQueryStreamPin {
            context, witness, ..
        } = self.project();

        debug_assert!(
            matches!(context.as_ref().get_ref(), RangeQueryContext::Dead),
            "GetRangeProof::get_proof called on an in-progress stream"
        );

        witness.get_proof()
    }
}

#[derive_where(Default)]
pub(crate) struct RangeProofBuilder<C: TreeConfig> {
    nodes: Vec<RangeProofNode<C>>,
    finished: bool,
}

impl<C: TreeConfig, O: NodeOwner<C>> RangeQueryWitness<C, O> for RangeProofBuilder<C> {
    fn witness_internal(&mut self, node: &TreeInternalNode<C>) {
        if !self.finished {
            self.nodes.push(RangeProofNode::Internal {
                keys: node.keys.as_ref().into(),
                children: node.children.as_ref().into(),
            });
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

        self.nodes.push(RangeProofNode::Leaf {
            before: hashed(0, start),
            inside: end - start,
            after: hashed(end, keys.len()),
        });
        self.finished = last;
    }

    fn get_proof(&mut self) -> RangeProof<C> {
        RangeProof {
            nodes: std::mem::take(&mut self.nodes).into_boxed_slice(),
        }
    }
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
    W: RangeQueryWitness<C, O>,
>(
    storage: S,
    root: RootTreeNode<C, O>,
    range: B,
    map: M,
    mut witness: W,
) -> impl Stream<Item = Result<R, S::Error>> + GetRangeProof<C>
where
    O::Internal: Clone + Send,
    C::Key: Borrow<Q>,
{
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

    use super::{GetRangeProof as _, RangeProof, RangeProofNode};
    use crate::hasher::Hasher as _;
    use crate::tests::{
        Blake3Hasher, TestConfig, TestTree, all_test_shapers, corrupt, filled_tree,
        filled_tree_with_shaper, insert_orders, new_tree, value_for,
    };

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

    async fn proven(
        tree: &TestTree,
        range: (Bound<u64>, Bound<u64>),
    ) -> (Vec<(u64, String)>, RangeProof<TestConfig>) {
        let mut query = std::pin::pin!(tree.proven_range(range));
        let entries = query.as_mut().try_collect::<Vec<_>>().await.unwrap();
        (entries, query.as_mut().get_proof())
    }

    async fn verifies(
        proof: &RangeProof<TestConfig>,
        root: &[u8; 32],
        range: (Bound<u64>, Bound<u64>),
        entries: &[(u64, String)],
    ) -> bool {
        proof
            .verify(
                root,
                range,
                stream::iter(entries.iter().map(|(k, v)| (k, v))),
            )
            .await
            .is_ok()
    }

    fn bounds_for(n: u64) -> Vec<(Bound<u64>, Bound<u64>)> {
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
                    let (entries, proof) = proven(&tree, bounds).await;
                    let expected: Vec<_> = (0..n)
                        .filter(|k| bounds.contains(k))
                        .map(|k| (k, value_for(k)))
                        .collect();
                    assert_eq!(
                        entries, expected,
                        "shaper={s:?} n={n} bounds={bounds:?}: entries mismatch"
                    );
                    assert!(
                        verifies(&proof, &root, bounds, &entries).await,
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
            let (entries, proof) = proven(&tree, bounds).await;
            let expected: Vec<_> = (10..90)
                .filter(|k| k % 3 != 0)
                .map(|k| (k, value_for(k)))
                .collect();
            assert_eq!(entries, expected, "insert_order={label}");
            assert!(
                verifies(&proof, &root, bounds, &entries).await,
                "insert_order={label}: range proof failed to verify",
            );
        }
    }

    #[tokio::test]
    async fn range_proof_rejects_tampered_entries() {
        let tree = filled_tree(4, 3, 0..40u64).await;
        let root = tree.root_hash();
        let bounds = (Bound::Included(7u64), Bound::Excluded(31u64));
        let (entries, proof) = proven(&tree, bounds).await;
        assert!(verifies(&proof, &root, bounds, &entries).await);

        for i in 0..entries.len() {
            let mut dropped = entries.clone();
            dropped.remove(i);
            assert!(
                !verifies(&proof, &root, bounds, &dropped).await,
                "dropping entry {i} must invalidate",
            );
        }

        let mut extra = entries.clone();
        extra.push((1000, "extra".to_string()));
        assert!(!verifies(&proof, &root, bounds, &extra).await);

        let mut modified = entries.clone();
        modified[3].1.push('x');
        assert!(!verifies(&proof, &root, bounds, &modified).await);

        let mut reordered = entries.clone();
        reordered.swap(0, 1);
        assert!(!verifies(&proof, &root, bounds, &reordered).await);

        let all: Vec<_> = (0..40u64).map(|k| (k, value_for(k))).collect();
        assert!(!verifies(&proof, &root, bounds, &all).await);
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
        let (entries, proof) = proven(&tree_a, bounds).await;
        assert!(verifies(&proof, &root_a, bounds, &entries).await);
        assert!(!verifies(&proof, &root_b, bounds, &entries).await);

        let mut bad_root = root_a;
        corrupt(&mut bad_root);
        assert!(!verifies(&proof, &bad_root, bounds, &entries).await);
    }

    #[tokio::test]
    async fn range_proof_rejects_tampered_proof() {
        let tree = filled_tree(4, 3, 0..40u64).await;
        let root = tree.root_hash();
        let bounds = (Bound::Included(7u64), Bound::Excluded(31u64));
        let (entries, proof) = proven(&tree, bounds).await;

        let mut corrupted = proof.clone();
        for node in &mut corrupted.nodes {
            if let RangeProofNode::Internal { children, .. } = node {
                corrupt(&mut children[0]);
                break;
            }
        }
        assert!(!verifies(&corrupted, &root, bounds, &entries).await);

        let mut hidden = proof.clone();
        let (k, v) = &entries[0];
        for node in &mut hidden.nodes {
            if let RangeProofNode::Leaf { before, inside, .. } = node
                && *inside > 0
            {
                let mut moved = std::mem::take(before).into_vec();
                moved.push((*k, Blake3Hasher::hash_value(v)));
                *before = moved.into_boxed_slice();
                *inside -= 1;
                break;
            }
        }
        assert!(!verifies(&hidden, &root, bounds, &entries[1..]).await);

        let mut truncated = proof.clone();
        let mut nodes = truncated.nodes.into_vec();
        nodes.pop();
        truncated.nodes = nodes.into_boxed_slice();
        assert!(!verifies(&truncated, &root, bounds, &entries).await);

        let mut padded = proof.clone();
        let mut nodes = padded.nodes.into_vec();
        nodes.push(nodes[0].clone());
        padded.nodes = nodes.into_boxed_slice();
        assert!(!verifies(&padded, &root, bounds, &entries).await);
    }

    #[tokio::test]
    async fn range_proof_for_empty_range_only_accepts_empty_stream() {
        let tree = filled_tree(4, 3, 0..20u64).await;
        let root = tree.root_hash();
        let bounds = (Bound::Included(5u64), Bound::Excluded(5u64));
        let (entries, proof) = proven(&tree, bounds).await;
        assert!(entries.is_empty());
        assert!(verifies(&proof, &root, bounds, &entries).await);
        assert!(!verifies(&proof, &root, bounds, &[(5, "v5".to_string())]).await);
    }
}
