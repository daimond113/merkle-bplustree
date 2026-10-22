//! Proofs for various operations.

use crate::{
    ExactIterExt as _, HasherOutput, TreeConfig,
    hasher::Hasher as _,
    merkle_tree::{merkle_root, merkle_root_from},
    node::{
        Borrowed, LeafSearchPath, NodeOwner, RootTreeNode, TreeInternalNode, TreeLeafNode,
        TreeNode, internal_slots, paired_hashes,
    },
    proof::{
        exclusion::{ExclusionProof, exclusion_proof},
        inclusion::{InclusionProof, inclusion_proof},
    },
    shape::{MIN_INTERNAL_CHILDREN, Shaper as _},
    storage::ReadNodeStorage,
};
use derive_where::derive_where;
use std::{
    borrow::{Borrow, Cow},
    num::NonZero,
    ops::Deref,
};
use thiserror::Error;

pub mod delete;
pub mod exclusion;
pub mod inclusion;
pub mod modify;
pub mod range;

/// An error that indicates that something is wrong with the proof and input combination being verified.
#[derive(Debug, Error)]
#[error("proof is invalid")]
pub struct InvalidProofError;

/// The upper bound of an internal node entry, present when the navigated child is not the rightmost.
/// When absent, the navigated child is the rightmost and its index is `child_count - 1`.
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
pub struct UpperBound<C: TreeConfig> {
    /// The index of the navigated child.
    pub child_index: usize,
    /// The separator key of the next child.
    pub next_separator_key: C::Key,
    /// The hash of the next child.
    pub next_child_hash: HasherOutput<C>,
    /// The Merkle proof of the next child's inclusion.
    pub next_siblings: Box<[HasherOutput<C>]>,
}

/// A step in a proof's internal node path.
#[derive_where(Debug; C::Key, HasherOutput<C>)]
#[derive_where(Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(
    feature = "serde",
    serde(bound(
        serialize = "C::Key: serde::Serialize, HasherOutput<C>: serde::Serialize, UpperBound<C>: serde::Serialize",
        deserialize = "C::Key: serde::Deserialize<'de>, HasherOutput<C>: serde::Deserialize<'de>, UpperBound<C>: serde::Deserialize<'de>",
    ))
)]
pub struct RoutedProofStep<C: TreeConfig> {
    /// The child count of this node.
    pub child_count: NonZero<usize>,
    /// The separator key of the navigated child, should one exist.
    pub separator_key: Option<C::Key>,
    /// The Merkle proof of the navigated node's inclusion.
    pub child_siblings: Box<[HasherOutput<C>]>,
    /// The upper bound of the navigated node. `None` means the child is rightmost
    /// (`child_index = child_count - 1`).
    pub upper_bound: Option<UpperBound<C>>,
}

pub(crate) fn routed_step_for<C: TreeConfig, I: Deref<Target = TreeInternalNode<C>>>(
    (child_index, node): &(usize, I),
) -> RoutedProofStep<C> {
    let child_index = *child_index;
    let children = node.children.as_ref();

    RoutedProofStep {
        child_count: children.len().try_into().unwrap(),
        separator_key: child_index
            .checked_sub(1)
            .map(|i| node.keys.as_ref()[i].clone()),
        child_siblings: node.prove_slot(child_index),
        upper_bound: (child_index + 1 < children.len()).then(|| UpperBound {
            child_index,
            next_separator_key: node.keys.as_ref()[child_index].clone(),
            next_child_hash: children[child_index + 1].clone(),
            next_siblings: node.prove_slot(child_index + 1),
        }),
    }
}

pub(crate) fn walk_up_routed<'a, C: TreeConfig, Q: Ord + ?Sized>(
    hash: &'a HasherOutput<C>,
    key: &Q,
    path: &[RoutedProofStep<C>],
) -> Result<Cow<'a, HasherOutput<C>>, InvalidProofError>
where
    C::Key: Borrow<Q>,
{
    let mut current = Cow::Borrowed(hash);

    for step in path {
        if step
            .separator_key
            .as_ref()
            .is_some_and(|sk| sk.borrow() > key)
        {
            return Err(InvalidProofError);
        }

        let child_index = match &step.upper_bound {
            Some(ub) => {
                if ub.child_index >= step.child_count.get() - 1
                    || ub.next_separator_key.borrow() <= key
                {
                    return Err(InvalidProofError);
                }

                ub.child_index
            }
            None => step.child_count.get() - 1,
        };

        let current_slot = match &step.separator_key {
            Some(k) => Cow::Owned(C::Hasher::hash_slot(k, &current)),
            None => current,
        };
        let slots_root =
            merkle_root_from::<C>(current_slot, child_index, step.child_siblings.iter())?;

        if let Some(ub) = &step.upper_bound {
            let next_slot = C::Hasher::hash_slot(&ub.next_separator_key, &ub.next_child_hash);
            let reconstructed = merkle_root_from::<C>(
                Cow::Owned(next_slot),
                child_index + 1,
                ub.next_siblings.iter(),
            )?;

            if reconstructed != slots_root {
                return Err(InvalidProofError);
            }
        }

        current = Cow::Owned(C::Hasher::hash_internal(
            step.child_count.get(),
            &slots_root,
        ));
    }

    Ok(current)
}

// TODO: This is not the most efficient by any means, ideally these would be restructured to send only what is truly necessary.
/// A full node as it appears in a transition proof; leaves carry value hashes instead of values.
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
pub enum TransitionProofNode<C: TreeConfig> {
    /// An internal node.
    Internal {
        /// The separator keys.
        keys: Box<[C::Key]>,
        /// The hashes of the children.
        children: Box<[HasherOutput<C>]>,
    },
    /// A leaf node.
    Leaf {
        /// The keys, in ascending order.
        keys: Box<[C::Key]>,
        /// The hashes of the values, in key order. May omit exactly one entry, the one of the key
        /// being operated on, which the verifier fills in.
        value_hashes: Box<[HasherOutput<C>]>,
    },
}

impl<C: TreeConfig> From<&TreeInternalNode<C>> for TransitionProofNode<C> {
    fn from(node: &TreeInternalNode<C>) -> Self {
        Self::Internal {
            keys: node.keys.as_ref().into(),
            children: node.children.as_ref().into(),
        }
    }
}

impl<C: TreeConfig> From<&TreeLeafNode<C>> for TransitionProofNode<C> {
    fn from(node: &TreeLeafNode<C>) -> Self {
        Self::Leaf {
            keys: node.keys.as_ref().into(),
            value_hashes: node
                .values
                .as_ref()
                .iter()
                .map(C::Hasher::hash_value)
                .into_boxed_slice(),
        }
    }
}

impl<C: TreeConfig> From<&TreeNode<C>> for TransitionProofNode<C> {
    fn from(node: &TreeNode<C>) -> Self {
        match node {
            TreeNode::Internal(node) => Self::from(&**node),
            TreeNode::Leaf(node) => Self::from(&**node),
        }
    }
}

pub(crate) trait Witness<C: TreeConfig>: Send + Sync + Sized {
    type Elided<T>;
    type Nodes;

    fn new<O: NodeOwner<C>>(search: &LeafSearchPath<C, O>) -> Self;
    fn elide<T>(f: impl FnOnce() -> T) -> Self::Elided<T>;
    fn record(&mut self, node: impl Into<TransitionProofNode<C>>);
    fn finish<K, Q>(self, elided: Self::Elided<(K, HasherOutput<C>)>) -> Self::Nodes
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
        C::Key: Borrow<Q>;
}

pub(crate) struct NoWitness;

impl<C: TreeConfig> Witness<C> for NoWitness {
    type Elided<T> = ();
    type Nodes = ();

    fn new<O: NodeOwner<C>>(_search: &LeafSearchPath<C, O>) -> Self {
        Self
    }

    fn elide<T>(_f: impl FnOnce() -> T) -> Self::Elided<T> {}

    fn record(&mut self, _node: impl Into<TransitionProofNode<C>>) {}

    fn finish<K, Q>(self, _elided: Self::Elided<(K, HasherOutput<C>)>) -> Self::Nodes
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
        C::Key: Borrow<Q>,
    {
    }
}

pub(crate) struct RecordingWitness<C: TreeConfig>(Vec<TransitionProofNode<C>>);

impl<C: TreeConfig> Witness<C> for RecordingWitness<C> {
    type Elided<T> = T;
    type Nodes = Box<[TransitionProofNode<C>]>;

    fn new<O: NodeOwner<C>>(search: &LeafSearchPath<C, O>) -> Self {
        let mut nodes = Vec::with_capacity(search.path.len() + 1);
        nodes.extend(
            search
                .path
                .iter()
                .map(|(_, node)| TransitionProofNode::from(&**node)),
        );
        nodes.push(TransitionProofNode::from(&*search.leaf));
        Self(nodes)
    }

    fn elide<T>(f: impl FnOnce() -> T) -> Self::Elided<T> {
        f()
    }

    fn record(&mut self, node: impl Into<TransitionProofNode<C>>) {
        self.0.push(node.into());
    }

    fn finish<K, Q>(self, (key, value_hash): Self::Elided<(K, HasherOutput<C>)>) -> Self::Nodes
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
        C::Key: Borrow<Q>,
    {
        let key = key.borrow();
        let mut nodes = self.0;
        for node in &mut nodes {
            if let TransitionProofNode::Leaf { keys, value_hashes } = node
                && let Ok(index) = keys.binary_search_by(|k| k.borrow().cmp(key))
                && value_hashes[index] == value_hash
            {
                let mut remaining = std::mem::take(value_hashes).into_vec();
                remaining.remove(index);
                *value_hashes = remaining.into_boxed_slice();
            }
        }
        nodes.into_boxed_slice()
    }
}

fn leaf_value_hashes<'a, C: TreeConfig, Q: Ord + ?Sized>(
    keys: &'a [C::Key],
    value_hashes: &'a [HasherOutput<C>],
    fill: (&'a Q, &'a HasherOutput<C>),
) -> Result<impl ExactSizeIterator<Item = &'a HasherOutput<C>>, InvalidProofError>
where
    C::Key: Borrow<Q>,
{
    let elided = match keys.len().checked_sub(value_hashes.len()) {
        Some(0) => None,
        Some(1) => Some(
            keys.binary_search_by(|k| k.borrow().cmp(fill.0))
                .map_err(|_i| InvalidProofError)?,
        ),
        _ => return Err(InvalidProofError),
    };

    Ok((0..keys.len()).map(move |i| match elided {
        Some(e) if i == e => fill.1,
        Some(e) if i > e => &value_hashes[i - 1],
        _ => &value_hashes[i],
    }))
}

impl<C: TreeConfig> TransitionProofNode<C> {
    fn hash<Q: Ord + ?Sized>(
        &self,
        fill: (&Q, &HasherOutput<C>),
    ) -> Result<HasherOutput<C>, InvalidProofError>
    where
        C::Key: Borrow<Q>,
    {
        match self {
            Self::Internal { keys, children } => {
                if children.len() < MIN_INTERNAL_CHILDREN.get() || keys.len() + 1 != children.len()
                {
                    return Err(InvalidProofError);
                }
                Ok(C::Hasher::hash_internal(
                    children.len(),
                    &merkle_root::<C>(internal_slots::<C>(keys, children)),
                ))
            }
            Self::Leaf { keys, value_hashes } => Ok(C::Hasher::hash_leaf(
                keys.len(),
                &merkle_root::<C>(paired_hashes::<C>(
                    keys,
                    leaf_value_hashes::<C, _>(keys, value_hashes, fill)?.cloned(),
                )),
            )),
        }
    }
}

#[derive_where(PartialEq; C::Key, HasherOutput<C>)]
enum Item<'a, C: TreeConfig> {
    Entry(&'a C::Key, &'a HasherOutput<C>),
    Subtree {
        hash: &'a HasherOutput<C>,
        height: usize,
        lower: Option<&'a C::Key>,
        upper: Option<&'a C::Key>,
    },
}

struct Walk<'a, C: TreeConfig, Q: ?Sized> {
    nodes: &'a [TransitionProofNode<C>],
    hashes: &'a [HasherOutput<C>],
    shaper: &'a C::Shaper,
    fill: (&'a Q, &'a HasherOutput<C>),
    items: Vec<Item<'a, C>>,
    found: Option<&'a HasherOutput<C>>,
    leaf_depth: Option<usize>,
    budget: usize,
}

impl<'a, C: TreeConfig, Q: Ord + ?Sized> Walk<'a, C, Q>
where
    C::Key: Borrow<Q>,
{
    fn run(
        nodes: &'a [TransitionProofNode<C>],
        hashes: &'a [HasherOutput<C>],
        shaper: &'a C::Shaper,
        fill: (&'a Q, &'a HasherOutput<C>),
        root: &'a HasherOutput<C>,
    ) -> Result<(Vec<Item<'a, C>>, Option<&'a HasherOutput<C>>), InvalidProofError> {
        let mut walk = Self {
            nodes,
            hashes,
            shaper,
            fill,
            items: Vec::new(),
            found: None,
            leaf_depth: None,
            budget: nodes.len(),
        };
        walk.visit(root, None, None, 0)?;

        let leaf_depth = walk.leaf_depth.ok_or(InvalidProofError)?;
        for item in &mut walk.items {
            if let Item::Subtree { height, .. } = item {
                *height = leaf_depth.checked_sub(*height).ok_or(InvalidProofError)?;
            }
        }

        Ok((walk.items, walk.found))
    }

    fn visit(
        &mut self,
        hash: &'a HasherOutput<C>,
        lower: Option<&'a C::Key>,
        upper: Option<&'a C::Key>,
        depth: usize,
    ) -> Result<(), InvalidProofError> {
        let Some(index) = self.hashes.iter().position(|h| h == hash) else {
            if depth == 0 {
                return Err(InvalidProofError);
            }

            self.items.push(Item::Subtree {
                hash,
                height: depth,
                lower,
                upper,
            });

            return Ok(());
        };

        self.budget = self.budget.checked_sub(1).ok_or(InvalidProofError)?;

        let node = &self.nodes[index];
        let (TransitionProofNode::Leaf { keys, .. } | TransitionProofNode::Internal { keys, .. }) =
            node;
        if !keys.array_windows::<2>().all(|[a, b]| a < b)
            || keys.first().zip(lower).is_some_and(|(k, l)| k < l)
            || keys.last().zip(upper).is_some_and(|(k, u)| k >= u)
        {
            return Err(InvalidProofError);
        }

        match node {
            TransitionProofNode::Leaf { keys, value_hashes } => {
                let value_hashes = leaf_value_hashes::<C, _>(keys, value_hashes, self.fill)?;
                if keys.len() > self.shaper.max_leaf_entries().get()
                    || (depth != 0 && keys.len() < self.shaper.min_leaf_entries().get())
                    || self.leaf_depth.replace(depth).is_some_and(|d| d != depth)
                {
                    return Err(InvalidProofError);
                }

                for (k, h) in keys.iter().zip(value_hashes) {
                    if k.borrow() == self.fill.0 {
                        self.found = Some(h);
                    } else {
                        self.items.push(Item::Entry(k, h));
                    }
                }
            }
            TransitionProofNode::Internal { keys, children } => {
                let min = if depth == 0 {
                    MIN_INTERNAL_CHILDREN
                } else {
                    self.shaper.min_internal_children()
                };
                if children.len() > self.shaper.max_internal_children().get()
                    || children.len() < min.get()
                {
                    return Err(InvalidProofError);
                }

                for (i, child) in children.iter().enumerate() {
                    let child_lower = if i == 0 { lower } else { Some(&keys[i - 1]) };
                    let child_upper = keys.get(i).or(upper);
                    self.visit(child, child_lower, child_upper, depth + 1)?;
                }
            }
        }

        Ok(())
    }
}

pub(crate) fn verify_transition<C: TreeConfig, Q: Ord + ?Sized>(
    nodes: &[TransitionProofNode<C>],
    old_root: &HasherOutput<C>,
    new_root: &HasherOutput<C>,
    key: &Q,
    value_hash: &HasherOutput<C>,
    shaper: &C::Shaper,
    expect: impl FnOnce(Option<&HasherOutput<C>>, Option<&HasherOutput<C>>) -> bool,
) -> Result<(), InvalidProofError>
where
    C::Key: Borrow<Q>,
{
    let fill = (key, value_hash);
    let hashes = nodes
        .iter()
        .map(|node| node.hash(fill))
        .collect::<Result<Vec<_>, _>>()?;

    let (old_items, old_entry) = Walk::run(nodes, &hashes, shaper, fill, old_root)?;
    let (new_items, new_entry) = Walk::run(nodes, &hashes, shaper, fill, new_root)?;

    if expect(old_entry, new_entry) && old_items == new_items {
        Ok(())
    } else {
        Err(InvalidProofError)
    }
}

/// The result of getting an entry's value along with cryptographic proof.
#[derive_where(Debug; InclusionProof<C>, R, ExclusionProof<C>)]
#[derive_where(Clone; R)]
pub enum GetWithProof<C: TreeConfig, R> {
    /// The entry is a member of the tree and its inclusion can be proven.
    Included(InclusionProof<C>, R),
    /// The entry is not a member of the tree.
    Excluded(ExclusionProof<C>),
}

impl<C: TreeConfig> RootTreeNode<C, Borrowed<'_>> {
    pub(crate) async fn get_with_proof<Q: Ord + ?Sized, R, S: ReadNodeStorage<C>>(
        self,
        storage: &S,
        key: &Q,
        map: impl FnOnce(&C::Value) -> R,
    ) -> Result<GetWithProof<C, R>, S::Error>
    where
        C::Key: Borrow<Q>,
    {
        let leaf_search = self
            .leaf_search::<true, _>(storage, |k| k.borrow() <= key)
            .await?;
        let result = match leaf_search
            .leaf
            .keys
            .as_ref()
            .binary_search_by(|k| k.borrow().cmp(key))
        {
            Ok(entry_index) => GetWithProof::Included(
                inclusion_proof(&leaf_search, entry_index),
                map(&leaf_search.leaf.values.as_ref()[entry_index]),
            ),
            Err(insertion_point) => {
                GetWithProof::Excluded(exclusion_proof(&leaf_search, insertion_point))
            }
        };

        Ok(result)
    }
}
