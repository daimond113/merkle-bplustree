//! B+Tree nodes.

use std::{borrow::Borrow, iter::Rev, marker::PhantomData, ops::Deref, sync::Arc};

use derive_where::derive_where;

use crate::{
    HasherOutput, TreeConfig,
    hasher::Hasher as _,
    merkle_tree::{merkle_prove, merkle_root},
    shape::Shaper,
    storage::ReadNodeStorage,
};

/// An internal node, providing children node hashes and separator keys.
#[derive_where(Debug; <C::Shaper as Shaper<C>>::InternalKeys, <C::Shaper as Shaper<C>>::InternalChildren)]
#[derive_where(Clone)]
pub struct TreeInternalNode<C: TreeConfig> {
    pub(crate) keys: <C::Shaper as Shaper<C>>::InternalKeys,
    pub(crate) children: <C::Shaper as Shaper<C>>::InternalChildren,
}

impl<C: TreeConfig> TreeInternalNode<C> {
    /// Constructs a new internal node, returning None if the invariants weren't upheld:
    /// - children.len() > 1
    /// - keys.len() = children.len() - 1
    pub fn new(
        keys: <C::Shaper as Shaper<C>>::InternalKeys,
        children: <C::Shaper as Shaper<C>>::InternalChildren,
    ) -> Option<Self> {
        let children_len = children.as_ref().len();
        if children_len <= 1 || keys.as_ref().len() != children_len - 1 {
            return None;
        }

        Some(Self { keys, children })
    }

    /// Separator keys, providing boundaries between children.
    pub fn keys(&self) -> &<C::Shaper as Shaper<C>>::InternalKeys {
        &self.keys
    }

    /// Children hashes.
    pub fn children(&self) -> &<C::Shaper as Shaper<C>>::InternalChildren {
        &self.children
    }

    pub(crate) fn slots(&self) -> impl ExactSizeIterator<Item = HasherOutput<C>> + '_ {
        internal_slots::<C>(self.keys.as_ref(), self.children.as_ref())
    }

    pub(crate) fn prove_slot(&self, index: usize) -> Box<[HasherOutput<C>]> {
        merkle_prove::<0, C>(self.slots(), index)
    }

    pub(crate) fn hash(&self) -> HasherOutput<C> {
        C::Hasher::hash_internal(
            self.children.as_ref().len(),
            &merkle_root::<C>(self.slots()),
        )
    }

    pub(crate) async fn leaf_search<
        const KEEP_PATH: bool,
        S: ReadNodeStorage<C>,
        O: NodeOwner<C>,
    >(
        this: O::Internal,
        storage: &S,
        cmp: impl Fn(&C::Key) -> bool,
    ) -> Result<LeafSearchPath<C, O>, S::Error> {
        let mut ancestors = vec![];
        let mut current = this;

        loop {
            let node_idx = current.keys.as_ref().partition_point(&cmp);
            let node = storage
                .get_node(&current.children.as_ref()[node_idx])
                .await?;

            if KEEP_PATH {
                ancestors.push((node_idx, current));
            }

            match node {
                TreeNode::Internal(node) => current = O::internal(node),
                TreeNode::Leaf(node) => {
                    return Ok(LeafSearchPath {
                        path: ancestors,
                        leaf: O::leaf(node),
                    });
                }
            }
        }
    }
}

pub(crate) fn internal_slots<'a, C: TreeConfig>(
    keys: &'a [C::Key],
    children: &'a [HasherOutput<C>],
) -> impl ExactSizeIterator<Item = HasherOutput<C>> + 'a {
    struct ExactChain<A, B>(A, B);
    impl<A: ExactSizeIterator, B: ExactSizeIterator<Item = A::Item>> Iterator for ExactChain<A, B> {
        type Item = A::Item;

        fn next(&mut self) -> Option<Self::Item> {
            self.0.next().or_else(|| self.1.next())
        }

        fn size_hint(&self) -> (usize, Option<usize>) {
            let a = self.0.len();
            let b = self.1.len();
            (a + b, Some(a + b))
        }
    }
    impl<A: ExactSizeIterator, B: ExactSizeIterator<Item = A::Item>> ExactSizeIterator
        for ExactChain<A, B>
    {
    }

    ExactChain(
        std::iter::once(children[0].clone()),
        keys.iter()
            .zip(&children[1..])
            .map(|(k, c)| C::Hasher::hash_slot(k, c)),
    )
}

/// A leaf node, storing key-value pairs.
#[derive_where(Debug; <C::Shaper as Shaper<C>>::LeafKeys, <C::Shaper as Shaper<C>>::LeafValues)]
#[derive_where(Clone, Default)]
pub struct TreeLeafNode<C: TreeConfig> {
    pub(crate) keys: <C::Shaper as Shaper<C>>::LeafKeys,
    pub(crate) values: <C::Shaper as Shaper<C>>::LeafValues,
}

impl<C: TreeConfig> TreeLeafNode<C> {
    /// Constructs a new leaf node, returning None if the invariants weren't upheld:
    /// - keys.len() = values.len()
    pub fn new(
        keys: <C::Shaper as Shaper<C>>::LeafKeys,
        values: <C::Shaper as Shaper<C>>::LeafValues,
    ) -> Option<Self> {
        if keys.as_ref().len() != values.as_ref().len() {
            return None;
        }

        Some(Self { keys, values })
    }

    /// The keys in this node.
    pub fn keys(&self) -> &<C::Shaper as Shaper<C>>::LeafKeys {
        &self.keys
    }
    /// The values in this node.
    pub fn values(&self) -> &<C::Shaper as Shaper<C>>::LeafValues {
        &self.values
    }

    pub(crate) fn entry_hashes(&self) -> impl ExactSizeIterator<Item = HasherOutput<C>> + '_ {
        paired_hashes::<C>(
            self.keys.as_ref(),
            self.values.as_ref().iter().map(C::Hasher::hash_value),
        )
    }

    pub(crate) fn entries_root(&self) -> HasherOutput<C> {
        merkle_root::<C>(self.entry_hashes())
    }

    pub(crate) fn prove_entry(&self, index: usize) -> Box<[HasherOutput<C>]> {
        merkle_prove::<0, C>(self.entry_hashes(), index * 2)
    }

    pub(crate) fn prove_entry_key(&self, index: usize) -> Box<[HasherOutput<C>]> {
        // skipping the first sibling is valid because the Merkle node is [key, value].
        // when proving the key, the value is naturally the first sibling.
        // instead of including it, we append it at verification sites
        // which also lets us prove we have the correct one for free
        merkle_prove::<1, C>(self.entry_hashes(), index * 2)
    }

    pub(crate) fn hash(&self) -> HasherOutput<C> {
        C::Hasher::hash_leaf(self.keys.as_ref().len(), &self.entries_root())
    }
}

pub(crate) fn paired_hashes<'a, C: TreeConfig>(
    keys: &'a [C::Key],
    value_hashes: impl ExactSizeIterator<Item = HasherOutput<C>> + 'a,
) -> impl ExactSizeIterator<Item = HasherOutput<C>> + 'a {
    struct PairIter<A, B> {
        a: A,
        b: B,
        next_a: bool,
    }
    impl<A: ExactSizeIterator, B: ExactSizeIterator<Item = A::Item>> Iterator for PairIter<A, B> {
        type Item = A::Item;

        fn next(&mut self) -> Option<Self::Item> {
            if self.next_a {
                self.next_a = false;
                self.a.next()
            } else {
                self.next_a = true;
                self.b.next()
            }
        }

        fn size_hint(&self) -> (usize, Option<usize>) {
            let len = self.a.len();
            debug_assert_eq!(len, self.b.len());
            (len * 2, Some(len * 2))
        }
    }
    impl<A: ExactSizeIterator, B: ExactSizeIterator<Item = A::Item>> ExactSizeIterator
        for PairIter<A, B>
    {
    }

    PairIter {
        a: keys.iter().map(C::Hasher::hash_key),
        b: value_hashes,
        next_a: true,
    }
}

/// A tree node that can be either internal or a leaf.
#[derive_where(Debug; TreeInternalNode<C>, TreeLeafNode<C>)]
#[derive_where(Clone)]
pub enum TreeNode<C: TreeConfig> {
    /// A [TreeInternalNode].
    Internal(Arc<TreeInternalNode<C>>),
    /// A [TreeLeafNode].
    Leaf(Arc<TreeLeafNode<C>>),
}

pub(crate) struct LeafSearchPath<C: TreeConfig, O: NodeOwner<C>> {
    pub(crate) path: Vec<(usize, O::Internal)>,
    pub(crate) leaf: O::Leaf,
}

impl<C: TreeConfig, O: NodeOwner<C>> LeafSearchPath<C, O> {
    pub(crate) fn into_root(self) -> RootTreeNode<C, O> {
        if let Some((_, node)) = self.path.into_iter().next() {
            RootTreeNode::Internal(node)
        } else {
            RootTreeNode::Leaf(self.leaf)
        }
    }
}

pub(crate) struct RebuildAncestors<C: TreeConfig> {
    start: Option<(HasherOutput<C>, TreeNode<C>)>,
    prev_hash: Option<HasherOutput<C>>,
    prev_node: TreeNode<C>,
    path: Rev<std::vec::IntoIter<(usize, Arc<TreeInternalNode<C>>)>>,
}

impl<C: TreeConfig> RebuildAncestors<C> {
    pub(crate) fn new(
        start: (HasherOutput<C>, TreeNode<C>),
        path: Vec<(usize, Arc<TreeInternalNode<C>>)>,
    ) -> Self {
        Self {
            prev_hash: Some(start.0.clone()),
            prev_node: start.1.clone(),
            start: Some(start),
            path: path.into_iter().rev(),
        }
    }

    pub(crate) fn into_root(self) -> RootTreeNode<C, Owned> {
        match self.prev_node {
            TreeNode::Internal(node) => RootTreeNode::Internal(node),
            TreeNode::Leaf(node) => RootTreeNode::Leaf(node),
        }
    }
}

impl<C: TreeConfig> Iterator for RebuildAncestors<C> {
    type Item = (HasherOutput<C>, TreeNode<C>);

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(start) = self.start.take() {
            return Some(start);
        }

        let (child_index, node) = self.path.next()?;
        let mut new_node = Arc::unwrap_or_clone(node);

        new_node.children.as_mut()[child_index] = self.prev_hash.take().unwrap();

        let hash = new_node.hash();
        let new_node = Arc::new(new_node);

        self.prev_hash = Some(hash.clone());
        self.prev_node = TreeNode::Internal(new_node);

        Some((hash, self.prev_node.clone()))
    }
}

// functions are implemented on this type to ensure that modifications can't be silently done in the middle of a tree
#[derive_where(Debug, Clone; O::Internal, O::Leaf)]
pub(crate) enum RootTreeNode<C: TreeConfig, O: NodeOwner<C>> {
    Internal(O::Internal),
    Leaf(O::Leaf),
}

impl<C: TreeConfig, O: NodeOwner<C>> RootTreeNode<C, O> {
    pub(crate) async fn leaf_search<const KEEP_PATH: bool, S: ReadNodeStorage<C>>(
        self,
        storage: &S,
        cmp: impl Fn(&C::Key) -> bool,
    ) -> Result<LeafSearchPath<C, O>, S::Error> {
        Ok(match self {
            Self::Internal(node) => {
                TreeInternalNode::leaf_search::<KEEP_PATH, _, _>(node, storage, cmp).await?
            }
            Self::Leaf(node) => LeafSearchPath {
                path: vec![],
                leaf: node,
            },
        })
    }

    pub(crate) async fn find<Q: Ord + ?Sized, R, S: ReadNodeStorage<C>>(
        self,
        storage: &S,
        key: &Q,
        map: impl FnOnce(&C::Value) -> R,
    ) -> Result<Option<R>, S::Error>
    where
        C::Key: Borrow<Q>,
    {
        let leaf_search = self
            .leaf_search::<false, _>(storage, |k| k.borrow() <= key)
            .await?;

        Ok(leaf_search
            .leaf
            .keys
            .as_ref()
            .binary_search_by(|k| k.borrow().cmp(key))
            .map(|idx| map(&leaf_search.leaf.values.as_ref()[idx]))
            .ok())
    }
}

impl<C: TreeConfig> RootTreeNode<C, Owned> {
    pub(crate) fn borrowed(&self) -> RootTreeNode<C, Borrowed<'_>> {
        match self {
            Self::Internal(node) => RootTreeNode::Internal(ArcCow::Borrowed(node.as_ref())),
            Self::Leaf(node) => RootTreeNode::Leaf(ArcCow::Borrowed(node.as_ref())),
        }
    }
}

impl<C: TreeConfig> From<TreeNode<C>> for RootTreeNode<C, Owned> {
    fn from(value: TreeNode<C>) -> Self {
        match value {
            TreeNode::Internal(node) => Self::Internal(node),
            TreeNode::Leaf(node) => Self::Leaf(node),
        }
    }
}

#[derive(Debug)]
pub(crate) enum ArcCow<'a, T> {
    Owned(Arc<T>),
    Borrowed(&'a T),
}

impl<T> Deref for ArcCow<'_, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        match self {
            Self::Owned(arc) => arc,
            Self::Borrowed(t) => t,
        }
    }
}

impl<T> Clone for ArcCow<'_, T> {
    fn clone(&self) -> Self {
        match self {
            Self::Owned(arc) => Self::Owned(arc.clone()),
            Self::Borrowed(t) => Self::Borrowed(t),
        }
    }
}

pub(crate) trait NodeOwner<C: TreeConfig> {
    type Internal: Deref<Target = TreeInternalNode<C>>;
    type Leaf: Deref<Target = TreeLeafNode<C>>;

    fn internal(node: Arc<TreeInternalNode<C>>) -> Self::Internal;
    fn leaf(node: Arc<TreeLeafNode<C>>) -> Self::Leaf;
}

pub(crate) struct Owned;
pub(crate) struct Borrowed<'a>(PhantomData<&'a ()>);

impl<C: TreeConfig> NodeOwner<C> for Owned {
    type Internal = Arc<TreeInternalNode<C>>;
    type Leaf = Arc<TreeLeafNode<C>>;

    fn internal(node: Arc<TreeInternalNode<C>>) -> Self::Internal {
        node
    }

    fn leaf(node: Arc<TreeLeafNode<C>>) -> Self::Leaf {
        node
    }
}

impl<'a, C: TreeConfig> NodeOwner<C> for Borrowed<'a> {
    type Internal = ArcCow<'a, TreeInternalNode<C>>;
    type Leaf = ArcCow<'a, TreeLeafNode<C>>;

    fn internal(node: Arc<TreeInternalNode<C>>) -> Self::Internal {
        ArcCow::Owned(node)
    }

    fn leaf(node: Arc<TreeLeafNode<C>>) -> Self::Leaf {
        ArcCow::Owned(node)
    }
}
