//! Node storage traits & utilities

use std::{
    error::Error,
    marker::PhantomData,
    ops::{Deref, DerefMut},
};

use derive_where::derive_where;

use crate::{HasherOutput, TreeConfig, node::TreeNode};

/// A storage that can read nodes by their hash identity.
pub trait ReadNodeStorage<C: TreeConfig> {
    /// An error that can occur during this storage's operation.
    type Error: Error + Send + Sync;

    /// Gets a node by its hash identity.
    /// A call to this method for an unknown hash must result in an error. If it was called by the library, the storage's
    /// state is corrupted. If called externally, the hash must've been an invalid key.
    ///
    /// The returned node's contents are wrapped in [Arc](std::sync::Arc) to allow efficient caching as well as internal optimisations.
    fn get_node(
        &self,
        hash: &HasherOutput<C>,
    ) -> impl Future<Output = Result<TreeNode<C>, Self::Error>> + Send;
}

/// A storage that can read and write nodes by their hash identity.
pub trait WriteNodeStorage<C: TreeConfig>: ReadNodeStorage<C> {
    /// Stores the nodes the library has generated, keyed by their hash identity.
    /// This method receives the nodes from leaf/leaves to root, so storages that validate children hash existence should be supported.
    ///
    /// # Implementation requirements
    /// Even if these nodes are not persisted, the iterator **MUST** be consumed whole.
    /// The library knows the root hash by getting the last element of the iterator, so not consuming it will result in state corruption and data loss.
    ///
    /// You may use [SinkStorage] to easily convert [ReadNodeStorage] into a discarding [WriteNodeStorage].
    fn store_nodes(
        &mut self,
        nodes: impl Iterator<Item = (HasherOutput<C>, TreeNode<C>)> + Send,
    ) -> impl Future<Output = Result<(), Self::Error>> + Send;
}

impl<C: TreeConfig, R: ReadNodeStorage<C> + ?Sized, T: Deref<Target = R> + Sync> ReadNodeStorage<C>
    for T
{
    type Error = R::Error;

    async fn get_node(&self, hash: &HasherOutput<C>) -> Result<TreeNode<C>, Self::Error> {
        self.deref().get_node(hash).await
    }
}

impl<C: TreeConfig, W: WriteNodeStorage<C> + ?Sized, T: DerefMut<Target = W> + Send + Sync>
    WriteNodeStorage<C> for T
{
    async fn store_nodes(
        &mut self,
        nodes: impl Iterator<Item = (HasherOutput<C>, TreeNode<C>)> + Send,
    ) -> Result<(), Self::Error> {
        self.deref_mut().store_nodes(nodes).await
    }
}

/// The error [InMemoryNodeStorage] returns when asked for a node it does not hold.
#[derive(Debug, thiserror::Error)]
#[error("node is not present in the storage")]
pub struct NodeNotFoundError;

/// An in-memory node storage.
#[derive_where(Clone, Default)]
#[derive_where(Debug; HasherOutput<C>, TreeNode<C>)]
pub struct InMemoryNodeStorage<C: TreeConfig>(
    std::collections::HashMap<HasherOutput<C>, TreeNode<C>>,
);

impl<C: TreeConfig> ReadNodeStorage<C> for InMemoryNodeStorage<C> {
    type Error = NodeNotFoundError;

    async fn get_node(&self, hash: &HasherOutput<C>) -> Result<TreeNode<C>, Self::Error> {
        self.0.get(hash).cloned().ok_or(NodeNotFoundError)
    }
}

impl<C: TreeConfig> WriteNodeStorage<C> for InMemoryNodeStorage<C> {
    async fn store_nodes(
        &mut self,
        nodes: impl Iterator<Item = (HasherOutput<C>, TreeNode<C>)> + Send,
    ) -> Result<(), Self::Error> {
        for (hash, node) in nodes {
            self.0.insert(hash, node);
        }

        Ok(())
    }
}

/// A wrapper that implements a discarding [WriteNodeStorage], which is particularly useful for proof generation.
///
/// The [ReadNodeStorage] implementation is forwarded to the wrapped type, while [WriteNodeStorage] merely consumes the iterator.
#[derive_where(Debug, Clone, Copy; R)]
pub struct SinkStorage<C: TreeConfig, R: ReadNodeStorage<C> + Send + Sync>(
    R,
    PhantomData<fn() -> C>,
);

impl<C: TreeConfig, R: ReadNodeStorage<C> + Send + Sync> SinkStorage<C, R> {
    /// Wraps [ReadNodeStorage] to provide a discarding [WriteNodeStorage].
    pub fn new(storage: R) -> Self {
        Self(storage, PhantomData)
    }
}

impl<C: TreeConfig, R: ReadNodeStorage<C> + Send + Sync> ReadNodeStorage<C> for SinkStorage<C, R> {
    type Error = R::Error;

    async fn get_node(&self, hash: &HasherOutput<C>) -> Result<TreeNode<C>, Self::Error> {
        self.0.get_node(hash).await
    }
}

impl<C: TreeConfig, R: ReadNodeStorage<C> + Send + Sync> WriteNodeStorage<C> for SinkStorage<C, R> {
    async fn store_nodes(
        &mut self,
        nodes: impl Iterator<Item = (HasherOutput<C>, TreeNode<C>)> + Send,
    ) -> Result<(), Self::Error> {
        for _ in nodes {}

        Ok(())
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use std::{convert::Infallible, fmt::Debug};

    use crate::shape::Shaper as _;

    use super::*;

    fn node_hash<C: TreeConfig>(node: &TreeNode<C>) -> HasherOutput<C> {
        match node {
            TreeNode::Internal(node) => node.hash(),
            TreeNode::Leaf(node) => node.hash(),
        }
    }

    pub struct CheckedStorage<C: TreeConfig>
    where
        C::Key: Debug,
        TreeNode<C>: Debug,
        C::Shaper: Send,
        HasherOutput<C>: Debug,
    {
        map: std::collections::HashMap<HasherOutput<C>, TreeNode<C>>,
        root_hash: Option<HasherOutput<C>>,
        shaper: C::Shaper,
    }

    impl<C: TreeConfig> CheckedStorage<C>
    where
        C::Key: Debug,
        TreeNode<C>: Debug,
        C::Shaper: Send,
        HasherOutput<C>: Debug,
    {
        pub fn new(shaper: C::Shaper) -> Self {
            Self {
                map: Default::default(),
                root_hash: None,
                shaper,
            }
        }
    }

    impl<C: TreeConfig> ReadNodeStorage<C> for CheckedStorage<C>
    where
        C::Key: Debug,
        TreeNode<C>: Debug,
        C::Shaper: Send,
        HasherOutput<C>: Debug,
    {
        type Error = Infallible;

        async fn get_node(&self, hash: &HasherOutput<C>) -> Result<TreeNode<C>, Self::Error> {
            Ok(self.map[hash].clone())
        }
    }

    impl<C: TreeConfig> WriteNodeStorage<C> for CheckedStorage<C>
    where
        C::Key: Debug,
        TreeNode<C>: Debug,
        C::Shaper: Send,
        HasherOutput<C>: Debug,
    {
        async fn store_nodes(
            &mut self,
            nodes: impl Iterator<Item = (HasherOutput<C>, TreeNode<C>)> + Send,
        ) -> Result<(), Self::Error> {
            for (hash, node) in nodes {
                self.root_hash = Some(hash.clone());
                self.map.insert(hash, node);
            }
            Ok(())
        }
    }

    impl<C: TreeConfig> CheckedStorage<C>
    where
        C::Key: Debug,
        TreeNode<C>: Debug,
        C::Shaper: Send,
        HasherOutput<C>: Debug,
    {
        fn check_subtree(&self, hash: &HasherOutput<C>, is_root: bool) -> usize {
            let node = &self.map[hash];

            assert_eq!(
                node_hash(node),
                *hash,
                "stored hash does not match recomputed node.hash(): {node:?}"
            );

            match node {
                TreeNode::Leaf(leaf) => {
                    let keys = leaf.keys.as_ref();
                    let values = leaf.values.as_ref();

                    assert_eq!(
                        keys.len(),
                        values.len(),
                        "leaf: keys.len() ({}) != values.len() ({}): {node:?}",
                        keys.len(),
                        values.len(),
                    );

                    for w in keys.array_windows::<2>() {
                        assert!(
                            w[0] < w[1],
                            "leaf keys not strictly ascending: {:?} then {:?}: {node:?}",
                            w[0],
                            w[1],
                        );
                    }

                    let max = self.shaper.max_leaf_entries().get();
                    assert!(
                        keys.len() <= max,
                        "leaf overfull: {} entries > max_leaf_entries={max}: {node:?}",
                        keys.len(),
                    );
                    if !is_root {
                        let min = self.shaper.min_leaf_entries().get();
                        assert!(
                            keys.len() >= min,
                            "non-root leaf underfull: {} entries < min_leaf_entries={min}: {node:?}",
                            keys.len(),
                        );
                    }

                    0
                }
                TreeNode::Internal(internal) => {
                    let keys = internal.keys.as_ref();
                    let children = internal.children.as_ref();

                    assert!(
                        !keys.is_empty(),
                        "internal node has zero keys (minimum is 1): {node:?}",
                    );
                    assert_eq!(
                        children.len(),
                        keys.len() + 1,
                        "internal node: children.len() ({}) != keys.len()+1 ({}): {node:?}",
                        children.len(),
                        keys.len() + 1,
                    );

                    for w in keys.array_windows::<2>() {
                        assert!(
                            w[0] < w[1],
                            "internal keys not strictly ascending: {:?} then {:?}: {node:?}",
                            w[0],
                            w[1],
                        );
                    }

                    let child_count = children.len();
                    let max = self.shaper.max_internal_children().get();

                    assert!(
                        child_count <= max,
                        "internal node overfull: {child_count} children > max_internal_children={max}: {node:?}",
                    );

                    if is_root {
                        assert!(
                            child_count >= 2,
                            "root internal node has fewer than 2 children: {child_count}: {node:?}",
                        );
                    } else {
                        let min = self.shaper.min_internal_children().get();
                        assert!(
                            child_count >= min,
                            "non-root internal node underfull: {child_count} children < min_internal_children={min}: {node:?}",
                        );
                    }

                    let mut child_height = None;

                    for child_hash in children {
                        assert!(
                            self.map.contains_key(child_hash),
                            "internal node references child hash not present in storage: {node:?}",
                        );

                        let h = self.check_subtree(child_hash, false);
                        match child_height {
                            None => child_height = Some(h),
                            Some(expected) => assert_eq!(
                                h, expected,
                                "tree is not height-balanced: sibling subtrees have heights {h} and {expected}: {node:?}",
                            ),
                        }
                    }

                    child_height.unwrap() + 1
                }
            }
        }
    }

    impl<C: TreeConfig> Drop for CheckedStorage<C>
    where
        C::Key: Debug,
        TreeNode<C>: Debug,
        C::Shaper: Send,
        HasherOutput<C>: Debug,
    {
        fn drop(&mut self) {
            for (stored_hash, node) in &self.map {
                assert_eq!(
                    *stored_hash,
                    node_hash(node),
                    "stored hash key does not match node.hash(): {node:?}",
                );
            }

            if let Some(root_hash) = self.root_hash.clone() {
                self.check_subtree(&root_hash, true);
            }
        }
    }
}
