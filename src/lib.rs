#![warn(missing_docs)]

//! merkle-bplustree provides an implementation of a [B+Tree](https://en.wikipedia.org/wiki/B%2B_tree)
//! that utilises Merkle Trees.
//!
//! The crate is designed for out-of-memory storage, and provides async-enabled storage traits to do so.
//! Additionally, you can configure almost everything about the tree, including the hasher and shape constraints.

use std::{borrow::Borrow, ops::RangeBounds, sync::Arc};

use derive_where::derive_where;
use futures_util::Stream;
use thiserror::Error;

use crate::{
    hasher::Hasher,
    node::{Owned, RootTreeNode, TreeInternalNode, TreeLeafNode, TreeNode},
    proof::{
        GetWithProof,
        delete::DeleteProof,
        modify::ModifyProof,
        range::{GetRangeProof, RangeProofBuilder, range_impl},
    },
    shape::Shaper,
    storage::{ReadNodeStorage, WriteNodeStorage},
};

pub mod hasher;
pub(crate) mod merkle_tree;
pub mod node;
pub mod proof;
pub mod shape;
pub mod storage;

/// Configuration for a [MerkleBPlusTree].
pub trait TreeConfig: Sized + 'static {
    /// The key this tree uses.
    type Key: Send + Sync + Ord + Clone;
    /// The value this tree uses.
    type Value: Send + Sync + Clone;
    /// The hasher this tree uses.
    type Hasher: Hasher<Self::Key, Self::Value>;
    /// The shaper this tree uses.
    type Shaper: Shaper<Self>;
}

/// Extracts the [Hasher::Output] from [TreeConfig].
pub type HasherOutput<C> =
    <<C as TreeConfig>::Hasher as Hasher<<C as TreeConfig>::Key, <C as TreeConfig>::Value>>::Output;

/// A B+Tree with Merkle Tree-based nodes, providing efficient proofs and operations.
///
/// # Warning
/// If any panic or *storage* error happens ([InsertNewError::AlreadyExists] is fine), this struct becomes unusable as a tree.
/// It must be discarded in such circumstance. Calling [Self::into_storage] is allowed.
#[derive_where(Debug; TreeInternalNode<C>, TreeLeafNode<C>, S, C::Shaper)]
#[derive_where(Clone; S, C::Shaper)]
pub struct MerkleBPlusTree<C: TreeConfig, S: ReadNodeStorage<C>> {
    root: Option<RootTreeNode<C, Owned>>,
    storage: S,
    shaper: C::Shaper,
}

impl<C: TreeConfig, S: ReadNodeStorage<C>> MerkleBPlusTree<C, S> {
    /// Constructs a Self from an existing root node; allows interacting with trees created in other contexts.
    pub fn from_root(root: TreeNode<C>, storage: S, shaper: C::Shaper) -> Self {
        #[cfg(debug_assertions)]
        crate::shape::validate_shaper(
            shaper.min_internal_children(),
            shaper.max_internal_children(),
            shaper.min_leaf_entries(),
            shaper.max_leaf_entries(),
        )
        .unwrap();

        Self {
            root: Some(root.into()),
            storage,
            shaper,
        }
    }

    /// Constructs a new, empty Self from the given arguments.
    pub fn new(storage: S, shaper: C::Shaper) -> Self {
        Self::from_root(
            TreeNode::Leaf(Arc::new(Default::default())),
            storage,
            shaper,
        )
    }

    /// Constructs a Self from an existing root node's hash.
    pub async fn from_root_hash(
        root_hash: &HasherOutput<C>,
        storage: S,
        shaper: C::Shaper,
    ) -> Result<Self, S::Error> {
        let node = storage.get_node(root_hash).await?;
        Ok(Self::from_root(node, storage, shaper))
    }

    /// Gets a value from a key, mapping a reference to the desired result.
    pub async fn get_mapped<Q: Ord + ?Sized, R>(
        &self,
        key: &Q,
        map: impl FnOnce(&C::Value) -> R,
    ) -> Result<Option<R>, S::Error>
    where
        C::Key: Borrow<Q>,
    {
        self.root
            .as_ref()
            .unwrap()
            .borrowed()
            .find(&self.storage, key, map)
            .await
    }

    /// Gets a value from a key, cloning the value and providing it owned.
    pub async fn get<Q: Ord + ?Sized>(&self, key: &Q) -> Result<Option<C::Value>, S::Error>
    where
        C::Key: Borrow<Q>,
    {
        self.get_mapped(key, Clone::clone).await
    }

    /// Gets a value from a key, mapping a reference to the desired result.
    /// Generates the appropriate proof for the state.
    pub async fn get_with_proof_mapped<Q: Ord + ?Sized, R>(
        &self,
        key: &Q,
        map: impl FnOnce(&C::Value) -> R,
    ) -> Result<GetWithProof<C, R>, S::Error>
    where
        C::Key: Borrow<Q>,
    {
        self.root
            .as_ref()
            .unwrap()
            .borrowed()
            .get_with_proof(&self.storage, key, map)
            .await
    }

    /// Gets a value from a key, cloning the value and providing it owned.
    /// Generates the appropriate proof for the state.
    pub async fn get_with_proof<Q: Ord + ?Sized>(
        &self,
        key: &Q,
    ) -> Result<GetWithProof<C, C::Value>, S::Error>
    where
        C::Key: Borrow<Q>,
    {
        self.get_with_proof_mapped(key, Clone::clone).await
    }

    /// Returns all entries within the provided range bounds, mapped.
    pub fn range_mapped<'a, Q: Ord + ?Sized + 'a, R>(
        &'a self,
        range: impl RangeBounds<Q>,
        map: impl Fn(&C::Key, &C::Value) -> R,
    ) -> impl Stream<Item = Result<R, S::Error>>
    where
        C::Key: Borrow<Q>,
        S: Sync,
    {
        range_impl(
            &self.storage,
            self.root.as_ref().unwrap().borrowed(),
            range,
            map,
            (),
        )
    }

    /// Returns all entries within the provided range bounds.
    pub fn range<'a, Q: Ord + ?Sized + 'a>(
        &'a self,
        range: impl RangeBounds<Q>,
    ) -> impl Stream<Item = Result<(C::Key, C::Value), S::Error>>
    where
        C::Key: Borrow<Q>,
        S: Sync,
    {
        self.range_mapped(range, |k, v| (k.clone(), v.clone()))
    }

    /// Returns all entries within the provided range bounds, mapped, alongside cryptographic proof
    /// of the completion of the values.
    pub fn proven_range_mapped<'a, Q: Ord + ?Sized + 'a, R>(
        &'a self,
        range: impl RangeBounds<Q>,
        map: impl Fn(&C::Key, &C::Value) -> R,
    ) -> impl Stream<Item = Result<R, S::Error>> + GetRangeProof<C>
    where
        C::Key: Borrow<Q>,
        S: Sync,
    {
        range_impl(
            &self.storage,
            self.root.as_ref().unwrap().borrowed(),
            range,
            map,
            RangeProofBuilder::default(),
        )
    }

    /// Returns all entries within the provided range bounds alongside cryptographic proof
    /// of the completion of the values.
    pub fn proven_range<'a, Q: Ord + ?Sized + 'a>(
        &'a self,
        range: impl RangeBounds<Q>,
    ) -> impl Stream<Item = Result<(C::Key, C::Value), S::Error>> + GetRangeProof<C>
    where
        C::Key: Borrow<Q>,
        S: Sync,
    {
        self.proven_range_mapped(range, |k, v| (k.clone(), v.clone()))
    }

    /// Returns all entries within the provided range bounds, mapped. Consumes self.
    pub fn into_range_mapped<Q: Ord + ?Sized + 'static, R>(
        self,
        range: impl RangeBounds<Q>,
        map: impl Fn(&C::Key, &C::Value) -> R,
    ) -> impl Stream<Item = Result<R, S::Error>>
    where
        C::Key: Borrow<Q>,
        S: Send + Sync + 'static,
    {
        range_impl(self.storage, self.root.unwrap(), range, map, ())
    }

    /// Returns all entries within the provided range bounds. Consumes self.
    pub fn into_range<Q: Ord + ?Sized + 'static>(
        self,
        range: impl RangeBounds<Q>,
    ) -> impl Stream<Item = Result<(C::Key, C::Value), S::Error>>
    where
        C::Key: Borrow<Q>,
        S: Send + Sync + 'static,
    {
        self.into_range_mapped(range, |k, v| (k.clone(), v.clone()))
    }

    /// Returns all entries within the provided range bounds, mapped, alongside cryptographic proof
    /// of the completion of the values. Consumes self.
    pub fn into_proven_range_mapped<Q: Ord + ?Sized + 'static, R>(
        self,
        range: impl RangeBounds<Q>,
        map: impl Fn(&C::Key, &C::Value) -> R,
    ) -> impl Stream<Item = Result<R, S::Error>> + GetRangeProof<C>
    where
        C::Key: Borrow<Q>,
        S: Send + Sync + 'static,
    {
        range_impl(
            self.storage,
            self.root.unwrap(),
            range,
            map,
            RangeProofBuilder::default(),
        )
    }

    /// Returns all entries within the provided range bounds alongside cryptographic proof
    /// of the completion of the values. Consumes self.
    pub fn into_proven_range<Q: Ord + ?Sized + 'static>(
        self,
        range: impl RangeBounds<Q>,
    ) -> impl Stream<Item = Result<(C::Key, C::Value), S::Error>> + GetRangeProof<C>
    where
        C::Key: Borrow<Q>,
        S: Send + Sync + 'static,
    {
        self.into_proven_range_mapped(range, |k, v| (k.clone(), v.clone()))
    }

    /// Returns the root node of the tree.
    pub fn root(&self) -> TreeNode<C> {
        match self.root.as_ref().unwrap() {
            RootTreeNode::Internal(node) => TreeNode::Internal(node.clone()),
            RootTreeNode::Leaf(node) => TreeNode::Leaf(node.clone()),
        }
    }

    /// Returns the hash of the root node of the tree.
    pub fn root_hash(&self) -> HasherOutput<C> {
        match self.root.as_ref().unwrap() {
            RootTreeNode::Internal(node) => node.hash(),
            RootTreeNode::Leaf(node) => node.hash(),
        }
    }

    /// Returns the underlying shaper.
    pub fn shaper(&self) -> &C::Shaper {
        &self.shaper
    }

    /// Consumes self and returns the underlying storage.
    pub fn into_storage(self) -> S {
        self.storage
    }
}

impl<C: TreeConfig, S: WriteNodeStorage<C>> MerkleBPlusTree<C, S> {
    /// Inserts an entry into the tree, overwriting the old value should one be present.
    pub async fn insert(
        &mut self,
        key: C::Key,
        value: C::Value,
    ) -> Result<Option<C::Value>, S::Error> {
        let (new_root, old_value_if_set) = self
            .root
            .take()
            .unwrap()
            .modify::<false, _>(&mut self.storage, &self.shaper, key, value)
            .await?;
        self.root = Some(new_root);
        Ok(old_value_if_set.unwrap())
    }

    /// Inserts an entry into the tree, overwriting the old value should one be present.
    /// Creates a [ModifyProof] which can be used to prove that this operation was how the old root became the new one,
    /// and verify the operation was done legally.
    pub async fn insert_with_proof(
        &mut self,
        key: C::Key,
        value: C::Value,
    ) -> Result<(Option<C::Value>, ModifyProof<C>), S::Error> {
        let (new_root, pair_if_set) = self
            .root
            .take()
            .unwrap()
            .modify_with_proof::<false, _>(&mut self.storage, &self.shaper, key, value)
            .await?;
        self.root = Some(new_root);
        Ok(pair_if_set.unwrap())
    }

    /// Inserts an entry into the tree, returning [InsertNewError::AlreadyExists] if the key already had a value associated.
    pub async fn insert_new(
        &mut self,
        key: C::Key,
        value: C::Value,
    ) -> Result<(), InsertNewError<S::Error>> {
        let (new_root, old_value_if_set) = self
            .root
            .take()
            .unwrap()
            .modify::<true, _>(&mut self.storage, &self.shaper, key, value)
            .await?;
        self.root = Some(new_root);
        old_value_if_set
            .map(|_| ())
            .ok_or(InsertNewError::AlreadyExists)
    }

    /// Inserts an entry into the tree, returning [InsertNewError::AlreadyExists] if the key already had a value associated.
    /// Creates a [ModifyProof] which can be used to prove that this operation was how the old root became the new one,
    /// and verify the operation was done legally.
    pub async fn insert_new_with_proof(
        &mut self,
        key: C::Key,
        value: C::Value,
    ) -> Result<ModifyProof<C>, InsertNewError<S::Error>> {
        let (new_root, pair_if_set) = self
            .root
            .take()
            .unwrap()
            .modify_with_proof::<true, _>(&mut self.storage, &self.shaper, key, value)
            .await?;
        self.root = Some(new_root);
        let Some((_, proof)) = pair_if_set else {
            return Err(InsertNewError::AlreadyExists);
        };
        Ok(proof)
    }

    /// Deletes the key from the tree, returning the value associated if it was present.
    pub async fn delete<Q: Ord + ?Sized>(&mut self, key: &Q) -> Result<Option<C::Value>, S::Error>
    where
        C::Key: Borrow<Q>,
    {
        let (new_root, value) = self
            .root
            .take()
            .unwrap()
            .delete(&mut self.storage, &self.shaper, key)
            .await?;
        self.root = Some(new_root);
        Ok(value)
    }

    /// Deletes the key from the tree, returning the value associated if it was present.
    /// Creates a [DeleteProof] which can be used to prove that this operation was how the old root became the new one,
    /// and verify the operation was done legally.
    pub async fn delete_with_proof<Q: Ord + ?Sized>(
        &mut self,
        key: &Q,
    ) -> Result<Option<(C::Value, DeleteProof<C>)>, S::Error>
    where
        C::Key: Borrow<Q>,
    {
        let (new_root, result) = self
            .root
            .take()
            .unwrap()
            .delete_with_proof(&mut self.storage, &self.shaper, key)
            .await?;
        self.root = Some(new_root);
        Ok(result)
    }
}

/// The error `insert_new` operations return.
#[derive(Debug, Error)]
pub enum InsertNewError<E> {
    /// The underlying storage errored.
    #[error(transparent)]
    StorageError(#[from] E),

    /// The key was already present in the map.
    #[error("key already in map")]
    AlreadyExists,
}

pub(crate) trait ExactIterExt<T>: ExactSizeIterator<Item = T> {
    fn into_boxed_slice(self) -> Box<[T]>;
}

impl<T, E: ExactSizeIterator<Item = T>> ExactIterExt<T> for E {
    fn into_boxed_slice(self) -> Box<[T]> {
        let mut buf = Vec::new();
        buf.reserve_exact(self.len());
        buf.extend(self);
        buf.into_boxed_slice()
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use std::collections::BTreeMap;

    use rand::RngExt as _;
    use rand::SeedableRng as _;
    use rand::rngs::StdRng;
    use rand::seq::SliceRandom as _;

    use super::*;
    use crate::hasher::Hasher;
    use crate::shape::RuntimeShaper;
    use crate::storage::tests::CheckedStorage;

    pub(crate) struct Blake3Hasher;

    impl Hasher<u64, String> for Blake3Hasher {
        type Output = [u8; 32];

        fn empty_hash() -> Self::Output {
            let mut hasher = blake3::Hasher::new();
            hasher.update(&[0xFF]);
            hasher.finalize().into()
        }

        fn hash_key(key: &u64) -> Self::Output {
            let mut hasher = blake3::Hasher::new();
            hasher.update(&[0x00]);
            hasher.update(&key.to_be_bytes());
            hasher.finalize().into()
        }

        fn hash_value(value: &String) -> Self::Output {
            let mut hasher = blake3::Hasher::new();
            hasher.update(&[0x01]);
            hasher.update(&(value.len() as u64).to_be_bytes());
            hasher.update(value.as_bytes());
            hasher.finalize().into()
        }

        fn hash_slot(key: &u64, child: &Self::Output) -> Self::Output {
            let mut hasher = blake3::Hasher::new();
            hasher.update(&[0x02]);
            hasher.update(&key.to_be_bytes());
            hasher.update(child);
            hasher.finalize().into()
        }

        fn merge_hashes(a: &Self::Output, b: &Self::Output) -> Self::Output {
            let mut hasher = blake3::Hasher::new();
            hasher.update(&[0x03]);
            hasher.update(a);
            hasher.update(b);
            hasher.finalize().into()
        }

        fn hash_leaf(entry_count: usize, merkle_root: &Self::Output) -> Self::Output {
            let mut hasher = blake3::Hasher::new();
            hasher.update(&[0x04]);
            hasher.update(&(entry_count as u64).to_be_bytes());
            hasher.update(merkle_root);
            hasher.finalize().into()
        }

        fn hash_internal(child_count: usize, slots_root: &Self::Output) -> Self::Output {
            let mut hasher = blake3::Hasher::new();
            hasher.update(&[0x05]);
            hasher.update(&(child_count as u64).to_be_bytes());
            hasher.update(slots_root);
            hasher.finalize().into()
        }
    }

    pub(crate) struct TestConfig;

    impl TreeConfig for TestConfig {
        type Key = u64;
        type Value = String;
        type Hasher = Blake3Hasher;
        type Shaper = RuntimeShaper;
    }

    pub(crate) type TestTree = MerkleBPlusTree<TestConfig, CheckedStorage<TestConfig>>;

    pub(crate) fn value_for(key: u64) -> String {
        format!("v{key}")
    }

    pub(crate) fn corrupt(hash: &mut [u8; 32]) {
        hash[0] ^= 0xFF;
    }

    pub(crate) fn shaper(max_internal_children: usize, max_leaf_entries: usize) -> RuntimeShaper {
        RuntimeShaper::with_max(
            max_internal_children.try_into().unwrap(),
            max_leaf_entries.try_into().unwrap(),
        )
        .unwrap()
    }

    pub(crate) fn shaper_with_min_max(
        min_internal_children: usize,
        max_internal_children: usize,
        min_leaf_entries: usize,
        max_leaf_entries: usize,
    ) -> RuntimeShaper {
        RuntimeShaper::with_min_max(
            min_internal_children.try_into().unwrap(),
            max_internal_children.try_into().unwrap(),
            min_leaf_entries.try_into().unwrap(),
            max_leaf_entries.try_into().unwrap(),
        )
        .unwrap()
    }

    pub(crate) fn new_tree_with_shaper(shaper: RuntimeShaper) -> TestTree {
        MerkleBPlusTree::new(CheckedStorage::new(shaper), shaper)
    }

    pub(crate) fn new_tree(max_internal_children: usize, max_leaf_entries: usize) -> TestTree {
        new_tree_with_shaper(shaper(max_internal_children, max_leaf_entries))
    }

    pub(crate) async fn fill(tree: &mut TestTree, keys: impl IntoIterator<Item = u64>) {
        for key in keys {
            tree.insert(key, value_for(key)).await.unwrap();
        }
    }

    pub(crate) async fn filled_tree_with_shaper(
        shaper: RuntimeShaper,
        keys: impl IntoIterator<Item = u64>,
    ) -> TestTree {
        let mut tree = new_tree_with_shaper(shaper);
        fill(&mut tree, keys).await;
        tree
    }

    pub(crate) async fn filled_tree(
        max_internal_children: usize,
        max_leaf_entries: usize,
        keys: impl IntoIterator<Item = u64>,
    ) -> TestTree {
        filled_tree_with_shaper(shaper(max_internal_children, max_leaf_entries), keys).await
    }

    pub(crate) fn all_test_shapers() -> Vec<RuntimeShaper> {
        let mut out = Vec::new();

        for max_int in [3usize, 4, 6, 8, 13] {
            for max_leaf in [2usize, 3, 4, 7, 10] {
                if let Ok(s) = RuntimeShaper::with_max(
                    max_int.try_into().unwrap(),
                    max_leaf.try_into().unwrap(),
                ) {
                    out.push(s);
                }

                let min_int = (max_int - 1).max(2);
                let min_leaf = (max_leaf - 1).max(1);
                if let Ok(s) = RuntimeShaper::with_min_max(
                    min_int.try_into().unwrap(),
                    max_int.try_into().unwrap(),
                    min_leaf.try_into().unwrap(),
                    max_leaf.try_into().unwrap(),
                ) {
                    out.push(s);
                }
            }
        }

        out
    }

    pub(crate) fn key_sequence(n: u64, seed: Option<u64>) -> Vec<u64> {
        let mut keys = (0..n).collect::<Vec<_>>();
        if let Some(s) = seed {
            keys.shuffle(&mut StdRng::seed_from_u64(s));
        }
        keys
    }

    pub(crate) fn insert_orders(n: u64) -> Vec<(&'static str, Vec<u64>)> {
        vec![
            ("ascending", key_sequence(n, None)),
            ("descending", {
                let mut v = key_sequence(n, None);
                v.reverse();
                v
            }),
            ("shuffled-1", key_sequence(n, Some(1))),
            ("shuffled-2", key_sequence(n, Some(2))),
            ("shuffled-3", key_sequence(n, Some(0xdead_beef))),
        ]
    }

    pub(crate) async fn assert_oracle(
        tree: &TestTree,
        oracle: &BTreeMap<u64, String>,
        key_space: u64,
        context: &str,
    ) {
        for (&k, v) in oracle {
            assert_eq!(
                tree.get(&k).await.unwrap().as_ref(),
                Some(v),
                "{context}: oracle key {k} missing or wrong",
            );
        }
        for k in 0..key_space {
            if !oracle.contains_key(&k) {
                assert!(
                    tree.get(&k).await.unwrap().is_none(),
                    "{context}: key {k} present but not in oracle",
                );
            }
        }
    }

    #[tokio::test]
    async fn get_on_empty_tree_returns_none() {
        let tree = new_tree(5, 4);
        assert!(tree.get(&42).await.unwrap().is_none());
    }

    #[tokio::test]
    async fn get_missing_key_returns_none_when_tree_nonempty() {
        let mut tree = new_tree(5, 4);
        tree.insert(1, "one".into()).await.unwrap();
        assert!(tree.get(&2).await.unwrap().is_none());
    }

    #[tokio::test]
    async fn load_round_trip_preserves_data() {
        let mut rng = StdRng::seed_from_u64(3);
        let max_internal = rng.random_range(3..=6);
        let max_leaf = rng.random_range(2..=6);
        let mut tree = new_tree(max_internal, max_leaf);

        let mut order = (0..50u64).collect::<Vec<_>>();
        order.shuffle(&mut rng);
        for &k in &order {
            tree.insert(k, format!("val-{k}")).await.unwrap();
        }

        let root_hash = tree.root_hash();
        let shaper = *tree.shaper();
        let storage = tree.into_storage();

        let loaded =
            TestTree::from_root(storage.get_node(&root_hash).await.unwrap(), storage, shaper);
        for i in 0..50u64 {
            assert_eq!(
                loaded.get(&i).await.unwrap().as_ref(),
                Some(&format!("val-{i}")),
                "key {i}",
            );
        }
    }

    #[tokio::test]
    async fn oracle_insert_delete_insert_new_many_seeds() {
        const N_OPS: u64 = 1500;
        const KEY_SPACE: u64 = 300;

        let shapers = all_test_shapers();

        for seed in [
            10u64, 20, 99, 100, 200, 777, 1000, 12345, 99999, 0xdead, 0xbeef, 0xcafe,
        ] {
            let s = shapers[seed as usize % shapers.len()];
            let mut rng = StdRng::seed_from_u64(seed);
            let mut tree = new_tree_with_shaper(s);
            let mut oracle = BTreeMap::new();

            for step in 0..N_OPS {
                let key = rng.random_range(0..KEY_SPACE);
                let op: u8 = rng.random_range(0..5);
                let value = format!("s{seed}-step{step}-k{key}");

                match op {
                    0 | 1 => {
                        tree.insert(key, value.clone()).await.unwrap();
                        oracle.insert(key, value);
                    }
                    2 | 3 => {
                        let tree_val = tree.delete(&key).await.unwrap();
                        let oracle_val = oracle.remove(&key);
                        assert_eq!(
                            tree_val.as_deref(),
                            oracle_val.as_deref(),
                            "seed={seed} step={step}: delete({key}) return mismatch",
                        );
                    }
                    _ => {
                        let existed = oracle.contains_key(&key);
                        match tree.insert_new(key, value.clone()).await {
                            Ok(_) => {
                                assert!(
                                    !existed,
                                    "seed={seed} step={step}: insert_new OK but oracle had key {key}",
                                );
                                oracle.insert(key, value);
                            }
                            Err(InsertNewError::AlreadyExists) => {
                                assert!(
                                    existed,
                                    "seed={seed} step={step}: insert_new rejected {key} but oracle didn't have it",
                                );
                            }
                            Err(e) => panic!("storage error at step {step}: {e}"),
                        }
                    }
                }

                if step % 100 == 0 {
                    assert_oracle(
                        &tree,
                        &oracle,
                        KEY_SPACE,
                        &format!("shaper={s:?} seed={seed} step={step}"),
                    )
                    .await;
                }
            }

            assert_oracle(
                &tree,
                &oracle,
                KEY_SPACE,
                &format!("shaper={s:?} seed={seed} FINAL"),
            )
            .await;
        }
    }

    #[tokio::test]
    async fn repeated_insert_delete_cycle_stays_consistent() {
        let mut tree = new_tree(4, 3);
        for round in 0u64..5 {
            for k in 0..50u64 {
                tree.insert(k, format!("round{round}-v{k}")).await.unwrap();
            }
            for k in 0..50u64 {
                assert_eq!(
                    tree.get(&k).await.unwrap().as_ref(),
                    Some(&format!("round{round}-v{k}")),
                    "round {round} key {k}",
                );
            }
            for k in (1..50u64).step_by(2) {
                tree.delete(&k).await.unwrap();
            }
            for k in 0..50u64 {
                let got = tree.get(&k).await.unwrap();
                if k % 2 == 0 {
                    assert_eq!(
                        got.as_ref(),
                        Some(&format!("round{round}-v{k}")),
                        "round {round}: even key {k} missing",
                    );
                } else {
                    assert!(
                        got.is_none(),
                        "round {round}: odd key {k} should be deleted"
                    );
                }
            }
            for k in (0..50u64).step_by(2) {
                tree.delete(&k).await.unwrap();
            }
        }
    }

    #[tokio::test]
    async fn interleaved_grow_shrink_cycles_across_shapers() {
        for s in all_test_shapers() {
            let mut tree = new_tree_with_shaper(s);

            let phases = [(50u64, 10usize), (60, 5), (30, 0)];
            let mut current_max = 0u64;
            let mut oracle = BTreeMap::new();

            for (grow_to, shrink_to) in phases {
                for k in current_max..grow_to {
                    tree.insert(k, value_for(k)).await.unwrap();
                    oracle.insert(k, value_for(k));
                }
                current_max = grow_to;

                while oracle.len() > shrink_to {
                    let &largest = oracle.keys().next_back().unwrap();
                    tree.delete(&largest).await.unwrap();
                    oracle.remove(&largest);
                }

                assert_oracle(
                    &tree,
                    &oracle,
                    current_max,
                    &format!("shaper={s:?} after grow_to={grow_to} shrink_to={shrink_to}"),
                )
                .await;
            }
        }
    }
}
