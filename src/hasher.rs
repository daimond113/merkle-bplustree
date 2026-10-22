//! An implementation of a hash producer.

use std::hash::Hash;

/// A hash producer.
///
/// All hashes must be deterministic and calling the same function with the same arguments (or lack thereof) must produce the same output.
///
/// # Security
/// It is **highly recommended** to domain-separate all operations as the first input to prevent [second preimage attacks](https://en.wikipedia.org/wiki/Merkle_tree#Second_preimage_attack).
pub trait Hasher<K: ?Sized, V> {
    /// The type of hashes this produces.
    type Output: Eq + Hash + Send + Sync + Clone;

    /// An empty hash, i.e. produced with no defined input data.
    fn empty_hash() -> Self::Output;

    /// A hash of a key.
    fn hash_key(key: &K) -> Self::Output;

    /// A hash of a value.
    fn hash_value(value: &V) -> Self::Output;

    /// A hash combining a key and child hash.
    fn hash_slot(key: &K, child: &Self::Output) -> Self::Output;

    /// A hash combining two hashes. Usually just a hash built over the 2 hashes.
    fn merge_hashes(a: &Self::Output, b: &Self::Output) -> Self::Output;

    /// A hash combining an entry count and the entry merkle root of a leaf node.
    ///
    /// # Important
    /// Remember that the count is `usize`, i.e. most common operations will NOT be the same across architectures.
    fn hash_leaf(entry_count: usize, merkle_root: &Self::Output) -> Self::Output;

    /// A hash combining the child count and slots merkle root of an internal node.
    ///
    /// # Important
    /// Remember that the count is `usize`, i.e. most common operations will NOT be the same across architectures.
    fn hash_internal(child_count: usize, slots_root: &Self::Output) -> Self::Output;
}
