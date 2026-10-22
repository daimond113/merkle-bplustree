//! A proof of a key's nonexistence within the tree.

use std::{
    borrow::{Borrow, Cow},
    num::NonZero,
};

use derive_where::derive_where;

use crate::{
    ExactIterExt as _, HasherOutput, TreeConfig,
    hasher::Hasher as _,
    merkle_tree::merkle_root_from,
    node::{Borrowed, LeafSearchPath, TreeLeafNode},
    proof::{InvalidProofError, RoutedProofStep, routed_step_for, walk_up_routed},
};

/// A proof that a key doesn't exist that points at where it would be if it were included.
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
pub enum LeafExclusion<C: TreeConfig> {
    /// The key would be before the first entry of the leaf.
    Start {
        /// The entry count of the leaf.
        entry_count: NonZero<usize>,
        /// The key of the first (upper-bounding) entry.
        upper_key: C::Key,
        /// The Merkle inclusion proof of the upper-bounding entry.
        upper_siblings: Box<[HasherOutput<C>]>,
    },
    /// The key would be after the last entry of the leaf.
    End {
        /// The entry count of the leaf.
        entry_count: NonZero<usize>,
        /// The key of the last (lower-bounding) entry.
        lower_key: C::Key,
        /// The Merkle inclusion proof of the lower-bounding entry.
        lower_siblings: Box<[HasherOutput<C>]>,
    },
    /// The key would be between two adjacent entries of the leaf.
    Between {
        /// The entry count of the leaf.
        entry_count: NonZero<usize>,
        /// The index of the lower-bounding entry.
        lower_index: usize,
        /// The key of the lower-bounding entry.
        lower_key: C::Key,
        /// The Merkle inclusion proof of the lower-bounding entry.
        lower_siblings: Box<[HasherOutput<C>]>,
        /// The key of the upper-bounding entry.
        upper_key: C::Key,
        /// The Merkle inclusion proof of the upper-bounding entry.
        upper_siblings: Box<[HasherOutput<C>]>,
    },
}

impl<C: TreeConfig> LeafExclusion<C> {
    pub(crate) fn for_leaf(leaf: &TreeLeafNode<C>, insertion_point: usize) -> Option<Self> {
        let keys = leaf.keys.as_ref();
        let entry_count = NonZero::new(keys.len())?;
        Some(match insertion_point {
            0 => LeafExclusion::Start {
                entry_count,
                upper_key: keys[0].clone(),
                upper_siblings: leaf.prove_entry(0),
            },
            i if i == entry_count.get() => LeafExclusion::End {
                entry_count,
                lower_key: keys[insertion_point - 1].clone(),
                lower_siblings: leaf.prove_entry(insertion_point - 1),
            },
            _ => LeafExclusion::Between {
                entry_count,
                lower_index: insertion_point - 1,
                lower_key: keys[insertion_point - 1].clone(),
                lower_siblings: leaf.prove_entry(insertion_point - 1),
                upper_key: keys[insertion_point].clone(),
                upper_siblings: leaf.prove_entry(insertion_point),
            },
        })
    }

    pub(crate) fn verify_and_reconstruct<Q: Ord + ?Sized>(
        &self,
        key: &Q,
    ) -> Result<(NonZero<usize>, HasherOutput<C>), InvalidProofError>
    where
        C::Key: Borrow<Q>,
    {
        match self {
            LeafExclusion::Start {
                entry_count,
                upper_key,
                upper_siblings,
            } => {
                if upper_key.borrow() <= key {
                    return Err(InvalidProofError);
                }

                let entries_root = merkle_root_from::<C>(
                    Cow::Owned(C::Hasher::hash_key(upper_key)),
                    0,
                    upper_siblings.iter(),
                )?;

                Ok((*entry_count, entries_root.into_owned()))
            }
            LeafExclusion::End {
                entry_count,
                lower_key,
                lower_siblings,
            } => {
                if lower_key.borrow() >= key {
                    return Err(InvalidProofError);
                }

                let lower_position = (entry_count.get() - 1)
                    .checked_mul(2)
                    .ok_or(InvalidProofError)?;
                let entries_root = merkle_root_from::<C>(
                    Cow::Owned(C::Hasher::hash_key(lower_key)),
                    lower_position,
                    lower_siblings.iter(),
                )?;

                Ok((*entry_count, entries_root.into_owned()))
            }
            LeafExclusion::Between {
                entry_count,
                lower_index,
                lower_key,
                lower_siblings,
                upper_key,
                upper_siblings,
            } => {
                if lower_key.borrow() >= key || upper_key.borrow() <= key {
                    return Err(InvalidProofError);
                }

                let lower_position = lower_index.checked_mul(2).ok_or(InvalidProofError)?;
                let upper_position = lower_position.checked_add(2).ok_or(InvalidProofError)?;

                let lower_root = merkle_root_from::<C>(
                    Cow::Owned(C::Hasher::hash_key(lower_key)),
                    lower_position,
                    lower_siblings.iter(),
                )?;
                let upper_root = merkle_root_from::<C>(
                    Cow::Owned(C::Hasher::hash_key(upper_key)),
                    upper_position,
                    upper_siblings.iter(),
                )?;

                if lower_root != upper_root {
                    return Err(InvalidProofError);
                }

                Ok((*entry_count, lower_root.into_owned()))
            }
        }
    }
}

/// A proof that a key doesn't exist that points at where it would be if it were included.
#[derive_where(Debug; C::Key, HasherOutput<C>, RoutedProofStep<C>)]
#[derive_where(Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(
    feature = "serde",
    serde(bound(
        serialize = "LeafExclusion<C>: serde::Serialize, RoutedProofStep<C>: serde::Serialize",
        deserialize = "LeafExclusion<C>: serde::Deserialize<'de>, RoutedProofStep<C>: serde::Deserialize<'de>"
    ))
)]
pub enum ExclusionProof<C: TreeConfig> {
    /// The entire tree is empty.
    Empty,
    /// The tree is non-empty; the key is absent from the leaf the routing chose.
    NonEmpty {
        /// The proof that the key is absent.
        bound: LeafExclusion<C>,
        /// The path that proves the leaf was chosen correctly according to B+Tree invariants.
        path: Box<[RoutedProofStep<C>]>,
    },
}

pub(crate) fn exclusion_proof<C: TreeConfig>(
    leaf_search: &LeafSearchPath<C, Borrowed<'_>>,
    insertion_point: usize,
) -> ExclusionProof<C> {
    match LeafExclusion::for_leaf(&leaf_search.leaf, insertion_point) {
        None => ExclusionProof::Empty,
        Some(bound) => ExclusionProof::NonEmpty {
            bound,
            path: leaf_search
                .path
                .iter()
                .rev()
                .map(routed_step_for)
                .into_boxed_slice(),
        },
    }
}

impl<C: TreeConfig> ExclusionProof<C> {
    /// Verifies that the `key` is not part of the tree `expected_root` represents.
    pub fn verify<Q: Ord + ?Sized>(
        &self,
        expected_root: &HasherOutput<C>,
        key: &Q,
    ) -> Result<(), InvalidProofError>
    where
        C::Key: Borrow<Q>,
    {
        match self {
            ExclusionProof::Empty => {
                if *expected_root == C::Hasher::hash_leaf(0, &C::Hasher::empty_hash()) {
                    Ok(())
                } else {
                    Err(InvalidProofError)
                }
            }
            ExclusionProof::NonEmpty { bound, path } => {
                let (entry_count, entries_root) = bound.verify_and_reconstruct(key)?;
                let leaf_hash = C::Hasher::hash_leaf(entry_count.get(), &entries_root);
                let current = walk_up_routed(&leaf_hash, key, path)?;

                if current.as_ref() == expected_root {
                    Ok(())
                } else {
                    Err(InvalidProofError)
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        MerkleBPlusTree,
        proof::{GetWithProof, UpperBound},
        storage::ReadNodeStorage,
        tests::{
            TestConfig, TestTree, all_test_shapers, corrupt, filled_tree, filled_tree_with_shaper,
            insert_orders, new_tree, value_for,
        },
    };

    async fn get_exclusion_proof<S: ReadNodeStorage<TestConfig>>(
        tree: &MerkleBPlusTree<TestConfig, S>,
        key: &u64,
    ) -> Result<Option<ExclusionProof<TestConfig>>, S::Error> {
        Ok(match tree.get_with_proof(key).await? {
            GetWithProof::Excluded(proof) => Some(proof),
            GetWithProof::Included(..) => None,
        })
    }

    async fn tree_with_gap_around_5(
        max_internal_children: usize,
        max_leaf_entries: usize,
    ) -> TestTree {
        filled_tree(
            max_internal_children,
            max_leaf_entries,
            (0..20u64).step_by(2),
        )
        .await
    }

    fn path_of(proof: &ExclusionProof<TestConfig>) -> &[RoutedProofStep<TestConfig>] {
        match proof {
            ExclusionProof::Empty => &[],
            ExclusionProof::NonEmpty { path, .. } => path,
        }
    }

    fn set_path(
        proof: &mut ExclusionProof<TestConfig>,
        new_path: Box<[RoutedProofStep<TestConfig>]>,
    ) -> Box<[RoutedProofStep<TestConfig>]> {
        let ExclusionProof::NonEmpty { path, .. } = proof else {
            panic!("empty proof has no path")
        };
        std::mem::replace(path, new_path)
    }

    fn edit_path(
        proof: &mut ExclusionProof<TestConfig>,
        f: impl FnOnce(&mut Vec<RoutedProofStep<TestConfig>>),
    ) {
        let mut path = path_of(proof).to_vec();
        f(&mut path);
        set_path(proof, path.into_boxed_slice());
    }

    #[tokio::test]
    async fn exclusion_proof_on_empty_tree_verifies() {
        let tree = new_tree(5, 4);
        let root = tree.root_hash();
        let proof = get_exclusion_proof(&tree, &42).await.unwrap().unwrap();
        assert!(matches!(proof, ExclusionProof::Empty));
        assert!(proof.verify(&root, &42).is_ok());
    }

    #[tokio::test]
    async fn exclusion_proof_for_present_key_returns_none() {
        let mut tree = new_tree(5, 4);
        tree.insert(1, "one".into()).await.unwrap();
        assert!(get_exclusion_proof(&tree, &1).await.unwrap().is_none());
    }

    #[tokio::test]
    async fn exclusion_proof_for_deleted_key_verifies() {
        let mut tree = new_tree(5, 4);
        tree.insert(1, "one".into()).await.unwrap();
        tree.delete(&1).await.unwrap();
        let root = tree.root_hash();
        let proof = get_exclusion_proof(&tree, &1).await.unwrap().unwrap();
        assert!(matches!(proof, ExclusionProof::Empty));
        assert!(proof.verify(&root, &1).is_ok());
    }

    #[tokio::test]
    async fn exclusion_below_lowest_key_is_start_variant() {
        let tree = filled_tree(5, 4, [10u64, 20, 30]).await;
        let root = tree.root_hash();
        let proof = get_exclusion_proof(&tree, &5).await.unwrap().unwrap();
        assert!(matches!(
            proof,
            ExclusionProof::NonEmpty {
                bound: LeafExclusion::Start { .. },
                ..
            }
        ));
        assert!(proof.verify(&root, &5).is_ok());
    }

    #[tokio::test]
    async fn exclusion_above_highest_key_is_end_variant() {
        let tree = filled_tree(5, 4, [10u64, 20, 30]).await;
        let root = tree.root_hash();
        let proof = get_exclusion_proof(&tree, &99).await.unwrap().unwrap();
        assert!(matches!(
            proof,
            ExclusionProof::NonEmpty {
                bound: LeafExclusion::End { .. },
                ..
            }
        ));
        assert!(proof.verify(&root, &99).is_ok());
    }

    #[tokio::test]
    async fn exclusion_between_keys_is_between_variant() {
        let tree = filled_tree(5, 4, [10u64, 20, 30]).await;
        let root = tree.root_hash();
        let proof = get_exclusion_proof(&tree, &15).await.unwrap().unwrap();
        assert!(matches!(
            proof,
            ExclusionProof::NonEmpty {
                bound: LeafExclusion::Between { .. },
                ..
            }
        ));
        assert!(proof.verify(&root, &15).is_ok());
    }

    #[tokio::test]
    async fn every_gap_has_a_verifying_proof_across_shapers_and_sizes() {
        for s in all_test_shapers() {
            for n in [1u64, 2, 3, 5, 8, 13, 50] {
                let tree = filled_tree_with_shaper(s, (0..n).map(|i| i * 2)).await;
                let root = tree.root_hash();
                for k in (0..n * 2).filter(|k| k % 2 == 1) {
                    let proof = get_exclusion_proof(&tree, &k)
                        .await
                        .unwrap()
                        .unwrap_or_else(|| panic!("shaper={s:?} n={n}: no proof for key {k}"));
                    assert!(
                        proof.verify(&root, &k).is_ok(),
                        "shaper={s:?} n={n}: proof for key {k} failed to verify",
                    );
                }
                let past_end = n * 2;
                let proof = get_exclusion_proof(&tree, &past_end)
                    .await
                    .unwrap()
                    .unwrap();
                assert!(
                    proof.verify(&root, &past_end).is_ok(),
                    "shaper={s:?} n={n}: proof for past-the-end key failed to verify",
                );
            }
        }
    }

    #[tokio::test]
    async fn proofs_still_verify_after_updates_and_deletes() {
        const N: u64 = 200;
        for s in all_test_shapers() {
            let mut tree = filled_tree_with_shaper(s, (0..N).step_by(2)).await;
            for k in (0..N).step_by(6) {
                tree.delete(&k).await.unwrap();
            }
            let root = tree.root_hash();
            for k in 0..N {
                let still_present = k % 2 == 0 && k % 6 != 0;
                let proof = get_exclusion_proof(&tree, &k).await.unwrap();
                if still_present {
                    assert!(
                        proof.is_none(),
                        "shaper={s:?}: got an exclusion proof for present key {k}",
                    );
                } else {
                    let proof = proof.unwrap_or_else(|| {
                        panic!("shaper={s:?}: missing exclusion proof for absent key {k}")
                    });
                    assert!(
                        proof.verify(&root, &k).is_ok(),
                        "shaper={s:?}: proof for absent key {k} failed to verify",
                    );
                }
            }
        }
    }

    #[tokio::test]
    async fn proofs_verify_regardless_of_insertion_order() {
        const N: u64 = 120;
        for (label, order) in insert_orders(N) {
            let mut tree = new_tree(4, 3);
            for &k in &order {
                if k % 2 == 0 {
                    tree.insert(k, value_for(k)).await.unwrap();
                }
            }
            let root = tree.root_hash();
            for k in (0..N).filter(|k| k % 2 == 1) {
                let proof = get_exclusion_proof(&tree, &k).await.unwrap().unwrap();
                assert!(
                    proof.verify(&root, &k).is_ok(),
                    "insert_order={label}: proof for key {k} failed to verify",
                );
            }
        }
    }

    #[tokio::test]
    async fn wrong_key_is_rejected() {
        let tree = tree_with_gap_around_5(4, 3).await;
        let root = tree.root_hash();
        let proof = get_exclusion_proof(&tree, &5).await.unwrap().unwrap();
        assert!(proof.verify(&root, &5).is_ok());
        assert!(proof.verify(&root, &7).is_err());
    }

    #[tokio::test]
    async fn proof_from_one_tree_does_not_verify_against_another_root() {
        let mut tree_a = new_tree(4, 3);
        let mut tree_b = new_tree(4, 3);
        for k in (0..20u64).step_by(2) {
            tree_a.insert(k, value_for(k)).await.unwrap();
            tree_b.insert(k, format!("other-{k}")).await.unwrap();
            tree_b.insert(k + 1, format!("filler-{k}")).await.unwrap();
        }
        let root_b = tree_b.root_hash();
        let proof_from_a = get_exclusion_proof(&tree_a, &5).await.unwrap().unwrap();
        assert!(proof_from_a.verify(&root_b, &5).is_err());
    }

    #[tokio::test]
    async fn tampering_with_lower_bound_key_is_rejected() {
        let tree = tree_with_gap_around_5(4, 3).await;
        let root = tree.root_hash();
        let mut proof = get_exclusion_proof(&tree, &5).await.unwrap().unwrap();
        let ExclusionProof::NonEmpty {
            bound: LeafExclusion::Between { lower_key, .. },
            ..
        } = &mut proof
        else {
            panic!("expected a NonEmpty/Between proof for key 5");
        };
        *lower_key += 1;
        assert!(proof.verify(&root, &5).is_err());
    }

    #[tokio::test]
    async fn tampering_with_upper_bound_key_is_rejected() {
        let tree = tree_with_gap_around_5(4, 3).await;
        let root = tree.root_hash();
        let mut proof = get_exclusion_proof(&tree, &5).await.unwrap().unwrap();
        let ExclusionProof::NonEmpty {
            bound: LeafExclusion::Between { upper_key, .. },
            ..
        } = &mut proof
        else {
            panic!("expected a NonEmpty/Between proof for key 5");
        };
        *upper_key -= 1;
        assert!(proof.verify(&root, &5).is_err());
    }

    #[tokio::test]
    async fn tampering_with_lower_index_is_rejected() {
        let tree = tree_with_gap_around_5(4, 3).await;
        let root = tree.root_hash();
        let mut proof = get_exclusion_proof(&tree, &5).await.unwrap().unwrap();
        let ExclusionProof::NonEmpty {
            bound: LeafExclusion::Between { lower_index, .. },
            ..
        } = &mut proof
        else {
            panic!("expected a NonEmpty/Between proof for key 5");
        };
        *lower_index = lower_index.wrapping_add(1);
        assert!(proof.verify(&root, &5).is_err());
    }

    #[tokio::test]
    async fn overflowing_lower_index_is_rejected() {
        let tree = tree_with_gap_around_5(4, 3).await;
        let root = tree.root_hash();
        #[expect(clippy::integer_division)]
        for index in [usize::MAX, usize::MAX / 2] {
            let mut proof = get_exclusion_proof(&tree, &5).await.unwrap().unwrap();
            let ExclusionProof::NonEmpty {
                bound: LeafExclusion::Between { lower_index, .. },
                ..
            } = &mut proof
            else {
                panic!("expected a NonEmpty/Between proof for key 5");
            };
            *lower_index = index;
            assert!(
                proof.verify(&root, &5).is_err(),
                "lower_index={index} must be rejected",
            );
        }
    }

    #[tokio::test]
    async fn non_canonical_lower_index_is_rejected() {
        let tree = tree_with_gap_around_5(4, 3).await;
        let root = tree.root_hash();
        let mut proof = get_exclusion_proof(&tree, &5).await.unwrap().unwrap();
        assert!(proof.verify(&root, &5).is_ok());
        let ExclusionProof::NonEmpty {
            bound:
                LeafExclusion::Between {
                    lower_index,
                    lower_siblings,
                    ..
                },
            ..
        } = &mut proof
        else {
            panic!("expected a NonEmpty/Between proof for key 5");
        };
        *lower_index += 1 << (lower_siblings.len() - 1);
        assert!(proof.verify(&root, &5).is_err());
    }

    #[tokio::test]
    async fn overflowing_entry_count_is_rejected() {
        let tree = tree_with_gap_around_5(4, 3).await;
        let root = tree.root_hash();
        let mut proof = get_exclusion_proof(&tree, &99).await.unwrap().unwrap();
        let ExclusionProof::NonEmpty {
            bound: LeafExclusion::End { entry_count, .. },
            ..
        } = &mut proof
        else {
            panic!("expected a NonEmpty/End proof for key 99");
        };
        *entry_count = NonZero::<usize>::MAX;
        assert!(proof.verify(&root, &99).is_err());
    }

    #[tokio::test]
    async fn tampering_with_bound_siblings_is_rejected() {
        let tree = tree_with_gap_around_5(4, 3).await;
        let root = tree.root_hash();
        let mut checked_at_least_one_lower = false;
        let mut checked_at_least_one_upper = false;
        for k in (0..20u64).filter(|k| k % 2 == 1) {
            let proof = get_exclusion_proof(&tree, &k).await.unwrap().unwrap();
            let ExclusionProof::NonEmpty { bound, .. } = &proof else {
                continue;
            };
            match bound {
                LeafExclusion::Start { upper_siblings, .. } => {
                    for i in 0..upper_siblings.len() {
                        let mut tampered = proof.clone();
                        let ExclusionProof::NonEmpty {
                            bound: LeafExclusion::Start { upper_siblings, .. },
                            ..
                        } = &mut tampered
                        else {
                            unreachable!()
                        };
                        corrupt(&mut upper_siblings[i]);
                        assert!(
                            tampered.verify(&root, &k).is_err(),
                            "key {k}: corrupting upper_siblings[{i}] must invalidate",
                        );
                        checked_at_least_one_upper = true;
                    }
                }
                LeafExclusion::End { lower_siblings, .. } => {
                    for i in 0..lower_siblings.len() {
                        let mut tampered = proof.clone();
                        let ExclusionProof::NonEmpty {
                            bound: LeafExclusion::End { lower_siblings, .. },
                            ..
                        } = &mut tampered
                        else {
                            unreachable!()
                        };
                        corrupt(&mut lower_siblings[i]);
                        assert!(
                            tampered.verify(&root, &k).is_err(),
                            "key {k}: corrupting lower_siblings[{i}] must invalidate",
                        );
                        checked_at_least_one_lower = true;
                    }
                }
                LeafExclusion::Between {
                    lower_siblings,
                    upper_siblings,
                    ..
                } => {
                    for i in 0..lower_siblings.len() {
                        let mut tampered = proof.clone();
                        let ExclusionProof::NonEmpty {
                            bound: LeafExclusion::Between { lower_siblings, .. },
                            ..
                        } = &mut tampered
                        else {
                            unreachable!()
                        };
                        corrupt(&mut lower_siblings[i]);
                        assert!(
                            tampered.verify(&root, &k).is_err(),
                            "key {k}: corrupting lower_siblings[{i}] must invalidate",
                        );
                        checked_at_least_one_lower = true;
                    }
                    for i in 0..upper_siblings.len() {
                        let mut tampered = proof.clone();
                        let ExclusionProof::NonEmpty {
                            bound: LeafExclusion::Between { upper_siblings, .. },
                            ..
                        } = &mut tampered
                        else {
                            unreachable!()
                        };
                        corrupt(&mut upper_siblings[i]);
                        assert!(
                            tampered.verify(&root, &k).is_err(),
                            "key {k}: corrupting upper_siblings[{i}] must invalidate",
                        );
                        checked_at_least_one_upper = true;
                    }
                }
            }
        }
        assert!(checked_at_least_one_lower);
        assert!(checked_at_least_one_upper);
    }

    #[tokio::test]
    async fn tampering_with_entry_count_is_rejected() {
        let tree = tree_with_gap_around_5(4, 3).await;
        let root = tree.root_hash();
        let mut proof = get_exclusion_proof(&tree, &5).await.unwrap().unwrap();
        let ExclusionProof::NonEmpty {
            bound: LeafExclusion::Between { entry_count, .. },
            ..
        } = &mut proof
        else {
            panic!("expected a NonEmpty/Between proof for key 5");
        };
        *entry_count = entry_count.checked_add(1).unwrap();
        assert!(proof.verify(&root, &5).is_err());
    }

    #[tokio::test]
    async fn swapping_start_for_between_is_rejected() {
        let tree = tree_with_gap_around_5(4, 3).await;
        let root = tree.root_hash();
        let proof = get_exclusion_proof(&tree, &5).await.unwrap().unwrap();
        let ExclusionProof::NonEmpty {
            bound:
                LeafExclusion::Between {
                    entry_count,
                    upper_key,
                    upper_siblings,
                    ..
                },
            path,
        } = proof
        else {
            panic!("expected a NonEmpty/Between proof for key 5");
        };
        let forged = ExclusionProof::NonEmpty {
            bound: LeafExclusion::Start {
                entry_count,
                upper_key,
                upper_siblings,
            },
            path,
        };
        assert!(forged.verify(&root, &5).is_err());
    }

    #[tokio::test]
    async fn swapping_end_for_between_is_rejected() {
        let tree = tree_with_gap_around_5(4, 3).await;
        let root = tree.root_hash();
        let proof = get_exclusion_proof(&tree, &5).await.unwrap().unwrap();
        let ExclusionProof::NonEmpty {
            bound:
                LeafExclusion::Between {
                    entry_count,
                    lower_key,
                    lower_siblings,
                    ..
                },
            path,
        } = proof
        else {
            panic!("expected a NonEmpty/Between proof for key 5");
        };
        let forged = ExclusionProof::NonEmpty {
            bound: LeafExclusion::End {
                entry_count,
                lower_key,
                lower_siblings,
            },
            path,
        };
        assert!(forged.verify(&root, &5).is_err());
    }

    #[tokio::test]
    async fn tampering_with_path_child_index_is_rejected() {
        let tree = tree_with_gap_around_5(3, 2).await;
        let root = tree.root_hash();
        let proof = get_exclusion_proof(&tree, &5).await.unwrap().unwrap();
        assert!(!path_of(&proof).is_empty());
        for step_idx in 0..path_of(&proof).len() {
            let mut tampered = proof.clone();
            edit_path(&mut tampered, |path| {
                let step = &mut path[step_idx];
                match &mut step.upper_bound {
                    Some(ub) => {
                        ub.child_index = ub.child_index.wrapping_add(1);
                    }
                    None => {
                        step.upper_bound = Some(UpperBound {
                            child_index: step.child_count.get().saturating_sub(2),
                            next_separator_key: 0,
                            next_child_hash: root,
                            next_siblings: [].into(),
                        });
                    }
                }
            });
            assert!(
                tampered.verify(&root, &5).is_err(),
                "tampering child_index at step {step_idx} must invalidate",
            );
        }
    }

    #[tokio::test]
    async fn tampering_with_path_child_count_is_rejected() {
        let tree = tree_with_gap_around_5(3, 2).await;
        let root = tree.root_hash();
        let proof = get_exclusion_proof(&tree, &5).await.unwrap().unwrap();
        assert!(!path_of(&proof).is_empty());
        for step_idx in 0..path_of(&proof).len() {
            let mut tampered = proof.clone();
            edit_path(&mut tampered, |path| {
                path[step_idx].child_count =
                    (path[step_idx].child_count.get() + 1).try_into().unwrap();
            });
            assert!(
                tampered.verify(&root, &5).is_err(),
                "tampering child_count at step {step_idx} must invalidate",
            );
        }
    }

    #[tokio::test]
    async fn tampering_with_path_child_siblings_is_rejected() {
        let tree = tree_with_gap_around_5(3, 2).await;
        let root = tree.root_hash();
        let proof = get_exclusion_proof(&tree, &5).await.unwrap().unwrap();
        assert!(!path_of(&proof).is_empty());
        for step_idx in 0..path_of(&proof).len() {
            for sib_idx in 0..path_of(&proof)[step_idx].child_siblings.len() {
                let mut tampered = proof.clone();
                edit_path(&mut tampered, |path| {
                    corrupt(&mut path[step_idx].child_siblings[sib_idx]);
                });
                assert!(
                    tampered.verify(&root, &5).is_err(),
                    "tampering child_siblings[{sib_idx}] at step {step_idx} must invalidate",
                );
            }
        }
    }

    #[tokio::test]
    async fn dropping_a_path_step_is_rejected() {
        let tree = filled_tree(3, 2, (0..160u64).step_by(2)).await;
        let root = tree.root_hash();
        let proof = get_exclusion_proof(&tree, &5).await.unwrap().unwrap();
        assert!(path_of(&proof).len() >= 2);
        for drop_idx in 0..path_of(&proof).len() {
            let mut truncated = proof.clone();
            edit_path(&mut truncated, |path| {
                path.remove(drop_idx);
            });
            assert!(
                truncated.verify(&root, &5).is_err(),
                "removing path step {drop_idx} must invalidate",
            );
        }
    }

    #[tokio::test]
    async fn appending_a_bogus_path_step_is_rejected() {
        let tree = tree_with_gap_around_5(4, 3).await;
        let root = tree.root_hash();
        let mut proof = get_exclusion_proof(&tree, &5).await.unwrap().unwrap();
        let bogus = if let Some(last) = path_of(&proof).last() {
            last.clone()
        } else {
            let mut sibling = root;
            corrupt(&mut sibling);
            RoutedProofStep::<TestConfig> {
                child_count: 2.try_into().unwrap(),
                separator_key: None,
                child_siblings: [sibling].into(),
                upper_bound: None,
            }
        };
        edit_path(&mut proof, |path| {
            path.push(bogus);
        });
        assert!(proof.verify(&root, &5).is_err());
    }

    #[tokio::test]
    async fn cross_key_forged_proof_is_rejected() {
        let tree = filled_tree(4, 3, (0..30u64).step_by(2)).await;
        let root = tree.root_hash();
        let proof_5 = get_exclusion_proof(&tree, &5).await.unwrap().unwrap();
        let proof_7 = get_exclusion_proof(&tree, &7).await.unwrap().unwrap();

        let mut frankenstein = proof_7;
        let borrowed_path_5 = path_of(&proof_5).into();
        set_path(&mut frankenstein, borrowed_path_5);
        assert!(frankenstein.verify(&root, &5).is_err());
    }

    #[tokio::test]
    async fn fabricated_empty_proof_only_verifies_for_empty_tree() {
        let tree = filled_tree(4, 3, 0..10u64).await;
        let root = tree.root_hash();
        let forged = ExclusionProof::<TestConfig>::Empty;
        assert!(forged.verify(&root, &500).is_err());

        let empty_tree = new_tree(4, 3);
        let empty_root = empty_tree.root_hash();
        assert!(forged.verify(&empty_root, &500).is_ok());
    }
}
