//! A proof of a key's existence within the tree.

use std::{
    borrow::{Borrow, Cow},
    num::NonZero,
};

use derive_where::derive_where;

use crate::{
    ExactIterExt as _, HasherOutput, TreeConfig,
    hasher::Hasher,
    merkle_tree::merkle_root_from,
    node::{Borrowed, LeafSearchPath},
    proof::{InvalidProofError, RoutedProofStep, routed_step_for, walk_up_routed},
};

/// A proof that a key exists within a tree.
#[derive_where(Debug; HasherOutput<C>, RoutedProofStep<C>)]
#[derive_where(Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(
    feature = "serde",
    serde(bound(
        serialize = "HasherOutput<C>: serde::Serialize, RoutedProofStep<C>: serde::Serialize",
        deserialize = "HasherOutput<C>: serde::Deserialize<'de>, RoutedProofStep<C>: serde::Deserialize<'de>"
    ))
)]
pub struct InclusionProof<C: TreeConfig> {
    /// The entry count of the leaf.
    pub entry_count: NonZero<usize>,
    /// The entry index within the leaf.
    pub entry_index: usize,
    /// A Merkle proof of the entry's key within the leaf. The first sibling, the entry's value hash, is omitted.
    pub entry_siblings: Box<[HasherOutput<C>]>,
    /// The path that proves the leaf was chosen correctly according to B+Tree invariants.
    pub path: Box<[RoutedProofStep<C>]>,
}

pub(crate) fn inclusion_proof<C: TreeConfig>(
    leaf_search: &LeafSearchPath<C, Borrowed<'_>>,
    entry_index: usize,
) -> InclusionProof<C> {
    InclusionProof {
        entry_count: leaf_search.leaf.keys.as_ref().len().try_into().unwrap(),
        entry_index,
        entry_siblings: leaf_search.leaf.prove_entry_key(entry_index),
        path: leaf_search
            .path
            .iter()
            .rev()
            .map(routed_step_for)
            .into_boxed_slice(),
    }
}

impl<C: TreeConfig> InclusionProof<C> {
    /// Verifies that `key` and `value` are included with the tree `expected_root` represents.
    pub fn verify<Q: Ord + ?Sized>(
        &self,
        expected_root: &HasherOutput<C>,
        key: &Q,
        value: &C::Value,
    ) -> Result<(), InvalidProofError>
    where
        C::Key: Borrow<Q>,
        C::Hasher: Hasher<Q, C::Value, Output = HasherOutput<C>>,
    {
        let key_index = self.entry_index.checked_mul(2).ok_or(InvalidProofError)?;
        let entries_root = merkle_root_from::<C>(
            Cow::Owned(C::Hasher::hash_key(key)),
            key_index,
            std::iter::once(&C::Hasher::hash_value(value)).chain(self.entry_siblings.iter()),
        )?;

        let leaf_hash = C::Hasher::hash_leaf(self.entry_count.get(), &entries_root);
        let root = walk_up_routed(&leaf_hash, key, &self.path)?;

        if root.as_ref() == expected_root {
            Ok(())
        } else {
            Err(InvalidProofError)
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
            TestConfig, all_test_shapers, corrupt, filled_tree, filled_tree_with_shaper,
            insert_orders, new_tree, value_for,
        },
    };

    async fn get_inclusion_proof<S: ReadNodeStorage<TestConfig>>(
        tree: &MerkleBPlusTree<TestConfig, S>,
        key: &u64,
    ) -> Result<Option<InclusionProof<TestConfig>>, S::Error> {
        Ok(match tree.get_with_proof(key).await? {
            GetWithProof::Included(proof, _value) => Some(proof),
            GetWithProof::Excluded(_) => None,
        })
    }

    #[tokio::test]
    async fn inclusion_proof_on_empty_tree_returns_none() {
        let tree = new_tree(5, 4);
        assert!(get_inclusion_proof(&tree, &42).await.unwrap().is_none());
    }

    #[tokio::test]
    async fn inclusion_proof_for_missing_key_returns_none() {
        let mut tree = new_tree(5, 4);
        tree.insert(1, "one".into()).await.unwrap();
        tree.insert(2, "two".into()).await.unwrap();
        assert!(get_inclusion_proof(&tree, &99).await.unwrap().is_none());
    }

    #[tokio::test]
    async fn inclusion_proof_for_deleted_key_returns_none() {
        let mut tree = new_tree(5, 4);
        tree.insert(1, "one".into()).await.unwrap();
        tree.delete(&1).await.unwrap();
        assert!(get_inclusion_proof(&tree, &1).await.unwrap().is_none());
    }

    #[tokio::test]
    async fn single_entry_proof_verifies() {
        let mut tree = new_tree(5, 4);
        tree.insert(1, "one".into()).await.unwrap();
        let root = tree.root_hash();
        let proof = get_inclusion_proof(&tree, &1).await.unwrap().unwrap();
        assert!(proof.verify(&root, &1, &"one".to_string()).is_ok());
    }

    #[tokio::test]
    async fn every_key_has_a_verifying_proof_across_shapers_and_sizes() {
        for s in all_test_shapers() {
            for n in [1u64, 2, 3, 5, 8, 13, 50] {
                let tree = filled_tree_with_shaper(s, 0..n).await;
                let root = tree.root_hash();
                for k in 0..n {
                    let proof = get_inclusion_proof(&tree, &k)
                        .await
                        .unwrap()
                        .unwrap_or_else(|| panic!("shaper={s:?} n={n}: no proof for key {k}"));
                    assert!(
                        proof.verify(&root, &k, &value_for(k)).is_ok(),
                        "shaper={s:?} n={n}: proof for key {k} failed to verify",
                    );
                }
            }
        }
    }

    #[tokio::test]
    async fn proofs_still_verify_after_updates_and_deletes() {
        const N: u64 = 200;
        for s in all_test_shapers() {
            let mut tree = filled_tree_with_shaper(s, 0..N).await;
            for k in (0..N).step_by(3) {
                tree.insert(k, format!("updated-v{k}")).await.unwrap();
            }
            for k in (0..N).step_by(5) {
                if k % 3 != 0 {
                    tree.delete(&k).await.unwrap();
                }
            }
            let root = tree.root_hash();
            for k in 0..N {
                let expected = if k % 3 == 0 {
                    Some(format!("updated-v{k}"))
                } else if k % 5 == 0 {
                    None
                } else {
                    Some(value_for(k))
                };
                let proof = get_inclusion_proof(&tree, &k).await.unwrap();
                match (&proof, &expected) {
                    (Some(p), Some(v)) => assert!(
                        p.verify(&root, &k, v).is_ok(),
                        "shaper={s:?}: proof for surviving key {k} failed to verify",
                    ),
                    (None, None) => {}
                    (Some(_), None) => panic!("shaper={s:?}: got a proof for deleted key {k}"),
                    (None, Some(_)) => panic!("shaper={s:?}: missing proof for surviving key {k}"),
                }
            }
        }
    }

    #[tokio::test]
    async fn proofs_verify_regardless_of_insertion_order() {
        const N: u64 = 120;
        for (label, order) in insert_orders(N) {
            let tree = filled_tree(4, 3, order).await;
            let root = tree.root_hash();
            for k in 0..N {
                let proof = get_inclusion_proof(&tree, &k).await.unwrap().unwrap();
                assert!(
                    proof.verify(&root, &k, &value_for(k)).is_ok(),
                    "insert_order={label}: proof for key {k} failed to verify",
                );
            }
        }
    }

    #[tokio::test]
    async fn forged_value_is_rejected() {
        let tree = filled_tree(4, 3, 0..20u64).await;
        let root = tree.root_hash();
        let proof = get_inclusion_proof(&tree, &5).await.unwrap().unwrap();
        assert!(proof.verify(&root, &5, &"v5".to_string()).is_ok());
        assert!(proof.verify(&root, &5, &"not-v5".to_string()).is_err());
    }

    #[tokio::test]
    async fn forged_key_is_rejected() {
        let tree = filled_tree(4, 3, 0..20u64).await;
        let root = tree.root_hash();
        let proof = get_inclusion_proof(&tree, &5).await.unwrap().unwrap();
        assert!(proof.verify(&root, &6, &"v6".to_string()).is_err());
    }

    #[tokio::test]
    async fn proof_from_one_tree_does_not_verify_against_another_root() {
        let mut tree_a = new_tree(4, 3);
        let mut tree_b = new_tree(4, 3);
        for k in 0..20u64 {
            tree_a.insert(k, value_for(k)).await.unwrap();
            tree_b.insert(k, format!("other-{k}")).await.unwrap();
        }
        let root_b = tree_b.root_hash();
        let proof_from_a = get_inclusion_proof(&tree_a, &5).await.unwrap().unwrap();
        assert!(proof_from_a.verify(&root_b, &5, &"v5".to_string()).is_err());
    }

    #[tokio::test]
    async fn tampering_with_entry_index_is_rejected() {
        let tree = filled_tree(8, 8, 0..8u64).await;
        let root = tree.root_hash();
        for k in 0..8u64 {
            let mut proof = get_inclusion_proof(&tree, &k).await.unwrap().unwrap();
            let original_index = proof.entry_index;
            let bound = 1usize << proof.entry_siblings.len();
            for candidate in 0..bound {
                if candidate == original_index {
                    continue;
                }
                proof.entry_index = candidate;
                assert!(
                    proof.verify(&root, &k, &value_for(k)).is_err(),
                    "key {k}: swapping entry_index from {original_index} to {candidate} must invalidate",
                );
            }
        }
    }

    #[tokio::test]
    async fn overflowing_entry_index_is_rejected() {
        let tree = filled_tree(4, 3, 0..20u64).await;
        let root = tree.root_hash();
        let mut proof = get_inclusion_proof(&tree, &5).await.unwrap().unwrap();
        #[expect(clippy::integer_division)]
        for index in [usize::MAX, usize::MAX / 2 + 1] {
            proof.entry_index = index;
            assert!(
                proof.verify(&root, &5, &value_for(5)).is_err(),
                "entry_index={index} must be rejected",
            );
        }
    }

    #[tokio::test]
    async fn overflowing_path_child_index_is_rejected() {
        let tree = filled_tree(3, 2, 0..40u64).await;
        let root = tree.root_hash();
        let proof = get_inclusion_proof(&tree, &5).await.unwrap().unwrap();
        assert!(proof.path.iter().any(|step| step.upper_bound.is_some()));
        for step_idx in 0..proof.path.len() {
            let mut tampered = proof.clone();
            if let Some(upper_bound) = &mut tampered.path[step_idx].upper_bound {
                upper_bound.child_index = usize::MAX;
                assert!(
                    tampered.verify(&root, &5, &value_for(5)).is_err(),
                    "overflowing child_index at step {step_idx} must invalidate",
                );
            }
        }
    }

    #[tokio::test]
    async fn non_canonical_entry_index_is_rejected() {
        let tree = filled_tree(4, 3, 0..20u64).await;
        let root = tree.root_hash();
        let mut proof = get_inclusion_proof(&tree, &5).await.unwrap().unwrap();
        assert!(proof.verify(&root, &5, &value_for(5)).is_ok());
        proof.entry_index += 1 << proof.entry_siblings.len();
        assert!(proof.verify(&root, &5, &value_for(5)).is_err());
    }

    #[tokio::test]
    async fn tampering_with_entry_count_is_rejected() {
        let tree = filled_tree(4, 3, 0..20u64).await;
        let root = tree.root_hash();
        let mut proof = get_inclusion_proof(&tree, &5).await.unwrap().unwrap();
        proof.entry_count = (proof.entry_count.get() + 1).try_into().unwrap();
        assert!(proof.verify(&root, &5, &"v5".to_string()).is_err());
    }

    #[tokio::test]
    async fn tampering_with_entry_siblings_is_rejected() {
        let tree = filled_tree(4, 3, 0..20u64).await;
        let root = tree.root_hash();
        for k in 0..20u64 {
            let proof = get_inclusion_proof(&tree, &k).await.unwrap().unwrap();
            for i in 0..proof.entry_siblings.len() {
                let mut tampered = proof.clone();
                corrupt(&mut tampered.entry_siblings[i]);
                assert!(
                    tampered.verify(&root, &k, &value_for(k)).is_err(),
                    "key {k}: corrupting entry_siblings[{i}] must invalidate",
                );
            }
        }
    }

    #[tokio::test]
    async fn dropping_an_entry_sibling_is_rejected() {
        let tree = filled_tree(4, 3, 0..20u64).await;
        let root = tree.root_hash();
        let mut proof = get_inclusion_proof(&tree, &5).await.unwrap().unwrap();
        assert!(!proof.entry_siblings.is_empty());
        let mut siblings = proof.entry_siblings.into_vec();
        siblings.pop();
        proof.entry_siblings = siblings.into_boxed_slice();
        assert!(proof.verify(&root, &5, &"v5".to_string()).is_err());
    }

    #[tokio::test]
    async fn tampering_with_path_child_index_is_rejected() {
        let tree = filled_tree(3, 2, 0..40u64).await;
        let root = tree.root_hash();
        let proof = get_inclusion_proof(&tree, &5).await.unwrap().unwrap();
        assert!(!proof.path.is_empty());
        for step_idx in 0..proof.path.len() {
            let mut tampered = proof.clone();
            let step = &mut tampered.path[step_idx];
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
            assert!(
                tampered.verify(&root, &5, &"v5".to_string()).is_err(),
                "tampering child_index at step {step_idx} must invalidate",
            );
        }
    }

    #[tokio::test]
    async fn tampering_with_path_child_count_is_rejected() {
        let tree = filled_tree(3, 2, 0..40u64).await;
        let root = tree.root_hash();
        let proof = get_inclusion_proof(&tree, &5).await.unwrap().unwrap();
        assert!(!proof.path.is_empty());
        for step_idx in 0..proof.path.len() {
            let mut tampered = proof.clone();
            tampered.path[step_idx].child_count = (tampered.path[step_idx].child_count.get() + 1)
                .try_into()
                .unwrap();
            assert!(
                tampered.verify(&root, &5, &"v5".to_string()).is_err(),
                "tampering child_count at step {step_idx} must invalidate",
            );
        }
    }

    #[tokio::test]
    async fn tampering_with_path_child_siblings_is_rejected() {
        let tree = filled_tree(3, 2, 0..40u64).await;
        let root = tree.root_hash();
        let proof = get_inclusion_proof(&tree, &5).await.unwrap().unwrap();
        assert!(!proof.path.is_empty());
        for step_idx in 0..proof.path.len() {
            for sib_idx in 0..proof.path[step_idx].child_siblings.len() {
                let mut tampered = proof.clone();
                corrupt(&mut tampered.path[step_idx].child_siblings[sib_idx]);
                assert!(
                    tampered.verify(&root, &5, &"v5".to_string()).is_err(),
                    "tampering child_siblings[{sib_idx}] at step {step_idx} must invalidate",
                );
            }
        }
    }

    #[tokio::test]
    async fn dropping_a_path_step_is_rejected() {
        let tree = filled_tree(3, 2, 0..80u64).await;
        let root = tree.root_hash();
        let proof = get_inclusion_proof(&tree, &5).await.unwrap().unwrap();
        assert!(proof.path.len() >= 2);
        for drop_idx in 0..proof.path.len() {
            let mut truncated = proof.clone();
            let mut path = truncated.path.into_vec();
            path.remove(drop_idx);
            truncated.path = path.into_boxed_slice();
            assert!(
                truncated.verify(&root, &5, &"v5".to_string()).is_err(),
                "removing path step {drop_idx} must invalidate",
            );
        }
    }

    #[tokio::test]
    async fn appending_a_bogus_path_step_is_rejected() {
        let tree = filled_tree(4, 3, 0..20u64).await;
        let root = tree.root_hash();
        let mut proof = get_inclusion_proof(&tree, &5).await.unwrap().unwrap();
        let bogus = if let Some(last) = proof.path.last() {
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
        let mut path = proof.path.into_vec();
        path.push(bogus);
        proof.path = path.into_boxed_slice();
        assert!(proof.verify(&root, &5, &"v5".to_string()).is_err());
    }

    #[tokio::test]
    async fn cross_key_forged_proof_is_rejected() {
        let tree = filled_tree(4, 3, 0..30u64).await;
        let root = tree.root_hash();
        let proof_5 = get_inclusion_proof(&tree, &5).await.unwrap().unwrap();
        let proof_6 = get_inclusion_proof(&tree, &6).await.unwrap().unwrap();
        let mut frankenstein = proof_5.clone();
        frankenstein.entry_index = proof_6.entry_index;
        frankenstein.entry_siblings = proof_6.entry_siblings;
        assert!(
            frankenstein
                .verify(&root, &5, &"forged".to_string())
                .is_err()
        );
    }

    #[tokio::test]
    async fn fabricated_empty_proof_does_not_verify() {
        let tree = filled_tree(4, 3, 0..10u64).await;
        let root = tree.root_hash();
        let forged = InclusionProof::<TestConfig> {
            entry_count: NonZero::new(1).unwrap(),
            entry_index: 0,
            entry_siblings: [].into(),
            path: [].into(),
        };
        assert!(forged.verify(&root, &5, &"v5".to_string()).is_err());
    }
}
