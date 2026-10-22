//! The delete operation.

use std::{borrow::Borrow, sync::Arc};

use derive_where::derive_where;

use crate::{
    HasherOutput, TreeConfig,
    hasher::Hasher as _,
    node::*,
    proof::{
        InvalidProofError, NoWitness, RecordingWitness, TransitionProofNode, Witness,
        verify_transition,
    },
    shape::{OrderedCollection as _, Shaper as _},
    storage::WriteNodeStorage,
};

impl<C: TreeConfig> RootTreeNode<C, Owned> {
    pub(crate) async fn delete<Q: Ord + ?Sized, S: WriteNodeStorage<C>>(
        self,
        storage: &mut S,
        shaper: &C::Shaper,
        key: &Q,
    ) -> Result<(Self, Option<C::Value>), S::Error>
    where
        C::Key: Borrow<Q>,
    {
        let (root, deleted) = self
            .delete_impl::<NoWitness, _, _>(storage, shaper, key)
            .await?;
        Ok((root, deleted.map(|(value, ())| value)))
    }

    pub(crate) async fn delete_with_proof<Q: Ord + ?Sized, S: WriteNodeStorage<C>>(
        self,
        storage: &mut S,
        shaper: &C::Shaper,
        key: &Q,
    ) -> Result<(Self, Option<(C::Value, DeleteProof<C>)>), S::Error>
    where
        C::Key: Borrow<Q>,
    {
        let (new_root, deleted) = self
            .delete_impl::<RecordingWitness<C>, _, _>(storage, shaper, key)
            .await?;
        Ok((
            new_root,
            deleted.map(|(value, nodes)| (value, DeleteProof { nodes })),
        ))
    }

    #[inline(always)]
    async fn delete_impl<W: Witness<C>, Q: Ord + ?Sized, S: WriteNodeStorage<C>>(
        self,
        storage: &mut S,
        shaper: &C::Shaper,
        key: &Q,
    ) -> Result<(Self, Option<(C::Value, W::Nodes)>), S::Error>
    where
        C::Key: Borrow<Q>,
    {
        let mut leaf_search = self
            .leaf_search::<true, _>(storage, |k| k.borrow() <= key)
            .await?;

        let Ok(idx) = leaf_search
            .leaf
            .keys
            .as_ref()
            .binary_search_by(|k| k.borrow().cmp(key))
        else {
            return Ok((leaf_search.into_root(), None));
        };

        let mut witness = W::new(&leaf_search);
        let mut leaf = Arc::unwrap_or_clone(leaf_search.leaf);

        leaf.keys.remove_at(idx);
        let value = leaf.values.remove_at(idx);

        let elided = W::elide(|| (key, C::Hasher::hash_value(&value)));

        if leaf_search.path.is_empty()
            || leaf.keys.as_ref().len() >= shaper.min_leaf_entries().get()
        {
            let mut rebuild = RebuildAncestors::new(
                (leaf.hash(), TreeNode::Leaf(Arc::new(leaf))),
                leaf_search.path,
            );
            storage
                .store_nodes(rebuild.by_ref().inspect(|(_, n)| witness.record(n)))
                .await?;

            let new_root = rebuild.into_root();
            let proof = witness.finish(elided);
            return Ok((new_root, Some((value, proof))));
        }

        let (mut leaf_idx, internal) = leaf_search.path.pop().unwrap();
        let mut internal = Arc::unwrap_or_clone(internal);

        let get_leaf = async |idx| {
            let node = storage.get_node(&internal.children.as_ref()[idx]).await?;
            match node {
                TreeNode::Internal(_) => unreachable!("expected leaf"),
                TreeNode::Leaf(node) => Ok(node),
            }
        };

        let (first_candidate, second_candidate) =
            sibling_candidates(leaf_idx, internal.children.as_ref().len());

        let first_leaf = get_leaf(first_candidate.idx).await?;
        let mut second_leaf = None;

        for candidate in std::iter::once(&first_candidate).chain(second_candidate.as_ref()) {
            let is_first = std::ptr::eq(candidate, &first_candidate);
            let candidate_leaf = if is_first {
                &first_leaf
            } else {
                second_leaf.insert(get_leaf(candidate.idx).await?)
            };
            witness.record(&**candidate_leaf);

            if candidate_leaf.keys.as_ref().len() <= shaper.min_leaf_entries().get() {
                continue;
            }

            let mut candidate_leaf = Arc::unwrap_or_clone(if is_first {
                first_leaf
            } else {
                second_leaf.take().unwrap()
            });

            let (pair_idx, insert_idx) = if candidate.is_left {
                (candidate_leaf.keys.as_ref().len() - 1, 0)
            } else {
                (0, leaf.keys.as_ref().len())
            };
            leaf.keys
                .insert_at(insert_idx, candidate_leaf.keys.remove_at(pair_idx));
            leaf.values
                .insert_at(insert_idx, candidate_leaf.values.remove_at(pair_idx));

            if candidate.is_left {
                internal.keys.as_mut()[leaf_idx - 1].clone_from(&leaf.keys.as_ref()[0]);
            } else {
                internal.keys.as_mut()[leaf_idx].clone_from(&candidate_leaf.keys.as_ref()[0]);
            }

            let leaf = (leaf.hash(), TreeNode::Leaf(Arc::new(leaf)));
            let candidate_leaf = (
                candidate_leaf.hash(),
                TreeNode::Leaf(Arc::new(candidate_leaf)),
            );

            internal.children.as_mut()[leaf_idx].clone_from(&leaf.0);
            internal.children.as_mut()[candidate.idx].clone_from(&candidate_leaf.0);

            let mut rebuild = RebuildAncestors::new(
                (internal.hash(), TreeNode::Internal(Arc::new(internal))),
                leaf_search.path,
            );
            storage
                .store_nodes(
                    [leaf, candidate_leaf]
                        .into_iter()
                        .chain(rebuild.by_ref())
                        .inspect(|(_, n)| witness.record(n)),
                )
                .await?;

            let new_root = rebuild.into_root();
            let proof = witness.finish(elided);
            return Ok((new_root, Some((value, proof))));
        }

        let (merging_candidate, merging_leaf) = second_candidate
            .zip(second_leaf)
            .unwrap_or((first_candidate, first_leaf));
        let mut merging_leaf = Arc::unwrap_or_clone(merging_leaf);

        if merging_candidate.is_left {
            leaf_idx -= 1;

            merging_leaf.keys.append(leaf.keys);
            merging_leaf.values.append(leaf.values);

            leaf = merging_leaf;
        } else {
            leaf.keys.append(merging_leaf.keys);
            leaf.values.append(merging_leaf.values);
        }

        internal.keys.remove_at(leaf_idx);
        internal.children.remove_at(leaf_idx + 1);

        let leaf = (leaf.hash(), TreeNode::Leaf(Arc::new(leaf)));
        internal.children.as_mut()[leaf_idx].clone_from(&leaf.0);

        let is_runt = internal.children.as_ref().len() == 1;
        if is_runt && leaf_search.path.is_empty() {
            witness.record(&leaf.1);
            storage.store_nodes(std::iter::once(leaf.clone())).await?;

            let proof = witness.finish(elided);
            return Ok((leaf.1.into(), Some((value, proof))));
        }

        enum UnderfullState<C: TreeConfig> {
            Pending(TreeInternalNode<C>),
            Settled((HasherOutput<C>, TreeNode<C>)),
        }
        let is_underfull =
            is_runt || internal.children.as_ref().len() < shaper.min_internal_children().get();
        let mut state = if is_underfull {
            UnderfullState::Pending(internal)
        } else {
            UnderfullState::Settled((internal.hash(), TreeNode::Internal(Arc::new(internal))))
        };

        let mut pending = vec![leaf];

        while let UnderfullState::Pending(node) = state {
            let Some((child_idx, parent)) = leaf_search.path.pop() else {
                state = UnderfullState::Pending(node);
                break;
            };

            let mut parent = Arc::unwrap_or_clone(parent);

            let get_internal = async |idx| {
                let node = storage.get_node(&parent.children.as_ref()[idx]).await?;
                Ok(match node {
                    TreeNode::Leaf(_) => unreachable!("expected internal sibling"),
                    TreeNode::Internal(node) => node,
                })
            };

            let (first_candidate, second_candidate) =
                sibling_candidates(child_idx, parent.children.as_ref().len());

            let first_sibling = get_internal(first_candidate.idx).await?;
            let mut second_sibling = None;

            let min_to_donate = shaper.min_internal_children().get() + 1;

            let mut best_rotation = None;
            let mut merge_target = &first_candidate;

            for candidate in std::iter::once(&first_candidate).chain(second_candidate.as_ref()) {
                let is_first = std::ptr::eq(candidate, &first_candidate);
                let sibling = if is_first {
                    &first_sibling
                } else {
                    second_sibling.insert(get_internal(candidate.idx).await?)
                };
                witness.record(&**sibling);

                let len = sibling.children.as_ref().len();
                let merge_would_overflow =
                    node.children.as_ref().len() + len > shaper.max_internal_children().get();

                let qualifies_to_rotate = len >= min_to_donate
                    && (merge_would_overflow || len > shaper.min_internal_children().get());
                let is_better_rotation = best_rotation.is_none_or(|(_, best_len)| len > best_len);

                if qualifies_to_rotate && is_better_rotation {
                    best_rotation = Some((candidate, len));
                }

                if !merge_would_overflow {
                    merge_target = candidate;
                }

                if qualifies_to_rotate && len > shaper.min_internal_children().get() {
                    break;
                }
            }

            if let Some((rotation_candidate, _)) = best_rotation {
                let mut sibling =
                    Arc::unwrap_or_clone(if std::ptr::eq(rotation_candidate, &first_candidate) {
                        first_sibling
                    } else {
                        second_sibling.unwrap()
                    });
                let mut node = node;

                if rotation_candidate.is_left {
                    let donated = sibling
                        .children
                        .remove_at(sibling.children.as_ref().len() - 1);
                    let old_sep = std::mem::replace(
                        &mut parent.keys.as_mut()[child_idx - 1],
                        sibling.keys.remove_at(sibling.keys.as_ref().len() - 1),
                    );

                    node.keys.insert_at(0, old_sep);
                    node.children.insert_at(0, donated);
                } else {
                    let donated = sibling.children.remove_at(0);
                    let old_sep = std::mem::replace(
                        &mut parent.keys.as_mut()[child_idx],
                        sibling.keys.remove_at(0),
                    );

                    node.keys.insert_at(node.keys.as_ref().len(), old_sep);
                    node.children
                        .insert_at(node.children.as_ref().len(), donated);
                }

                let node = (node.hash(), TreeNode::Internal(Arc::new(node)));
                let sibling = (sibling.hash(), TreeNode::Internal(Arc::new(sibling)));
                parent.children.as_mut()[child_idx].clone_from(&node.0);
                parent.children.as_mut()[rotation_candidate.idx].clone_from(&sibling.0);

                let mut rebuild = RebuildAncestors::new(
                    (parent.hash(), TreeNode::Internal(Arc::new(parent))),
                    leaf_search.path,
                );
                storage
                    .store_nodes(
                        pending
                            .into_iter()
                            .chain([node, sibling])
                            .chain(rebuild.by_ref())
                            .inspect(|(_, n)| witness.record(n)),
                    )
                    .await?;

                let new_root = rebuild.into_root();
                let proof = witness.finish(elided);
                return Ok((new_root, Some((value, proof))));
            }

            let mut merging_sibling =
                Arc::unwrap_or_clone(if std::ptr::eq(merge_target, &first_candidate) {
                    first_sibling
                } else {
                    second_sibling.unwrap()
                });
            let mut node = node;

            let merged_child_idx = if merge_target.is_left {
                let sep = parent.keys.remove_at(child_idx - 1);

                parent.children.remove_at(child_idx);

                merging_sibling
                    .keys
                    .insert_at(merging_sibling.keys.as_ref().len(), sep);
                merging_sibling.keys.append(node.keys);
                merging_sibling.children.append(node.children);
                node = merging_sibling;

                child_idx - 1
            } else {
                let sep = parent.keys.remove_at(child_idx);

                parent.children.remove_at(child_idx + 1);

                node.keys.insert_at(node.keys.as_ref().len(), sep);
                node.keys.append(merging_sibling.keys);
                node.children.append(merging_sibling.children);

                child_idx
            };

            if parent.children.as_ref().len() == 1 && leaf_search.path.is_empty() {
                state = UnderfullState::Settled((node.hash(), TreeNode::Internal(Arc::new(node))));
                break;
            }

            let node = (node.hash(), TreeNode::Internal(Arc::new(node)));
            parent.children.as_mut()[merged_child_idx].clone_from(&node.0);
            pending.push(node);

            let still_underfull = parent.children.as_ref().len() == 1
                || parent.children.as_ref().len() < shaper.min_internal_children().get();

            state = if still_underfull {
                UnderfullState::Pending(parent)
            } else {
                UnderfullState::Settled((parent.hash(), TreeNode::Internal(Arc::new(parent))))
            };
        }

        let start = match state {
            UnderfullState::Pending(node) => (node.hash(), TreeNode::Internal(Arc::new(node))),
            UnderfullState::Settled(node) => node,
        };
        let mut rebuild = RebuildAncestors::new(start, leaf_search.path);
        storage
            .store_nodes(
                pending
                    .into_iter()
                    .chain(rebuild.by_ref())
                    .inspect(|(_, n)| witness.record(n)),
            )
            .await?;

        let new_root = rebuild.into_root();
        let proof = witness.finish(elided);
        Ok((new_root, Some((value, proof))))
    }
}

#[derive(Clone, Copy)]
struct Candidate {
    idx: usize,
    is_left: bool,
}

fn sibling_candidates(idx: usize, children_len: usize) -> (Candidate, Option<Candidate>) {
    if idx == 0 {
        (
            Candidate {
                idx: 1,
                is_left: false,
            },
            None,
        )
    } else {
        let left = Candidate {
            idx: idx - 1,
            is_left: true,
        };

        let right = (idx + 1 < children_len).then_some(Candidate {
            idx: idx + 1,
            is_left: false,
        });

        (left, right)
    }
}

/// A proof of a deletion operation that proves that the operation has deleted the required key only
/// and preserved B+Tree invariants in doing so.
#[derive_where(Debug; TransitionProofNode<C>)]
#[derive_where(Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(
    feature = "serde",
    serde(bound(
        serialize = "TransitionProofNode<C>: serde::Serialize",
        deserialize = "TransitionProofNode<C>: serde::Deserialize<'de>"
    ))
)]
pub struct DeleteProof<C: TreeConfig> {
    /// The old nodes the operation touched and the new nodes it produced.
    pub nodes: Box<[TransitionProofNode<C>]>,
}

impl<C: TreeConfig> DeleteProof<C> {
    /// Verifies that `old_root` has become `new_root` by deleting `key`, which held `value`, and
    /// respecting B+Tree invariants in doing so.
    pub fn verify<Q: Ord + ?Sized>(
        &self,
        old_root: &HasherOutput<C>,
        new_root: &HasherOutput<C>,
        key: &Q,
        value: &C::Value,
        shaper: &C::Shaper,
    ) -> Result<(), InvalidProofError>
    where
        C::Key: Borrow<Q>,
    {
        let value_hash = C::Hasher::hash_value(value);
        verify_transition::<C, _>(
            &self.nodes,
            old_root,
            new_root,
            key,
            &value_hash,
            shaper,
            |old, new| old == Some(&value_hash) && new.is_none(),
        )
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use rand::RngExt as _;
    use rand::SeedableRng as _;
    use rand::rngs::StdRng;

    use crate::tests::{
        all_test_shapers, corrupt, filled_tree, filled_tree_with_shaper, insert_orders, new_tree,
        new_tree_with_shaper, shaper, shaper_with_min_max, value_for,
    };

    use super::*;

    #[tokio::test]
    async fn delete_from_empty_tree_returns_none() {
        let mut tree = new_tree(5, 4);
        assert!(tree.delete(&42).await.unwrap().is_none());
    }

    #[tokio::test]
    async fn delete_returns_the_stored_value() {
        let mut tree = new_tree(5, 4);
        tree.insert(7, "seven".into()).await.unwrap();
        assert_eq!(tree.delete(&7).await.unwrap().as_deref(), Some("seven"));
    }

    #[tokio::test]
    async fn delete_then_get_returns_none() {
        let mut tree = new_tree(5, 4);
        tree.insert(3, "three".into()).await.unwrap();
        tree.delete(&3).await.unwrap();
        assert!(tree.get(&3).await.unwrap().is_none());
    }

    #[tokio::test]
    async fn delete_missing_key_returns_none_and_leaves_tree_intact() {
        let mut tree = new_tree(5, 4);
        tree.insert(1, "one".into()).await.unwrap();
        assert!(tree.delete(&99).await.unwrap().is_none());
        assert_eq!(tree.get(&1).await.unwrap().as_deref(), Some("one"));
    }

    #[tokio::test]
    async fn delete_missing_key_does_not_alter_root_hash() {
        let mut tree = filled_tree(5, 4, 0u64..10).await;
        let hash_before = tree.root_hash();
        tree.delete(&99).await.unwrap();
        assert_eq!(tree.root_hash(), hash_before);
    }

    #[tokio::test]
    async fn tree_after_insert_delete_matches_tree_that_never_had_key() {
        let base_keys = (1..=20).collect::<Vec<_>>();
        for s in all_test_shapers() {
            for extra_key in [0u64, 21, 100] {
                let mut a = new_tree_with_shaper(s);
                for &k in &base_keys {
                    a.insert(k, format!("val-{k}")).await.unwrap();
                }
                a.insert(extra_key, "extra".into()).await.unwrap();
                let removed = a.delete(&extra_key).await.unwrap();
                assert_eq!(
                    removed.as_deref(),
                    Some("extra"),
                    "shaper={s:?} extra_key={extra_key}"
                );
                for &k in &base_keys {
                    assert_eq!(
                        a.get(&k).await.unwrap().as_ref(),
                        Some(&format!("val-{k}")),
                        "shaper={s:?} extra_key={extra_key}: key {k} missing",
                    );
                }
                assert!(a.get(&extra_key).await.unwrap().is_none());
            }
        }
    }

    #[tokio::test]
    async fn root_hash_changes_after_delete() {
        let mut tree = new_tree(4, 3);
        tree.insert(1, "one".into()).await.unwrap();
        tree.insert(2, "two".into()).await.unwrap();
        let hash_before = tree.root_hash();
        tree.delete(&2).await.unwrap();
        assert_ne!(tree.root_hash(), hash_before);
    }

    #[tokio::test]
    async fn tree_shape_valid_after_partial_delete_across_shapers() {
        const N: u64 = 300;
        for s in all_test_shapers() {
            for delete_every in [2u64, 3, 5, 7] {
                let mut tree = filled_tree_with_shaper(s, 0..N).await;
                for k in (0..N).filter(|k| k % delete_every == 0) {
                    tree.delete(&k).await.unwrap();
                }
                for k in 0..N {
                    let got = tree.get(&k).await.unwrap();
                    if k % delete_every == 0 {
                        assert!(
                            got.is_none(),
                            "shaper={s:?} delete_every={delete_every}: deleted key {k} still present",
                        );
                    } else {
                        assert_eq!(
                            got.as_ref(),
                            Some(&value_for(k)),
                            "shaper={s:?} delete_every={delete_every}: surviving key {k} missing",
                        );
                    }
                }
            }
        }
    }

    #[tokio::test]
    async fn delete_all_keys_empties_tree_in_all_orders() {
        const N: u64 = 100;
        for s in all_test_shapers() {
            for (del_label, del_order) in insert_orders(N) {
                let mut tree = filled_tree_with_shaper(s, 0..N).await;
                for &k in &del_order {
                    let ret = tree.delete(&k).await.unwrap();
                    assert_eq!(
                        ret.as_deref(),
                        Some(value_for(k).as_str()),
                        "shaper={s:?} del_order={del_label}: wrong value for key {k}",
                    );
                }
                for k in 0..N {
                    assert!(
                        tree.get(&k).await.unwrap().is_none(),
                        "shaper={s:?} del_order={del_label}: key {k} survived",
                    );
                }
            }
        }
    }

    #[tokio::test]
    async fn delete_to_minimum_then_one_more_triggers_merge() {
        let s = shaper_with_min_max(2, 4, 2, 4);
        let mut tree = filled_tree_with_shaper(s, 0..8u64).await;
        for i in 0..4u64 {
            tree.delete(&i).await.unwrap();
        }
        tree.delete(&4).await.unwrap();
        for i in 5..8u64 {
            assert_eq!(
                tree.get(&i).await.unwrap().as_ref(),
                Some(&value_for(i)),
                "key {i} missing after merge",
            );
        }
    }

    #[tokio::test]
    async fn delete_proof_verifies_for_every_key_across_shapers() {
        for s in all_test_shapers() {
            for n in [1u64, 2, 5, 20, 50] {
                for k in 0..n {
                    let mut tree = filled_tree_with_shaper(s, 0..n).await;
                    let old_root = tree.root_hash();
                    let (val, proof) = tree.delete_with_proof(&k).await.unwrap().unwrap();
                    let new_root = tree.root_hash();
                    assert_eq!(val, value_for(k));
                    assert!(
                        proof
                            .verify(&old_root, &new_root, &k, &value_for(k), &s)
                            .is_ok(),
                        "shaper={s:?} n={n} k={k}: delete proof failed to verify",
                    );
                }
            }
        }
    }

    #[tokio::test]
    async fn delete_proof_wrong_value_is_rejected() {
        let s = shaper(4, 3);
        let mut tree = filled_tree_with_shaper(s, 0..20u64).await;
        let old_root = tree.root_hash();
        let (_, proof) = tree.delete_with_proof(&5).await.unwrap().unwrap();
        let new_root = tree.root_hash();
        assert!(
            proof
                .verify(&old_root, &new_root, &5, &"v5".to_string(), &s)
                .is_ok()
        );
        assert!(
            proof
                .verify(&old_root, &new_root, &5, &"wrong".to_string(), &s)
                .is_err()
        );
    }

    #[tokio::test]
    async fn delete_proof_wrong_key_is_rejected() {
        let s = shaper(4, 3);
        let mut tree = filled_tree_with_shaper(s, 0..20u64).await;
        let old_root = tree.root_hash();
        let (_, proof) = tree.delete_with_proof(&5).await.unwrap().unwrap();
        let new_root = tree.root_hash();
        assert!(
            proof
                .verify(&old_root, &new_root, &6, &"v5".to_string(), &s)
                .is_err()
        );
    }

    #[tokio::test]
    async fn delete_proof_swapped_roots_is_rejected() {
        let s = shaper(4, 3);
        let mut tree = filled_tree_with_shaper(s, 0..20u64).await;
        let old_root = tree.root_hash();
        let (_, proof) = tree.delete_with_proof(&5).await.unwrap().unwrap();
        let new_root = tree.root_hash();
        assert!(
            proof
                .verify(&new_root, &old_root, &5, &"v5".to_string(), &s)
                .is_err()
        );
    }

    #[tokio::test]
    async fn delete_proof_verifies_across_many_shapers_and_seeds() {
        const N_OPS: u64 = 300;
        const KEY_SPACE: u64 = 80;

        for s in all_test_shapers() {
            for seed in [1u64, 42, 0xdead] {
                let mut rng = StdRng::seed_from_u64(seed);
                let mut tree = new_tree_with_shaper(s);
                let mut oracle: BTreeMap<u64, String> = BTreeMap::new();

                for step in 0..N_OPS {
                    let key: u64 = rng.random_range(0..KEY_SPACE);
                    let insert: bool = rng.random_bool(0.6);

                    if insert {
                        let value = format!("s{seed}-step{step}-k{key}");
                        tree.insert(key, value.clone()).await.unwrap();
                        oracle.insert(key, value);
                    } else if oracle.contains_key(&key) {
                        let expected = oracle.remove(&key).unwrap();
                        let old_root = tree.root_hash();
                        let (val, proof) = tree.delete_with_proof(&key).await.unwrap().unwrap();
                        let new_root = tree.root_hash();
                        assert_eq!(val, expected);
                        assert!(
                            proof
                                .verify(&old_root, &new_root, &key, &expected, &s)
                                .is_ok(),
                            "shaper={s:?} seed={seed} step={step}: delete proof failed",
                        );
                    } else {
                        assert!(tree.delete(&key).await.unwrap().is_none());
                    }
                }
            }
        }
    }

    #[tokio::test]
    async fn delete_proof_new_leaf_entry_count_satisfies_invariants() {
        let s = shaper_with_min_max(2, 4, 2, 4);
        let mut tree = filled_tree_with_shaper(s, 0..8u64).await;
        for i in 0..4u64 {
            tree.delete(&i).await.unwrap();
        }

        let old_root = tree.root_hash();
        let (val, proof) = tree.delete_with_proof(&4).await.unwrap().unwrap();
        let new_root = tree.root_hash();
        assert_eq!(val, "v4");

        assert!(
            proof
                .verify(&old_root, &new_root, &4, &"v4".to_string(), &s)
                .is_ok(),
            "post-merge delete proof must verify",
        );
    }

    #[tokio::test]
    async fn delete_proof_corrupted_old_leaf_is_rejected() {
        let s = shaper(4, 3);
        let mut tree = filled_tree_with_shaper(s, 0..20u64).await;
        let old_root = tree.root_hash();
        let (_, mut proof) = tree.delete_with_proof(&5).await.unwrap().unwrap();
        let new_root = tree.root_hash();
        for node in &mut proof.nodes {
            if let TransitionProofNode::Leaf { keys, value_hashes } = node
                && keys.contains(&5)
            {
                corrupt(&mut value_hashes[0]);
            }
        }
        assert!(
            proof
                .verify(&old_root, &new_root, &5, &"v5".to_string(), &s)
                .is_err()
        );
    }
}
