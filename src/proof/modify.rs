//! The insert/update operation.

use std::{borrow::Borrow, cmp::Ordering, iter::Rev, sync::Arc};

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
    pub(crate) async fn modify<const NEW: bool, S: WriteNodeStorage<C>>(
        self,
        storage: &mut S,
        shaper: &C::Shaper,
        key: C::Key,
        value: C::Value,
    ) -> Result<(Self, Option<Option<C::Value>>), S::Error> {
        let (root, pair) = self
            .modify_impl::<NEW, NoWitness, _>(storage, shaper, key, value)
            .await?;
        Ok((root, pair.map(|(v, ())| v)))
    }

    pub(crate) async fn modify_with_proof<const NEW: bool, S: WriteNodeStorage<C>>(
        self,
        storage: &mut S,
        shaper: &C::Shaper,
        key: C::Key,
        value: C::Value,
    ) -> Result<(Self, Option<(Option<C::Value>, ModifyProof<C>)>), S::Error> {
        let (new_root, pair) = self
            .modify_impl::<NEW, RecordingWitness<C>, _>(storage, shaper, key, value)
            .await?;
        Ok((new_root, pair.map(|(v, nodes)| (v, ModifyProof { nodes }))))
    }

    #[inline(always)]
    async fn modify_impl<const NEW: bool, W: Witness<C>, S: WriteNodeStorage<C>>(
        self,
        storage: &mut S,
        shaper: &C::Shaper,
        key: C::Key,
        value: C::Value,
    ) -> Result<(Self, Option<(Option<C::Value>, W::Nodes)>), S::Error> {
        let leaf_search = self.leaf_search::<true, _>(storage, |k| *k <= key).await?;

        let search_result = leaf_search.leaf.keys.as_ref().binary_search(&key);
        if NEW && search_result.is_ok() {
            return Ok((leaf_search.into_root(), None));
        }

        let mut witness = W::new(&leaf_search);
        let mut leaf = Arc::unwrap_or_clone(leaf_search.leaf);

        let elided = W::elide(|| (key.clone(), C::Hasher::hash_value(&value)));

        let (leaf, old_value) = match search_result {
            Ok(idx) => {
                let old_value = std::mem::replace(&mut leaf.values.as_mut()[idx], value);
                (leaf, Some(old_value))
            }
            Err(idx) if leaf.keys.as_ref().len() < shaper.max_leaf_entries().get() => {
                leaf.keys.insert_at(idx, key);
                leaf.values.insert_at(idx, value);
                (leaf, None)
            }
            Err(idx) => {
                let mut left_leaf = leaf;

                let split_at = (left_leaf.keys.as_ref().len() + 1).div_ceil(2);
                let target_length = if idx < split_at {
                    split_at - 1
                } else {
                    split_at
                };
                let mut right_leaf = TreeLeafNode::<C> {
                    keys: left_leaf.keys.split_off(target_length),
                    values: left_leaf.values.split_off(target_length),
                };

                let (current_leaf, new_entry_index) = if idx < split_at {
                    (&mut left_leaf, idx)
                } else {
                    (&mut right_leaf, idx - target_length)
                };
                current_leaf.keys.insert_at(new_entry_index, key);
                current_leaf.values.insert_at(new_entry_index, value);

                if leaf_search.path.is_empty() {
                    let mut node = TreeInternalNode::<C> {
                        keys: Default::default(),
                        children: Default::default(),
                    };
                    node.keys.push(right_leaf.keys.as_ref()[0].clone());

                    let (left_hash, right_hash) = (left_leaf.hash(), right_leaf.hash());
                    node.children.push(left_hash.clone());
                    node.children.push(right_hash.clone());

                    let node = (node.hash(), Arc::new(node));

                    storage
                        .store_nodes(
                            [(left_hash, left_leaf), (right_hash, right_leaf)]
                                .into_iter()
                                .map(|(hash, leaf)| (hash, TreeNode::Leaf(Arc::new(leaf))))
                                .chain(std::iter::once((
                                    node.0,
                                    TreeNode::Internal(node.1.clone()),
                                )))
                                .inspect(|(_, n)| witness.record(n)),
                        )
                        .await?;

                    let proof = witness.finish(elided);
                    return Ok((Self::Internal(node.1), Some((None, proof))));
                }

                let mut iter = SplitterIterator::Ready(ReadySplitterIterator {
                    split: Some(Split {
                        separator: right_leaf.keys.as_ref()[0].clone(),
                        node: (right_leaf.hash(), TreeNode::Leaf(Arc::new(right_leaf))),
                    }),
                    node: (left_leaf.hash(), TreeNode::Leaf(Arc::new(left_leaf))),
                    nodes_emitted: NodesEmitted::None,
                    path: leaf_search.path.into_iter().rev(),
                    shaper,
                });
                storage
                    .store_nodes(iter.by_ref().inspect(|(_, n)| witness.record(n)))
                    .await?;

                let SplitterIterator::Finished(root) = iter else {
                    unreachable!("storage implementation didn't consume entire iterator");
                };

                let proof = witness.finish(elided);
                return Ok((root.into(), Some((None, proof))));
            }
        };

        let start = (leaf.hash(), TreeNode::Leaf(Arc::new(leaf)));
        let mut rebuild = RebuildAncestors::new(start, leaf_search.path);
        storage
            .store_nodes(rebuild.by_ref().inspect(|(_, n)| witness.record(n)))
            .await?;

        let proof = witness.finish(elided);

        Ok((rebuild.into_root(), Some((old_value, proof))))
    }
}

struct Split<C: TreeConfig> {
    node: (HasherOutput<C>, TreeNode<C>),
    separator: C::Key,
}

struct ReadySplitterIterator<'a, C: TreeConfig> {
    node: (HasherOutput<C>, TreeNode<C>),
    split: Option<Split<C>>,
    nodes_emitted: NodesEmitted,
    path: Rev<std::vec::IntoIter<(usize, Arc<TreeInternalNode<C>>)>>,
    shaper: &'a C::Shaper,
}

enum SplitterIterator<'a, C: TreeConfig> {
    Ready(ReadySplitterIterator<'a, C>),
    Finished(TreeNode<C>),
    Dead,
}

enum NodesEmitted {
    None,
    Left,
    Right,
}

impl<C: TreeConfig> Iterator for SplitterIterator<'_, C> {
    type Item = (HasherOutput<C>, TreeNode<C>);

    fn next(&mut self) -> Option<Self::Item> {
        if !matches!(self, Self::Ready(_)) {
            return None;
        }
        // above check was used to ensure Finished won't get replaced
        let Self::Ready(mut ready) = std::mem::replace(self, Self::Dead) else {
            return None;
        };

        match ready.nodes_emitted {
            NodesEmitted::None => {
                let left_node = ready.node.clone();
                ready.nodes_emitted = NodesEmitted::Left;
                *self = Self::Ready(ready);
                return Some(left_node);
            }
            NodesEmitted::Left => {
                if let Some(right_node) = ready.split.as_ref().map(|s| s.node.clone()) {
                    ready.nodes_emitted = NodesEmitted::Right;
                    *self = Self::Ready(ready);
                    return Some(right_node);
                }
            }
            NodesEmitted::Right => {}
        }

        if let Some((child_idx, node)) = ready.path.next() {
            let mut node = Arc::unwrap_or_clone(node);

            node.children.as_mut()[child_idx] = ready.node.0;

            if let Some(split) = ready.split.take() {
                if node.children.as_ref().len() < ready.shaper.max_internal_children().get() {
                    node.keys.insert_at(child_idx, split.separator);
                    node.children.insert_at(child_idx + 1, split.node.0);

                    ready.node = (node.hash(), TreeNode::Internal(Arc::new(node)));
                } else {
                    let mut left_node = node;
                    let pivot_idx = left_node.keys.as_ref().len().div_ceil(2);

                    let (separator, right_node) = match child_idx.cmp(&pivot_idx) {
                        Ordering::Less => {
                            let separator = left_node.keys.remove_at(pivot_idx - 1);
                            let right_node = TreeInternalNode::<C> {
                                keys: left_node.keys.split_off(pivot_idx - 1),
                                children: left_node.children.split_off(pivot_idx),
                            };
                            left_node.keys.insert_at(child_idx, split.separator);
                            left_node.children.insert_at(child_idx + 1, split.node.0);
                            (separator, right_node)
                        }
                        Ordering::Equal => {
                            let mut right_node = TreeInternalNode::<C> {
                                keys: left_node.keys.split_off(pivot_idx),
                                children: left_node.children.split_off(pivot_idx + 1),
                            };
                            right_node.children.insert_at(0, split.node.0);
                            (split.separator, right_node)
                        }
                        Ordering::Greater => {
                            let separator = left_node.keys.remove_at(pivot_idx);
                            let mut right_node = TreeInternalNode::<C> {
                                keys: left_node.keys.split_off(pivot_idx),
                                children: left_node.children.split_off(pivot_idx + 1),
                            };
                            right_node
                                .keys
                                .insert_at(child_idx - pivot_idx - 1, split.separator);
                            right_node
                                .children
                                .insert_at(child_idx - pivot_idx, split.node.0);
                            (separator, right_node)
                        }
                    };

                    ready.node = (left_node.hash(), TreeNode::Internal(Arc::new(left_node)));
                    ready.split = Some(Split {
                        node: (right_node.hash(), TreeNode::Internal(Arc::new(right_node))),
                        separator,
                    });
                }
            } else {
                ready.node = (node.hash(), TreeNode::Internal(Arc::new(node)));
            }

            let left_node = ready.node.clone();

            ready.nodes_emitted = NodesEmitted::Left;
            *self = Self::Ready(ready);

            return Some(left_node);
        }

        let root = if let Some(split) = ready.split.take() {
            let mut root = TreeInternalNode::<C> {
                keys: Default::default(),
                children: Default::default(),
            };

            root.keys.push(split.separator);
            root.children.push(ready.node.0);
            root.children.push(split.node.0);

            (root.hash(), TreeNode::Internal(Arc::new(root)))
        } else {
            ready.node
        };

        *self = Self::Finished(root.1.clone());
        Some(root)
    }
}

/// A proof of a modify operation that proves that the operation has modified the specified key only
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
pub struct ModifyProof<C: TreeConfig> {
    /// The old nodes the operation touched and the new nodes it produced.
    pub nodes: Box<[TransitionProofNode<C>]>,
}

impl<C: TreeConfig> ModifyProof<C> {
    /// Verifies that `old_root` has become `new_root` by setting `key` to `new_value` and
    /// respecting B+Tree invariants in doing so.
    pub fn verify<Q: Ord + ?Sized>(
        &self,
        old_root: &HasherOutput<C>,
        new_root: &HasherOutput<C>,
        key: &Q,
        new_value: &C::Value,
        shaper: &C::Shaper,
    ) -> Result<(), InvalidProofError>
    where
        C::Key: Borrow<Q>,
    {
        let value_hash = C::Hasher::hash_value(new_value);
        verify_transition::<C, _>(
            &self.nodes,
            old_root,
            new_root,
            key,
            &value_hash,
            shaper,
            |_, new| new == Some(&value_hash),
        )
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use rand::RngExt as _;
    use rand::SeedableRng as _;
    use rand::rngs::StdRng;

    use crate::InsertNewError;
    use crate::proof::TransitionProofNode;
    use crate::tests::{
        all_test_shapers, assert_oracle, corrupt, filled_tree_with_shaper, insert_orders, new_tree,
        new_tree_with_shaper, shaper, value_for,
    };

    #[tokio::test]
    async fn insert_then_get_returns_value() {
        let mut tree = new_tree(5, 4);
        tree.insert(1, "one".into()).await.unwrap();
        assert_eq!(tree.get(&1).await.unwrap().as_ref(), Some(&"one".into()));
    }

    #[tokio::test]
    async fn insert_overwrites_existing_key() {
        let mut tree = new_tree(5, 4);
        tree.insert(1, "first".into()).await.unwrap();
        tree.insert(1, "second".into()).await.unwrap();
        assert_eq!(tree.get(&1).await.unwrap().as_ref(), Some(&"second".into()));
    }

    #[tokio::test]
    async fn insert_new_succeeds_for_fresh_key() {
        let mut tree = new_tree(5, 4);
        tree.insert_new(1, "one".into()).await.unwrap();
        assert_eq!(tree.get(&1).await.unwrap().as_ref(), Some(&"one".into()));
    }

    #[tokio::test]
    async fn insert_new_rejects_existing_key() {
        let mut tree = new_tree(5, 4);
        tree.insert_new(1, "original".into()).await.unwrap();
        let err = tree.insert_new(1, "replacement".into()).await.unwrap_err();
        assert!(matches!(err, InsertNewError::AlreadyExists));
        assert_eq!(
            tree.get(&1).await.unwrap().as_ref(),
            Some(&"original".into())
        );
    }

    #[tokio::test]
    async fn insert_new_then_insert_can_overwrite() {
        let mut tree = new_tree(5, 4);
        tree.insert_new(1, "original".into()).await.unwrap();
        tree.insert(1, "overwritten".into()).await.unwrap();
        assert_eq!(
            tree.get(&1).await.unwrap().as_ref(),
            Some(&"overwritten".into())
        );
    }

    #[tokio::test]
    async fn insert_new_succeeds_after_delete() {
        let mut tree = new_tree(5, 4);
        tree.insert_new(42, "original".into()).await.unwrap();
        tree.delete(&42).await.unwrap();
        tree.insert_new(42, "reborn".into()).await.unwrap();
        assert_eq!(
            tree.get(&42).await.unwrap().as_ref(),
            Some(&"reborn".into())
        );
    }

    #[tokio::test]
    async fn insert_new_does_not_mutate_root_on_rejection() {
        let mut tree = new_tree(3, 2);
        for i in 0..30u64 {
            tree.insert_new(i, format!("val-{i}")).await.unwrap();
        }
        let hash_before = tree.root_hash();
        for key in [0u64, 14, 29] {
            let err = tree
                .insert_new(key, "overwrite-attempt".into())
                .await
                .unwrap_err();
            assert!(matches!(err, InsertNewError::AlreadyExists));
            assert_eq!(tree.root_hash(), hash_before);
        }
        for i in 0..30u64 {
            assert_eq!(
                tree.get(&i).await.unwrap().as_ref(),
                Some(&format!("val-{i}"))
            );
        }
    }

    #[tokio::test]
    async fn identical_sequences_produce_identical_root_hash() {
        let ops = (0..40).collect::<Vec<_>>();
        let mut a = new_tree(4, 3);
        let mut b = new_tree(4, 3);
        for &k in &ops {
            a.insert(k, format!("val-{k}")).await.unwrap();
            b.insert(k, format!("val-{k}")).await.unwrap();
        }
        assert_eq!(a.root_hash(), b.root_hash());
    }

    #[tokio::test]
    async fn differing_content_produces_differing_root_hash() {
        let mut a = new_tree(4, 3);
        a.insert(1, "value-a".into()).await.unwrap();
        let mut b = new_tree(4, 3);
        b.insert(1, "value-b".into()).await.unwrap();
        assert_ne!(a.root_hash(), b.root_hash());
    }

    #[tokio::test]
    async fn root_hash_is_deterministic() {
        let ops = [
            (10u64, "ten"),
            (5, "five"),
            (20, "twenty"),
            (1, "one"),
            (15, "fifteen"),
            (8, "eight"),
            (3, "three"),
            (12, "twelve"),
        ];
        for s in all_test_shapers() {
            let mut a = new_tree_with_shaper(s);
            let mut b = new_tree_with_shaper(s);
            for &(k, v) in &ops {
                a.insert(k, v.into()).await.unwrap();
                b.insert(k, v.into()).await.unwrap();
            }
            assert_eq!(a.root_hash(), b.root_hash(), "shaper={s:?}");
        }
    }

    #[tokio::test]
    async fn tree_shape_valid_after_inserts_across_all_shapers_and_orders() {
        const N: u64 = 300;
        for s in all_test_shapers() {
            for (label, keys) in insert_orders(N) {
                let tree = filled_tree_with_shaper(s, keys).await;
                for k in 0..N {
                    assert_eq!(
                        tree.get(&k).await.unwrap().as_ref(),
                        Some(&value_for(k)),
                        "shaper={s:?} order={label} key={k}",
                    );
                }
            }
        }
    }

    #[tokio::test]
    async fn oracle_insert_only_many_seeds() {
        const N_OPS: u64 = 1000;
        const KEY_SPACE: u64 = 200;
        for s in all_test_shapers() {
            for seed in [1u64, 2, 3, 17, 42, 1337, 0xdead_beef, 0xcafe_babe] {
                let mut rng = StdRng::seed_from_u64(seed);
                let mut tree = new_tree_with_shaper(s);
                let mut oracle = BTreeMap::new();
                for step in 0..N_OPS {
                    let key: u64 = rng.random_range(0..KEY_SPACE);
                    let use_insert_new: bool = rng.random_bool(0.3);
                    let value = format!("s{seed}-step{step}-k{key}");
                    if use_insert_new {
                        let existed = oracle.contains_key(&key);
                        match tree.insert_new(key, value.clone()).await {
                            Ok(_) => {
                                assert!(!existed);
                                oracle.insert(key, value);
                            }
                            Err(InsertNewError::AlreadyExists) => assert!(existed),
                            Err(e) => panic!("storage error: {e}"),
                        }
                    } else {
                        tree.insert(key, value.clone()).await.unwrap();
                        oracle.insert(key, value);
                    }
                }
                assert_oracle(
                    &tree,
                    &oracle,
                    KEY_SPACE,
                    &format!("shaper={s:?} seed={seed}"),
                )
                .await;
            }
        }
    }

    #[tokio::test]
    async fn insert_proof_verifies_for_new_key() {
        for s in all_test_shapers() {
            for n in [0u64, 1, 5, 20, 50] {
                let mut tree = filled_tree_with_shaper(s, 0..n).await;
                let old_root = tree.root_hash();
                let proof = tree.insert_new_with_proof(n, value_for(n)).await.unwrap();
                let new_root = tree.root_hash();
                assert!(
                    proof
                        .verify(&old_root, &new_root, &n, &value_for(n), &s)
                        .is_ok(),
                    "shaper={s:?} n={n}: insert proof failed to verify",
                );
            }
        }
    }

    #[tokio::test]
    async fn insert_proof_verifies_for_update() {
        for s in all_test_shapers() {
            for n in [1u64, 5, 20, 50] {
                let mut tree = filled_tree_with_shaper(s, 0..n).await;
                for k in 0..n {
                    let old_root = tree.root_hash();
                    let (_, proof) = tree
                        .insert_with_proof(k, format!("new-v{k}"))
                        .await
                        .unwrap();
                    let new_root = tree.root_hash();
                    assert!(
                        proof
                            .verify(&old_root, &new_root, &k, &format!("new-v{k}"), &s)
                            .is_ok(),
                        "shaper={s:?} n={n} k={k}: update proof failed to verify",
                    );
                }
            }
        }
    }

    #[tokio::test]
    async fn insert_proof_wrong_new_value_is_rejected() {
        let s = shaper(4, 3);
        let mut tree = filled_tree_with_shaper(s, 0..20u64).await;
        let old_root = tree.root_hash();
        let (_, proof) = tree.insert_with_proof(5, "new".into()).await.unwrap();
        let new_root = tree.root_hash();
        assert!(
            proof
                .verify(&old_root, &new_root, &5, &"new".to_string(), &s)
                .is_ok()
        );
        assert!(
            proof
                .verify(&old_root, &new_root, &5, &"wrong".to_string(), &s)
                .is_err()
        );
    }

    #[tokio::test]
    async fn insert_proof_wrong_new_root_is_rejected() {
        let s = shaper(4, 3);
        let mut tree = filled_tree_with_shaper(s, 0..20u64).await;
        let old_root = tree.root_hash();
        let (_, proof) = tree.insert_with_proof(99, "new".into()).await.unwrap();
        assert!(
            proof
                .verify(&old_root, &old_root, &99, &"new".to_string(), &s)
                .is_err(),
            "using old_root as new_root must be rejected",
        );
    }

    #[tokio::test]
    async fn insert_proof_wrong_key_is_rejected() {
        let s = shaper(4, 3);
        let mut tree = filled_tree_with_shaper(s, 0..20u64).await;
        let old_root = tree.root_hash();
        let (_, proof) = tree.insert_with_proof(5, "new-v5".into()).await.unwrap();
        let new_root = tree.root_hash();
        assert!(
            proof
                .verify(&old_root, &new_root, &6, &"new-v5".to_string(), &s)
                .is_err()
        );
    }

    #[tokio::test]
    async fn insert_proof_wrong_old_root_is_rejected() {
        let s = shaper(4, 3);
        let mut tree = filled_tree_with_shaper(s, 0..20u64).await;
        let old_root = tree.root_hash();
        let (_, proof) = tree.insert_with_proof(5, "updated".into()).await.unwrap();
        let new_root = tree.root_hash();
        assert!(
            proof
                .verify(&old_root, &new_root, &5, &"updated".to_string(), &s)
                .is_ok()
        );
        let mut bad_old_root = old_root;
        corrupt(&mut bad_old_root);
        assert!(
            proof
                .verify(&bad_old_root, &new_root, &5, &"updated".to_string(), &s)
                .is_err(),
            "corrupted old_root must be rejected",
        );
    }

    #[tokio::test]
    async fn insert_proof_swapped_roots_is_rejected() {
        let s = shaper(4, 3);
        let mut tree = filled_tree_with_shaper(s, 0..20u64).await;
        let old_root = tree.root_hash();
        let (_, proof) = tree.insert_with_proof(99, "new".into()).await.unwrap();
        let new_root = tree.root_hash();
        assert!(
            proof
                .verify(&old_root, &new_root, &99, &"new".to_string(), &s)
                .is_ok()
        );
        assert!(
            proof
                .verify(&new_root, &old_root, &99, &"new".to_string(), &s)
                .is_err(),
            "swapping old_root and new_root must be rejected",
        );
    }

    #[tokio::test]
    async fn insert_proof_verifies_across_many_shapers_and_seeds() {
        const N_OPS: u64 = 300;
        const KEY_SPACE: u64 = 80;
        for s in all_test_shapers() {
            for seed in [1u64, 42, 0xdead] {
                let mut rng = StdRng::seed_from_u64(seed);
                let mut tree = new_tree_with_shaper(s);
                let mut oracle: BTreeMap<u64, String> = BTreeMap::new();
                for step in 0..N_OPS {
                    let key: u64 = rng.random_range(0..KEY_SPACE);
                    let new_value = format!("s{seed}-step{step}-k{key}");
                    let old_root = tree.root_hash();
                    let (_, proof) = tree
                        .insert_with_proof(key, new_value.clone())
                        .await
                        .unwrap();
                    let new_root = tree.root_hash();
                    assert!(
                        proof
                            .verify(&old_root, &new_root, &key, &new_value, &s)
                            .is_ok(),
                        "shaper={s:?} seed={seed} step={step}: proof failed",
                    );
                    oracle.insert(key, new_value);

                    if step % 50 == 0 {
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
    }

    #[tokio::test]
    async fn insert_proof_corrupted_leaf_is_rejected() {
        let s = shaper(4, 3);
        let mut tree = filled_tree_with_shaper(s, 0..20u64).await;
        let old_root = tree.root_hash();
        let (_, mut proof) = tree.insert_with_proof(5, "new".into()).await.unwrap();
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
                .verify(&old_root, &new_root, &5, &"new".to_string(), &s)
                .is_err()
        );
    }
}
