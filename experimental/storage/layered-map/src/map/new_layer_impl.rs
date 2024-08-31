// Copyright (c) Aptos Foundation
// SPDX-License-Identifier: Apache-2.0

use crate::{
    metrics::TIMER,
    node::{CollisionCell, LeafContent, LeafNode, NodeRef, NodeStrongRef},
    Key, KeyHash, LayeredMap, MapLayer, Value,
};
use aptos_drop_helper::ArcAsyncDrop;
use aptos_metrics_core::TimerHelper;
use itertools::Itertools;
use std::collections::BTreeMap;

impl<K, V, S> LayeredMap<K, V, S>
where
    K: ArcAsyncDrop + Key,
    V: ArcAsyncDrop + Value,
{
    fn new_leaf(&self, key_hash: KeyHash, items: &[Item<K, V>]) -> NodeRef<K, V> {
        let new_layer = self.top_layer() + 1;
        NodeRef::new_leaf(key_hash, to_leaf_content(items, new_layer), new_layer)
    }

    fn new_leaf_overwriting_old(
        &self,
        key_hash: KeyHash,
        old_leaf: &LeafNode<K, V>,
        new_items: &[Item<K, V>],
    ) -> NodeRef<K, V> {
        let new_layer = self.top_layer() + 1;

        let old = old_leaf.content.clone();
        let new = to_leaf_content(new_items, new_layer);
        let content = old.combined_with(old_leaf.layer, new, new_layer, self.base_layer());

        NodeRef::new_leaf(key_hash, content, new_layer)
    }

    fn new_internal(&self, left: NodeRef<K, V>, right: NodeRef<K, V>) -> NodeRef<K, V> {
        NodeRef::new_internal(left, right, self.top_layer() + 1)
    }

    fn branch_down(
        &self,
        depth: usize,
        node: NodeStrongRef<K, V>,
    ) -> (NodeStrongRef<K, V>, NodeStrongRef<K, V>) {
        use crate::node::NodeStrongRef::*;

        match &node {
            Empty => (Empty, Empty),
            Leaf(leaf) => {
                if leaf.key_hash.bit(depth) {
                    (Empty, node)
                } else {
                    (node, Empty)
                }
            },
            Internal(internal) => (
                self.get_node_strong(&internal.left),
                self.get_node_strong(&internal.right),
            ),
        }
    }

    fn merge_up(&self, left: NodeRef<K, V>, right: NodeRef<K, V>) -> NodeRef<K, V> {
        use crate::node::NodeRef::*;

        match (&left, &right) {
            (Empty, Leaf(..)) => right,
            (Leaf(..), Empty) => left,
            (Empty, Empty) => unreachable!("merge_up with two empty nodes"),
            _ => self.new_internal(left, right),
        }
    }

    fn create_tree(
        &self,
        depth: usize,
        current_root: NodeStrongRef<K, V>,
        items: &[Item<K, V>],
    ) -> NodeRef<K, V> {
        if items.is_empty() {
            return current_root.weak_ref();
        }

        // See if the whole range is of the same key hash, which maps to a leaf node
        let first_key_hash = items[0].key_hash();
        if first_key_hash == items[items.len() - 1].key_hash() {
            match &current_root {
                NodeStrongRef::Empty => return self.new_leaf(first_key_hash, items),
                NodeStrongRef::Leaf(leaf) => {
                    if leaf.key_hash == first_key_hash {
                        return self.new_leaf_overwriting_old(first_key_hash, leaf, items);
                    }
                },
                NodeStrongRef::Internal(_) => {},
            }
        }

        let pivot = items.partition_point(|item| !item.key_hash.bit(depth));
        let (left_items, right_items) = items.split_at(pivot);
        let (left_root, right_root) = self.branch_down(depth, current_root);
        self.merge_up(
            self.create_tree(depth + 1, left_root, left_items),
            self.create_tree(depth + 1, right_root, right_items),
        )
    }

    pub fn new_layer_with_hasher(&self, kvs: &[(K, V)], hash_builder: &S) -> MapLayer<K, V>
    where
        S: core::hash::BuildHasher,
    {
        let _timer = TIMER.timer_with(&[self.top_layer.use_case(), "new_layer"]);

        // Hash the keys and sort items in key hash order.
        //
        // n.b. no need to dedup at this point, as we will do it anyway at the leaf level.
        let items = kvs
            .iter()
            .map(|kv| {
                let key = &kv.0;
                let key_hash = KeyHash(hash_builder.hash_one(key));
                Item { key_hash, kv }
            })
            .sorted_by_key(Item::full_key)
            .collect_vec();

        let root = self.create_tree(0, self.root(), &items);

        self.top_layer.spawn(root, self.base_layer())
    }

    pub fn new_layer(&self, items: &[(K, V)]) -> MapLayer<K, V>
    where
        S: core::hash::BuildHasher + Default,
    {
        self.new_layer_with_hasher(items, &Default::default())
    }
}

pub(crate) struct Item<'a, K, V> {
    key_hash: KeyHash,
    kv: &'a (K, V),
}

impl<'a, K, V> Item<'a, K, V> {
    fn key_hash(&self) -> KeyHash {
        self.key_hash
    }

    fn key(&self) -> &'a K {
        &self.kv.0
    }

    /// Full key used for sorting and deduplication.
    ///
    /// Inequality is detected if key hash is different, keys only need to be compared in case of
    /// hash collision.
    fn full_key(&self) -> (KeyHash, &'a K) {
        (self.key_hash(), self.key())
    }

    fn kv(&self) -> &(K, V) {
        self.kv
    }
}

fn to_leaf_content<K: Key, V: Value>(items: &[Item<K, V>], layer: u64) -> LeafContent<K, V> {
    assert!(!items.is_empty());
    if items.len() == 1 {
        let (key, value) = items[0].kv().clone();
        LeafContent::UniqueLatest { key, value }
    } else {
        // deduplication
        let mut map: BTreeMap<_, _> = items
            .iter()
            .map(|item| {
                let (key, value) = item.kv().clone();
                (key, CollisionCell { value, layer })
            })
            .collect();
        if map.len() == 1 {
            let (key, cell) = map.pop_first().unwrap();
            LeafContent::UniqueLatest {
                key,
                value: cell.value,
            }
        } else {
            LeafContent::Collision(map)
        }
    }
}
