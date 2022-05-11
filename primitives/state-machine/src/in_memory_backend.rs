// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! State machine in memory backend.

use crate::{
	backend::Backend, trie_backend::TrieBackend, StorageCollection, StorageKey, StorageValue,
};
use codec::Codec;
use hash_db::Hasher;
use sp_core::storage::{ChildInfo, StateVersion, Storage};
use sp_trie::{empty_trie_root, LayoutV1, MemoryDB};
use std::collections::{BTreeMap, HashMap};

/// Create a new empty instance of in-memory backend.
pub fn new_in_mem<H: Hasher>() -> TrieBackend<MemoryDB<H>, H>
where
	H::Out: Codec + Ord,
{
	let db = MemoryDB::default();
	// V1 is same as V0 for an empty trie.
	TrieBackend::new(db, empty_trie_root::<LayoutV1<H>>())
}

impl<H: Hasher> TrieBackend<MemoryDB<H>, H>
where
	H::Out: Codec + Ord,
{
	/// Copy the state, with applied updates
	pub fn update<T: IntoIterator<Item = (Option<ChildInfo>, StorageCollection)>>(
		&self,
		changes: T,
		state_version: StateVersion,
	) -> Self {
		let mut clone = self.clone();
		clone.insert(changes, state_version);
		clone
	}

	/// Insert values into backend trie.
	pub fn insert<T: IntoIterator<Item = (Option<ChildInfo>, StorageCollection)>>(
		&mut self,
		changes: T,
		state_version: StateVersion,
	) {
		let (top, child) = changes.into_iter().partition::<Vec<_>, _>(|v| v.0.is_none());
		let (root, transaction) = self.full_storage_root(
			top.iter().flat_map(|(_, v)| v).map(|(k, v)| (&k[..], v.as_deref())),
			child.iter().filter_map(|v| {
				v.0.as_ref().map(|c| (c, v.1.iter().map(|(k, v)| (&k[..], v.as_deref()))))
			}),
			state_version,
		);

		self.apply_transaction(root, transaction);
	}

	/// Merge trie nodes into this backend.
	pub fn update_backend(&self, root: H::Out, changes: MemoryDB<H>) -> Self {
		let mut clone = self.backend_storage().clone();
		clone.consolidate(changes);
		Self::new(clone, root)
	}

	/// Apply the given transaction to this backend and set the root to the given value.
	pub fn apply_transaction(&mut self, root: H::Out, transaction: MemoryDB<H>) {
		let mut storage = sp_std::mem::take(self).into_storage();
		storage.consolidate(transaction);
		*self = TrieBackend::new(storage, root);
	}

	/// Compare with another in-memory backend.
	pub fn eq(&self, other: &Self) -> bool {
		self.root() == other.root()
	}
}

impl<H: Hasher> Clone for TrieBackend<MemoryDB<H>, H>
where
	H::Out: Codec + Ord,
{
	fn clone(&self) -> Self {
		TrieBackend::new(self.backend_storage().clone(), *self.root())
	}
}

impl<H: Hasher> Default for TrieBackend<MemoryDB<H>, H>
where
	H::Out: Codec + Ord,
{
	fn default() -> Self {
		new_in_mem()
	}
}

impl<H: Hasher> From<(HashMap<Option<ChildInfo>, BTreeMap<StorageKey, StorageValue>>, StateVersion)>
	for TrieBackend<MemoryDB<H>, H>
where
	H::Out: Codec + Ord,
{
	fn from(
		(inner, state_version): (
			HashMap<Option<ChildInfo>, BTreeMap<StorageKey, StorageValue>>,
			StateVersion,
		),
	) -> Self {
		let mut backend = new_in_mem();
		backend.insert(
			inner
				.into_iter()
				.map(|(k, m)| (k, m.into_iter().map(|(k, v)| (k, Some(v))).collect())),
			state_version,
		);
		backend
	}
}

impl<H: Hasher> From<(Storage, StateVersion)> for TrieBackend<MemoryDB<H>, H>
where
	H::Out: Codec + Ord,
{
	fn from((inners, state_version): (Storage, StateVersion)) -> Self {
		let mut inner: HashMap<Option<ChildInfo>, BTreeMap<StorageKey, StorageValue>> = inners
			.children_default
			.into_iter()
			.map(|(_k, c)| (Some(c.child_info), c.data))
			.collect();
		inner.insert(None, inners.top);
		(inner, state_version).into()
	}
}

impl<H: Hasher> From<(BTreeMap<StorageKey, StorageValue>, StateVersion)>
	for TrieBackend<MemoryDB<H>, H>
where
	H::Out: Codec + Ord,
{
	fn from((inner, state_version): (BTreeMap<StorageKey, StorageValue>, StateVersion)) -> Self {
		let mut expanded = HashMap::new();
		expanded.insert(None, inner);
		(expanded, state_version).into()
	}
}

impl<H: Hasher> From<(Vec<(Option<ChildInfo>, StorageCollection)>, StateVersion)>
	for TrieBackend<MemoryDB<H>, H>
where
	H::Out: Codec + Ord,
{
	fn from(
		(inner, state_version): (Vec<(Option<ChildInfo>, StorageCollection)>, StateVersion),
	) -> Self {
		let mut expanded: HashMap<Option<ChildInfo>, BTreeMap<StorageKey, StorageValue>> =
			HashMap::new();
		for (child_info, key_values) in inner {
			let entry = expanded.entry(child_info).or_default();
			for (key, value) in key_values {
				if let Some(value) = value {
					entry.insert(key, value);
				}
			}
		}
		(expanded, state_version).into()
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::backend::Backend;
	use sp_core::storage::StateVersion;
	use sp_runtime::traits::BlakeTwo256;

	/// Assert in memory backend with only child trie keys works as trie backend.
	#[test]
	fn in_memory_with_child_trie_only() {
		let state_version = StateVersion::default();
		let storage = new_in_mem::<BlakeTwo256>();
		let child_info = ChildInfo::new_default(b"1");
		let child_info = &child_info;
		let storage = storage.update(
			vec![(Some(child_info.clone()), vec![(b"2".to_vec(), Some(b"3".to_vec()))])],
			state_version,
		);
		let trie_backend = storage.as_trie_backend().unwrap();
		assert_eq!(trie_backend.child_storage(child_info, b"2").unwrap(), Some(b"3".to_vec()));
		let storage_key = child_info.prefixed_storage_key();
		assert!(trie_backend.storage(storage_key.as_slice()).unwrap().is_some());
	}

	#[test]
	fn insert_multiple_times_child_data_works() {
		let state_version = StateVersion::default();
		let mut storage = new_in_mem::<BlakeTwo256>();
		let child_info = ChildInfo::new_default(b"1");

		storage.insert(
			vec![(Some(child_info.clone()), vec![(b"2".to_vec(), Some(b"3".to_vec()))])],
			state_version,
		);
		storage.insert(
			vec![(Some(child_info.clone()), vec![(b"1".to_vec(), Some(b"3".to_vec()))])],
			state_version,
		);

		assert_eq!(storage.child_storage(&child_info, &b"2"[..]), Ok(Some(b"3".to_vec())));
		assert_eq!(storage.child_storage(&child_info, &b"1"[..]), Ok(Some(b"3".to_vec())));
	}
}
