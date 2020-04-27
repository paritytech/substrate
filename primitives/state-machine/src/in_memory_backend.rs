// Copyright 2017-2019 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! State machine in memory backend.

use crate::{
	StorageKey, StorageValue, StorageCollection,
	trie_backend::TrieBackend,
};
use std::{collections::{BTreeMap, HashMap}};
use hash_db::Hasher;
use sp_trie::{
	MemoryDB, TrieMut,
	trie_types::TrieDBMut,
};
use codec::Codec;
use sp_core::storage::{ChildInfo, Storage};

/// Insert input pairs into memory db.
fn insert_into_memory_db<H, I>(mut root: H::Out, mdb: &mut MemoryDB<H>, input: I) -> H::Out
where
	H: Hasher,
	I: IntoIterator<Item=(StorageKey, Option<StorageValue>)>,
{
	{
		let mut trie = if root == Default::default() {
			TrieDBMut::<H>::new(mdb, &mut root)
		} else {
			TrieDBMut::<H>::from_existing(mdb, &mut root).unwrap()
		};
		for (key, value) in input {
			if let Err(e) = match value {
				Some(value) => {
					trie.insert(&key, &value)
				},
				None => {
					trie.remove(&key)
				},
			}  {
				panic!("Failed to write to trie: {}", e);
			}
		}
		trie.commit();
	}
	root
}

/// Create a new empty instance of in-memory backend.
pub fn new_in_mem<H: Hasher>() -> TrieBackend<MemoryDB<H>, H>
where
	H::Out: Codec + Ord,
{
	let db = MemoryDB::default();
	let mut backend = TrieBackend::new(db, Default::default());
	backend.insert(std::iter::empty());
	backend
}

impl<H: Hasher> TrieBackend<MemoryDB<H>, H>
where
	H::Out: Codec + Ord,
{
	/// Copy the state, with applied updates
	pub fn update<
		T: IntoIterator<Item = (Option<ChildInfo>, StorageCollection)>
	>(
		&self,
		changes: T,
	) -> Self {
		let mut clone = self.clone();
		clone.insert(changes);
		clone
	}

	/// Insert values into backend trie.
	pub fn insert<
		T: IntoIterator<Item = (Option<ChildInfo>, StorageCollection)>
	>(
		&mut self,
		changes: T,
	) {
		let mut new_child_roots = Vec::new();
		let mut root_map = None;
		let root = self.root().clone();
		for (child_info, map) in changes {
			if let Some(child_info) = child_info.as_ref() {
				let prefix_storage_key = child_info.prefixed_storage_key();
				let ch = insert_into_memory_db::<H, _>(root, self.backend_storage_mut(), map.clone().into_iter());
				new_child_roots.push((prefix_storage_key.into_inner(), Some(ch.as_ref().into())));
			} else {
				root_map = Some(map);
			}
		}

		let root = match root_map {
			Some(map) => insert_into_memory_db::<H, _>(
				root,
				self.backend_storage_mut(),
				map.clone().into_iter().chain(new_child_roots.into_iter()),
			),
			None => insert_into_memory_db::<H, _>(
				root,
				self.backend_storage_mut(),
				new_child_roots.into_iter(),
			),
		};
		self.essence.set_root(root);
	}

	/// Merge trie nodes into this backend.
	pub fn update_backend(&self, root: H::Out, changes: MemoryDB<H>) -> Self {
		let mut clone = self.backend_storage().clone();
		clone.consolidate(changes);
		Self::new(clone, root)
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
		TrieBackend::new(self.backend_storage().clone(), self.root().clone())
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

impl<H: Hasher> From<HashMap<Option<ChildInfo>, BTreeMap<StorageKey, StorageValue>>>
	for TrieBackend<MemoryDB<H>, H>
where
	H::Out: Codec + Ord,
{
	fn from(inner: HashMap<Option<ChildInfo>, BTreeMap<StorageKey, StorageValue>>) -> Self {
		let mut backend = new_in_mem();
		backend.insert(inner.into_iter().map(|(k, m)| (k, m.into_iter().map(|(k, v)| (k, Some(v))).collect())));
		backend
	}
}

impl<H: Hasher> From<Storage> for TrieBackend<MemoryDB<H>, H>
where
	H::Out: Codec + Ord,
{
	fn from(inners: Storage) -> Self {
		let mut inner: HashMap<Option<ChildInfo>, BTreeMap<StorageKey, StorageValue>>
			= inners.children_default.into_iter().map(|(_k, c)| (Some(c.child_info), c.data)).collect();
		inner.insert(None, inners.top);
		inner.into()
	}
}

impl<H: Hasher> From<BTreeMap<StorageKey, StorageValue>> for TrieBackend<MemoryDB<H>, H>
where
	H::Out: Codec + Ord,
{
	fn from(inner: BTreeMap<StorageKey, StorageValue>) -> Self {
		let mut expanded = HashMap::new();
		expanded.insert(None, inner);
		expanded.into()
	}
}

impl<H: Hasher> From<Vec<(Option<ChildInfo>, StorageCollection)>>
	for TrieBackend<MemoryDB<H>, H>
where
	H::Out: Codec + Ord,
{
	fn from(
		inner: Vec<(Option<ChildInfo>, StorageCollection)>,
	) -> Self {
		let mut expanded: HashMap<Option<ChildInfo>, BTreeMap<StorageKey, StorageValue>>
			= HashMap::new();
		for (child_info, key_values) in inner {
			let entry = expanded.entry(child_info).or_default();
			for (key, value) in key_values {
				if let Some(value) = value {
					entry.insert(key, value);
				}
			}
		}
		expanded.into()
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use sp_runtime::traits::BlakeTwo256;
	use crate::backend::Backend;

	/// Assert in memory backend with only child trie keys works as trie backend.
	#[test]
	fn in_memory_with_child_trie_only() {
		let storage = new_in_mem::<BlakeTwo256>();
		let child_info = ChildInfo::new_default(b"1");
		let child_info = &child_info;
		let mut storage = storage.update(
			vec![(
				Some(child_info.clone()),
				vec![(b"2".to_vec(), Some(b"3".to_vec()))]
			)]
		);
		let trie_backend = storage.as_trie_backend().unwrap();
		assert_eq!(trie_backend.child_storage(child_info, b"2").unwrap(),
			Some(b"3".to_vec()));
		let storage_key = child_info.prefixed_storage_key();
		assert!(trie_backend.storage(storage_key.as_slice()).unwrap().is_some());
	}
}
