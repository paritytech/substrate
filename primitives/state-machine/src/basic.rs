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

//! Basic implementation for Externalities.

use crate::{Changes, StorageKey, StorageValue};
use codec::Encode;
use hash_db::Hasher;
use log::warn;
use sp_core::{
	storage::{
		well_known_keys::is_child_storage_key, ChildInfo, ChildType, StateVersion, Storage,
		StorageChild, TrackedStorageKey,
	},
	traits::Externalities,
	Blake2Hasher,
};
use sp_externalities::{result_from_slice, Extension, Extensions, MultiRemovalResults};
use sp_trie::{empty_child_trie_root, HashKey, LayoutV0, LayoutV1, TrieConfiguration};
use std::{
	any::{Any, TypeId},
	borrow::Cow,
	collections::BTreeMap,
	iter::FromIterator,
};

/// Simple Map-based Externalities impl.
#[derive(Debug)]
pub struct BasicExternalities {
	overlay: Changes,
	extensions: Extensions,
}

impl BasicExternalities {
	/// Create a new instance of `BasicExternalities`
	pub fn new(inner: Storage) -> Self {
		BasicExternalities { overlay: inner.into(), extensions: Default::default() }
	}

	/// New basic externalities with empty storage.
	pub fn new_empty() -> Self {
		Self::new(Storage::default())
	}

	/// Insert key/value
	pub fn insert(&mut self, k: StorageKey, v: StorageValue) {
		self.overlay.set_storage(k, Some(v));
	}

	/// Consume self and returns inner storages
	pub fn into_storages(self) -> Storage {
		let mut children_default: std::collections::HashMap<Vec<u8>, StorageChild> =
			Default::default();
		self.overlay.children().for_each(|(iter, i)| {
			let child = StorageChild {
				data: iter
					.filter_map(|(k, v)| v.value().map(|v| (k.to_vec(), v.to_vec())))
					.collect(),
				info: i.clone(),
			};
			children_default.insert(i.name.clone(), child);
		});
		Storage {
			top: self
				.overlay
				.changes()
				.filter_map(|(k, v)| v.value().map(|v| (k.to_vec(), v.to_vec())))
				.collect(),
			children_default,
		}
	}

	/// Execute the given closure `f` with the externalities set and initialized with `storage`.
	///
	/// Returns the result of the closure and updates `storage` with all changes.
	pub fn execute_with_storage<R>(
		storage: &mut sp_core::storage::Storage,
		f: impl FnOnce() -> R,
	) -> R {
		let mut ext = Self::new(std::mem::take(storage));

		let r = ext.execute_with(f);

		*storage = ext.into_storages();

		r
	}

	/// Execute the given closure while `self` is set as externalities.
	///
	/// Returns the result of the given closure.
	pub fn execute_with<R>(&mut self, f: impl FnOnce() -> R) -> R {
		sp_externalities::set_and_run_with_externalities(self, f)
	}

	/// List of active extensions.
	pub fn extensions(&mut self) -> &mut Extensions {
		&mut self.extensions
	}

	/// Register an extension.
	pub fn register_extension(&mut self, ext: impl Extension) {
		self.extensions.register(ext);
	}
}

impl PartialEq for BasicExternalities {
	fn eq(&self, other: &BasicExternalities) -> bool {
		self.overlay.changes().map(|(k, v)| (k, v.value())).collect::<BTreeMap<_, _>>() ==
			other.overlay.changes().map(|(k, v)| (k, v.value())).collect::<BTreeMap<_, _>>() &&
			self.overlay
				.children()
				.map(|(iter, i)| (i, iter.map(|(k, v)| (k, v.value())).collect::<BTreeMap<_, _>>()))
				.collect::<BTreeMap<_, _>>() ==
				other
					.overlay
					.children()
					.map(|(iter, i)| {
						(i, iter.map(|(k, v)| (k, v.value())).collect::<BTreeMap<_, _>>())
					})
					.collect::<BTreeMap<_, _>>()
	}
}

impl FromIterator<(StorageKey, StorageValue)> for BasicExternalities {
	fn from_iter<I: IntoIterator<Item = (StorageKey, StorageValue)>>(iter: I) -> Self {
		let mut t = Self::default();
		iter.into_iter().for_each(|(k, v)| t.insert(k, v));
		t
	}
}

impl Default for BasicExternalities {
	fn default() -> Self {
		Self::new(Default::default())
	}
}

impl From<BTreeMap<StorageKey, StorageValue>> for BasicExternalities {
	fn from(map: BTreeMap<StorageKey, StorageValue>) -> Self {
		Self::from_iter(map.into_iter())
	}
}

impl Externalities for BasicExternalities {
	fn set_offchain_storage(&mut self, _key: &[u8], _value: Option<&[u8]>) {}

	fn storage(&mut self, key: &[u8], start: u32, limit: Option<u32>) -> Option<Cow<[u8]>> {
		self.overlay.storage(key).and_then(|v| result_from_slice(v, start, limit))
	}

	fn storage_hash(&mut self, key: &[u8]) -> Option<Vec<u8>> {
		self.overlay.storage(key).flatten().map(|v| Blake2Hasher::hash(v).encode())
	}

	fn child_storage(
		&mut self,
		child_info: &ChildInfo,
		key: &[u8],
		start: u32,
		limit: Option<u32>,
	) -> Option<Cow<[u8]>> {
		self.overlay.child_storage(child_info, key, start, limit).flatten()
	}

	fn child_storage_len(&mut self, child_info: &ChildInfo, key: &[u8]) -> Option<u32> {
		self.overlay.child_storage_len(child_info, key).flatten()
	}

	fn child_storage_hash(&mut self, child_info: &ChildInfo, key: &[u8]) -> Option<Vec<u8>> {
		self.overlay
			.child_storage(child_info, key, 0, None)
			.flatten()
			.map(|v| Blake2Hasher::hash(v.as_ref()).encode())
	}

	fn next_storage_key(&mut self, key: &[u8]) -> Option<StorageKey> {
		self.overlay.iter_after(key).find_map(|(k, v)| v.value().map(|_| k.to_vec()))
	}

	fn next_child_storage_key(
		&mut self,
		child_info: &ChildInfo,
		key: &[u8],
		count: u32,
	) -> Option<Vec<StorageKey>> {
		let iter = self.overlay.child_iter_after(child_info, key)?;

		let mut result = Vec::with_capacity(count as usize);
		if count == 0 {
			return Some(result)
		}
		for (k, v) in iter {
			if v.value().is_some() {
				result.push(k.to_vec());
				if result.len() == count as usize {
					break
				}
			}
		}
		Some(result)
	}

	fn place_storage(&mut self, key: StorageKey, maybe_value: Option<StorageValue>) {
		if is_child_storage_key(&key) {
			warn!(target: "trie", "Refuse to set child storage key via main storage");
			return
		}

		self.overlay.set_storage(key, maybe_value)
	}

	fn place_child_storage(
		&mut self,
		child_info: &ChildInfo,
		key: &[u8],
		value: Option<&[u8]>,
	) -> bool {
		self.overlay.set_child_storage(child_info, key, value)
	}

	fn kill_child_storage(
		&mut self,
		child_info: &ChildInfo,
		_maybe_limit: Option<u32>,
		_maybe_cursor: Option<&[u8]>,
	) -> MultiRemovalResults {
		let count = self.overlay.clear_child_storage(child_info);
		MultiRemovalResults { maybe_cursor: None, backend: count, unique: count, loops: count }
	}

	fn clear_prefix(
		&mut self,
		prefix: &[u8],
		_maybe_limit: Option<u32>,
		_maybe_cursor: Option<&[u8]>,
	) -> MultiRemovalResults {
		if is_child_storage_key(prefix) {
			warn!(
				target: "trie",
				"Refuse to clear prefix that is part of child storage key via main storage"
			);
			let maybe_cursor = Some(prefix.to_vec());
			return MultiRemovalResults { maybe_cursor, backend: 0, unique: 0, loops: 0 }
		}

		let count = self.overlay.clear_prefix(prefix);
		MultiRemovalResults { maybe_cursor: None, backend: count, unique: count, loops: count }
	}

	fn clear_child_prefix(
		&mut self,
		child_info: &ChildInfo,
		prefix: &[u8],
		_maybe_limit: Option<u32>,
		_maybe_cursor: Option<&[u8]>,
	) -> MultiRemovalResults {
		let count = self.overlay.clear_child_prefix(child_info, prefix);
		MultiRemovalResults { maybe_cursor: None, backend: count, unique: count, loops: count }
	}

	fn storage_append(&mut self, key: Vec<u8>, value: Vec<u8>) {
		let current_value = self.overlay.value_mut_or_insert_with(&key, || Default::default());
		crate::ext::StorageAppend::new(current_value).append(value);
	}

	fn storage_root(&mut self, state_version: StateVersion) -> Vec<u8> {
		let mut top = self
			.overlay
			.changes()
			.filter_map(|(k, v)| v.value().map(|v| (k.clone(), v.clone())))
			.collect::<BTreeMap<_, _>>();
		// Single child trie implementation currently allows using the same child
		// empty root for all child trie. Using null storage key until multiple
		// type of child trie support.
		let empty_hash = empty_child_trie_root::<LayoutV1<Blake2Hasher>>();
		for info in self.overlay.children().map(|d| d.1.clone()).collect::<Vec<_>>() {
			if let Some(child_root) = self.default_child_storage_root(&info.name, state_version) {
				let parent_key = ChildType::Default.new_prefixed_key(&info.name);
				if empty_hash[..] == child_root[..] {
					top.remove(parent_key.as_slice());
				} else {
					top.insert(parent_key.into_inner(), child_root);
				}
			}
		}

		match state_version {
			StateVersion::V0 => LayoutV0::<Blake2Hasher>::trie_root(top).as_ref().into(),
			StateVersion::V1 => LayoutV1::<Blake2Hasher>::trie_root(top).as_ref().into(),
		}
	}

	fn child_storage_root(
		&mut self,
		child_info: &ChildInfo,
		state_version: StateVersion,
	) -> Option<Vec<u8>> {
		let ChildInfo::Default(info) = child_info;

		self.default_child_storage_root(&info.name, state_version)
	}

	fn storage_start_transaction(&mut self) {
		self.overlay.start_transaction()
	}

	fn storage_rollback_transaction(&mut self) -> Result<(), ()> {
		self.overlay.rollback_transaction().map_err(drop)
	}

	fn storage_commit_transaction(&mut self) -> Result<(), ()> {
		self.overlay.commit_transaction().map_err(drop)
	}

	fn wipe(&mut self) {}

	fn commit(&mut self) {}

	fn read_write_count(&self) -> (u32, u32, u32, u32) {
		unimplemented!("read_write_count is not supported in Basic")
	}

	fn reset_read_write_count(&mut self) {
		unimplemented!("reset_read_write_count is not supported in Basic")
	}

	fn get_whitelist(&self) -> Vec<TrackedStorageKey> {
		unimplemented!("get_whitelist is not supported in Basic")
	}

	fn set_whitelist(&mut self, _: Vec<TrackedStorageKey>) {
		unimplemented!("set_whitelist is not supported in Basic")
	}

	fn get_read_and_written_keys(&self) -> Vec<(Vec<u8>, u32, u32, bool)> {
		unimplemented!("get_read_and_written_keys is not supported in Basic")
	}
}

impl BasicExternalities {
	fn default_child_storage_root(
		&mut self,
		name: &[u8],
		state_version: StateVersion,
	) -> Option<Vec<u8>> {
		Some(
			if let Some((data, _child_info)) = self.overlay.child_changes(name) {
				let delta =
					data.into_iter().map(|(k, v)| (k.as_ref(), v.value().map(|v| v.as_slice())));
				crate::in_memory_backend::new_in_mem::<Blake2Hasher, HashKey<_>>()
					.default_child_storage_root(name, delta, state_version)
					.0
			} else {
				empty_child_trie_root::<LayoutV1<Blake2Hasher>>()
			}
			.encode(),
		)
	}
}

impl sp_externalities::ExtensionStore for BasicExternalities {
	fn extension_by_type_id(&mut self, type_id: TypeId) -> Option<&mut dyn Any> {
		self.extensions.get_mut(type_id)
	}

	fn register_extension_with_type_id(
		&mut self,
		type_id: TypeId,
		extension: Box<dyn sp_externalities::Extension>,
	) -> Result<(), sp_externalities::Error> {
		self.extensions.register_with_type_id(type_id, extension)
	}

	fn deregister_extension_by_type_id(
		&mut self,
		type_id: TypeId,
	) -> Result<(), sp_externalities::Error> {
		if self.extensions.deregister(type_id) {
			Ok(())
		} else {
			Err(sp_externalities::Error::ExtensionIsNotRegistered(type_id))
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use sp_core::{
		map,
		storage::{well_known_keys::CODE, DefaultChild, Storage, StorageChild},
	};

	#[test]
	fn commit_should_work() {
		let mut ext = BasicExternalities::default();
		ext.set_storage(b"doe".to_vec(), b"reindeer".to_vec());
		ext.set_storage(b"dog".to_vec(), b"puppy".to_vec());
		ext.set_storage(b"dogglesworth".to_vec(), b"cat".to_vec());
		let root = array_bytes::hex2bytes_unchecked(
			"39245109cef3758c2eed2ccba8d9b370a917850af3824bc8348d505df2c298fa",
		);

		assert_eq!(&ext.storage_root(StateVersion::default())[..], &root);
	}

	#[test]
	fn set_and_retrieve_code() {
		let mut ext = BasicExternalities::default();

		let code = vec![1, 2, 3];
		ext.set_storage(CODE.to_vec(), code.clone());

		assert_eq!(ext.storage(CODE, 0, None), Some(code[..].into()));
		assert_eq!(ext.storage(CODE, 1, Some(1)), Some(code[1..2].into()));
	}

	#[test]
	fn children_works() {
		let child_info = DefaultChild::new(b"storage_key");
		let mut ext = BasicExternalities::new(Storage {
			top: Default::default(),
			children_default: map![
				child_info.name.clone() => StorageChild {
					data: map![	b"doe".to_vec() => b"reindeer".to_vec()	],
					info: child_info.clone(),
				}
			],
		});

		let child_info = ChildInfo::Default(child_info);
		let child_info = &child_info;
		assert_eq!(ext.child_storage(child_info, b"doe", 0, None), Some(b"reindeer"[..].into()));

		ext.set_child_storage(child_info, b"dog", b"puppy");
		assert_eq!(ext.child_storage(child_info, b"dog", 0, None), Some(b"puppy"[..].into()));

		ext.clear_child_storage(child_info, b"dog");
		assert_eq!(ext.child_storage(child_info, b"dog", 0, None), None);

		let _ = ext.kill_child_storage(child_info, None, None);
		assert_eq!(ext.child_storage(child_info, b"doe", 0, None), None);
	}

	#[test]
	fn kill_child_storage_returns_num_elements_removed() {
		let child_info = DefaultChild::new(b"storage_key");
		let mut ext = BasicExternalities::new(Storage {
			top: Default::default(),
			children_default: map![
				child_info.name.clone() => StorageChild {
					data: map![
						b"doe".to_vec() => b"reindeer".to_vec(),
						b"dog".to_vec() => b"puppy".to_vec(),
						b"hello".to_vec() => b"world".to_vec(),
					],
					info: child_info.clone(),
				}
			],
		});

		let child_info = ChildInfo::Default(child_info);
		let child_info = &child_info;
		let res = ext.kill_child_storage(child_info, None, None);
		assert_eq!(res.deconstruct(), (None, 3, 3, 3));
	}

	#[test]
	fn basic_externalities_is_empty() {
		// Make sure no values are set by default in `BasicExternalities`.
		let storage = BasicExternalities::new_empty().into_storages();
		assert!(storage.top.is_empty());
		assert!(storage.children_default.is_empty());
	}
}
