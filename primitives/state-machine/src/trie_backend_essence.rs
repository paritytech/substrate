// This file is part of Substrate.

// Copyright (C) 2017-2020 Parity Technologies (UK) Ltd.
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

//! Trie-based state machine backend essence used to read values
//! from storage.

use std::ops::Deref;
use std::sync::Arc;
use std::marker::PhantomData;
use log::{debug, warn};
use hash_db::{self, Hasher, Prefix};
use sp_trie::{Trie, MemoryDB, PrefixedMemoryDB, DBValue, ChildrenProofMap,
	empty_child_trie_root, read_trie_value, read_child_trie_value,
	for_keys_in_child_trie, KeySpacedDB, TrieDBIterator};
use sp_trie::trie_types::{TrieDB, TrieError, Layout};
use crate::{backend::Consolidate, StorageKey, StorageValue};
use sp_core::storage::{ChildInfo, ChildrenMap};
use codec::{Decode, Encode};
use parking_lot::RwLock;

type Result<T> = std::result::Result<T, String>;

/// Patricia trie-based storage trait.
pub trait Storage<H: Hasher>: Send + Sync {
	/// Get a trie node.
	fn get(&self, key: &H::Out, prefix: Prefix) -> Result<Option<DBValue>>;
}

/// Patricia trie-based pairs storage essence.
pub struct TrieBackendEssence<S: TrieBackendStorage<H>, H: Hasher> {
	storage: S,
	root: H::Out,
	empty: H::Out,
	/// If defined, we store encoded visited roots for top_trie and child trie in this
	/// map. It also act as a cache.
	register_roots: Option<RwLock<ChildrenMap<Option<StorageValue>>>>,
}

/// Patricia trie-based pairs storage essence, with reference to child info.
pub struct ChildTrieBackendEssence<'a, S: TrieBackendStorage<H>, H: Hasher> {
	/// Trie backend to use.
	/// For the default child trie it is the top trie one.
	pub essence: &'a TrieBackendEssence<S, H>,
	/// Definition of the child trie, this is use to be able to pass
	/// child_info information when registering proof.
	pub child_info: Option<&'a ChildInfo>,
}

impl<S: TrieBackendStorage<H>, H: Hasher> TrieBackendEssence<S, H> where H::Out: Decode + Encode {
	/// Get trie backend for top trie. 
	pub fn top_backend(&self) -> ChildTrieBackendEssence<S, H> {
		ChildTrieBackendEssence{
			essence: self,
			child_info: None,
		}
	}

	/// Get trie backend for child trie. 
	pub fn child_backend<'a>(
		&'a self,
		child_info: &'a ChildInfo,
	) -> ChildTrieBackendEssence<'a, S, H> {
		ChildTrieBackendEssence{
			essence: self,
			child_info: Some(child_info),
		}
	}

	/// Create new trie-based backend.
	pub fn new(
		storage: S,
		root: H::Out,
		register_roots: Option<RwLock<ChildrenMap<Option<StorageValue>>>>,
	) -> Self {
		TrieBackendEssence {
			storage,
			root,
			empty: H::hash(&[0u8]),
			register_roots,
		}
	}

	/// Get backend storage reference.
	pub fn backend_storage(&self) -> &S {
		&self.storage
	}

	/// Get backend storage reference.
	pub fn backend_storage_mut(&mut self) -> &mut S {
		&mut self.storage
	}

	/// Get register root reference.
	pub fn register_roots(&self) -> Option<&RwLock<ChildrenMap<Option<StorageValue>>>> {
		self.register_roots.as_ref()
	}

	/// Get trie root.
	pub fn root(&self) -> &H::Out {
		&self.root
	}

	/// Set trie root. This is useful for testing.
	pub fn set_root(&mut self, root: H::Out) {
		self.root = root;
	}

	/// Consumes self and returns underlying storage.
	pub fn into_storage(self) -> S {
		self.storage
	}

	/// Return the next key in the trie i.e. the minimum key that is strictly superior to `key` in
	/// lexicographic order.
	pub fn next_storage_key(&self, key: &[u8]) -> Result<Option<StorageKey>> {
		self.next_storage_key_from_root(&self.root, None, key)
	}

	/// Access the root of the child storage in its parent trie
	pub(crate) fn child_root_encoded(
		&self,
		child_info: &ChildInfo,
	) -> Result<Option<StorageValue>> {
		if let Some(cache) = self.register_roots.as_ref() {
			if let Some(result) = cache.read().get(child_info) {
				return Ok(result.clone());
			}
		}

		let root: Option<StorageValue> = self.storage(child_info.prefixed_storage_key().as_slice())?;

		if let Some(cache) = self.register_roots.as_ref() {
			cache.write().insert(child_info.clone(), root.clone());
		}

		Ok(root)
	}

	/// Access the root of the child storage in its parent trie
	fn child_root(&self, child_info: &ChildInfo) -> Result<Option<H::Out>> {
		if let Some(cache) = self.register_roots.as_ref() {
			if let Some(root) = cache.read().get(child_info) {
				let root = root.as_ref()
					.and_then(|encoded_root| Decode::decode(&mut &encoded_root[..]).ok());
				return Ok(root);
			}
		}

		let encoded_root = self.storage(child_info.prefixed_storage_key().as_slice())?;
		if let Some(cache) = self.register_roots.as_ref() {
			cache.write().insert(child_info.clone(), encoded_root.clone());
		}

		let root: Option<H::Out> = encoded_root
			.and_then(|encoded_root| Decode::decode(&mut &encoded_root[..]).ok());

		Ok(root)
	}

	/// Return the next key in the child trie i.e. the minimum key that is strictly superior to
	/// `key` in lexicographic order.
	pub fn next_child_storage_key(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Result<Option<StorageKey>> {
		let hash = match self.child_root(child_info)? {
			Some(child_root) => child_root,
			None => return Ok(None),
		};

		self.next_storage_key_from_root(&hash, Some(child_info), key)
	}

	/// Return next key from main trie or child trie by providing corresponding root.
	fn next_storage_key_from_root(
		&self,
		root: &H::Out,
		child_info: Option<&ChildInfo>,
		key: &[u8],
	) -> Result<Option<StorageKey>> {
		let dyn_eph: &dyn hash_db::HashDBRef<_, _>;
		let keyspace_eph;
		let top_backend;
		let child_backend;
		if let Some(child_info) = child_info.as_ref() {
			child_backend = self.child_backend(&child_info);
			keyspace_eph = KeySpacedDB::new(&child_backend, child_info.keyspace());
			dyn_eph = &keyspace_eph;
		} else {
			top_backend = self.top_backend();
			dyn_eph = &top_backend;
		}

		let trie = TrieDB::<H>::new(dyn_eph, root)
			.map_err(|e| format!("TrieDB creation error: {}", e))?;
		let mut iter = trie.iter()
			.map_err(|e| format!("TrieDB iteration error: {}", e))?;

		// The key just after the one given in input, basically `key++0`.
		// Note: We are sure this is the next key if:
		// * size of key has no limit (i.e. we can always add 0 to the path),
		// * and no keys can be inserted between `key` and `key++0` (this is ensured by sp-io).
		let mut potential_next_key = Vec::with_capacity(key.len() + 1);
		potential_next_key.extend_from_slice(key);
		potential_next_key.push(0);

		iter.seek(&potential_next_key)
			.map_err(|e| format!("TrieDB iterator seek error: {}", e))?;

		let next_element = iter.next();

		let next_key = if let Some(next_element) = next_element {
			let (next_key, _) = next_element
				.map_err(|e| format!("TrieDB iterator next error: {}", e))?;
			Some(next_key)
		} else {
			None
		};

		Ok(next_key)
	}

	/// Get the value of storage at given key.
	pub fn storage(&self, key: &[u8]) -> Result<Option<StorageValue>> {
		let map_e = |e| format!("Trie lookup error: {}", e);

		read_trie_value::<Layout<H>, _>(&self.top_backend(), &self.root, key).map_err(map_e)
	}

	/// Get the value of child storage at given key.
	pub fn child_storage(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Result<Option<StorageValue>> {
		let root = self.child_root_encoded(child_info)?
			.unwrap_or_else(|| empty_child_trie_root::<Layout<H>>().encode());

		let map_e = |e| format!("Trie lookup error: {}", e);

		read_child_trie_value::<Layout<H>, _>(
			child_info.keyspace(),
			&self.child_backend(child_info),
			&root,
			key,
		).map_err(map_e)
	}

	/// Retrieve all entries keys of child storage and call `f` for each of those keys.
	pub fn for_keys_in_child_storage<F: FnMut(&[u8])>(
		&self,
		child_info: &ChildInfo,
		f: F,
	) {
		let root = match self.child_root_encoded(child_info) {
			Ok(v) => v.unwrap_or_else(|| empty_child_trie_root::<Layout<H>>().encode()),
			Err(e) => {
				debug!(target: "trie", "Error while iterating child storage: {}", e);
				return;
			}
		};

		if let Err(e) = for_keys_in_child_trie::<Layout<H>, _, _>(
			child_info.keyspace(),
			&self.child_backend(child_info),
			&root,
			f,
		) {
			debug!(target: "trie", "Error while iterating child storage: {}", e);
		}
	}

	/// Execute given closure for all keys starting with prefix.
	pub fn for_child_keys_with_prefix<F: FnMut(&[u8])>(
		&self,
		child_info: &ChildInfo,
		prefix: &[u8],
		mut f: F,
	) {
		let root_vec = match self.child_root_encoded(child_info) {
			Ok(v) => v.unwrap_or_else(|| empty_child_trie_root::<Layout<H>>().encode()),
			Err(e) => {
				debug!(target: "trie", "Error while iterating child storage: {}", e);
				return;
			}
		};
		let mut root = H::Out::default();
		root.as_mut().copy_from_slice(&root_vec);
		self.keys_values_with_prefix_inner(&root, prefix, |k, _v| f(k), Some(child_info))
	}

	/// Execute given closure for all keys starting with prefix.
	pub fn for_keys_with_prefix<F: FnMut(&[u8])>(&self, prefix: &[u8], mut f: F) {
		self.keys_values_with_prefix_inner(&self.root, prefix, |k, _v| f(k), None)
	}

	fn keys_values_with_prefix_inner<F: FnMut(&[u8], &[u8])>(
		&self,
		root: &H::Out,
		prefix: &[u8],
		mut f: F,
		child_info: Option<&ChildInfo>,
	) {
		let mut iter = move |db| -> std::result::Result<(), Box<TrieError<H::Out>>> {
			let trie = TrieDB::<H>::new(db, root)?;

			for x in TrieDBIterator::new_prefixed(&trie, prefix)? {
				let (key, value) = x?;

				debug_assert!(key.starts_with(prefix));

				f(&key, &value);
			}

			Ok(())
		};

		let result = if let Some(child_info) = child_info {
			let backend = self.child_backend(&child_info);
			let db = KeySpacedDB::new(&backend, child_info.keyspace());
			iter(&db)
		} else {
			iter(&self.top_backend())
		};
		if let Err(e) = result {
			debug!(target: "trie", "Error while iterating by prefix: {}", e);
		}
	}

	/// Execute given closure for all key and values starting with prefix.
	pub fn for_key_values_with_prefix<F: FnMut(&[u8], &[u8])>(&self, prefix: &[u8], f: F) {
		self.keys_values_with_prefix_inner(&self.root, prefix, f, None)
	}
}

pub(crate) struct Ephemeral<'a, S: 'a + TrieBackendStorage<H>, H: 'a + Hasher> {
	storage: &'a S,
	overlay: &'a mut S::Overlay,
	child_info: Option<&'a ChildInfo>,
	_ph: PhantomData<H>,
}

impl<'a, S: 'a + TrieBackendStorage<H>, H: 'a + Hasher> hash_db::AsHashDB<H, DBValue>
	for Ephemeral<'a, S, H>
{
	fn as_hash_db<'b>(&'b self) -> &'b (dyn hash_db::HashDB<H, DBValue> + 'b) { self }
	fn as_hash_db_mut<'b>(&'b mut self) -> &'b mut (dyn hash_db::HashDB<H, DBValue> + 'b) { self }
}

impl<'a, S: TrieBackendStorage<H>, H: Hasher> Ephemeral<'a, S, H> {
	pub fn new(
		storage: &'a S,
		overlay: &'a mut S::Overlay,
		child_info: Option<&'a ChildInfo>,
	) -> Self {
		Ephemeral {
			storage,
			overlay,
			child_info,
			_ph: PhantomData,
		}
	}
}

impl<'a, S: 'a + TrieBackendStorage<H>, H: Hasher> hash_db::HashDB<H, DBValue>
	for Ephemeral<'a, S, H>
{
	fn get(&self, key: &H::Out, prefix: Prefix) -> Option<DBValue> {
		if let Some(val) = hash_db::HashDB::get(self.overlay, key, prefix) {
			Some(val)
		} else {
			let top;
			let child_info = if let Some(child_info) = self.child_info {
				child_info
			} else {
				top = ChildInfo::top_trie();
				&top
			};
			match self.storage.get(child_info, &key, prefix) {
				Ok(x) => x,
				Err(e) => {
					warn!(target: "trie", "Failed to read from DB: {}", e);
					None
				},
			}
		}
	}

	fn contains(&self, key: &H::Out, prefix: Prefix) -> bool {
		hash_db::HashDB::get(self, key, prefix).is_some()
	}

	fn insert(&mut self, prefix: Prefix, value: &[u8]) -> H::Out {
		hash_db::HashDB::insert(self.overlay, prefix, value)
	}

	fn emplace(&mut self, key: H::Out, prefix: Prefix, value: DBValue) {
		hash_db::HashDB::emplace(self.overlay, key, prefix, value)
	}

	fn remove(&mut self, key: &H::Out, prefix: Prefix) {
		hash_db::HashDB::remove(self.overlay, key, prefix)
	}
}

impl<'a, S: 'a + TrieBackendStorage<H>, H: Hasher> hash_db::HashDBRef<H, DBValue>
	for Ephemeral<'a, S, H>
{
	fn get(&self, key: &H::Out, prefix: Prefix) -> Option<DBValue> {
		hash_db::HashDB::get(self, key, prefix)
	}

	fn contains(&self, key: &H::Out, prefix: Prefix) -> bool {
		hash_db::HashDB::contains(self, key, prefix)
	}
}

/// Key-value pairs storage that is used by trie backend essence.
pub trait TrieBackendStorage<H: Hasher>: Send + Sync {
	/// Type of in-memory overlay.
	type Overlay: hash_db::HashDB<H, DBValue> + Default + Consolidate;
	/// Get the value stored at key.
	fn get(&self, child_info: &ChildInfo, key: &H::Out, prefix: Prefix) -> Result<Option<DBValue>>;
}

impl<'a, H: Hasher, S: TrieBackendStorage<H>> TrieBackendStorage<H> for &'a S {
	type Overlay = S::Overlay;

	fn get(&self, child_info: &ChildInfo, key: &H::Out, prefix: Prefix) -> Result<Option<DBValue>> {
		<S as TrieBackendStorage<H>>::get(self, child_info, key, prefix)
	}
}

// This implementation is used by normal storage trie clients.
impl<H: Hasher> TrieBackendStorage<H> for Arc<dyn Storage<H>> {
	type Overlay = PrefixedMemoryDB<H>;

	fn get(&self, _child_info: &ChildInfo, key: &H::Out, prefix: Prefix) -> Result<Option<DBValue>> {
		Storage::<H>::get(self.deref(), key, prefix)
	}
}

// This implementation is used by test storage trie clients.
impl<H: Hasher> TrieBackendStorage<H> for PrefixedMemoryDB<H> {
	type Overlay = PrefixedMemoryDB<H>;

	fn get(&self, _child_info: &ChildInfo, key: &H::Out, prefix: Prefix) -> Result<Option<DBValue>> {
		Ok(hash_db::HashDB::get(self, key, prefix))
	}
}

impl<H: Hasher> TrieBackendStorage<H> for MemoryDB<H> {
	type Overlay = MemoryDB<H>;

	fn get(&self, _child_info: &ChildInfo, key: &H::Out, prefix: Prefix) -> Result<Option<DBValue>> {
		Ok(hash_db::HashDB::get(self, key, prefix))
	}
}

impl<H: Hasher> TrieBackendStorage<H> for ChildrenProofMap<MemoryDB<H>> {
	type Overlay = MemoryDB<H>;

	fn get(
		&self,
		child_info: &ChildInfo,
		key: &H::Out,
		prefix: Prefix,
	) -> Result<Option<DBValue>> {
		let child_info_proof = child_info.proof_info();
		Ok(self.deref().get(&child_info_proof).and_then(|s|
			hash_db::HashDB::get(s, key, prefix)
		))
	}
}

impl<'a, S: TrieBackendStorage<H>, H: Hasher> hash_db::AsHashDB<H, DBValue>
	for ChildTrieBackendEssence<'a, S, H>
{
	fn as_hash_db<'b>(&'b self) -> &'b (dyn hash_db::HashDB<H, DBValue> + 'b) { self }
	fn as_hash_db_mut<'b>(&'b mut self) -> &'b mut (dyn hash_db::HashDB<H, DBValue> + 'b) { self }
}

impl<'a, S: TrieBackendStorage<H>, H: Hasher> hash_db::HashDB<H, DBValue>
	for ChildTrieBackendEssence<'a, S, H>
{
	fn get(&self, key: &H::Out, prefix: Prefix) -> Option<DBValue> {
		if *key == self.essence.empty {
			return Some([0u8].to_vec())
		}
		let top;
		let child_info = if let Some(child_info) = self.child_info {
			child_info
		} else {
			top = ChildInfo::top_trie();
			&top
		};
		match self.essence.storage.get(child_info, &key, prefix) {
			Ok(x) => x,
			Err(e) => {
				warn!(target: "trie", "Failed to read from DB: {}", e);
				None
			},
		}
	}

	fn contains(&self, key: &H::Out, prefix: Prefix) -> bool {
		hash_db::HashDB::get(self, key, prefix).is_some()
	}

	fn insert(&mut self, _prefix: Prefix, _value: &[u8]) -> H::Out {
		unimplemented!();
	}

	fn emplace(&mut self, _key: H::Out, _prefix: Prefix, _value: DBValue) {
		unimplemented!();
	}

	fn remove(&mut self, _key: &H::Out, _prefix: Prefix) {
		unimplemented!();
	}
}

impl<'a, S: TrieBackendStorage<H>, H: Hasher> hash_db::HashDBRef<H, DBValue>
	for ChildTrieBackendEssence<'a, S, H>
{
	fn get(&self, key: &H::Out, prefix: Prefix) -> Option<DBValue> {
		hash_db::HashDB::get(self, key, prefix)
	}

	fn contains(&self, key: &H::Out, prefix: Prefix) -> bool {
		hash_db::HashDB::contains(self, key, prefix)
	}
}

#[cfg(test)]
mod test {
	use sp_core::{Blake2Hasher, H256};
	use sp_trie::{TrieMut, PrefixedMemoryDB, trie_types::TrieDBMut, KeySpacedDBMut};
	use super::*;

	#[test]
	fn next_storage_key_and_next_child_storage_key_work() {
		let child_info = ChildInfo::new_default(b"MyChild");
		let child_info = &child_info;
		// Contains values
		let mut root_1 = H256::default();
		// Contains child trie
		let mut root_2 = H256::default();

		let mut mdb = PrefixedMemoryDB::<Blake2Hasher>::default();
		{
			let mut trie = TrieDBMut::new(&mut mdb, &mut root_1);
			trie.insert(b"3", &[1]).expect("insert failed");
			trie.insert(b"4", &[1]).expect("insert failed");
			trie.insert(b"6", &[1]).expect("insert failed");
		}
		{
			let mut mdb = KeySpacedDBMut::new(&mut mdb, child_info.keyspace());
			// reuse of root_1 implicitly assert child trie root is same
			// as top trie (contents must remain the same).
			let mut trie = TrieDBMut::new(&mut mdb, &mut root_1);
			trie.insert(b"3", &[1]).expect("insert failed");
			trie.insert(b"4", &[1]).expect("insert failed");
			trie.insert(b"6", &[1]).expect("insert failed");
		}
		{
			let mut trie = TrieDBMut::new(&mut mdb, &mut root_2);
			trie.insert(child_info.prefixed_storage_key().as_slice(), root_1.as_ref())
				.expect("insert failed");
		};

		let essence_1 = TrieBackendEssence::new(mdb, root_1, None);

		assert_eq!(essence_1.next_storage_key(b"2"), Ok(Some(b"3".to_vec())));
		assert_eq!(essence_1.next_storage_key(b"3"), Ok(Some(b"4".to_vec())));
		assert_eq!(essence_1.next_storage_key(b"4"), Ok(Some(b"6".to_vec())));
		assert_eq!(essence_1.next_storage_key(b"5"), Ok(Some(b"6".to_vec())));
		assert_eq!(essence_1.next_storage_key(b"6"), Ok(None));

		let mdb = essence_1.into_storage();
		let essence_2 = TrieBackendEssence::new(mdb, root_2, None);

		assert_eq!(
			essence_2.next_child_storage_key(child_info, b"2"), Ok(Some(b"3".to_vec()))
		);
		assert_eq!(
			essence_2.next_child_storage_key(child_info, b"3"), Ok(Some(b"4".to_vec()))
		);
		assert_eq!(
			essence_2.next_child_storage_key(child_info, b"4"), Ok(Some(b"6".to_vec()))
		);
		assert_eq!(
			essence_2.next_child_storage_key(child_info, b"5"), Ok(Some(b"6".to_vec()))
		);
		assert_eq!(
			essence_2.next_child_storage_key(child_info, b"6"), Ok(None)
		);
	}
}
