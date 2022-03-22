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

//! Trie-based state machine backend essence used to read values
//! from storage.

use crate::{backend::Consolidate, debug, warn, StorageKey, StorageValue};
use codec::Encode;
use hash_db::{self, AsHashDB, HashDB, HashDBRef, Hasher, Prefix};
#[cfg(feature = "std")]
use parking_lot::RwLock;
use sp_core::storage::{ChildInfo, ChildType, StateVersion};
use sp_std::{boxed::Box, vec::Vec};
use sp_trie::{
	child_delta_trie_root, delta_trie_root, empty_child_trie_root, read_child_trie_value,
	read_trie_value,
	trie_types::{TrieDB, TrieError},
	DBValue, KeySpacedDB, LayoutV1 as Layout, PrefixedMemoryDB, Trie, TrieDBIterator,
	TrieDBKeyIterator,
};
#[cfg(feature = "std")]
use std::collections::HashMap;
#[cfg(feature = "std")]
use std::sync::Arc;

#[cfg(not(feature = "std"))]
macro_rules! format {
	( $message:expr, $( $arg:expr )* ) => {
		{
			$( let _ = &$arg; )*
			crate::DefaultError
		}
	};
}

type Result<V> = sp_std::result::Result<V, crate::DefaultError>;

/// Patricia trie-based storage trait.
pub trait Storage<H: Hasher>: Send + Sync {
	/// Get a trie node.
	fn get(&self, key: &H::Out, prefix: Prefix) -> Result<Option<DBValue>>;
}

/// Local cache for child root.
#[cfg(feature = "std")]
pub(crate) struct Cache<H> {
	pub child_root: HashMap<Vec<u8>, Option<H>>,
}

#[cfg(feature = "std")]
impl<H> Cache<H> {
	fn new() -> Self {
		Cache { child_root: HashMap::new() }
	}
}

/// Patricia trie-based pairs storage essence.
pub struct TrieBackendEssence<S: TrieBackendStorage<H>, H: Hasher> {
	storage: S,
	root: H::Out,
	empty: H::Out,
	#[cfg(feature = "std")]
	pub(crate) cache: Arc<RwLock<Cache<H::Out>>>,
}

impl<S: TrieBackendStorage<H>, H: Hasher> TrieBackendEssence<S, H>
where
	H::Out: Encode,
{
	/// Create new trie-based backend.
	pub fn new(storage: S, root: H::Out) -> Self {
		TrieBackendEssence {
			storage,
			root,
			empty: H::hash(&[0u8]),
			#[cfg(feature = "std")]
			cache: Arc::new(RwLock::new(Cache::new())),
		}
	}

	/// Get backend storage reference.
	pub fn backend_storage(&self) -> &S {
		&self.storage
	}

	/// Get trie root.
	pub fn root(&self) -> &H::Out {
		&self.root
	}

	/// Set trie root. This is useful for testing.
	pub fn set_root(&mut self, root: H::Out) {
		// If root did change so can have cached content.
		self.reset_cache();
		self.root = root;
	}

	#[cfg(feature = "std")]
	fn reset_cache(&mut self) {
		self.cache = Arc::new(RwLock::new(Cache::new()));
	}

	#[cfg(not(feature = "std"))]
	fn reset_cache(&mut self) {}

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
	fn child_root(&self, child_info: &ChildInfo) -> Result<Option<H::Out>> {
		#[cfg(feature = "std")]
		{
			if let Some(result) = self.cache.read().child_root.get(child_info.storage_key()) {
				return Ok(*result)
			}
		}

		let result = self.storage(child_info.prefixed_storage_key().as_slice())?.map(|r| {
			let mut hash = H::Out::default();

			// root is fetched from DB, not writable by runtime, so it's always valid.
			hash.as_mut().copy_from_slice(&r[..]);

			hash
		});

		#[cfg(feature = "std")]
		{
			self.cache.write().child_root.insert(child_info.storage_key().to_vec(), result);
		}

		Ok(result)
	}

	/// Return the next key in the child trie i.e. the minimum key that is strictly superior to
	/// `key` in lexicographic order.
	pub fn next_child_storage_key(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Result<Option<StorageKey>> {
		let child_root = match self.child_root(child_info)? {
			Some(child_root) => child_root,
			None => return Ok(None),
		};

		self.next_storage_key_from_root(&child_root, Some(child_info), key)
	}

	/// Return next key from main trie or child trie by providing corresponding root.
	fn next_storage_key_from_root(
		&self,
		root: &H::Out,
		child_info: Option<&ChildInfo>,
		key: &[u8],
	) -> Result<Option<StorageKey>> {
		let dyn_eph: &dyn HashDBRef<_, _>;
		let keyspace_eph;
		if let Some(child_info) = child_info.as_ref() {
			keyspace_eph = KeySpacedDB::new(self, child_info.keyspace());
			dyn_eph = &keyspace_eph;
		} else {
			dyn_eph = self;
		}

		let trie =
			TrieDB::<H>::new(dyn_eph, root).map_err(|e| format!("TrieDB creation error: {}", e))?;
		let mut iter = trie.key_iter().map_err(|e| format!("TrieDB iteration error: {}", e))?;

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
			let next_key =
				next_element.map_err(|e| format!("TrieDB iterator next error: {}", e))?;
			Some(next_key)
		} else {
			None
		};

		Ok(next_key)
	}

	/// Get the value of storage at given key.
	pub fn storage(&self, key: &[u8]) -> Result<Option<StorageValue>> {
		let map_e = |e| format!("Trie lookup error: {}", e);

		read_trie_value::<Layout<H>, _>(self, &self.root, key).map_err(map_e)
	}

	/// Get the value of child storage at given key.
	pub fn child_storage(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Result<Option<StorageValue>> {
		let root = match self.child_root(child_info)? {
			Some(root) => root,
			None => return Ok(None),
		};

		let map_e = |e| format!("Trie lookup error: {}", e);

		read_child_trie_value::<Layout<H>, _>(child_info.keyspace(), self, &root, key)
			.map_err(map_e)
	}

	/// Retrieve all entries keys of storage and call `f` for each of those keys.
	/// Aborts as soon as `f` returns false.
	///
	/// Returns `true` when all keys were iterated.
	pub fn apply_to_key_values_while(
		&self,
		child_info: Option<&ChildInfo>,
		prefix: Option<&[u8]>,
		start_at: Option<&[u8]>,
		f: impl FnMut(Vec<u8>, Vec<u8>) -> bool,
		allow_missing_nodes: bool,
	) -> Result<bool> {
		let root = if let Some(child_info) = child_info.as_ref() {
			match self.child_root(child_info)? {
				Some(child_root) => child_root,
				None => return Ok(true),
			}
		} else {
			self.root
		};

		self.trie_iter_inner(&root, prefix, f, child_info, start_at, allow_missing_nodes)
	}

	/// Retrieve all entries keys of a storage and call `f` for each of those keys.
	/// Aborts as soon as `f` returns false.
	pub fn apply_to_keys_while<F: FnMut(&[u8]) -> bool>(
		&self,
		child_info: Option<&ChildInfo>,
		prefix: Option<&[u8]>,
		mut f: F,
	) {
		let root = if let Some(child_info) = child_info.as_ref() {
			match self.child_root(child_info) {
				Ok(Some(v)) => v,
				// If the child trie doesn't exist, there is no need to continue.
				Ok(None) => return,
				Err(e) => {
					debug!(target: "trie", "Error while iterating child storage: {}", e);
					return
				},
			}
		} else {
			self.root
		};

		self.trie_iter_key_inner(&root, prefix, |k| f(k), child_info)
	}

	/// Execute given closure for all keys starting with prefix.
	pub fn for_child_keys_with_prefix(
		&self,
		child_info: &ChildInfo,
		prefix: &[u8],
		mut f: impl FnMut(&[u8]),
	) {
		let root = match self.child_root(child_info) {
			Ok(Some(v)) => v,
			// If the child trie doesn't exist, there is no need to continue.
			Ok(None) => return,
			Err(e) => {
				debug!(target: "trie", "Error while iterating child storage: {}", e);
				return
			},
		};

		self.trie_iter_key_inner(
			&root,
			Some(prefix),
			|k| {
				f(k);
				true
			},
			Some(child_info),
		)
	}

	/// Execute given closure for all keys starting with prefix.
	pub fn for_keys_with_prefix<F: FnMut(&[u8])>(&self, prefix: &[u8], mut f: F) {
		self.trie_iter_key_inner(
			&self.root,
			Some(prefix),
			|k| {
				f(k);
				true
			},
			None,
		)
	}

	fn trie_iter_key_inner<F: FnMut(&[u8]) -> bool>(
		&self,
		root: &H::Out,
		prefix: Option<&[u8]>,
		mut f: F,
		child_info: Option<&ChildInfo>,
	) {
		let mut iter = move |db| -> sp_std::result::Result<(), Box<TrieError<H::Out>>> {
			let trie = TrieDB::<H>::new(db, root)?;
			let iter = if let Some(prefix) = prefix.as_ref() {
				TrieDBKeyIterator::new_prefixed(&trie, prefix)?
			} else {
				TrieDBKeyIterator::new(&trie)?
			};

			for x in iter {
				let key = x?;

				debug_assert!(prefix
					.as_ref()
					.map(|prefix| key.starts_with(prefix))
					.unwrap_or(true));

				if !f(&key) {
					break
				}
			}

			Ok(())
		};

		let result = if let Some(child_info) = child_info {
			let db = KeySpacedDB::new(self, child_info.keyspace());
			iter(&db)
		} else {
			iter(self)
		};
		if let Err(e) = result {
			debug!(target: "trie", "Error while iterating by prefix: {}", e);
		}
	}

	fn trie_iter_inner<F: FnMut(Vec<u8>, Vec<u8>) -> bool>(
		&self,
		root: &H::Out,
		prefix: Option<&[u8]>,
		mut f: F,
		child_info: Option<&ChildInfo>,
		start_at: Option<&[u8]>,
		allow_missing_nodes: bool,
	) -> Result<bool> {
		let mut iter = move |db| -> sp_std::result::Result<bool, Box<TrieError<H::Out>>> {
			let trie = TrieDB::<H>::new(db, root)?;

			let prefix = prefix.unwrap_or(&[]);
			let iterator = if let Some(start_at) = start_at {
				TrieDBIterator::new_prefixed_then_seek(&trie, prefix, start_at)?
			} else {
				TrieDBIterator::new_prefixed(&trie, prefix)?
			};
			for x in iterator {
				let (key, value) = x?;

				debug_assert!(key.starts_with(prefix));

				if !f(key, value) {
					return Ok(false)
				}
			}

			Ok(true)
		};

		let result = if let Some(child_info) = child_info {
			let db = KeySpacedDB::new(self, child_info.keyspace());
			iter(&db)
		} else {
			iter(self)
		};
		match result {
			Ok(completed) => Ok(completed),
			Err(e) if matches!(*e, TrieError::IncompleteDatabase(_)) && allow_missing_nodes =>
				Ok(false),
			Err(e) => Err(format!("TrieDB iteration error: {}", e)),
		}
	}

	/// Execute given closure for all key and values starting with prefix.
	pub fn for_key_values_with_prefix<F: FnMut(&[u8], &[u8])>(&self, prefix: &[u8], mut f: F) {
		let _ = self.trie_iter_inner(
			&self.root,
			Some(prefix),
			|k, v| {
				f(&k, &v);
				true
			},
			None,
			None,
			false,
		);
	}

	/// Returns all `(key, value)` pairs in the trie.
	pub fn pairs(&self) -> Vec<(StorageKey, StorageValue)> {
		let collect_all = || -> sp_std::result::Result<_, Box<TrieError<H::Out>>> {
			let trie = TrieDB::<H>::new(self, &self.root)?;
			let mut v = Vec::new();
			for x in trie.iter()? {
				let (key, value) = x?;
				v.push((key.to_vec(), value.to_vec()));
			}

			Ok(v)
		};

		match collect_all() {
			Ok(v) => v,
			Err(e) => {
				debug!(target: "trie", "Error extracting trie values: {}", e);
				Vec::new()
			},
		}
	}

	/// Returns all keys that start with the given `prefix`.
	pub fn keys(&self, prefix: &[u8]) -> Vec<StorageKey> {
		let collect_all = || -> sp_std::result::Result<_, Box<TrieError<H::Out>>> {
			let trie = TrieDB::<H>::new(self, &self.root)?;
			let mut v = Vec::new();
			for x in trie.iter()? {
				let (key, _) = x?;
				if key.starts_with(prefix) {
					v.push(key.to_vec());
				}
			}

			Ok(v)
		};

		collect_all()
			.map_err(|e| debug!(target: "trie", "Error extracting trie keys: {}", e))
			.unwrap_or_default()
	}

	/// Return the storage root after applying the given `delta`.
	pub fn storage_root<'a>(
		&self,
		delta: impl Iterator<Item = (&'a [u8], Option<&'a [u8]>)>,
		state_version: StateVersion,
	) -> (H::Out, S::Overlay)
	where
		H::Out: Ord,
	{
		let mut write_overlay = S::Overlay::default();
		let mut root = self.root;

		{
			let mut eph = Ephemeral::new(self.backend_storage(), &mut write_overlay);
			let res = match state_version {
				StateVersion::V0 =>
					delta_trie_root::<sp_trie::LayoutV0<H>, _, _, _, _, _>(&mut eph, root, delta),
				StateVersion::V1 =>
					delta_trie_root::<sp_trie::LayoutV1<H>, _, _, _, _, _>(&mut eph, root, delta),
			};

			match res {
				Ok(ret) => root = ret,
				Err(e) => warn!(target: "trie", "Failed to write to trie: {}", e),
			}
		}

		(root, write_overlay)
	}

	/// Returns the child storage root for the child trie `child_info` after applying the given
	/// `delta`.
	pub fn child_storage_root<'a>(
		&self,
		child_info: &ChildInfo,
		delta: impl Iterator<Item = (&'a [u8], Option<&'a [u8]>)>,
		state_version: StateVersion,
	) -> (H::Out, bool, S::Overlay)
	where
		H::Out: Ord,
	{
		let default_root = match child_info.child_type() {
			ChildType::ParentKeyId => empty_child_trie_root::<sp_trie::LayoutV1<H>>(),
		};
		let mut write_overlay = S::Overlay::default();
		let mut root = match self.child_root(child_info) {
			Ok(Some(hash)) => hash,
			Ok(None) => default_root,
			Err(e) => {
				warn!(target: "trie", "Failed to read child storage root: {}", e);
				default_root.clone()
			},
		};

		{
			let mut eph = Ephemeral::new(self.backend_storage(), &mut write_overlay);
			match match state_version {
				StateVersion::V0 =>
					child_delta_trie_root::<sp_trie::LayoutV0<H>, _, _, _, _, _, _>(
						child_info.keyspace(),
						&mut eph,
						root,
						delta,
					),
				StateVersion::V1 =>
					child_delta_trie_root::<sp_trie::LayoutV1<H>, _, _, _, _, _, _>(
						child_info.keyspace(),
						&mut eph,
						root,
						delta,
					),
			} {
				Ok(ret) => root = ret,
				Err(e) => warn!(target: "trie", "Failed to write to trie: {}", e),
			}
		}

		let is_default = root == default_root;

		(root, is_default, write_overlay)
	}
}

pub(crate) struct Ephemeral<'a, S: 'a + TrieBackendStorage<H>, H: 'a + Hasher> {
	storage: &'a S,
	overlay: &'a mut S::Overlay,
}

impl<'a, S: 'a + TrieBackendStorage<H>, H: 'a + Hasher> AsHashDB<H, DBValue>
	for Ephemeral<'a, S, H>
{
	fn as_hash_db<'b>(&'b self) -> &'b (dyn HashDB<H, DBValue> + 'b) {
		self
	}
	fn as_hash_db_mut<'b>(&'b mut self) -> &'b mut (dyn HashDB<H, DBValue> + 'b) {
		self
	}
}

impl<'a, S: TrieBackendStorage<H>, H: Hasher> Ephemeral<'a, S, H> {
	pub fn new(storage: &'a S, overlay: &'a mut S::Overlay) -> Self {
		Ephemeral { storage, overlay }
	}
}

impl<'a, S: 'a + TrieBackendStorage<H>, H: Hasher> hash_db::HashDB<H, DBValue>
	for Ephemeral<'a, S, H>
{
	fn get(&self, key: &H::Out, prefix: Prefix) -> Option<DBValue> {
		if let Some(val) = HashDB::get(self.overlay, key, prefix) {
			Some(val)
		} else {
			match self.storage.get(&key, prefix) {
				Ok(x) => x,
				Err(e) => {
					warn!(target: "trie", "Failed to read from DB: {}", e);
					None
				},
			}
		}
	}

	fn contains(&self, key: &H::Out, prefix: Prefix) -> bool {
		HashDB::get(self, key, prefix).is_some()
	}

	fn insert(&mut self, prefix: Prefix, value: &[u8]) -> H::Out {
		HashDB::insert(self.overlay, prefix, value)
	}

	fn emplace(&mut self, key: H::Out, prefix: Prefix, value: DBValue) {
		HashDB::emplace(self.overlay, key, prefix, value)
	}

	fn remove(&mut self, key: &H::Out, prefix: Prefix) {
		HashDB::remove(self.overlay, key, prefix)
	}
}

impl<'a, S: 'a + TrieBackendStorage<H>, H: Hasher> HashDBRef<H, DBValue> for Ephemeral<'a, S, H> {
	fn get(&self, key: &H::Out, prefix: Prefix) -> Option<DBValue> {
		HashDB::get(self, key, prefix)
	}

	fn contains(&self, key: &H::Out, prefix: Prefix) -> bool {
		HashDB::contains(self, key, prefix)
	}
}

/// Key-value pairs storage that is used by trie backend essence.
pub trait TrieBackendStorage<H: Hasher>: Send + Sync {
	/// Type of in-memory overlay.
	type Overlay: HashDB<H, DBValue> + Default + Consolidate;

	/// Get the value stored at key.
	fn get(&self, key: &H::Out, prefix: Prefix) -> Result<Option<DBValue>>;
}

// This implementation is used by normal storage trie clients.
#[cfg(feature = "std")]
impl<H: Hasher> TrieBackendStorage<H> for Arc<dyn Storage<H>> {
	type Overlay = PrefixedMemoryDB<H>;

	fn get(&self, key: &H::Out, prefix: Prefix) -> Result<Option<DBValue>> {
		Storage::<H>::get(std::ops::Deref::deref(self), key, prefix)
	}
}

impl<H, KF> TrieBackendStorage<H> for sp_trie::GenericMemoryDB<H, KF>
where
	H: Hasher,
	KF: sp_trie::KeyFunction<H> + Send + Sync,
{
	type Overlay = Self;

	fn get(&self, key: &H::Out, prefix: Prefix) -> Result<Option<DBValue>> {
		Ok(hash_db::HashDB::get(self, key, prefix))
	}
}

impl<S: TrieBackendStorage<H>, H: Hasher> AsHashDB<H, DBValue> for TrieBackendEssence<S, H> {
	fn as_hash_db<'b>(&'b self) -> &'b (dyn HashDB<H, DBValue> + 'b) {
		self
	}
	fn as_hash_db_mut<'b>(&'b mut self) -> &'b mut (dyn HashDB<H, DBValue> + 'b) {
		self
	}
}

impl<S: TrieBackendStorage<H>, H: Hasher> HashDB<H, DBValue> for TrieBackendEssence<S, H> {
	fn get(&self, key: &H::Out, prefix: Prefix) -> Option<DBValue> {
		if *key == self.empty {
			return Some([0u8].to_vec())
		}
		match self.storage.get(&key, prefix) {
			Ok(x) => x,
			Err(e) => {
				warn!(target: "trie", "Failed to read from DB: {}", e);
				None
			},
		}
	}

	fn contains(&self, key: &H::Out, prefix: Prefix) -> bool {
		HashDB::get(self, key, prefix).is_some()
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

impl<S: TrieBackendStorage<H>, H: Hasher> HashDBRef<H, DBValue> for TrieBackendEssence<S, H> {
	fn get(&self, key: &H::Out, prefix: Prefix) -> Option<DBValue> {
		HashDB::get(self, key, prefix)
	}

	fn contains(&self, key: &H::Out, prefix: Prefix) -> bool {
		HashDB::contains(self, key, prefix)
	}
}

#[cfg(test)]
mod test {
	use super::*;
	use sp_core::{Blake2Hasher, H256};
	use sp_trie::{
		trie_types::TrieDBMutV1 as TrieDBMut, KeySpacedDBMut, PrefixedMemoryDB, TrieMut,
	};

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

		let essence_1 = TrieBackendEssence::new(mdb, root_1);

		assert_eq!(essence_1.next_storage_key(b"2"), Ok(Some(b"3".to_vec())));
		assert_eq!(essence_1.next_storage_key(b"3"), Ok(Some(b"4".to_vec())));
		assert_eq!(essence_1.next_storage_key(b"4"), Ok(Some(b"6".to_vec())));
		assert_eq!(essence_1.next_storage_key(b"5"), Ok(Some(b"6".to_vec())));
		assert_eq!(essence_1.next_storage_key(b"6"), Ok(None));

		let mdb = essence_1.into_storage();
		let essence_2 = TrieBackendEssence::new(mdb, root_2);

		assert_eq!(essence_2.next_child_storage_key(child_info, b"2"), Ok(Some(b"3".to_vec())));
		assert_eq!(essence_2.next_child_storage_key(child_info, b"3"), Ok(Some(b"4".to_vec())));
		assert_eq!(essence_2.next_child_storage_key(child_info, b"4"), Ok(Some(b"6".to_vec())));
		assert_eq!(essence_2.next_child_storage_key(child_info, b"5"), Ok(Some(b"6".to_vec())));
		assert_eq!(essence_2.next_child_storage_key(child_info, b"6"), Ok(None));
	}
}
