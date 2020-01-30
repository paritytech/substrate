// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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

//! Trie-based state machine backend essence used to read values
//! from storage.

use std::ops::Deref;
use std::sync::Arc;
use std::marker::PhantomData;
use log::{debug, warn};
use hash_db::{self, Hasher, EMPTY_PREFIX, Prefix};
use sp_trie::{Trie, MemoryDB, PrefixedMemoryDB, DBValue,
	read_trie_value,
	for_keys_in_trie, KeySpacedDB, keyspace_as_prefix_alloc};
use sp_trie::trie_types::{TrieDB, TrieError, Layout};
use crate::{backend::Consolidate, StorageKey, StorageValue};
use sp_core::storage::{ChildInfo, OwnedChildInfo};
use codec::Encode;

/// Patricia trie-based storage trait.
pub trait Storage<H: Hasher>: Send + Sync {
	/// Get a trie node.
	fn get(
		&self,
		trie: Option<ChildInfo>,
		key: &H::Out,
		prefix: Prefix,
	) -> Result<Option<DBValue>, String>;
}

/// Patricia trie-based pairs storage essence.
pub struct TrieBackendEssence<S: TrieBackendStorageRef<H>, H: Hasher> {
	storage: S,
	root: H::Out,
}

impl<S: TrieBackendStorageRef<H>, H: Hasher> TrieBackendEssence<S, H> where H::Out: Encode {
	/// Create new trie-based backend.
	pub fn new(storage: S, root: H::Out) -> Self {
		TrieBackendEssence {
			storage,
			root,
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

	/// Consumes self and returns underlying storage.
	pub fn into_storage(self) -> S {
		self.storage
	}

	/// Return the next key in the trie i.e. the minimum key that is strictly superior to `key` in
	/// lexicographic order.
	pub fn next_storage_key(&self, key: &[u8]) -> Result<Option<StorageKey>, String> {
		let eph = BackendStorageDBRef::new(&self.storage);

		let trie = TrieDB::<H>::new(&eph, &self.root)
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
	pub fn storage(&self, key: &[u8]) -> Result<Option<StorageValue>, String> {
		let eph = BackendStorageDBRef::new(&self.storage);

		let map_e = |e| format!("Trie lookup error: {}", e);

		read_trie_value::<Layout<H>, _>(&eph, &self.root, key).map_err(map_e)
	}

	/// Retrieve all entries keys of storage and call `f` for each of those keys.
	pub fn for_keys<F: FnMut(&[u8])>(
		&self,
		f: F,
	) {
		let eph = BackendStorageDBRef::new(&self.storage);

		if let Err(e) = for_keys_in_trie::<Layout<H>, _, BackendStorageDBRef<S, H>>(
			&eph,
			&self.root,
			f,
		) {
			debug!(target: "trie", "Error while iterating child storage: {}", e);
		}
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
		child_info: Option<ChildInfo>,
	) {
		let eph = BackendStorageDBRef::new(&self.storage);

		let mut iter = move |db| -> Result<(), Box<TrieError<H::Out>>> {
			let trie = TrieDB::<H>::new(db, root)?;
			let mut iter = trie.iter()?;

			iter.seek(prefix)?;

			for x in iter {
				let (key, value) = x?;

				if !key.starts_with(prefix) {
					break;
				}

				f(&key, &value);
			}

			Ok(())
		};

		let result = if let Some(child_info) = child_info {
			let db = KeySpacedDB::new(&eph, child_info.keyspace());
			iter(&db)
		} else {
			iter(&eph)
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

pub(crate) struct Ephemeral<'a, S, H, O> where
	S: 'a + TrieBackendStorageRef<H>,
	H: 'a + Hasher,
	O: hash_db::HashDB<H, DBValue> + Default + Consolidate,
{
	storage: &'a S,
	overlay: &'a mut O,
	_ph: PhantomData<H>,
}

pub(crate) struct BackendStorageDBRef<'a, S, H> where
	S: 'a + TrieBackendStorageRef<H>,
	H: 'a + Hasher,
{
	storage: &'a S,
	_ph: PhantomData<H>,
}

impl<'a, S, H, O> hash_db::AsPlainDB<H::Out, DBValue> for Ephemeral<'a, S, H, O> where
	S: 'a + TrieBackendStorage<H>,
	H: 'a + Hasher,
	O: hash_db::HashDB<H, DBValue> + Default + Consolidate,
{
	fn as_plain_db<'b>(&'b self) -> &'b (dyn hash_db::PlainDB<H::Out, DBValue> + 'b) { self }
	fn as_plain_db_mut<'b>(&'b mut self) -> &'b mut (dyn hash_db::PlainDB<H::Out, DBValue> + 'b) {
		self
	}
}

impl<'a, S, H, O> hash_db::AsHashDB<H, DBValue> for Ephemeral<'a, S, H, O> where
	S: 'a + TrieBackendStorage<H>,
	H: 'a + Hasher,
	O: hash_db::HashDB<H, DBValue> + Default + Consolidate,
{
	fn as_hash_db<'b>(&'b self) -> &'b (dyn hash_db::HashDB<H, DBValue> + 'b) { self }
	fn as_hash_db_mut<'b>(&'b mut self) -> &'b mut (dyn hash_db::HashDB<H, DBValue> + 'b) { self }
}

impl<'a, S, H, O> Ephemeral<'a, S, H, O> where
	S: 'a + TrieBackendStorageRef<H>,
	H: 'a + Hasher,
	O: hash_db::HashDB<H, DBValue> + Default + Consolidate,
{
	pub fn new(storage: &'a S, overlay: &'a mut O) -> Self {
		Ephemeral {
			storage,
			overlay,
			_ph: PhantomData,
		}
	}
}

impl<'a, S, H> BackendStorageDBRef<'a, S, H> where
	S: 'a + TrieBackendStorageRef<H>,
	H: 'a + Hasher,
{
	pub fn new(storage: &'a S) -> Self {
		BackendStorageDBRef {
			storage,
			_ph: PhantomData,
		}
	}
}

impl<'a, S, H, O> hash_db::PlainDB<H::Out, DBValue> for Ephemeral<'a, S, H, O> where
	S: 'a + TrieBackendStorage<H>,
	H: 'a + Hasher,
	O: hash_db::HashDB<H, DBValue> + Default + Consolidate,
{
	fn get(&self, key: &H::Out) -> Option<DBValue> {
		hash_db::PlainDBRef::get(self, key)
	}

	fn contains(&self, key: &H::Out) -> bool {
		hash_db::PlainDBRef::contains(self, key)
	}

	fn emplace(&mut self, key: H::Out, value: DBValue) {
		hash_db::HashDB::emplace(self.overlay, key, EMPTY_PREFIX, value)
	}

	fn remove(&mut self, key: &H::Out) {
		hash_db::HashDB::remove(self.overlay, key, EMPTY_PREFIX)
	}
}

impl<'a, S, H, O> hash_db::PlainDBRef<H::Out, DBValue> for Ephemeral<'a, S, H, O> where
	S: 'a + TrieBackendStorageRef<H>,
	H: 'a + Hasher,
	O: hash_db::HashDB<H, DBValue> + Default + Consolidate,
{
	fn get(&self, key: &H::Out) -> Option<DBValue> {
		// TODO need new trait with ct as parameter!!!
		if let Some(val) = hash_db::HashDB::get(self.overlay, key, EMPTY_PREFIX) {
			Some(val)
		} else {
			match self.storage.get(&key, EMPTY_PREFIX) {
				Ok(x) => x,
				Err(e) => {
					warn!(target: "trie", "Failed to read from DB: {}", e);
					None
				},
			}
		}
	}

	fn contains(&self, key: &H::Out) -> bool {
		hash_db::HashDBRef::get(self, key, EMPTY_PREFIX).is_some()
	}
}

impl<'a, S, H> hash_db::PlainDBRef<H::Out, DBValue> for BackendStorageDBRef<'a, S, H> where
	S: 'a + TrieBackendStorageRef<H>,
	H: 'a + Hasher,
{
	fn get(&self, key: &H::Out) -> Option<DBValue> {
		match self.storage.get(&key, EMPTY_PREFIX) {
			Ok(x) => x,
			Err(e) => {
				warn!(target: "trie", "Failed to read from DB: {}", e);
				None
			},
		}
	}

	fn contains(&self, key: &H::Out) -> bool {
		hash_db::HashDBRef::get(self, key, EMPTY_PREFIX).is_some()
	}
}


impl<'a, S, H, O> hash_db::HashDB<H, DBValue> for Ephemeral<'a, S, H, O> where
	S: 'a + TrieBackendStorage<H>,
	H: 'a + Hasher,
	O: hash_db::HashDB<H, DBValue> + Default + Consolidate,
{

	fn get(&self, key: &H::Out, prefix: Prefix) -> Option<DBValue> {
		hash_db::HashDBRef::get(self, key, prefix)
	}

	fn contains(&self, key: &H::Out, prefix: Prefix) -> bool {
		hash_db::HashDBRef::contains(self, key, prefix)
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

impl<'a, S, H, O> hash_db::HashDBRef<H, DBValue> for Ephemeral<'a, S, H, O> where
	S: 'a + TrieBackendStorageRef<H>,
	H: 'a + Hasher,
	O: hash_db::HashDB<H, DBValue> + Default + Consolidate,
{
	fn get(&self, key: &H::Out, prefix: Prefix) -> Option<DBValue> {
		if let Some(val) = hash_db::HashDB::get(self.overlay, key, prefix) {
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
		hash_db::HashDBRef::get(self, key, prefix).is_some()
	}
}

impl<'a, S, H> hash_db::HashDBRef<H, DBValue> for BackendStorageDBRef<'a, S, H> where
	S: 'a + TrieBackendStorageRef<H>,
	H: 'a + Hasher,
{
	fn get(&self, key: &H::Out, prefix: Prefix) -> Option<DBValue> {
		match self.storage.get(&key, prefix) {
			Ok(x) => x,
			Err(e) => {
				warn!(target: "trie", "Failed to read from DB: {}", e);
				None
			},
		}
	}

	fn contains(&self, key: &H::Out, prefix: Prefix) -> bool {
		hash_db::HashDBRef::get(self, key, prefix).is_some()
	}
}


/// Key-value pairs storage that is used by trie backend essence.
pub trait TrieBackendStorageRef<H: Hasher> {
	/// Type of in-memory overlay.
	type Overlay: hash_db::HashDB<H, DBValue> + Default + Consolidate;
	/// Get the value stored at key.
	fn get(
		&self,
		key: &H::Out,
		prefix: Prefix,
	) -> Result<Option<DBValue>, String>;
}

/// Key-value pairs storage that is used by trie backend essence.
pub trait TrieBackendStorage<H: Hasher>: TrieBackendStorageRef<H> + Send + Sync { }

impl<H: Hasher, B: TrieBackendStorageRef<H> + Send + Sync> TrieBackendStorage<H> for B {}

// This implementation is used by normal storage trie clients.
impl<H: Hasher> TrieBackendStorageRef<H> for (Arc<dyn Storage<H>>, Option<OwnedChildInfo>) {
	type Overlay = PrefixedMemoryDB<H>;

	fn get(
		&self,
		key: &H::Out,
		prefix: Prefix,
	) -> Result<Option<DBValue>, String> {
		let child_info = self.1.as_ref();
		Storage::<H>::get(self.0.deref(), child_info.map(|c| c.as_ref()), key, prefix)
	}
}


/// This is an essence for the child trie backend.
pub struct ChildTrieBackendStorage<'a, H: Hasher, B: TrieBackendStorageRef<H>> {
	db: &'a B,
	info: Option<ChildInfo<'a>>,
	buffer: &'a mut Vec<u8>,
	_ph: PhantomData<H>,
}

impl<'a, H: Hasher, B: TrieBackendStorageRef<H>> ChildTrieBackendStorage<'a, H, B> {
	/// Instantiate a `ChildTrieBackendStorage`.
	pub fn new(db: &'a B, info: Option<ChildInfo<'a>>, buffer: &'a mut Vec<u8>) -> Self {
		ChildTrieBackendStorage {
			db,
			info,
			buffer,
			_ph: PhantomData,
		}
	}
}

impl<'a, H: Hasher, B: TrieBackendStorageRef<H>> TrieBackendStorageRef<H> for ChildTrieBackendStorage<'a, H, B> {
	type Overlay = PrefixedMemoryDB<H>;

	fn get(
		&self,
		key: &H::Out,
		prefix: Prefix,
	) -> Result<Option<DBValue>, String> {
		if let Some(keyspace) = self.info.as_ref().map(|ci| ci.keyspace()) {
			// TODO switch to &mut self like in overlay pr and use commented code
			/*self.buffer.resize(keyspace.len() + prefix.0.len(), 0);
			self.buffer[..keyspace.len()].copy_from_slice(keyspace);
			self.buffer[keyspace.len()..].copy_from_slice(prefix.0);
			self.db.get(key, (self.buffer.as_slice(), prefix.1))*/

			let prefix = keyspace_as_prefix_alloc(keyspace, prefix);
			self.db.get(key, (prefix.0.as_slice(), prefix.1))
		} else {
			self.db.get(key, prefix)
		}
	}
}


// This implementation is used by test storage trie clients.
impl<H: Hasher> TrieBackendStorageRef<H> for PrefixedMemoryDB<H> {
	type Overlay = PrefixedMemoryDB<H>;

	fn get(
		&self,
		key: &H::Out,
		prefix: Prefix,
	) -> Result<Option<DBValue>, String> {
		// TODO should we split prefixed memory db too?? -> likely yes: sharing
		// rc does not make sense -> change type of PrefixedMemoryDB.
		Ok(hash_db::HashDB::get(self, key, prefix))
	}
}

impl<H: Hasher> TrieBackendStorageRef<H> for MemoryDB<H> {
	type Overlay = MemoryDB<H>;

	fn get(
		&self,
		key: &H::Out,
		prefix: Prefix,
	) -> Result<Option<DBValue>, String> {
		Ok(hash_db::HashDB::get(self, key, prefix))
	}
}

#[cfg(test)]
mod test {
	use sp_core::{Blake2Hasher, H256};
	use sp_trie::{TrieMut, PrefixedMemoryDB, trie_types::TrieDBMut, KeySpacedDBMut};
	use super::*;
	use crate::trie_backend::TrieBackend;
	use crate::backend::Backend;

	#[test]
	fn next_storage_key_and_next_child_storage_key_work() {
		let child_info = ChildInfo::new_default(b"uniqueid");
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
			trie.insert(b"MyChild", root_1.as_ref()).expect("insert failed");
		};

		let essence_1 = TrieBackend::new(mdb, root_1);

		assert_eq!(essence_1.next_storage_key(b"2"), Ok(Some(b"3".to_vec())));
		assert_eq!(essence_1.next_storage_key(b"3"), Ok(Some(b"4".to_vec())));
		assert_eq!(essence_1.next_storage_key(b"4"), Ok(Some(b"6".to_vec())));
		assert_eq!(essence_1.next_storage_key(b"5"), Ok(Some(b"6".to_vec())));
		assert_eq!(essence_1.next_storage_key(b"6"), Ok(None));

		let mdb = essence_1.into_storage();
		let essence_2 = TrieBackend::new(mdb, root_2);

		assert_eq!(
			essence_2.next_child_storage_key(b"MyChild", child_info, b"2"), Ok(Some(b"3".to_vec()))
		);
		assert_eq!(
			essence_2.next_child_storage_key(b"MyChild", child_info, b"3"), Ok(Some(b"4".to_vec()))
		);
		assert_eq!(
			essence_2.next_child_storage_key(b"MyChild", child_info, b"4"), Ok(Some(b"6".to_vec()))
		);
		assert_eq!(
			essence_2.next_child_storage_key(b"MyChild", child_info, b"5"), Ok(Some(b"6".to_vec()))
		);
		assert_eq!(
			essence_2.next_child_storage_key(b"MyChild", child_info, b"6"), Ok(None)
		);
	}
}
