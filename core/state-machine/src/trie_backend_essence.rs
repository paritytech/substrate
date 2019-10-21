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

//! Trie-based state machine backend essence used to read values
//! from storage.

use std::ops::Deref;
use std::sync::Arc;
use log::{debug, warn};
use hash_db::{self, Hasher, EMPTY_PREFIX, Prefix};
use trie::{Trie, MemoryDB, PrefixedMemoryDB, DBValue,
	default_child_trie_root, read_trie_value, read_child_trie_value,
	for_keys_in_child_trie};
use trie::trie_types::{TrieDB, TrieError, Layout};
use crate::backend::Consolidate;

/// Patricia trie-based storage trait.
pub trait Storage<H: Hasher>: Send + Sync {
	/// Get a trie node.
	fn get(&self, key: &H::Out, prefix: Prefix) -> Result<Option<DBValue>, String>;
}

/// Patricia trie-based pairs storage essence.
pub struct TrieBackendEssence<S: TrieBackendStorage<H>, H: Hasher> {
	storage: S,
	root: H::Out,
}

impl<S: TrieBackendStorage<H>, H: Hasher> TrieBackendEssence<S, H> {
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

	/// Get the value of storage at given key.
	pub fn storage(&self, key: &[u8]) -> Result<Option<Vec<u8>>, String> {
		let mut read_overlay = S::Overlay::default();
		let eph = Ephemeral {
			storage: &self.storage,
			overlay: &mut read_overlay,
		};

		let map_e = |e| format!("Trie lookup error: {}", e);

		read_trie_value::<Layout<H>, _>(&eph, &self.root, key).map_err(map_e)
	}

	/// Get the value of child storage at given key.
	pub fn child_storage(&self, storage_key: &[u8], key: &[u8]) -> Result<Option<Vec<u8>>, String> {
		let root = self.storage(storage_key)?
			.unwrap_or_else(|| default_child_trie_root::<Layout<H>>(storage_key));

		let mut read_overlay = S::Overlay::default();
		let eph = Ephemeral {
			storage: &self.storage,
			overlay: &mut read_overlay,
		};

		let map_e = |e| format!("Trie lookup error: {}", e);

		read_child_trie_value::<Layout<H>, _>(storage_key, &eph, &root, key).map_err(map_e)
	}

	/// Retrieve all entries keys of child storage and call `f` for each of those keys.
	pub fn for_keys_in_child_storage<F: FnMut(&[u8])>(&self, storage_key: &[u8], f: F) {
		let root = match self.storage(storage_key) {
			Ok(v) => v.unwrap_or_else(|| default_child_trie_root::<Layout<H>>(storage_key)),
			Err(e) => {
				debug!(target: "trie", "Error while iterating child storage: {}", e);
				return;
			}
		};

		let mut read_overlay = S::Overlay::default();
		let eph = Ephemeral {
			storage: &self.storage,
			overlay: &mut read_overlay,
		};

		if let Err(e) = for_keys_in_child_trie::<Layout<H>, _, Ephemeral<S, H>>(
			storage_key,
			&eph,
			&root,
			f,
		) {
			debug!(target: "trie", "Error while iterating child storage: {}", e);
		}
	}

	/// Execute given closure for all keys starting with prefix.
	pub fn for_child_keys_with_prefix<F: FnMut(&[u8])>(&self, storage_key: &[u8], prefix: &[u8], mut f: F) {
		let root_vec = match self.storage(storage_key) {
			Ok(v) => v.unwrap_or_else(|| default_child_trie_root::<Layout<H>>(storage_key)),
			Err(e) => {
				debug!(target: "trie", "Error while iterating child storage: {}", e);
				return;
			}
		};
		let mut root = H::Out::default();
		root.as_mut().copy_from_slice(&root_vec);

		self.keys_values_with_prefix_inner(&root, prefix, |k, _v| f(k))
	}

	/// Execute given closure for all keys starting with prefix.
	pub fn for_keys_with_prefix<F: FnMut(&[u8])>(&self, prefix: &[u8], mut f: F) {
		self.keys_values_with_prefix_inner(&self.root, prefix, |k, _v| f(k))
	}


	fn keys_values_with_prefix_inner<F: FnMut(&[u8], &[u8])>(
		&self,
		root: &H::Out,
		prefix: &[u8],
		mut f: F,
	) {
		let mut read_overlay = S::Overlay::default();
		let eph = Ephemeral {
			storage: &self.storage,
			overlay: &mut read_overlay,
		};

		let mut iter = move || -> Result<(), Box<TrieError<H::Out>>> {
			let trie = TrieDB::<H>::new(&eph, root)?;
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

		if let Err(e) = iter() {
			debug!(target: "trie", "Error while iterating by prefix: {}", e);
		}
	}

	/// Execute given closure for all key and values starting with prefix.
	pub fn for_key_values_with_prefix<F: FnMut(&[u8], &[u8])>(&self, prefix: &[u8], f: F) {
		self.keys_values_with_prefix_inner(&self.root, prefix, f)
	}

}

pub(crate) struct Ephemeral<'a, S: 'a + TrieBackendStorage<H>, H: 'a + Hasher> {
	storage: &'a S,
	overlay: &'a mut S::Overlay,
}

impl<'a,
	S: 'a + TrieBackendStorage<H>,
	H: 'a + Hasher
> hash_db::AsPlainDB<H::Out, DBValue>
	for Ephemeral<'a, S, H>
{
	fn as_plain_db<'b>(&'b self) -> &'b (dyn hash_db::PlainDB<H::Out, DBValue> + 'b) { self }
	fn as_plain_db_mut<'b>(&'b mut self) -> &'b mut (dyn hash_db::PlainDB<H::Out, DBValue> + 'b) { self }
}

impl<'a,
	S: 'a + TrieBackendStorage<H>,
	H: 'a + Hasher
> hash_db::AsHashDB<H, DBValue>
	for Ephemeral<'a, S, H>
{
	fn as_hash_db<'b>(&'b self) -> &'b (dyn hash_db::HashDB<H, DBValue> + 'b) { self }
	fn as_hash_db_mut<'b>(&'b mut self) -> &'b mut (dyn hash_db::HashDB<H, DBValue> + 'b) { self }
}

impl<'a, S: TrieBackendStorage<H>, H: Hasher> Ephemeral<'a, S, H> {
	pub fn new(storage: &'a S, overlay: &'a mut S::Overlay) -> Self {
		Ephemeral {
			storage,
			overlay,
		}
	}
}

impl<'a,
	S: 'a + TrieBackendStorage<H>,
	H: Hasher
> hash_db::PlainDB<H::Out, DBValue>
	for Ephemeral<'a, S, H>
{
	fn get(&self, key: &H::Out) -> Option<DBValue> {
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
		hash_db::HashDB::get(self, key, EMPTY_PREFIX).is_some()
	}

	fn emplace(&mut self, key: H::Out, value: DBValue) {
		hash_db::HashDB::emplace(self.overlay, key, EMPTY_PREFIX, value)
	}

	fn remove(&mut self, key: &H::Out) {
		hash_db::HashDB::remove(self.overlay, key, EMPTY_PREFIX)
	}
}

impl<'a,
	S: 'a + TrieBackendStorage<H>,
	H: Hasher
> hash_db::PlainDBRef<H::Out, DBValue>
	for Ephemeral<'a, S, H>
{
	fn get(&self, key: &H::Out) -> Option<DBValue> { hash_db::PlainDB::get(self, key) }
	fn contains(&self, key: &H::Out) -> bool { hash_db::PlainDB::contains(self, key) }
}

impl<'a,
	S: 'a + TrieBackendStorage<H>,
	H: Hasher
> hash_db::HashDB<H, DBValue>
	for Ephemeral<'a, S, H>
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

impl<'a,
	S: 'a + TrieBackendStorage<H>,
	H: Hasher
> hash_db::HashDBRef<H, DBValue>
	for Ephemeral<'a, S, H>
{
	fn get(&self, key: &H::Out, prefix: Prefix) -> Option<DBValue> { hash_db::HashDB::get(self, key, prefix) }
	fn contains(&self, key: &H::Out, prefix: Prefix) -> bool { hash_db::HashDB::contains(self, key, prefix) }
}

/// Key-value pairs storage that is used by trie backend essence.
pub trait TrieBackendStorage<H: Hasher>: Send + Sync {
	/// Type of in-memory overlay.
	type Overlay: hash_db::HashDB<H, DBValue> + Default + Consolidate;
	/// Get the value stored at key.
	fn get(&self, key: &H::Out, prefix: Prefix) -> Result<Option<DBValue>, String>;
}

// This implementation is used by normal storage trie clients.
impl<H: Hasher> TrieBackendStorage<H> for Arc<dyn Storage<H>> {
	type Overlay = PrefixedMemoryDB<H>;

	fn get(&self, key: &H::Out, prefix: Prefix) -> Result<Option<DBValue>, String> {
		Storage::<H>::get(self.deref(), key, prefix)
	}
}

// This implementation is used by test storage trie clients.
impl<H: Hasher> TrieBackendStorage<H> for PrefixedMemoryDB<H> {
	type Overlay = PrefixedMemoryDB<H>;

	fn get(&self, key: &H::Out, prefix: Prefix) -> Result<Option<DBValue>, String> {
		Ok(hash_db::HashDB::get(self, key, prefix))
	}
}

impl<H: Hasher> TrieBackendStorage<H> for MemoryDB<H> {
	type Overlay = MemoryDB<H>;

	fn get(&self, key: &H::Out, prefix: Prefix) -> Result<Option<DBValue>, String> {
		Ok(hash_db::HashDB::get(self, key, prefix))
	}
}
