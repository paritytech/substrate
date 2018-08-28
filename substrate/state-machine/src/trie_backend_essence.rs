// Copyright 2017 Parity Technologies (UK) Ltd.
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

use std::collections::HashMap;
use std::marker::PhantomData;
use std::ops::Deref;
use std::sync::Arc;
use hashdb::{Hasher, DBValue, AsHashDB, HashDB};
use heapsize::HeapSizeOf;
use memorydb::MemoryDB;
use patricia_trie::{TrieDB, TrieError, Trie, NodeCodec};
use changes_trie::Storage as ChangesTrieStorage;

/// Patricia trie-based storage trait.
pub trait Storage<H: Hasher>: Send + Sync {
	/// Get a trie node.
	fn get(&self, key: &H::Out) -> Result<Option<DBValue>, String>;
}

/// Patricia trie-based pairs storage essence.
pub struct TrieBackendEssence<S: TrieBackendStorage<H>, H: Hasher, C: NodeCodec<H>> {
	storage: S,
	root: H::Out,
	_codec: PhantomData<C>,
}

impl<S: TrieBackendStorage<H>, H: Hasher, C: NodeCodec<H>> TrieBackendEssence<S, H, C> where H::Out: HeapSizeOf {
	/// Create new trie-based backend.
	pub fn new(storage: S, root: H::Out) -> Self {
		TrieBackendEssence {
			storage,
			root,
			_codec: Default::default(),
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

	/// Get the value of storage at given key.
	pub fn storage(&self, key: &[u8]) -> Result<Option<Vec<u8>>, String> {
		let mut read_overlay = MemoryDB::default();
		let eph = Ephemeral {
			storage: &self.storage,
			overlay: &mut read_overlay,
		};

		let map_e = |e| format!("Trie lookup error: {}", e);

		TrieDB::<H, C>::new(&eph, &self.root).map_err(map_e)?
			.get(key).map(|x| x.map(|val| val.to_vec())).map_err(map_e)
	}

	/// Execute given closure for all keys starting with prefix.
	pub fn for_keys_with_prefix<F: FnMut(&[u8])>(&self, prefix: &[u8], mut f: F) {
		let mut read_overlay = MemoryDB::default();
		let eph = Ephemeral {
			storage: &self.storage,
			overlay: &mut read_overlay,
		};

		let mut iter = move || -> Result<(), Box<TrieError<H::Out, C::Error>>> {
			let trie = TrieDB::<H, C>::new(&eph, &self.root)?;
			let mut iter = trie.iter()?;

			iter.seek(prefix)?;

			for x in iter {
				let (key, _) = x?;

				if !key.starts_with(prefix) {
					break;
				}

				f(&key);
			}

			Ok(())
		};

		if let Err(e) = iter() {
			debug!(target: "trie", "Error while iterating by prefix: {}", e);
		}
	}
}

pub(crate) struct Ephemeral<'a, S: 'a + TrieBackendStorage<H>, H: 'a + Hasher> {
	storage: &'a S,
	overlay: &'a mut MemoryDB<H>,
}

impl<'a, S: TrieBackendStorage<H>, H: Hasher> AsHashDB<H> for Ephemeral<'a, S, H> where H::Out: HeapSizeOf {
	fn as_hashdb(&self) -> &HashDB<H> { self }
	fn as_hashdb_mut(&mut self) -> &mut HashDB<H> { self }
}

impl<'a, S: 'a + TrieBackendStorage<H>, H: Hasher> Ephemeral<'a, S, H> {
	pub fn new(storage: &'a S, overlay: &'a mut MemoryDB<H>) -> Self {
		Ephemeral {
			storage,
			overlay,
		}
	}
}

impl<'a, S: TrieBackendStorage<H>, H: Hasher> HashDB<H> for Ephemeral<'a, S, H> where H::Out: HeapSizeOf {
	fn keys(&self) -> HashMap<H::Out, i32> {
		self.overlay.keys() // TODO: iterate backing
	}

	fn get(&self, key: &H::Out) -> Option<DBValue> {
		match self.overlay.raw(key) {
			Some((val, i)) => {
				if i <= 0 {
					None
				} else {
					Some(val)
				}
			}
			None => match self.storage.get(&key) {
				Ok(x) => x,
				Err(e) => {
					warn!(target: "trie", "Failed to read from DB: {}", e);
					None
				},
			},
		}
	}

	fn contains(&self, key: &H::Out) -> bool {
		self.get(key).is_some()
	}

	fn insert(&mut self, value: &[u8]) -> H::Out {
		self.overlay.insert(value)
	}

	fn emplace(&mut self, key: H::Out, value: DBValue) {
		self.overlay.emplace(key, value)
	}

	fn remove(&mut self, key: &H::Out) {
		self.overlay.remove(key)
	}
}

/// Key-value pairs storage that is used by trie backend essence.
pub trait TrieBackendStorage<H: Hasher>: Send + Sync {
	fn get(&self, key: &H::Out) -> Result<Option<DBValue>, String>;
}

// This implementation is used by normal storage trie clients.
impl<H: Hasher> TrieBackendStorage<H> for Arc<Storage<H>> {
	fn get(&self, key: &H::Out) -> Result<Option<DBValue>, String> {
		Storage::<H>::get(self.deref(), key)
	}
}

// This implementation is used by test storage trie clients.
impl<H: Hasher> TrieBackendStorage<H> for MemoryDB<H> {
	fn get(&self, key: &H::Out) -> Result<Option<DBValue>, String> {
		Ok(HashDB::<H>::get(self, key))
	}
}

// This implementation is used by changes trie clients.
impl<'a, S, H: Hasher> TrieBackendStorage<H> for &'a S where S: ChangesTrieStorage<H> {
	fn get(&self, key: &H::Out) -> Result<Option<DBValue>, String> {
		ChangesTrieStorage::<H>::get(*self, key)
	}
}
