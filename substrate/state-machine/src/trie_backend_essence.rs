/*

	1. Storage должен быть точно такой же, как и в TrieBackend - get(H256)
	2. Нужен общий ProvingBackend, который будет экспозить только storage() + for_keys_with_prefix
		=> нужна общая часть TrieBackend с теми же методами

*/

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

//! Trie-based state machine backend.

use std::collections::HashMap;
use std::sync::Arc;
use ethereum_types::H256 as TrieH256;
use hashdb::{DBValue, HashDB};
use memorydb::MemoryDB;
use patricia_trie::{TrieDB, TrieDBMut, TrieError, Trie};

/// Patricia trie-based storage trait.
pub trait Storage: Send + Sync {
	/// Get a trie node.
	fn get(&self, key: &TrieH256) -> Result<Option<DBValue>, String>;
}

/// Patricia trie-based pairs storage.
pub struct TrieBackendEssence {
	storage: TrieBackendStorage,
	root: TrieH256,
}

impl TrieBackendEssence {
	/// Create new trie-based backend.
	pub fn with_storage(db: Arc<Storage>, root: TrieH256) -> Self {
		TrieBackendEssence {
			storage: TrieBackendStorage::Storage(db),
			root,
		}
	}

	/// Create new trie-based backend for genesis block.
	pub fn with_storage_for_genesis(db: Arc<Storage>) -> Self {
		let mut root = TrieH256::default();
		let mut mdb = MemoryDB::default();
		TrieDBMut::new(&mut mdb, &mut root);

		Self::with_storage(db, root)
	}

	/// Create new trie-based backend backed by MemoryDb storage.
	pub fn with_memorydb(db: MemoryDB, root: TrieH256) -> Self {
		TrieBackendEssence {
			storage: TrieBackendStorage::MemoryDb(db),
			root,
		}
	}

	/// Get backend storage reference.
	pub fn backend_storage(&self) -> &TrieBackendStorage {
		&self.storage
	}

	/// Get trie root.
	pub fn root(&self) -> &TrieH256 {
		&self.root
	}

	/// Get the value of storage at given key.
	pub fn storage(&self, key: &[u8]) -> Result<Option<Vec<u8>>, String> {
		let mut read_overlay = MemoryDB::default();
		let eph = Ephemeral {
			storage: &self.storage,
			overlay: &mut read_overlay,
		};

		let map_e = |e: Box<TrieError>| format!("Trie lookup error: {}", e);

		TrieDB::new(&eph, &self.root).map_err(map_e)?
			.get(key).map(|x| x.map(|val| val.to_vec())).map_err(map_e)
	}

	/// Execute given closure for all keys starting with prefix.
	pub fn for_keys_with_prefix<F: FnMut(&[u8])>(&self, prefix: &[u8], mut f: F) {
		let mut read_overlay = MemoryDB::default();
		let eph = Ephemeral {
			storage: &self.storage,
			overlay: &mut read_overlay,
		};

		let mut iter = move || -> Result<(), Box<TrieError>> {
			let trie = TrieDB::new(&eph, &self.root)?;
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

pub struct Ephemeral<'a> {
	storage: &'a TrieBackendStorage,
	overlay: &'a mut MemoryDB,
}

impl<'a> Ephemeral<'a> {
	pub fn new(storage: &'a TrieBackendStorage, overlay: &'a mut MemoryDB) -> Self {
		Ephemeral {
			storage,
			overlay,
		}
	}
}

impl<'a> HashDB for Ephemeral<'a> {
	fn keys(&self) -> HashMap<TrieH256, i32> {
		self.overlay.keys() // TODO: iterate backing
	}

	fn get(&self, key: &TrieH256) -> Option<DBValue> {
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

	fn contains(&self, key: &TrieH256) -> bool {
		self.get(key).is_some()
	}

	fn insert(&mut self, value: &[u8]) -> TrieH256 {
		self.overlay.insert(value)
	}

	fn emplace(&mut self, key: TrieH256, value: DBValue) {
		self.overlay.emplace(key, value)
	}

	fn remove(&mut self, key: &TrieH256) {
		self.overlay.remove(key)
	}
}

pub enum TrieBackendStorage {
	/// Key value db + storage column.
	Storage(Arc<Storage>),
	/// Hash db.
	MemoryDb(MemoryDB),
}

impl TrieBackendStorage {
	pub fn get(&self, key: &TrieH256) -> Result<Option<DBValue>, String> {
		match *self {
			TrieBackendStorage::Storage(ref db) =>
				db.get(key)
					.map_err(|e| format!("Trie lookup error: {}", e)),
			TrieBackendStorage::MemoryDb(ref db) =>
				Ok(db.get(key)),
		}
	}
}
