// Copyright 2017-2019 Parity Technologies (UK) Ltd
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//! Changes trie storage utilities.

use std::collections::HashMap;
use hash_db::Hasher;
use trie::DBValue;
use heapsize::HeapSizeOf;
use trie::MemoryDB;
use parking_lot::RwLock;
use crate::changes_trie::{AnchorBlockId, RootsStorage, Storage};
use crate::trie_backend_essence::TrieBackendStorage;

#[cfg(test)]
use std::collections::HashSet;
#[cfg(test)]
use crate::backend::insert_into_memory_db;
#[cfg(test)]
use crate::changes_trie::input::InputPair;

/// In-memory implementation of changes trie storage.
pub struct InMemoryStorage<H: Hasher> where H::Out: HeapSizeOf {
	data: RwLock<InMemoryStorageData<H>>,
}

/// Adapter for using changes trie storage as a TrieBackendEssence' storage.
pub struct TrieBackendAdapter<'a, H: Hasher, S: 'a + Storage<H>> {
	storage: &'a S,
	_hasher: ::std::marker::PhantomData<H>,
}

struct InMemoryStorageData<H: Hasher> where H::Out: HeapSizeOf {
	roots: HashMap<u64, H::Out>,
	mdb: MemoryDB<H>,
}

impl<H: Hasher> InMemoryStorage<H> where H::Out: HeapSizeOf {
	/// Create the storage from given in-memory database.
	pub fn with_db(mdb: MemoryDB<H>) -> Self {
		Self {
			data: RwLock::new(InMemoryStorageData {
				roots: HashMap::new(),
				mdb,
			}),
		}
	}

	/// Create the storage with empty database.
	pub fn new() -> Self {
		Self::with_db(Default::default())
	}

	#[cfg(test)]
	pub fn with_inputs(inputs: Vec<(u64, Vec<InputPair>)>) -> Self {
		let mut mdb = MemoryDB::default();
		let mut roots = HashMap::new();
		for (block, pairs) in inputs {
			let root = insert_into_memory_db::<H, _>(&mut mdb, pairs.into_iter().map(Into::into));
			if let Some(root) = root {
				roots.insert(block, root);
			}
		}

		InMemoryStorage {
			data: RwLock::new(InMemoryStorageData {
				roots,
				mdb,
			}),
		}
	}

	#[cfg(test)]
	pub fn clear_storage(&self) {
		self.data.write().mdb = MemoryDB::default();	// use new to be more correct
	}

	#[cfg(test)]
	pub fn remove_from_storage(&self, keys: &HashSet<H::Out>) {
		let mut data = self.data.write();
		for key in keys {
			data.mdb.remove_and_purge(key, &[]);
		}
	}

	#[cfg(test)]
	pub fn into_mdb(self) -> MemoryDB<H> {
		self.data.into_inner().mdb
	}

	/// Insert changes trie for given block.
	pub fn insert(&self, block: u64, changes_trie_root: H::Out, trie: MemoryDB<H>) {
		let mut data = self.data.write();
		data.roots.insert(block, changes_trie_root);
		data.mdb.consolidate(trie);
	}
}

impl<H: Hasher> RootsStorage<H> for InMemoryStorage<H> where H::Out: HeapSizeOf {
	fn root(&self, _anchor_block: &AnchorBlockId<H::Out>, block: u64) -> Result<Option<H::Out>, String> {
		Ok(self.data.read().roots.get(&block).cloned())
	}
}

impl<H: Hasher> Storage<H> for InMemoryStorage<H> where H::Out: HeapSizeOf {
	fn get(&self, key: &H::Out, prefix: &[u8]) -> Result<Option<DBValue>, String> {
		MemoryDB::<H>::get(&self.data.read().mdb, key, prefix)
	}
}

impl<'a, H: Hasher, S: 'a + Storage<H>> TrieBackendAdapter<'a, H, S> {
	pub fn new(storage: &'a S) -> Self {
		Self { storage, _hasher: Default::default() }
	}
}

impl<'a, H: Hasher, S: 'a + Storage<H>> TrieBackendStorage<H> for TrieBackendAdapter<'a, H, S> {
	type Overlay = MemoryDB<H>;

	fn get(&self, key: &H::Out, prefix: &[u8]) -> Result<Option<DBValue>, String> {
		self.storage.get(key, prefix)
	}
}
