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

//! Changes trie storage utilities.

use std::collections::HashMap;
use std::sync::Arc;
use backend::insert_into_memory_db;
use hashdb::{Hasher, HashDB, DBValue};
use heapsize::HeapSizeOf;
use memorydb::MemoryDB;
use patricia_trie::NodeCodec;
use changes_trie::Storage;
use changes_trie::input::InputPair;
use trie_backend_essence::Storage as TrieStorage;

/// Adapter to use changes trie storage where backend storage is required.
pub struct TrieStorageAdapter<H: Hasher>(pub Arc<Storage<H>>);

/// Storage implementation that uses proof as a source for trie nodes.
pub struct ProofCheckStorage<H: Hasher> {
	proof_db: MemoryDB<H>,
}

/// In-memory implementation of changes trie storage.
#[derive(Default)]
pub struct InMemoryStorage<H: Hasher, C: NodeCodec<H>> where H::Out: HeapSizeOf {
	roots: HashMap<u64, H::Out>,
	mdb: MemoryDB<H>,
	_codec: ::std::marker::PhantomData<C>,
}

impl<H: Hasher> TrieStorage<H> for TrieStorageAdapter<H> {
	fn get(&self, key: &H::Out) -> Result<Option<DBValue>, String> {
		self.0.get(key)
	}
}

impl<H: Hasher> ProofCheckStorage<H> where H::Out: HeapSizeOf {
	pub fn new(proof: Vec<Vec<u8>>) -> Self {
		let mut proof_db = MemoryDB::<H>::new();
		for item in proof {
			proof_db.insert(&item);
		}

		ProofCheckStorage {
			proof_db,
		}
	}
}

impl<H: Hasher> Storage<H> for ProofCheckStorage<H> {
	fn root(&self, _block: u64) -> Result<Option<H::Out>, String> {
		unreachable!("This storage must not be used to read trie roots")
	}

	fn get(&self, key: &H::Out) -> Result<Option<DBValue>, String> {
		Ok(self.proof_db.get(key))
	}
}

impl<H: Hasher, C: NodeCodec<H>> InMemoryStorage<H, C> where C: Send + Sync, H::Out: HeapSizeOf {
	pub fn clear_storage(&mut self) {
		self.mdb = MemoryDB::new();
	}
}

impl<H: Hasher, C: NodeCodec<H>> Storage<H> for InMemoryStorage<H, C> where C: Send + Sync, H::Out: HeapSizeOf {
	fn root(&self, block: u64) -> Result<Option<H::Out>, String> {
		Ok(self.roots.get(&block).cloned())
	}

	fn get(&self, key: &H::Out) -> Result<Option<DBValue>, String> {
		Ok(self.mdb.get(key))
	}
}

impl<H, C> From<Vec<(u64, Vec<InputPair>)>> for InMemoryStorage<H, C>
	where
		H: Hasher,
		H::Out: HeapSizeOf,
		C: NodeCodec<H>,
{
	fn from(inputs: Vec<(u64, Vec<InputPair>)>) -> Self {
		let mut mdb = MemoryDB::default();
		let mut roots = HashMap::new();
		for (block, pairs) in inputs {
			if let Some(root) = insert_into_memory_db::<H, C, _>(&mut mdb, pairs.into_iter().map(Into::into)) {
				roots.insert(block, root);
			}
		}

		InMemoryStorage { mdb, roots, _codec: ::std::marker::PhantomData::<C>::default(), }
	}
}
