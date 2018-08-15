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
use ethereum_types::H256 as TrieH256;
use backend::insert_into_memory_db;
use hashdb::{HashDB, DBValue};
use memorydb::MemoryDB;
use changes_trie::Storage;
use changes_trie::input::InputPair;
use {Storage as TrieStorage};

/// Adapter to use changes trie storage where backend storage is required.
pub struct TrieStorageAdapter(pub Arc<Storage>);

/// Storage implementation that uses proof as a source for trie nodes.
pub struct ProofCheckStorage {
	roots_storage: Arc<Storage>,
	proof_db: MemoryDB,
}

/// In-memory implementation of changes trie storage.
#[derive(Default)]
pub struct InMemoryStorage {
	roots: HashMap<u64, TrieH256>,
	mdb: MemoryDB,
}

impl TrieStorage for TrieStorageAdapter {
	fn get(&self, key: &TrieH256) -> Result<Option<DBValue>, String> {
		self.0.get(key)
	}
}

impl ProofCheckStorage {
	pub fn new(roots_storage: Arc<Storage>, proof: Vec<Vec<u8>>) -> Self {
		let mut proof_db = MemoryDB::new();
		for item in proof {
			proof_db.insert(&item);
		}

		ProofCheckStorage {
			roots_storage,
			proof_db,
		}
	}
}

impl Storage for ProofCheckStorage {
	fn root(&self, block: u64) -> Result<Option<TrieH256>, String> {
		let root = self.roots_storage.root(block)?;

		// every root that we're asking for MUST be a part of proof db
		if let Some(root) = root {
			if !self.proof_db.contains(&root) {
				return Err("TODO".into());
			}
		}

		Ok(root)
	}

	fn get(&self, key: &TrieH256) -> Result<Option<DBValue>, String> {
		Ok(self.proof_db.get(key))
	}
}

impl Storage for InMemoryStorage {
	fn root(&self, block: u64) -> Result<Option<TrieH256>, String> {
		Ok(self.roots.get(&block).cloned())
	}

	fn get(&self, key: &TrieH256) -> Result<Option<DBValue>, String> {
		Ok(self.mdb.get(key))
	}
}

impl From<Vec<(u64, Vec<InputPair>)>> for InMemoryStorage {
	fn from(inputs: Vec<(u64, Vec<InputPair>)>) -> Self {
		let mut mdb = MemoryDB::default();
		let mut roots = HashMap::new();
		for (block, pairs) in inputs {
			if let Some(root) = insert_into_memory_db(&mut mdb, pairs.into_iter().map(Into::into)) {
				roots.insert(block, root);
			}
		}

		InMemoryStorage { mdb, roots }
	}
}
