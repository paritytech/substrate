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

use std::sync::Arc;
use memorydb::MemoryDB;
use changes_trie::{Storage as ChangesTrieStorage, compute_changes_trie_root};
use overlayed_changes::OverlayedChanges;
use patricia_trie::{TrieDB, TrieDBMut, TrieError, Trie, TrieMut};
use trie_backend_essence::{TrieBackendEssence, TrieBackendStorage, Ephemeral, Storage};
use {Backend};
pub use ethereum_types::H256 as TrieH256;
pub use hashdb::DBValue;

/// Try convert into trie-based backend.
pub trait TryIntoTrieBackend {
	/// Try to convert self into trie backend.
	fn try_into_trie_backend(self) -> Option<TrieBackend>;
}

/// Patricia trie-based backend. Transaction type is an overlay of changes to commit.
pub struct TrieBackend {
	essence: TrieBackendEssence,
	changes_trie_storage: Option<Arc<ChangesTrieStorage>>,
}

impl TrieBackend {
	/// Create new trie-based backend.
	pub fn with_storage(db: Arc<Storage>, root: TrieH256, changes_trie_storage: Option<Arc<ChangesTrieStorage>>) -> Self {
		TrieBackend {
			essence: TrieBackendEssence::with_storage(db, root),
			changes_trie_storage,
		}
	}

	/// Create new trie-based backend for genesis block.
	pub fn with_storage_for_genesis(db: Arc<Storage>, changes_trie_storage: Option<Arc<ChangesTrieStorage>>) -> Self {
		TrieBackend {
			essence: TrieBackendEssence::with_storage_for_genesis(db),
			changes_trie_storage,
		}
	}

	/// Create new trie-based backend backed by MemoryDb storage.
	pub fn with_memorydb(db: MemoryDB, root: TrieH256, changes_trie_storage: Option<Arc<ChangesTrieStorage>>) -> Self {
		TrieBackend {
			essence: TrieBackendEssence::with_memorydb(db, root),
			changes_trie_storage,
		}
	}

	/// Get backend essence reference.
	pub fn essence(&self) -> &TrieBackendEssence {
		&self.essence
	}

	/// Get backend storage reference.
	pub fn backend_storage(&self) -> &TrieBackendStorage {
		self.essence.backend_storage()
	}

	/// Get trie root.
	pub fn root(&self) -> &TrieH256 {
		self.essence.root()
	}
}

impl super::Error for String {}

impl Backend for TrieBackend {
	type Error = String;
	type StorageTransaction = MemoryDB;
	type ChangesTrieTransaction = MemoryDB;

	fn changes_trie_storage(&self) -> Option<Arc<ChangesTrieStorage>> {
		self.changes_trie_storage.clone()
	}

	fn storage(&self, key: &[u8]) -> Result<Option<Vec<u8>>, Self::Error> {
		self.essence.storage(key)
	}

	fn for_keys_with_prefix<F: FnMut(&[u8])>(&self, prefix: &[u8], f: F) {
		self.essence.for_keys_with_prefix(prefix, f)
	}

	fn pairs(&self) -> Vec<(Vec<u8>, Vec<u8>)> {
		let mut read_overlay = MemoryDB::default();
		let eph = Ephemeral::new(
			self.essence.backend_storage(),
			&mut read_overlay,
		);

		let collect_all = || -> Result<_, Box<TrieError>> {
			let trie = TrieDB::new(&eph, self.essence.root())?;
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
			}
		}
	}

	fn storage_root<I>(&self, delta: I) -> ([u8; 32], MemoryDB)
		where I: IntoIterator<Item=(Vec<u8>, Option<Vec<u8>>)>
	{
		let mut write_overlay = MemoryDB::default();
		let mut root = *self.essence.root();
		{
			let mut eph = Ephemeral::new(
				self.essence.backend_storage(),
				&mut write_overlay,
			);

			let mut trie = TrieDBMut::from_existing(&mut eph, &mut root).expect("prior state root to exist"); // TODO: handle gracefully
			for (key, change) in delta {
				let result = match change {
					Some(val) => trie.insert(&key, &val),
					None => trie.remove(&key), // TODO: archive mode
				};

				if let Err(e) = result {
					warn!(target: "trie", "Failed to write to trie: {}", e);
				}
			}
		}

		(root.0.into(), write_overlay)
	}

	fn changes_trie_root(&self, overlay: &OverlayedChanges) -> Option<([u8; 32], MemoryDB)> {
		compute_changes_trie_root(self.changes_trie_storage.clone(), overlay)
			.map(|(root, changes)| {
				let mut calculated_root = Default::default();
				let mut mdb = MemoryDB::new();
				{
					let mut trie = TrieDBMut::new(&mut mdb, &mut calculated_root);
					for (key, value) in changes {
						trie.insert(&key, &value);
					}
				}

				(root, mdb)
			})
	}
}

impl TryIntoTrieBackend for TrieBackend {
	fn try_into_trie_backend(self) -> Option<TrieBackend> {
		Some(self)
	}
}

#[cfg(test)]
pub mod tests {
	use std::collections::HashSet;
	use super::*;

	fn test_db() -> (MemoryDB, TrieH256) {
		let mut root = TrieH256::default();
		let mut mdb = MemoryDB::default();
		{
			let mut trie = TrieDBMut::new(&mut mdb, &mut root);
			trie.insert(b"key", b"value").unwrap();
			trie.insert(b"value1", &[42]).unwrap();
			trie.insert(b"value2", &[24]).unwrap();
			trie.insert(b":code", b"return 42").unwrap();
			for i in 128u8..255u8 {
				trie.insert(&[i], &[i]).unwrap();
			}
		}
		(mdb, root)
	}

	pub fn test_trie() -> TrieBackend {
		let (mdb, root) = test_db();
		TrieBackend::with_memorydb(mdb, root, None)
	}

	#[test]
	fn read_from_storage_returns_some() {
		assert_eq!(test_trie().storage(b"key").unwrap(), Some(b"value".to_vec()));
	}

	#[test]
	fn read_from_storage_returns_none() {
		assert_eq!(test_trie().storage(b"non-existing-key").unwrap(), None);
	}

	#[test]
	fn pairs_are_not_empty_on_non_empty_storage() {
		assert!(!test_trie().pairs().is_empty());
	}

	#[test]
	fn pairs_are_empty_on_empty_storage() {
		assert!(TrieBackend::with_memorydb(MemoryDB::new(), Default::default(), None).pairs().is_empty());
	}

	#[test]
	fn storage_root_is_non_default() {
		assert!(test_trie().storage_root(::std::iter::empty()).0 != [0; 32]);
	}

	#[test]
	fn storage_root_transaction_is_empty() {
		assert!(test_trie().storage_root(::std::iter::empty()).1.drain().is_empty());
	}

	#[test]
	fn storage_root_transaction_is_non_empty() {
		let (new_root, mut tx) = test_trie().storage_root(vec![(b"new-key".to_vec(), Some(b"new-value".to_vec()))]);
		assert!(!tx.drain().is_empty());
		assert!(new_root != test_trie().storage_root(::std::iter::empty()).0);
	}

	#[test]
	fn prefix_walking_works() {
		let trie = test_trie();

		let mut seen = HashSet::new();
		trie.for_keys_with_prefix(b"value", |key| {
			let for_first_time = seen.insert(key.to_vec());
			assert!(for_first_time, "Seen key '{:?}' more than once", key);
		});

		let mut expected = HashSet::new();
		expected.insert(b"value1".to_vec());
		expected.insert(b"value2".to_vec());
		assert_eq!(seen, expected);
	}
}
