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
use Backend;
use hashdb::{Hasher, HashDB, AsHashDB};
use memorydb::MemoryDB;
use patricia_trie::{TrieDB, TrieDBMut, TrieError, Trie, TrieMut, NodeCodec};
use std::collections::HashMap;
use std::sync::Arc;
use std::marker::PhantomData;
use heapsize::HeapSizeOf;

pub use hashdb::DBValue;

/// Backend trie storage trait.
pub trait Storage<H: Hasher>: Send + Sync {
	/// Get a trie node.
	fn get(&self, key: &H::Out) -> Result<Option<DBValue>, String>;
}

/// Try convert into trie-based backend.
pub trait TryIntoTrieBackend<H: Hasher, C: NodeCodec<H>> {
	/// Try to convert self into trie backend.
	fn try_into_trie_backend(self) -> Option<TrieBackend<H, C>>;
}

/// Patricia trie-based backend. Transaction type is an overlay of changes to commit.
#[derive(Clone)]
pub struct TrieBackend<H: Hasher, C: NodeCodec<H>> {
	storage: TrieBackendStorage<H>,
	root: H::Out,
	_codec: PhantomData<C>
}

impl<H: Hasher, C: NodeCodec<H>> TrieBackend<H, C> where H::Out: HeapSizeOf {
	/// Create new trie-based backend.
	pub fn with_storage(db: Arc<Storage<H>>, root: H::Out) -> Self {
		TrieBackend {
			storage: TrieBackendStorage::Storage(db),
			root,
			_codec: PhantomData,
		}
	}

	/// Create new trie-based backend for genesis block.
	pub fn with_storage_for_genesis(db: Arc<Storage<H>>) -> Self {
		let mut root = <H as Hasher>::Out::default();
		let mut mdb = MemoryDB::<H>::new();
		TrieDBMut::<H, C>::new(&mut mdb, &mut root);

		Self::with_storage(db, root)
	}

	/// Create new trie-based backend backed by MemoryDb storage.
	pub fn with_memorydb(db: MemoryDB<H>, root: H::Out) -> Self {
		// TODO: check that root is a part of db???
		TrieBackend {
			storage: TrieBackendStorage::MemoryDb(db),
			root,
			_codec: PhantomData,
		}
	}

	/// Get backend storage reference.
	pub fn backend_storage(&self) -> &TrieBackendStorage<H> {
		&self.storage
	}

	/// Get trie root.
	pub fn root(&self) -> &H::Out {
		&self.root
	}
}

impl super::Error for String {}

impl<H: Hasher, C: NodeCodec<H>> Backend<H, C> for TrieBackend<H, C> where H::Out: HeapSizeOf {
	type Error = String;
	type Transaction = MemoryDB<H>;

	fn storage(&self, key: &[u8]) -> Result<Option<Vec<u8>>, Self::Error> {
		let mut read_overlay = MemoryDB::new();
		let eph = Ephemeral {
			storage: &self.storage,
			overlay: &mut read_overlay,
		};

		let map_e = |e| format!("Trie lookup error: {}", e);
		TrieDB::<H, C>::new(&eph, &self.root).map_err(map_e)?
			.get(key).map(|x| x.map(|val| val.to_vec())).map_err(map_e)
	}

	fn for_keys_with_prefix<F: FnMut(&[u8])>(&self, prefix: &[u8], mut f: F) {
		let mut read_overlay = MemoryDB::new();
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

	fn pairs(&self) -> Vec<(Vec<u8>, Vec<u8>)> {
		let mut read_overlay = MemoryDB::new();
		let eph = Ephemeral {
			storage: &self.storage,
			overlay: &mut read_overlay,
		};

		let collect_all = || -> Result<_, Box<TrieError<H::Out, C::Error>>> {
			let trie = TrieDB::<H, C>::new(&eph, &self.root)?;
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

	fn storage_root<I>(&self, delta: I) -> (H::Out, MemoryDB<H>)
		where I: IntoIterator<Item=(Vec<u8>, Option<Vec<u8>>)>
	{
		let mut write_overlay = MemoryDB::new();
		let mut root = self.root;
		{
			let mut eph = Ephemeral {
				storage: &self.storage,
				overlay: &mut write_overlay,
			};

			let mut trie = TrieDBMut::<H, C>::from_existing(&mut eph, &mut root).expect("prior state root to exist"); // TODO: handle gracefully
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

		(root, write_overlay)
	}
}

impl<H: Hasher, C: NodeCodec<H>> TryIntoTrieBackend<H, C> for TrieBackend<H, C> {
	fn try_into_trie_backend(self) -> Option<TrieBackend<H, C>> {
		Some(self)
	}
}

pub struct Ephemeral<'a, H: 'a + Hasher> {
	storage: &'a TrieBackendStorage<H>,
	overlay: &'a mut MemoryDB<H>,
}

impl<'a, H: Hasher> AsHashDB<H> for Ephemeral<'a, H> where H::Out: HeapSizeOf {
	fn as_hashdb(&self) -> &HashDB<H> { self }
	fn as_hashdb_mut(&mut self) -> &mut HashDB<H> { self }
}

impl<'a, H: Hasher> Ephemeral<'a, H> {
	pub fn new(storage: &'a TrieBackendStorage<H>, overlay: &'a mut MemoryDB<H>) -> Self {
		Ephemeral {
			storage,
			overlay,
		}
	}
}

impl<'a, H: Hasher> HashDB<H> for Ephemeral<'a, H> where H::Out: HeapSizeOf {
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
			None => match self.storage.get(key) {
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

#[derive(Clone)]
pub enum TrieBackendStorage<H: Hasher> {
	/// Key value db + storage column.
	Storage(Arc<Storage<H>>),
	/// Hash db.
	MemoryDb(MemoryDB<H>),
}

impl<H: Hasher> TrieBackendStorage<H> {
	pub fn get(&self, key: &H::Out) -> Result<Option<DBValue>, String> {
		match *self {
			TrieBackendStorage::Storage(ref db) =>
				db.get(key)
					.map_err(|e| format!("Trie lookup error: {}", e)),
			TrieBackendStorage::MemoryDb(ref db) =>
				Ok(db.get(key)),
		}
	}
}

#[cfg(test)]
pub mod tests {
	use super::*;
	use std::collections::HashSet;
	use primitives::{KeccakHasher, RlpCodec, H256};

	fn test_db() -> (MemoryDB<KeccakHasher>, H256) {
		let mut root = H256::default();
		let mut mdb = MemoryDB::<KeccakHasher>::new();
		{
			let mut trie = TrieDBMut::<_, RlpCodec>::new(&mut mdb, &mut root);
			trie.insert(b"key", b"value").expect("insert failed");
			trie.insert(b"value1", &[42]).expect("insert failed");
			trie.insert(b"value2", &[24]).expect("insert failed");
			trie.insert(b":code", b"return 42").expect("insert failed");
			for i in 128u8..255u8 {
				trie.insert(&[i], &[i]).unwrap();
			}
		}
		(mdb, root)
	}

	pub(crate) fn test_trie() -> TrieBackend<KeccakHasher, RlpCodec> {
		let (mdb, root) = test_db();
		TrieBackend::with_memorydb(mdb, root)
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
		let db = TrieBackend::<KeccakHasher, RlpCodec>::with_memorydb(
			MemoryDB::new(),
			Default::default()
		);
		assert!(db.pairs().is_empty());
	}

	#[test]
	fn storage_root_is_non_default() {
		assert!(test_trie().storage_root(::std::iter::empty()).0 != H256([0; 32]));
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
