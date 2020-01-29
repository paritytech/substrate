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

//! Logic for checking Substrate storage proofs.

use hash_db::{Hasher, HashDB, EMPTY_PREFIX};
use sp_trie::{MemoryDB, Trie, trie_types::TrieDB};
use sp_runtime::RuntimeDebug;

pub(crate) type StorageProof = Vec<Vec<u8>>;

/// This struct is used to read storage values from a subset of a Merklized database. The "proof"
/// is a subset of the nodes in the Merkle structure of the database, so that it provides
/// authentication against a known Merkle root as well as the values in the database themselves.
pub struct StorageProofChecker<H>
	where H: Hasher
{
	root: H::Out,
	db: MemoryDB<H>,
}

impl<H> StorageProofChecker<H>
	where H: Hasher
{
	/// Constructs a new storage proof checker.
	///
	/// This returns an error if the given proof is invalid with respect to the given root.
	pub fn new(root: H::Out, proof: StorageProof) -> Result<Self, Error> {
		let mut db = MemoryDB::default();
		for item in proof {
			db.insert(EMPTY_PREFIX, &item);
		}
		let checker = StorageProofChecker {
			root,
			db,
		};
		// Return error if trie would be invalid.
		let _ = checker.trie()?;
		Ok(checker)
	}

	/// Reads a value from the available subset of storage. If the value cannot be read due to an
	/// incomplete or otherwise invalid proof, this returns an error.
	pub fn read_value(&self, key: &[u8]) -> Result<Option<Vec<u8>>, Error> {
		self.trie()?
			.get(key)
			.map(|value| value.map(|value| value.to_vec()))
			.map_err(|_| Error::StorageValueUnavailable)
	}

	fn trie(&self) -> Result<TrieDB<H>, Error> {
		TrieDB::new(&self.db, &self.root)
			.map_err(|_| Error::StorageRootMismatch)
	}
}

#[derive(RuntimeDebug, PartialEq)]
pub enum Error {
	StorageRootMismatch,
	StorageValueUnavailable,
}

#[cfg(test)]
mod tests {
	use super::*;

	use sp_core::{Blake2Hasher, H256};
	use sp_state_machine::{prove_read, backend::Backend, InMemoryBackend};

	#[test]
	fn storage_proof_check() {
		// construct storage proof
		let backend = <InMemoryBackend<Blake2Hasher>>::from(vec![
			(None, vec![(b"key1".to_vec(), Some(b"value1".to_vec()))]),
			(None, vec![(b"key2".to_vec(), Some(b"value2".to_vec()))]),
			(None, vec![(b"key3".to_vec(), Some(b"value3".to_vec()))]),
			// Value is too big to fit in a branch node
			(None, vec![(b"key11".to_vec(), Some(vec![0u8; 32]))]),
		]);
		let root = backend.storage_root(std::iter::empty()).0;
		let proof: StorageProof = prove_read(backend, &[&b"key1"[..], &b"key2"[..], &b"key22"[..]])
			.unwrap()
			.iter_nodes()
			.collect();

		// check proof in runtime
		let checker = <StorageProofChecker<Blake2Hasher>>::new(root, proof.clone()).unwrap();
		assert_eq!(checker.read_value(b"key1"), Ok(Some(b"value1".to_vec())));
		assert_eq!(checker.read_value(b"key2"), Ok(Some(b"value2".to_vec())));
		assert_eq!(checker.read_value(b"key11111"), Err(Error::StorageValueUnavailable));
		assert_eq!(checker.read_value(b"key22"), Ok(None));

		// checking proof against invalid commitment fails
		assert_eq!(
			<StorageProofChecker<Blake2Hasher>>::new(H256::random(), proof).err(),
			Some(Error::StorageRootMismatch)
		);
	}
}
