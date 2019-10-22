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

//! Proving state machine backend.

use std::sync::Arc;
use parking_lot::RwLock;
use std::{cell::RefCell, rc::Rc};
use log::debug;
use hash_db::{self, Hasher, EMPTY_PREFIX, Prefix, HashDB};
use trie::{
	MemoryDB, PrefixedMemoryDB, default_child_trie_root,
	read_trie_value_with, read_child_trie_value_with, record_all_keys
};
pub use trie::trie_types::{Layout, TrieError};
use crate::trie_backend::TrieBackend;
use crate::trie_backend_essence::{Ephemeral, TrieBackendEssence, TrieBackendStorage};
use crate::{Error, ExecutionError, Backend};
use std::collections::HashMap;
use crate::DBValue;

pub type ProofRecorder<H: Hasher> = Arc<RwLock<HashMap<H::Out, DBValue>>>;

/// Patricia trie-based backend which also tracks all touched storage trie values.
/// These can be sent to remote node and used as a proof of execution.
pub struct ProvingBackend<'a, S: 'a + TrieBackendStorage<H>, H: 'a + Hasher> {
	backend: &'a TrieBackend<S, H>,
	proof_recorder: ProofRecorder<H>,
}

pub struct ProofRecorderBackend<'a, S: 'a + TrieBackendStorage<H>, H: 'a + Hasher> {
	backend: &'a S,
	proof_recorder: ProofRecorder<H>,
}

impl<'a, S: 'a + TrieBackendStorage<H>, H: 'a + Hasher> ProvingBackend<'a, S, H> {
	/// Create new proving backend.
	pub fn new(backend: &'a TrieBackend<S, H>) -> Self {
		ProvingBackend {
			backend,
			proof_recorder: Arc::new(RwLock::new(HashMap::new())),
		}
	}

	/// Create new proving backend with the given recorder.
	pub fn new_with_recorder(
		backend: &'a TrieBackend<S, H>,
		proof_recorder: ProofRecorder<H>,
	) -> Self {
		ProvingBackend {
			backend,
			proof_recorder,
		}
	}

	/// Consume the backend, extracting the gathered proof in lexicographical order by value.
	pub fn extract_proof(&self) -> Vec<Vec<u8>> {
		// TODO mem replace hashmap and into_iter instead of clone.
		// and store as vec in the first place?.
		self.proof_recorder
			.read()
			//.borrow()
			.iter()
			.map(|(k, v)| v.to_vec())
			.collect()
	}
}

impl<'a, S: 'a + TrieBackendStorage<H>, H: 'a + Hasher> TrieBackendStorage<H> for ProofRecorderBackend<'a, S, H> {
	type Overlay = S::Overlay;

	fn get(&self, key: &H::Out, prefix: Prefix) -> Result<Option<DBValue>, String> {
		// crazy bad mutex handle : mutex should not be needed, and get is occuring a lot so even
		// if we use mutex we should use the mut handle of write TODO only for testing now

		if let Some(v) = self.proof_recorder.read().get(key) {
			// TODO Notice that proof recorder could also stored missing value and be use as a better cache.
			return Ok(Some(v.clone()));
		}
		Ok(match self.backend.get(key, prefix)? {
			Some(v) => {
				self.proof_recorder.write().insert(key.clone(), v.clone());
				Some(v)
			},
			None => None,
		})
	}
}
impl<'a, S: 'a + TrieBackendStorage<H>, H: 'a + Hasher> std::fmt::Debug for ProvingBackend<'a, S, H> {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "ProvingBackend")
	}
}

impl<'a, S, H> ProvingBackend<'a, S, H>
	where
		S: 'a + TrieBackendStorage<H>,// + Clone,
		H: 'a + Hasher,
		H::Out: Ord,
{
	
	fn backend(&self) -> TrieBackend<ProofRecorderBackend<S, H>, H> {
		let essence = self.backend.essence();
		let root = essence.root().clone();
//		// TODO bad code: TODO specialize for explicit type (one that
//		// is an Arc some backend).
		let recorder = ProofRecorderBackend {
			backend: essence.backend_storage(),
			proof_recorder: self.proof_recorder.clone(),
		};
		TrieBackend::new(recorder, root)
	}
}

impl<'a, S, H> Backend<H> for ProvingBackend<'a, S, H>
	where
		S: 'a + TrieBackendStorage<H>,
		H: 'a + Hasher,
		H::Out: Ord,
{
	type Error = String;
	type Transaction = S::Overlay;
	type TrieBackendStorage = PrefixedMemoryDB<H>;

	fn storage(&self, key: &[u8]) -> Result<Option<Vec<u8>>, Self::Error> {
		self.backend().storage(key)
	}

	fn child_storage(&self, storage_key: &[u8], key: &[u8]) -> Result<Option<Vec<u8>>, Self::Error> {
		self.backend().child_storage(storage_key, key)
	}

	fn for_keys_in_child_storage<F: FnMut(&[u8])>(&self, storage_key: &[u8], f: F) {
		self.backend().for_keys_in_child_storage(storage_key, f)
	}

	fn for_keys_with_prefix<F: FnMut(&[u8])>(&self, prefix: &[u8], f: F) {
		self.backend().for_keys_with_prefix(prefix, f)
	}

	fn for_key_values_with_prefix<F: FnMut(&[u8], &[u8])>(&self, prefix: &[u8], f: F) {
		self.backend().for_key_values_with_prefix(prefix, f)
	}

	fn for_child_keys_with_prefix<F: FnMut(&[u8])>(&self, storage_key: &[u8], prefix: &[u8], f: F) {
		self.backend().for_child_keys_with_prefix(storage_key, prefix, f)
	}

	fn pairs(&self) -> Vec<(Vec<u8>, Vec<u8>)> {
		self.backend().pairs()
	}

	fn keys(&self, prefix: &[u8]) -> Vec<Vec<u8>> {
		self.backend().keys(prefix)
	}

	fn child_keys(&self, child_storage_key: &[u8], prefix: &[u8]) -> Vec<Vec<u8>> {
		self.backend().child_keys(child_storage_key, prefix)
	}

	fn storage_root<I>(&self, delta: I) -> (H::Out, Self::Transaction)
		where I: IntoIterator<Item=(Vec<u8>, Option<Vec<u8>>)>
	{
		self.backend().storage_root(delta)
	}

	fn child_storage_root<I>(&self, storage_key: &[u8], delta: I) -> (Vec<u8>, bool, Self::Transaction)
	where
		I: IntoIterator<Item=(Vec<u8>, Option<Vec<u8>>)>,
		H::Out: Ord
	{
		self.backend().child_storage_root(storage_key, delta)
	}
}

#[cfg(test)]
mod tests {
	use crate::backend::{InMemory};
	use crate::trie_backend::tests::test_trie;
	use super::*;
	use primitives::{Blake2Hasher, storage::ChildStorageKey};
	use crate::proving_backend::create_proof_check_backend;

	fn test_proving<'a>(
		trie_backend: &'a TrieBackend<PrefixedMemoryDB<Blake2Hasher>,Blake2Hasher>,
	) -> ProvingBackend<'a, PrefixedMemoryDB<Blake2Hasher>, Blake2Hasher> {
		ProvingBackend::new(trie_backend)
	}

	#[test]
	fn proof_is_empty_until_value_is_read() {
		let trie_backend = test_trie();
		assert!(test_proving(&trie_backend).extract_proof().is_empty());
	}

	#[test]
	fn proof_is_non_empty_after_value_is_read() {
		let trie_backend = test_trie();
		let backend = test_proving(&trie_backend);
		assert_eq!(backend.storage(b"key").unwrap(), Some(b"value".to_vec()));
		assert!(!backend.extract_proof().is_empty());
	}

	#[test]
	fn proof_is_invalid_when_does_not_contains_root() {
		use primitives::H256;
		assert!(create_proof_check_backend::<Blake2Hasher>(H256::from_low_u64_be(1), vec![]).is_err());
	}

	#[test]
	fn passes_throgh_backend_calls() {
		let trie_backend = test_trie();
		let proving_backend = test_proving(&trie_backend);
		assert_eq!(trie_backend.storage(b"key").unwrap(), proving_backend.storage(b"key").unwrap());
		assert_eq!(trie_backend.pairs(), proving_backend.pairs());

		let (trie_root, mut trie_mdb) = trie_backend.storage_root(::std::iter::empty());
		let (proving_root, mut proving_mdb) = proving_backend.storage_root(::std::iter::empty());
		assert_eq!(trie_root, proving_root);
		assert_eq!(trie_mdb.drain(), proving_mdb.drain());
	}

	#[test]
	fn proof_recorded_and_checked() {
		let contents = (0..64).map(|i| (None, vec![i], Some(vec![i]))).collect::<Vec<_>>();
		let in_memory = InMemory::<Blake2Hasher>::default();
		let mut in_memory = in_memory.update(contents);
		let in_memory_root = in_memory.storage_root(::std::iter::empty()).0;
		(0..64).for_each(|i| assert_eq!(in_memory.storage(&[i]).unwrap().unwrap(), vec![i]));

		let trie = in_memory.as_trie_backend().unwrap();
		let trie_root = trie.storage_root(::std::iter::empty()).0;
		assert_eq!(in_memory_root, trie_root);
		(0..64).for_each(|i| assert_eq!(trie.storage(&[i]).unwrap().unwrap(), vec![i]));

		let proving = ProvingBackend::new(trie);
		assert_eq!(proving.storage(&[42]).unwrap().unwrap(), vec![42]);

		let proof = proving.extract_proof();

		let proof_check = create_proof_check_backend::<Blake2Hasher>(in_memory_root.into(), proof).unwrap();
		assert_eq!(proof_check.storage(&[42]).unwrap().unwrap(), vec![42]);
	}

	#[test]
	fn proof_recorded_and_checked_with_child() {
		let subtrie1 = ChildStorageKey::from_slice(b":child_storage:default:sub1").unwrap();
		let subtrie2 = ChildStorageKey::from_slice(b":child_storage:default:sub2").unwrap();
		let own1 = subtrie1.into_owned();
		let own2 = subtrie2.into_owned();
		let contents = (0..64).map(|i| (None, vec![i], Some(vec![i])))
			.chain((28..65).map(|i| (Some(own1.clone()), vec![i], Some(vec![i]))))
			.chain((10..15).map(|i| (Some(own2.clone()), vec![i], Some(vec![i]))))
			.collect::<Vec<_>>();
		let in_memory = InMemory::<Blake2Hasher>::default();
		let mut in_memory = in_memory.update(contents);
		let in_memory_root = in_memory.full_storage_root::<_, Vec<_>, _>(
			::std::iter::empty(),
			in_memory.child_storage_keys().map(|k|(k.to_vec(), Vec::new()))
		).0;
		(0..64).for_each(|i| assert_eq!(
			in_memory.storage(&[i]).unwrap().unwrap(),
			vec![i]
		));
		(28..65).for_each(|i| assert_eq!(
			in_memory.child_storage(&own1[..], &[i]).unwrap().unwrap(),
			vec![i]
		));
		(10..15).for_each(|i| assert_eq!(
			in_memory.child_storage(&own2[..], &[i]).unwrap().unwrap(),
			vec![i]
		));

		let trie = in_memory.as_trie_backend().unwrap();
		let trie_root = trie.storage_root(::std::iter::empty()).0;
		assert_eq!(in_memory_root, trie_root);
		(0..64).for_each(|i| assert_eq!(
			trie.storage(&[i]).unwrap().unwrap(),
			vec![i]
		));

		let proving = ProvingBackend::new(trie);
		assert_eq!(proving.storage(&[42]).unwrap().unwrap(), vec![42]);

		let proof = proving.extract_proof();

		let proof_check = create_proof_check_backend::<Blake2Hasher>(
			in_memory_root.into(),
			proof
		).unwrap();
		assert!(proof_check.storage(&[0]).is_err());
		assert_eq!(proof_check.storage(&[42]).unwrap().unwrap(), vec![42]);
		// note that it is include in root because proof close
		assert_eq!(proof_check.storage(&[41]).unwrap().unwrap(), vec![41]);
		assert_eq!(proof_check.storage(&[64]).unwrap(), None);

		let proving = ProvingBackend::new(trie);
		assert_eq!(proving.child_storage(&own1[..], &[64]), Ok(Some(vec![64])));

		let proof = proving.extract_proof();
		let proof_check = create_proof_check_backend::<Blake2Hasher>(
			in_memory_root.into(),
			proof
		).unwrap();
		assert_eq!(
			proof_check.child_storage(&own1[..], &[64]).unwrap().unwrap(),
			vec![64]
		);
	}

}
