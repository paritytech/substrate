// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Proving state machine backend.

use crate::{
	trie_backend::TrieBackend, trie_backend_essence::TrieBackendStorage, Backend, DBValue, Error,
	ExecutionError, TrieBackendBuilder,
};
use codec::{Codec, Encode};
use hash_db::{HashDB, Hasher, Prefix, EMPTY_PREFIX};
use parking_lot::RwLock;
use sp_core::storage::{ChildInfo, StateVersion};
pub use sp_trie::trie_types::TrieError;
use sp_trie::{MemoryDB, StorageProof};
use std::{
	collections::{hash_map::Entry, HashMap},
	sync::Arc,
};

#[derive(Default)]
struct ProofRecorderInner<Hash> {
	/// All the records that we have stored so far.
	records: HashMap<Hash, Option<DBValue>>,
	/// The encoded size of all recorded values.
	encoded_size: usize,
}

/// Global proof recorder, act as a layer over a hash db for recording queried data.
#[derive(Clone, Default)]
pub struct ProofRecorder<Hash> {
	inner: Arc<RwLock<ProofRecorderInner<Hash>>>,
}

impl<Hash: std::hash::Hash + Eq> ProofRecorder<Hash> {
	/// Record the given `key` => `val` combination.
	pub fn record(&self, key: Hash, val: Option<DBValue>) {
		let mut inner = self.inner.write();
		let encoded_size = if let Entry::Vacant(entry) = inner.records.entry(key) {
			let encoded_size = val.as_ref().map(Encode::encoded_size).unwrap_or(0);

			entry.insert(val);
			encoded_size
		} else {
			0
		};

		inner.encoded_size += encoded_size;
	}

	/// Returns the value at the given `key`.
	pub fn get(&self, key: &Hash) -> Option<Option<DBValue>> {
		self.inner.read().records.get(key).cloned()
	}

	/// Returns the estimated encoded size of the proof.
	///
	/// The estimation is maybe bigger (by in maximum 4 bytes), but never smaller than the actual
	/// encoded proof.
	pub fn estimate_encoded_size(&self) -> usize {
		let inner = self.inner.read();
		inner.encoded_size + codec::Compact(inner.records.len() as u32).encoded_size()
	}

	/// Convert into a [`StorageProof`].
	pub fn to_storage_proof(&self) -> StorageProof {
		StorageProof::new(
			self.inner
				.read()
				.records
				.iter()
				.filter_map(|(_k, v)| v.as_ref().map(|v| v.to_vec())),
		)
	}

	/// Reset the internal state.
	pub fn reset(&self) {
		let mut inner = self.inner.write();
		inner.records.clear();
		inner.encoded_size = 0;
	}
}

/// Patricia trie-based backend which also tracks all touched storage trie values.
/// These can be sent to remote node and used as a proof of execution.
pub struct ProvingBackend<'a, S: 'a + TrieBackendStorage<H>, H: 'a + Hasher>(
	TrieBackend<ProofRecorderBackend<'a, S, H>, H>,
);

/// Trie backend storage with its proof recorder.
pub struct ProofRecorderBackend<'a, S: 'a + TrieBackendStorage<H>, H: 'a + Hasher> {
	backend: &'a S,
	proof_recorder: ProofRecorder<H::Out>,
}

impl<'a, S: 'a + TrieBackendStorage<H>, H: 'a + Hasher> ProvingBackend<'a, S, H>
where
	H::Out: Codec,
{
	/// Create new proving backend.
	pub fn new(backend: &'a TrieBackend<S, H>) -> Self {
		let proof_recorder = Default::default();
		Self::new_with_recorder(backend, proof_recorder)
	}

	/// Create new proving backend with the given recorder.
	pub fn new_with_recorder(
		backend: &'a TrieBackend<S, H>,
		proof_recorder: ProofRecorder<H::Out>,
	) -> Self {
		let essence = backend.essence();
		let root = essence.root().clone();
		let recorder = ProofRecorderBackend { backend: essence.backend_storage(), proof_recorder };
		ProvingBackend(TrieBackendBuilder::new(recorder, root).build())
	}

	/// Extracting the gathered unordered proof.
	pub fn extract_proof(&self) -> StorageProof {
		self.0.essence().backend_storage().proof_recorder.to_storage_proof()
	}

	/// Returns the estimated encoded size of the proof.
	///
	/// The estimation is maybe bigger (by in maximum 4 bytes), but never smaller than the actual
	/// encoded proof.
	pub fn estimate_encoded_size(&self) -> usize {
		self.0.essence().backend_storage().proof_recorder.estimate_encoded_size()
	}

	/// Clear the proof recorded data.
	pub fn clear_recorder(&self) {
		self.0.essence().backend_storage().proof_recorder.reset()
	}
}

impl<'a, S: 'a + TrieBackendStorage<H>, H: 'a + Hasher> TrieBackendStorage<H>
	for ProofRecorderBackend<'a, S, H>
{
	type Overlay = S::Overlay;

	fn get(&self, key: &H::Out, prefix: Prefix) -> Result<Option<DBValue>, String> {
		if let Some(v) = self.proof_recorder.get(key) {
			return Ok(v)
		}

		let backend_value = self.backend.get(key, prefix)?;
		self.proof_recorder.record(key.clone(), backend_value.clone());
		Ok(backend_value)
	}
}

impl<'a, S: 'a + TrieBackendStorage<H>, H: 'a + Hasher> std::fmt::Debug
	for ProvingBackend<'a, S, H>
{
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "ProvingBackend")
	}
}

impl<'a, S, H> Backend<H> for ProvingBackend<'a, S, H>
where
	S: 'a + TrieBackendStorage<H>,
	H: 'a + Hasher,
	H::Out: Ord + Codec,
{
	type Error = String;
	type Transaction = S::Overlay;
	type TrieBackendStorage = S;

	fn storage(&self, key: &[u8]) -> Result<Option<Vec<u8>>, Self::Error> {
		self.0.storage(key)
	}

	fn child_storage(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Result<Option<Vec<u8>>, Self::Error> {
		self.0.child_storage(child_info, key)
	}

	fn apply_to_key_values_while<F: FnMut(Vec<u8>, Vec<u8>) -> bool>(
		&self,
		child_info: Option<&ChildInfo>,
		prefix: Option<&[u8]>,
		start_at: Option<&[u8]>,
		f: F,
		allow_missing: bool,
	) -> Result<bool, Self::Error> {
		self.0.apply_to_key_values_while(child_info, prefix, start_at, f, allow_missing)
	}

	fn apply_to_keys_while<F: FnMut(&[u8]) -> bool>(
		&self,
		child_info: Option<&ChildInfo>,
		prefix: Option<&[u8]>,
		f: F,
	) {
		self.0.apply_to_keys_while(child_info, prefix, f)
	}

	fn next_storage_key(&self, key: &[u8]) -> Result<Option<Vec<u8>>, Self::Error> {
		self.0.next_storage_key(key)
	}

	fn next_child_storage_key(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Result<Option<Vec<u8>>, Self::Error> {
		self.0.next_child_storage_key(child_info, key)
	}

	fn for_keys_with_prefix<F: FnMut(&[u8])>(&self, prefix: &[u8], f: F) {
		self.0.for_keys_with_prefix(prefix, f)
	}

	fn for_key_values_with_prefix<F: FnMut(&[u8], &[u8])>(&self, prefix: &[u8], f: F) {
		self.0.for_key_values_with_prefix(prefix, f)
	}

	fn for_child_keys_with_prefix<F: FnMut(&[u8])>(
		&self,
		child_info: &ChildInfo,
		prefix: &[u8],
		f: F,
	) {
		self.0.for_child_keys_with_prefix(child_info, prefix, f)
	}

	fn pairs(&self) -> Vec<(Vec<u8>, Vec<u8>)> {
		self.0.pairs()
	}

	fn keys(&self, prefix: &[u8]) -> Vec<Vec<u8>> {
		self.0.keys(prefix)
	}

	fn child_keys(&self, child_info: &ChildInfo, prefix: &[u8]) -> Vec<Vec<u8>> {
		self.0.child_keys(child_info, prefix)
	}

	fn storage_root<'b>(
		&self,
		delta: impl Iterator<Item = (&'b [u8], Option<&'b [u8]>)>,
		state_version: StateVersion,
	) -> (H::Out, Self::Transaction)
	where
		H::Out: Ord,
	{
		self.0.storage_root(delta, state_version)
	}

	fn child_storage_root<'b>(
		&self,
		child_info: &ChildInfo,
		delta: impl Iterator<Item = (&'b [u8], Option<&'b [u8]>)>,
		state_version: StateVersion,
	) -> (H::Out, bool, Self::Transaction)
	where
		H::Out: Ord,
	{
		self.0.child_storage_root(child_info, delta, state_version)
	}

	fn register_overlay_stats(&self, _stats: &crate::stats::StateMachineStats) {}

	fn usage_info(&self) -> crate::stats::UsageInfo {
		self.0.usage_info()
	}
}

/// Create a backend used for checking the proof., using `H` as hasher.
///
/// `proof` and `root` must match, i.e. `root` must be the correct root of `proof` nodes.
pub fn create_proof_check_backend<H>(
	root: H::Out,
	proof: StorageProof,
) -> Result<TrieBackend<MemoryDB<H>, H>, Box<dyn Error>>
where
	H: Hasher,
	H::Out: Codec,
{
	let db = proof.into_memory_db();

	if db.contains(&root, EMPTY_PREFIX) {
		Ok(TrieBackendBuilder::new(db, root).build())
	} else {
		Err(Box::new(ExecutionError::InvalidProof))
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::{
		proving_backend::create_proof_check_backend, trie_backend::tests::test_trie,
		InMemoryBackend,
	};
	use sp_core::H256;
	use sp_runtime::traits::BlakeTwo256;
	use sp_trie::PrefixedMemoryDB;

	fn test_proving<'a>(
		trie_backend: &'a TrieBackend<PrefixedMemoryDB<BlakeTwo256>, BlakeTwo256>,
	) -> ProvingBackend<'a, PrefixedMemoryDB<BlakeTwo256>, BlakeTwo256> {
		ProvingBackend::new(trie_backend)
	}

	#[test]
	fn proof_is_empty_until_value_is_read() {
		proof_is_empty_until_value_is_read_inner(StateVersion::V0);
		proof_is_empty_until_value_is_read_inner(StateVersion::V1);
	}
	fn proof_is_empty_until_value_is_read_inner(test_hash: StateVersion) {
		let trie_backend = test_trie(test_hash, None, None);
		assert!(test_proving(&trie_backend).extract_proof().is_empty());
	}

	#[test]
	fn proof_is_non_empty_after_value_is_read() {
		proof_is_non_empty_after_value_is_read_inner(StateVersion::V0);
		proof_is_non_empty_after_value_is_read_inner(StateVersion::V1);
	}
	fn proof_is_non_empty_after_value_is_read_inner(test_hash: StateVersion) {
		let trie_backend = test_trie(test_hash, None, None);
		let backend = test_proving(&trie_backend);
		assert_eq!(backend.storage(b"key").unwrap(), Some(b"value".to_vec()));
		assert!(!backend.extract_proof().is_empty());
	}

	#[test]
	fn proof_is_invalid_when_does_not_contains_root() {
		let result = create_proof_check_backend::<BlakeTwo256>(
			H256::from_low_u64_be(1),
			StorageProof::empty(),
		);
		assert!(result.is_err());
	}

	#[test]
	fn passes_through_backend_calls() {
		passes_through_backend_calls_inner(StateVersion::V0);
		passes_through_backend_calls_inner(StateVersion::V1);
	}
	fn passes_through_backend_calls_inner(state_version: StateVersion) {
		let trie_backend = test_trie(state_version, None, None);
		let proving_backend = test_proving(&trie_backend);
		assert_eq!(trie_backend.storage(b"key").unwrap(), proving_backend.storage(b"key").unwrap());
		assert_eq!(trie_backend.pairs(), proving_backend.pairs());

		let (trie_root, mut trie_mdb) =
			trie_backend.storage_root(std::iter::empty(), state_version);
		let (proving_root, mut proving_mdb) =
			proving_backend.storage_root(std::iter::empty(), state_version);
		assert_eq!(trie_root, proving_root);
		assert_eq!(trie_mdb.drain(), proving_mdb.drain());
	}

	#[test]
	fn proof_recorded_and_checked_top() {
		proof_recorded_and_checked_inner(StateVersion::V0);
		proof_recorded_and_checked_inner(StateVersion::V1);
	}
	fn proof_recorded_and_checked_inner(state_version: StateVersion) {
		let size_content = 34; // above hashable value threshold.
		let value_range = 0..64;
		let contents = value_range
			.clone()
			.map(|i| (vec![i], Some(vec![i; size_content])))
			.collect::<Vec<_>>();
		let in_memory = InMemoryBackend::<BlakeTwo256>::default();
		let in_memory = in_memory.update(vec![(None, contents)], state_version);
		let in_memory_root = in_memory.storage_root(std::iter::empty(), state_version).0;
		value_range.clone().for_each(|i| {
			assert_eq!(in_memory.storage(&[i]).unwrap().unwrap(), vec![i; size_content])
		});

		let trie = in_memory.as_trie_backend().unwrap();
		let trie_root = trie.storage_root(std::iter::empty(), state_version).0;
		assert_eq!(in_memory_root, trie_root);
		value_range
			.clone()
			.for_each(|i| assert_eq!(trie.storage(&[i]).unwrap().unwrap(), vec![i; size_content]));

		let proving = ProvingBackend::new(trie);
		assert_eq!(proving.storage(&[42]).unwrap().unwrap(), vec![42; size_content]);

		let proof = proving.extract_proof();

		let proof_check =
			create_proof_check_backend::<BlakeTwo256>(in_memory_root.into(), proof).unwrap();
		assert_eq!(proof_check.storage(&[42]).unwrap().unwrap(), vec![42; size_content]);
	}

	#[test]
	fn proof_record_works_with_iter() {
		let contents = (0..64).map(|i| (vec![i], Some(vec![i]))).collect::<Vec<_>>();
		let in_memory = InMemoryBackend::<BlakeTwo256>::default();
		let in_memory = in_memory.update(vec![(None, contents)], StateVersion::V1);
		let in_memory_root = in_memory.storage_root(std::iter::empty(), StateVersion::V1).0;
		(0..64).for_each(|i| assert_eq!(in_memory.storage(&[i]).unwrap().unwrap(), vec![i]));

		let trie = in_memory.as_trie_backend().unwrap();
		let trie_root = trie.storage_root(std::iter::empty(), StateVersion::V1).0;
		assert_eq!(in_memory_root, trie_root);
		(0..64).for_each(|i| assert_eq!(trie.storage(&[i]).unwrap().unwrap(), vec![i]));

		let proving = ProvingBackend::new(trie);
		(0..63)
			.for_each(|i| assert_eq!(proving.next_storage_key(&[i]).unwrap(), Some(vec![i + 1])));

		let proof = proving.extract_proof();

		let proof_check =
			create_proof_check_backend::<BlakeTwo256>(in_memory_root.into(), proof).unwrap();
		(0..63).for_each(|i| {
			assert_eq!(proof_check.next_storage_key(&[i]).unwrap(), Some(vec![i + 1]))
		});
	}

	#[test]
	fn proof_recorded_and_checked_with_child() {
		proof_recorded_and_checked_with_child_inner(StateVersion::V0);
		proof_recorded_and_checked_with_child_inner(StateVersion::V1);
	}
	fn proof_recorded_and_checked_with_child_inner(state_version: StateVersion) {
		let child_info_1 = ChildInfo::new_default(b"sub1");
		let child_info_2 = ChildInfo::new_default(b"sub2");
		let child_info_1 = &child_info_1;
		let child_info_2 = &child_info_2;
		let contents = vec![
			(None, (0..64).map(|i| (vec![i], Some(vec![i]))).collect::<Vec<_>>()),
			(Some(child_info_1.clone()), (28..65).map(|i| (vec![i], Some(vec![i]))).collect()),
			(Some(child_info_2.clone()), (10..15).map(|i| (vec![i], Some(vec![i]))).collect()),
		];
		let in_memory = InMemoryBackend::<BlakeTwo256>::default();
		let in_memory = in_memory.update(contents, state_version);
		let child_storage_keys = vec![child_info_1.to_owned(), child_info_2.to_owned()];
		let in_memory_root = in_memory
			.full_storage_root(
				std::iter::empty(),
				child_storage_keys.iter().map(|k| (k, std::iter::empty())),
				state_version,
			)
			.0;
		(0..64).for_each(|i| assert_eq!(in_memory.storage(&[i]).unwrap().unwrap(), vec![i]));
		(28..65).for_each(|i| {
			assert_eq!(in_memory.child_storage(child_info_1, &[i]).unwrap().unwrap(), vec![i])
		});
		(10..15).for_each(|i| {
			assert_eq!(in_memory.child_storage(child_info_2, &[i]).unwrap().unwrap(), vec![i])
		});

		let trie = in_memory.as_trie_backend().unwrap();
		let trie_root = trie.storage_root(std::iter::empty(), state_version).0;
		assert_eq!(in_memory_root, trie_root);
		(0..64).for_each(|i| assert_eq!(trie.storage(&[i]).unwrap().unwrap(), vec![i]));

		let proving = ProvingBackend::new(trie);
		assert_eq!(proving.storage(&[42]).unwrap().unwrap(), vec![42]);

		let proof = proving.extract_proof();

		let proof_check =
			create_proof_check_backend::<BlakeTwo256>(in_memory_root.into(), proof).unwrap();
		assert!(proof_check.storage(&[0]).is_err());
		assert_eq!(proof_check.storage(&[42]).unwrap().unwrap(), vec![42]);
		// note that it is include in root because proof close
		assert_eq!(proof_check.storage(&[41]).unwrap().unwrap(), vec![41]);
		assert_eq!(proof_check.storage(&[64]).unwrap(), None);

		let proving = ProvingBackend::new(trie);
		assert_eq!(proving.child_storage(child_info_1, &[64]), Ok(Some(vec![64])));

		let proof = proving.extract_proof();
		let proof_check =
			create_proof_check_backend::<BlakeTwo256>(in_memory_root.into(), proof).unwrap();
		assert_eq!(proof_check.child_storage(child_info_1, &[64]).unwrap().unwrap(), vec![64]);
	}

	#[test]
	fn storage_proof_encoded_size_estimation_works() {
		storage_proof_encoded_size_estimation_works_inner(StateVersion::V0);
		storage_proof_encoded_size_estimation_works_inner(StateVersion::V1);
	}
	fn storage_proof_encoded_size_estimation_works_inner(state_version: StateVersion) {
		let trie_backend = test_trie(state_version, None, None);
		let backend = test_proving(&trie_backend);

		let check_estimation =
			|backend: &ProvingBackend<'_, PrefixedMemoryDB<BlakeTwo256>, BlakeTwo256>| {
				let storage_proof = backend.extract_proof();
				let estimation =
					backend.0.essence().backend_storage().proof_recorder.estimate_encoded_size();

				assert_eq!(storage_proof.encoded_size(), estimation);
			};

		assert_eq!(backend.storage(b"key").unwrap(), Some(b"value".to_vec()));
		check_estimation(&backend);

		assert_eq!(backend.storage(b"value1").unwrap(), Some(vec![42]));
		check_estimation(&backend);

		assert_eq!(backend.storage(b"value2").unwrap(), Some(vec![24]));
		check_estimation(&backend);

		assert!(backend.storage(b"doesnotexist").unwrap().is_none());
		check_estimation(&backend);

		assert!(backend.storage(b"doesnotexist2").unwrap().is_none());
		check_estimation(&backend);
	}

	#[test]
	fn proof_recorded_for_same_execution_should_be_deterministic() {
		let storage_changes = vec![
			(H256::random(), Some(b"value1".to_vec())),
			(H256::random(), Some(b"value2".to_vec())),
			(H256::random(), Some(b"value3".to_vec())),
			(H256::random(), Some(b"value4".to_vec())),
			(H256::random(), Some(b"value5".to_vec())),
			(H256::random(), Some(b"value6".to_vec())),
			(H256::random(), Some(b"value7".to_vec())),
			(H256::random(), Some(b"value8".to_vec())),
		];

		let proof_recorder =
			ProofRecorder::<H256> { inner: Arc::new(RwLock::new(ProofRecorderInner::default())) };
		storage_changes
			.clone()
			.into_iter()
			.for_each(|(key, val)| proof_recorder.record(key, val));
		let proof1 = proof_recorder.to_storage_proof();

		let proof_recorder =
			ProofRecorder::<H256> { inner: Arc::new(RwLock::new(ProofRecorderInner::default())) };
		storage_changes
			.into_iter()
			.for_each(|(key, val)| proof_recorder.record(key, val));
		let proof2 = proof_recorder.to_storage_proof();

		assert_eq!(proof1, proof2);
	}
}
