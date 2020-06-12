// This file is part of Substrate.

// Copyright (C) 2017-2020 Parity Technologies (UK) Ltd.
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

use parking_lot::RwLock;
use codec::{Decode, Codec};
use log::debug;
use hash_db::{Hasher, HashDB, EMPTY_PREFIX, Prefix};
use sp_trie::{
	empty_child_trie_root, read_trie_value_with, read_child_trie_value_with, RecordBackendFor,
	ProofInput, RecordBackend, RecordableProof, BackendProof,
	record_all_keys, ProofInputKind, FullBackendProof,
};
pub use sp_trie::{Recorder, ChildrenProofMap, trie_types::{Layout, TrieError}};
use crate::trie_backend::TrieBackend;
use crate::trie_backend_essence::{Ephemeral, TrieBackendEssence, TrieBackendStorage};
use crate::{Error, ExecutionError, DBValue};
use crate::backend::{Backend, RegProofBackend, ProofRawFor};
use sp_core::storage::{ChildInfo, ChildInfoProof};
use std::marker::PhantomData;

/// Patricia trie-based backend specialized in get value proofs.
pub struct ProvingBackendRecorder<'a, S: 'a + TrieBackendStorage<H>, H: 'a + Hasher> {
	pub(crate) backend: &'a TrieBackendEssence<S, H>,
	pub(crate) proof_recorder: &'a mut Recorder<H::Out>,
}

impl<'a, S, H> ProvingBackendRecorder<'a, S, H>
	where
		S: TrieBackendStorage<H>,
		H: Hasher,
		H::Out: Codec,
{
	/// Produce proof for a key query.
	pub fn storage(&mut self, key: &[u8]) -> Result<Option<Vec<u8>>, String> {
		let mut read_overlay = S::Overlay::default();
		let eph = Ephemeral::new(
			self.backend.backend_storage(),
			&mut read_overlay,
			None,
		);

		let map_e = |e| format!("Trie lookup error: {}", e);

		read_trie_value_with::<Layout<H>, _, Ephemeral<S, H>>(
			&eph,
			self.backend.root(),
			key,
			&mut *self.proof_recorder,
		).map_err(map_e)
	}

	/// Produce proof for a child key query.
	pub fn child_storage(
		&mut self,
		child_info: &ChildInfo,
		key: &[u8]
	) -> Result<Option<Vec<u8>>, String> {
		let storage_key = child_info.storage_key();
		let root = self.storage(storage_key)?
			.and_then(|r| Decode::decode(&mut &r[..]).ok())
			.unwrap_or(empty_child_trie_root::<Layout<H>>());

		let mut read_overlay = S::Overlay::default();
		let eph = Ephemeral::new(
			self.backend.backend_storage(),
			&mut read_overlay,
			Some(child_info),
		);

		let map_e = |e| format!("Trie lookup error: {}", e);

		read_child_trie_value_with::<Layout<H>, _, _>(
			child_info.keyspace(),
			&eph,
			&root.as_ref(),
			key,
			&mut *self.proof_recorder
		).map_err(map_e)
	}

	/// Produce proof for the whole backend.
	pub fn record_all_keys(&mut self) {
		let mut read_overlay = S::Overlay::default();
		let eph = Ephemeral::new(
			self.backend.backend_storage(),
			&mut read_overlay,
			None,
		);

		let mut iter = move || -> Result<(), Box<TrieError<H::Out>>> {
			let root = self.backend.root();
			record_all_keys::<Layout<H>, _>(&eph, root, &mut *self.proof_recorder)
		};

		if let Err(e) = iter() {
			debug!(target: "trie", "Error while recording all keys: {}", e);
		}
	}
}

/// Patricia trie-based backend which also tracks all touched storage trie values.
/// These can be sent to remote node and used as a proof of execution.
pub struct ProvingBackend<
	S: TrieBackendStorage<H>,
	H: Hasher,
	P: BackendProof<H>,
> {
	pub(crate) trie_backend: TrieBackend<ProofRecorderBackend<S, H, RecordBackendFor<P, H>>, H, P>,
	_ph: PhantomData<P>,
}

/// Trie backend storage with its proof recorder.
pub struct ProofRecorderBackend<S: TrieBackendStorage<H>, H: Hasher, R: RecordBackend<H>> {
	backend: S,
	proof_recorder: RwLock<R>,
	_ph: PhantomData<H>,
}

impl<'a, S, H, P> ProvingBackend<&'a S, H, P>
	where
		S: TrieBackendStorage<H>,
		H: Hasher,
		H::Out: Codec,
		P: BackendProof<H>,
{
	/// Create new proving backend.
	pub fn new(backend: &'a TrieBackend<S, H, P>) -> Self {
		let proof_recorder = Default::default();
		Self::new_with_recorder(backend, proof_recorder)
	}

	fn new_with_recorder(
		backend: &'a TrieBackend<S, H, P>,
		proof_recorder: RecordBackendFor<P, H>,
	) -> Self {
		let essence = backend.essence();
		let root = essence.root().clone();
		let recorder = ProofRecorderBackend {
			backend: essence.backend_storage(),
			proof_recorder: RwLock::new(proof_recorder),
			_ph: PhantomData,
		};
		match P::ProofRaw::INPUT_KIND {
			ProofInputKind::ChildTrieRoots => {
				ProvingBackend {
					trie_backend: TrieBackend::new_with_roots(recorder, root),
					_ph: PhantomData
				}
			},
			ProofInputKind::None
			| ProofInputKind::QueryPlan
			| ProofInputKind::QueryPlanWithValues => {
				ProvingBackend {
					trie_backend: TrieBackend::new(recorder, root),
					_ph: PhantomData,
				}
			},
		}
	}
}

impl<S, H, P> ProvingBackend<S, H, P>
	where
		S: TrieBackendStorage<H>,
		H: Hasher,
		H::Out: Codec,
		P: BackendProof<H>,
{
	/// Create new proving backend with the given recorder.
	pub fn from_backend_with_recorder(
		backend: S,
		root: H::Out,
		proof_recorder: RecordBackendFor<P, H>,
	) -> Self {
		let recorder = ProofRecorderBackend {
			backend,
			proof_recorder: RwLock::new(proof_recorder),
			_ph: PhantomData,
		};
		match P::ProofRaw::INPUT_KIND {
			ProofInputKind::ChildTrieRoots => {
				ProvingBackend {
					trie_backend: TrieBackend::new_with_roots(recorder, root),
					_ph: PhantomData
				}
			},
			ProofInputKind::None
			| ProofInputKind::QueryPlan
			| ProofInputKind::QueryPlanWithValues => {
				ProvingBackend {
					trie_backend: TrieBackend::new(recorder, root),
					_ph: PhantomData,
				}
			},
		}
	}

}

impl<S: TrieBackendStorage<H>, H: Hasher, R: RecordBackend<H>> TrieBackendStorage<H>
	for ProofRecorderBackend<S, H, R>
{
	type Overlay = S::Overlay;

	fn get(&self, child_info: &ChildInfo, key: &H::Out, prefix: Prefix) -> Result<Option<DBValue>, String> {
		if let Some(v) = self.proof_recorder.read().get(child_info, key) {
			return Ok(v.clone());
		}
		let backend_value = self.backend.get(child_info, key, prefix)?;
		self.proof_recorder.write().record(child_info.clone(), key.clone(), backend_value.clone());
		Ok(backend_value)
	}
}

impl<S: TrieBackendStorage<H>, H: Hasher, P: BackendProof<H>> std::fmt::Debug
	for ProvingBackend<S, H, P>
{
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "ProvingBackend")
	}
}

impl<S, H, P> RegProofBackend<H> for ProvingBackend<S, H, P>
	where
		S: TrieBackendStorage<H>,
		H: Hasher,
		H::Out: Ord + Codec,
		P: BackendProof<H>,
{
	fn extract_proof(&self) -> Result<ProofRawFor<Self, H>, Box<dyn Error>> {
		let input = self.trie_backend.extract_registered_roots();
		<Self::StorageProof as BackendProof<H>>::ProofRaw::extract_proof(
			&self.trie_backend.essence().backend_storage().proof_recorder.read(),
			input,
		).map_err(|e| Box::new(e) as Box<dyn Error>)
	}

	fn extract_recorder(self) -> (RecordBackendFor<P, H>, ProofInput) {
		let input = self.trie_backend.extract_registered_roots();
		let recorder = self.trie_backend.into_storage().proof_recorder.into_inner();
		(recorder, input)
	}

	fn extract_proof_reg(recorder_state: &RecordBackendFor<P, H>, input: ProofInput) -> Result<ProofRawFor<Self, H>, Box<dyn crate::Error>> {
		<<Self::StorageProof as BackendProof<H>>::ProofRaw>::extract_proof(
			recorder_state,
			input,
		).map_err(|e| Box::new(e) as Box<dyn Error>)
	}
}

impl<S, H, P> Backend<H> for ProvingBackend<S, H, P>
	where
		S: TrieBackendStorage<H>,
		H: Hasher,
		H::Out: Ord + Codec,
		P: BackendProof<H>,
{
	type Error = String;
	type Transaction = S::Overlay;
	type StorageProof = P;
	type RegProofBackend = Self;
	type ProofCheckBackend = crate::InMemoryProofCheckBackend<H, P>;

	fn storage(&self, key: &[u8]) -> Result<Option<Vec<u8>>, Self::Error> {
		self.trie_backend.storage(key)
	}

	fn child_storage(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Result<Option<Vec<u8>>, Self::Error> {
		self.trie_backend.child_storage(child_info, key)
	}

	fn for_keys_in_child_storage<F: FnMut(&[u8])>(
		&self,
		child_info: &ChildInfo,
		f: F,
	) {
		self.trie_backend.for_keys_in_child_storage(child_info, f)
	}

	fn next_storage_key(&self, key: &[u8]) -> Result<Option<Vec<u8>>, Self::Error> {
		self.trie_backend.next_storage_key(key)
	}

	fn next_child_storage_key(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Result<Option<Vec<u8>>, Self::Error> {
		self.trie_backend.next_child_storage_key(child_info, key)
	}

	fn for_keys_with_prefix<F: FnMut(&[u8])>(&self, prefix: &[u8], f: F) {
		self.trie_backend.for_keys_with_prefix(prefix, f)
	}

	fn for_key_values_with_prefix<F: FnMut(&[u8], &[u8])>(&self, prefix: &[u8], f: F) {
		self.trie_backend.for_key_values_with_prefix(prefix, f)
	}

	fn for_child_keys_with_prefix<F: FnMut(&[u8])>(
		&self,
		child_info: &ChildInfo,
		prefix: &[u8],
		f: F,
	) {
		self.trie_backend.for_child_keys_with_prefix( child_info, prefix, f)
	}

	fn pairs(&self) -> Vec<(Vec<u8>, Vec<u8>)> {
		self.trie_backend.pairs()
	}

	fn keys(&self, prefix: &[u8]) -> Vec<Vec<u8>> {
		self.trie_backend.keys(prefix)
	}

	fn child_keys(
		&self,
		child_info: &ChildInfo,
		prefix: &[u8],
	) -> Vec<Vec<u8>> {
		self.trie_backend.child_keys(child_info, prefix)
	}

	fn storage_root<'b>(
		&self,
		delta: impl Iterator<Item=(&'b [u8], Option<&'b [u8]>)>,
	) -> (H::Out, Self::Transaction) where H::Out: Ord {
		self.trie_backend.storage_root(delta)
	}

	fn child_storage_root<'b>(
		&self,
		child_info: &ChildInfo,
		delta: impl Iterator<Item=(&'b [u8], Option<&'b [u8]>)>,
	) -> (H::Out, bool, Self::Transaction) where H::Out: Ord {
		self.trie_backend.child_storage_root(child_info, delta)
	}

	fn register_overlay_stats(&mut self, _stats: &crate::stats::StateMachineStats) { }

	fn usage_info(&self) -> crate::stats::UsageInfo {
		self.trie_backend.usage_info()
	}

	fn from_reg_state(
		self,
		previous_recorder: crate::backend::RecordBackendFor<Self, H>,
		previous_input: ProofInput,
	) -> Option<Self::RegProofBackend> {
		let root = self.trie_backend.essence().root().clone();
		let storage = self.trie_backend.into_storage();
		let current_recorder = storage.proof_recorder;
		let backend = storage.backend;
		if current_recorder.write().merge(previous_recorder) {
			let current_recorder = current_recorder.into_inner();

			Some(ProvingBackend::<S, H, P>::from_backend_with_recorder(backend, root, current_recorder))
		} else {
			None
		}.filter(|backend| {
			match previous_input {
				ProofInput::ChildTrieRoots(roots) => {
					backend.trie_backend.push_registered_roots(roots)
				},
				ProofInput::None => true,
				_ => false,
			}
		})
	}
}

/// Create flat proof check backend.
pub fn create_proof_check_backend<H, P>(
	root: H::Out,
	proof: P,
) -> Result<crate::InMemoryProofCheckBackend<H, P>, Box<dyn Error>>
where
	H: Hasher,
	H::Out: Codec,
	P: BackendProof<H>,
{
	let db = proof.into_partial_db()
		.map_err(|e| Box::new(format!("{}", e)) as Box<dyn Error>)?;
	if db.contains(&root, EMPTY_PREFIX) {
		Ok(TrieBackend::new(db, root))
	} else {
		Err(Box::new(ExecutionError::InvalidProof))
	}
}

/// Create proof check backend.
pub fn create_full_proof_check_backend<H, P>(
	root: H::Out,
	proof: P,
) -> Result<crate::InMemoryFullProofCheckBackend<H, P>, Box<dyn Error>>
where
	H: Hasher,
	H::Out: Codec,
	P: FullBackendProof<H>,
{
	use std::ops::Deref;
	let db = proof.into_partial_full_db()
		.map_err(|e| Box::new(format!("{}", e)) as Box<dyn Error>)?;
	if db.deref().get(&ChildInfoProof::top_trie())
		.map(|db| db.contains(&root, EMPTY_PREFIX))
		.unwrap_or(false) {
		Ok(TrieBackend::new(db, root))
	} else {
		Err(Box::new(ExecutionError::InvalidProof))
	}
}

#[cfg(test)]
mod tests {
	use crate::InMemoryProofCheckBackend;
	use crate::trie_backend::tests::test_trie_proof;
	use super::*;
	use crate::proving_backend::create_proof_check_backend;
	use sp_trie::PrefixedMemoryDB;
	use sp_trie::{SimpleProof, ProofCommon};
	use sp_runtime::traits::BlakeTwo256;

	type CompactProof = sp_trie::CompactProof<Layout<BlakeTwo256>>;

	fn test_proving<P: sp_trie::BackendProof<BlakeTwo256>>(
		trie_backend: &TrieBackend<PrefixedMemoryDB<BlakeTwo256>, BlakeTwo256, P>,
	) -> ProvingBackend<&PrefixedMemoryDB<BlakeTwo256>, BlakeTwo256, P> {
		ProvingBackend::new(trie_backend)
	}

	#[test]
	fn proof_is_empty_until_value_is_read() {
		proof_is_empty_until_value_is_read_inner::<SimpleProof>();
		proof_is_empty_until_value_is_read_inner::<CompactProof>();
	}
	fn proof_is_empty_until_value_is_read_inner<P: BackendProof<BlakeTwo256>>() {
		let trie_backend = test_trie_proof::<P>();
		assert!(test_proving(&trie_backend).extract_proof().unwrap().is_empty());
	}

	#[test]
	fn proof_is_non_empty_after_value_is_read() {
		proof_is_non_empty_after_value_is_read_inner::<SimpleProof>();
		proof_is_non_empty_after_value_is_read_inner::<CompactProof>();
	}
	fn proof_is_non_empty_after_value_is_read_inner<P: BackendProof<BlakeTwo256>>() {
		let trie_backend = test_trie_proof::<P>();
		let backend = test_proving(&trie_backend);
		assert_eq!(backend.storage(b"key").unwrap(), Some(b"value".to_vec()));
		assert!(!backend.extract_proof().unwrap().is_empty());
	}

	#[test]
	fn proof_is_invalid_when_does_not_contains_root() {
		use sp_core::H256;
		let result = create_proof_check_backend::<BlakeTwo256, SimpleProof>(
			H256::from_low_u64_be(1),
			SimpleProof::empty()
		);
		assert!(result.is_err());
		let result = create_proof_check_backend::<BlakeTwo256, CompactProof>(
			H256::from_low_u64_be(1),
			CompactProof::empty()
		);
		assert!(result.is_err());
	}

	#[test]
	fn passes_through_backend_calls() {
		passes_through_backend_calls_inner::<SimpleProof>();
		passes_through_backend_calls_inner::<CompactProof>();
	}
	fn passes_through_backend_calls_inner<P: BackendProof<BlakeTwo256>>() {
		let trie_backend = test_trie_proof::<P>();
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
		proof_recorded_and_checked_inner::<SimpleProof>();
		proof_recorded_and_checked_inner::<CompactProof>();
	}
	fn proof_recorded_and_checked_inner<P: BackendProof<BlakeTwo256>>() {
		let contents = (0..64).map(|i| (vec![i], Some(vec![i]))).collect::<Vec<_>>();
		let in_memory = InMemoryProofCheckBackend::<BlakeTwo256, P>::default();
		let in_memory = in_memory.update(vec![(None, contents)]);
		let in_memory_root = in_memory.storage_root(::std::iter::empty()).0;
		(0..64).for_each(|i| assert_eq!(in_memory.storage(&[i]).unwrap().unwrap(), vec![i]));

		let trie = &in_memory;
		let trie_root = trie.storage_root(::std::iter::empty()).0;
		assert_eq!(in_memory_root, trie_root);
		(0..64).for_each(|i| assert_eq!(trie.storage(&[i]).unwrap().unwrap(), vec![i]));

		let proving = in_memory.as_proof_backend().unwrap();
		assert_eq!(proving.storage(&[42]).unwrap().unwrap(), vec![42]);

		let proof = proving.extract_proof().unwrap();

		let proof_check = create_proof_check_backend::<BlakeTwo256, P>(in_memory_root.into(), proof.into()).unwrap();
		assert_eq!(proof_check.storage(&[42]).unwrap().unwrap(), vec![42]);
	}

	#[test]
	fn proof_recorded_and_checked_with_child() {
		proof_recorded_and_checked_with_child_inner::<SimpleProof>();
		proof_recorded_and_checked_with_child_inner::<CompactProof>();
	}
	fn proof_recorded_and_checked_with_child_inner<P: BackendProof<BlakeTwo256>>() {
		let child_info_1 = ChildInfo::new_default(b"sub1");
		let child_info_2 = ChildInfo::new_default(b"sub2");
		let child_info_1 = &child_info_1;
		let child_info_2 = &child_info_2;
		let contents = vec![
			(None, (0..64).map(|i| (vec![i], Some(vec![i]))).collect()),
			(Some(child_info_1.clone()),
				(28..65).map(|i| (vec![i], Some(vec![i]))).collect()),
			(Some(child_info_2.clone()),
				(10..15).map(|i| (vec![i], Some(vec![i]))).collect()),
		];
		let in_memory = InMemoryProofCheckBackend::<BlakeTwo256, P>::default();
		let in_memory = in_memory.update(contents);
		let child_storage_keys = vec![child_info_1.to_owned(), child_info_2.to_owned()];
		let in_memory_root = in_memory.full_storage_root(
			std::iter::empty(),
			child_storage_keys.iter().map(|k|(k, std::iter::empty()))
		).0;
		(0..64).for_each(|i| assert_eq!(
			in_memory.storage(&[i]).unwrap().unwrap(),
			vec![i]
		));
		(28..65).for_each(|i| assert_eq!(
			in_memory.child_storage(child_info_1, &[i]).unwrap().unwrap(),
			vec![i]
		));
		(10..15).for_each(|i| assert_eq!(
			in_memory.child_storage(child_info_2, &[i]).unwrap().unwrap(),
			vec![i]
		));

		let trie = &in_memory;
		let trie_root = trie.storage_root(::std::iter::empty()).0;
		assert_eq!(in_memory_root, trie_root);
		(0..64).for_each(|i| assert_eq!(
			trie.storage(&[i]).unwrap().unwrap(),
			vec![i]
		));

		let proving = in_memory.clone().as_proof_backend().unwrap();
		assert_eq!(proving.storage(&[42]).unwrap().unwrap(), vec![42]);

		let proof = proving.extract_proof().unwrap();

		let proof_check = create_proof_check_backend::<BlakeTwo256, P>(
			in_memory_root.into(),
			proof.into(),
		).unwrap();
		assert!(proof_check.storage(&[0]).is_err());
		assert_eq!(proof_check.storage(&[42]).unwrap().unwrap(), vec![42]);
		// note that it is include in root because proof close
		assert_eq!(proof_check.storage(&[41]).unwrap().unwrap(), vec![41]);
		assert_eq!(proof_check.storage(&[64]).unwrap(), None);

		let proving = in_memory.as_proof_backend().unwrap();
		assert_eq!(proving.child_storage(child_info_1, &[64]), Ok(Some(vec![64])));

		let proof = proving.extract_proof().unwrap();
		let proof_check = create_proof_check_backend::<BlakeTwo256, P>(
			in_memory_root.into(),
			proof.into(),
		).unwrap();

		assert_eq!(
			proof_check.child_storage(&child_info_1, &[64]).unwrap().unwrap(),
			vec![64]
		);
	}
}
