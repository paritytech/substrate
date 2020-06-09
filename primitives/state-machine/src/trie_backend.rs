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

//! Trie-based state machine backend.

use log::{warn, debug};
use hash_db::Hasher;
use sp_trie::{Trie, delta_trie_root, empty_child_trie_root, child_delta_trie_root,
	ChildrenProofMap, ProofInput, BackendStorageProof};
use sp_trie::trie_types::{TrieDB, TrieError, Layout};
use sp_trie::RegStorageProof;
use crate::backend::{ProofRegStateFor};
use sp_core::storage::{ChildInfo, ChildInfoProof, ChildType};
use codec::{Codec, Decode, Encode};
use crate::{
	StorageKey, StorageValue, Backend, backend::ProofCheckBackend,
	trie_backend_essence::{TrieBackendEssence, TrieBackendStorage, Ephemeral},
};
use sp_trie::MemoryDB;
use parking_lot::RwLock;
use std::marker::PhantomData;

/// Patricia trie-based backend. Transaction type is an overlay of changes to commit.
pub struct TrieBackend<S: TrieBackendStorage<H>, H: Hasher, P> {
	pub (crate) essence: TrieBackendEssence<S, H>,
	_ph: PhantomData<P>,
}

impl<S: TrieBackendStorage<H>, H: Hasher, P> TrieBackend<S, H, P> where H::Out: Codec {
	/// Create new trie-based backend.
	pub fn new(storage: S, root: H::Out) -> Self {
		TrieBackend {
			essence: TrieBackendEssence::new(storage, root, None),
			_ph: PhantomData,
		}
	}

	/// Create a trie backend that also record visited trie roots.
	/// to pack proofs and does small caching of child trie root)).
	pub fn new_with_roots(storage: S, root: H::Out) -> Self {
		let register_roots = Some(RwLock::new(Default::default()));
		TrieBackend {
			essence: TrieBackendEssence::new(storage, root, register_roots),
			_ph: PhantomData,
		}
	}

	/// Get registered roots. Empty input is returned when the backend is
	/// not configured to register roots.
	pub fn extract_registered_roots(&self) -> ProofInput {
		if let Some(register_roots) = self.essence.register_roots() {
			let mut dest = ChildrenProofMap::default();
			dest.insert(ChildInfoProof::top_trie(), self.essence.root().encode());
			let roots = {
				std::mem::replace(&mut *register_roots.write(), Default::default())
			};
			for (child_info, root) in roots.into_iter() {
				if let Some(root) = root {
					dest.insert(child_info.proof_info(), root);
				}
			}
			ProofInput::ChildTrieRoots(dest)
		} else {
			ProofInput::None
		}
	}

	/// Get backend essence reference.
	pub fn essence(&self) -> &TrieBackendEssence<S, H> {
		&self.essence
	}

	/// Get backend storage reference.
	pub fn backend_storage(&self) -> &S {
		self.essence.backend_storage()
	}

	/// Get backend storage reference.
	pub fn backend_storage_mut(&mut self) -> &mut S {
		self.essence.backend_storage_mut()
	}

	/// Get trie root.
	pub fn root(&self) -> &H::Out {
		self.essence.root()
	}

	/// Consumes self and returns underlying storage.
	pub fn into_storage(self) -> S {
		self.essence.into_storage()
	}
}

impl<S: TrieBackendStorage<H>, H: Hasher, P> std::fmt::Debug for TrieBackend<S, H, P> {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "TrieBackend")
	}
}

impl<S, H, P> Backend<H> for TrieBackend<S, H, P> where
	H: Hasher,
	S: TrieBackendStorage<H>,
	H::Out: Ord + Codec,
	P: BackendStorageProof<H>,
{
	type Error = String;
	type Transaction = S::Overlay;
	type StorageProof = P;
	type ProofRegBackend = crate::proving_backend::ProvingBackend<
		S,
		H,
		Self::StorageProof,
	>;
	type ProofCheckBackend = TrieBackend<crate::MemoryDB<H>, H, P>;

	fn storage(&self, key: &[u8]) -> Result<Option<StorageValue>, Self::Error> {
		self.essence.storage(key)
	}

	fn child_storage(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Result<Option<StorageValue>, Self::Error> {
		self.essence.child_storage(child_info, key)
	}

	fn next_storage_key(&self, key: &[u8]) -> Result<Option<StorageKey>, Self::Error> {
		self.essence.next_storage_key(key)
	}

	fn next_child_storage_key(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Result<Option<StorageKey>, Self::Error> {
		self.essence.next_child_storage_key(child_info, key)
	}

	fn for_keys_with_prefix<F: FnMut(&[u8])>(&self, prefix: &[u8], f: F) {
		self.essence.for_keys_with_prefix(prefix, f)
	}

	fn for_key_values_with_prefix<F: FnMut(&[u8], &[u8])>(&self, prefix: &[u8], f: F) {
		self.essence.for_key_values_with_prefix(prefix, f)
	}

	fn for_keys_in_child_storage<F: FnMut(&[u8])>(
		&self,
		child_info: &ChildInfo,
		f: F,
	) {
		self.essence.for_keys_in_child_storage(child_info, f)
	}

	fn for_child_keys_with_prefix<F: FnMut(&[u8])>(
		&self,
		child_info: &ChildInfo,
		prefix: &[u8],
		f: F,
	) {
		self.essence.for_child_keys_with_prefix(child_info, prefix, f)
	}

	fn pairs(&self) -> Vec<(StorageKey, StorageValue)> {
		let collect_all = || -> Result<_, Box<TrieError<H::Out>>> {
			let backend = self.essence().top_backend();
			let trie = TrieDB::<H>::new(&backend, self.essence.root())?;
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

	fn keys(&self, prefix: &[u8]) -> Vec<StorageKey> {
		let collect_all = || -> Result<_, Box<TrieError<H::Out>>> {
			let backend = self.essence().top_backend();
			let trie = TrieDB::<H>::new(&backend, self.essence.root())?;
			let mut v = Vec::new();
			for x in trie.iter()? {
				let (key, _) = x?;
				if key.starts_with(prefix) {
					v.push(key.to_vec());
				}
			}

			Ok(v)
		};

		collect_all().map_err(|e| debug!(target: "trie", "Error extracting trie keys: {}", e)).unwrap_or_default()
	}

	fn storage_root<'a>(
		&self,
		delta: impl Iterator<Item=(&'a [u8], Option<&'a [u8]>)>,
	) -> (H::Out, Self::Transaction) where H::Out: Ord {
		let mut write_overlay = S::Overlay::default();
		let mut root = *self.essence.root();

		{
			let mut eph = Ephemeral::new(
				self.essence.backend_storage(),
				&mut write_overlay,
				None,
			);

			match delta_trie_root::<Layout<H>, _, _, _, _, _>(&mut eph, root, delta) {
				Ok(ret) => root = ret,
				Err(e) => warn!(target: "trie", "Failed to write to trie: {}", e),
			}
		}

		(root, write_overlay)
	}

	fn child_storage_root<'a>(
		&self,
		child_info: &ChildInfo,
		delta: impl Iterator<Item=(&'a [u8], Option<&'a [u8]>)>,
	) -> (H::Out, bool, Self::Transaction) where H::Out: Ord {
		let default_root = match child_info.child_type() {
			ChildType::ParentKeyId => empty_child_trie_root::<Layout<H>>()
		};

		let mut write_overlay = S::Overlay::default();
		let mut root = match self.essence.child_root_encoded(child_info) {
			Ok(value) =>
				value.and_then(|r| Decode::decode(&mut &r[..]).ok()).unwrap_or(default_root.clone()),
			Err(e) => {
				warn!(target: "trie", "Failed to read child storage root: {}", e);
				default_root.clone()
			},
		};

		{
			let mut eph = Ephemeral::new(
				self.essence.backend_storage(),
				&mut write_overlay,
				Some(child_info),
			);

			match child_delta_trie_root::<Layout<H>, _, _, _, _, _, _>(
				child_info.keyspace(),
				&mut eph,
				root,
				delta,
			) {
				Ok(ret) => root = ret,
				Err(e) => warn!(target: "trie", "Failed to write to trie: {}", e),
			}
		}

		let is_default = root == default_root;

		(root, is_default, write_overlay)
	}

	fn from_reg_state(self, recorder: ProofRegStateFor<Self, H>) -> Option<Self::ProofRegBackend> {
		let root = self.essence.root().clone();
		Some(crate::proving_backend::ProvingBackend::from_backend_with_recorder(
			self.essence.into_storage(),
			root,
			recorder,
		))
	}

	fn register_overlay_stats(&mut self, _stats: &crate::stats::StateMachineStats) { }

	fn usage_info(&self) -> crate::UsageInfo {
		crate::UsageInfo::empty()
	}

	fn wipe(&self) -> Result<(), Self::Error> {
		Ok(())
	}
}

impl<H: Hasher, P> ProofCheckBackend<H> for TrieBackend<MemoryDB<H>, H, P>
	where
		H::Out: Ord + Codec,
		P: BackendStorageProof<H>,
{
	fn create_proof_check_backend(
		root: H::Out,
		proof: Self::StorageProof,
	) -> Result<Self, Box<dyn crate::Error>> {
		let mem_db = proof.into_partial_db()
			.map_err(|e| Box::new(e) as Box<dyn crate::Error>)?;
		Ok(TrieBackend::new(mem_db, root))
	}
}
	
#[cfg(test)]
pub mod tests {
	use std::{collections::HashSet, iter};
	use sp_core::H256;
	use codec::Encode;
	use sp_trie::{TrieMut, PrefixedMemoryDB, trie_types::TrieDBMut, KeySpacedDBMut, SimpleProof};
	use sp_runtime::traits::BlakeTwo256;
	use super::*;

	const CHILD_KEY_1: &[u8] = b"sub1";

	fn test_db() -> (PrefixedMemoryDB<BlakeTwo256>, H256) {
		let child_info = ChildInfo::new_default(CHILD_KEY_1);
		let mut root = H256::default();
		let mut mdb = PrefixedMemoryDB::<BlakeTwo256>::default();
		{
			let mut mdb = KeySpacedDBMut::new(&mut mdb, child_info.keyspace());
			let mut trie = TrieDBMut::new(&mut mdb, &mut root);
			trie.insert(b"value3", &[142]).expect("insert failed");
			trie.insert(b"value4", &[124]).expect("insert failed");
		};

		{
			let mut sub_root = Vec::new();
			root.encode_to(&mut sub_root);
			let mut trie = TrieDBMut::new(&mut mdb, &mut root);
			trie.insert(child_info.prefixed_storage_key().as_slice(), &sub_root[..])
				.expect("insert failed");
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

	pub(crate) fn test_trie_proof<P: sp_trie::BackendStorageProof<BlakeTwo256>>()
		-> TrieBackend<PrefixedMemoryDB<BlakeTwo256>, BlakeTwo256, P> {
		let (mdb, root) = test_db();
		TrieBackend::new(mdb, root)
	}

	pub(crate) fn test_trie() -> TrieBackend<PrefixedMemoryDB<BlakeTwo256>, BlakeTwo256, SimpleProof> {
		let (mdb, root) = test_db();
		TrieBackend::new(mdb, root)
	}

	#[test]
	fn read_from_storage_returns_some() {
		assert_eq!(test_trie().storage(b"key").unwrap(), Some(b"value".to_vec()));
	}

	#[test]
	fn read_from_child_storage_returns_some() {
		let test_trie = test_trie();
		assert_eq!(
			test_trie.child_storage(&ChildInfo::new_default(CHILD_KEY_1), b"value3").unwrap(),
			Some(vec![142u8]),
		);
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
		assert!(TrieBackend::<PrefixedMemoryDB<BlakeTwo256>, BlakeTwo256, SimpleProof>::new(
			PrefixedMemoryDB::default(),
			Default::default(),
		).pairs().is_empty());
	}

	#[test]
	fn storage_root_is_non_default() {
		assert!(test_trie().storage_root(iter::empty()).0 != H256::repeat_byte(0));
	}

	#[test]
	fn storage_root_transaction_is_empty() {
		assert!(test_trie().storage_root(iter::empty()).1.drain().is_empty());
	}

	#[test]
	fn storage_root_transaction_is_non_empty() {
		let (new_root, mut tx) = test_trie().storage_root(
			iter::once((&b"new-key"[..], Some(&b"new-value"[..]))),
		);
		assert!(!tx.drain().is_empty());
		assert!(new_root != test_trie().storage_root(iter::empty()).0);
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
