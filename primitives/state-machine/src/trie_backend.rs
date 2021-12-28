// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
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

use crate::{
	debug,
	trie_backend_essence::{Ephemeral, TrieBackendEssence, TrieBackendStorage},
	warn, Backend, StorageKey, StorageValue,
};
use codec::{Codec, Decode};
use hash_db::Hasher;
use sp_core::storage::{ChildInfo, ChildType, StateVersion};
use sp_std::{boxed::Box, vec::Vec};
use sp_trie::{
	child_delta_trie_root, delta_trie_root, empty_child_trie_root,
	trie_types::{TrieDB, TrieError},
	LayoutV0, LayoutV1, Trie,
};

/// Patricia trie-based backend. Transaction type is an overlay of changes to commit.
pub struct TrieBackend<S: TrieBackendStorage<H>, H: Hasher> {
	pub(crate) essence: TrieBackendEssence<S, H>,
}

impl<S: TrieBackendStorage<H>, H: Hasher> TrieBackend<S, H>
where
	H::Out: Codec,
{
	/// Create new trie-based backend.
	pub fn new(storage: S, root: H::Out) -> Self {
		TrieBackend { essence: TrieBackendEssence::new(storage, root) }
	}

	/// Get backend essence reference.
	pub fn essence(&self) -> &TrieBackendEssence<S, H> {
		&self.essence
	}

	/// Get backend storage reference.
	pub fn backend_storage(&self) -> &S {
		self.essence.backend_storage()
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

impl<S: TrieBackendStorage<H>, H: Hasher> sp_std::fmt::Debug for TrieBackend<S, H> {
	fn fmt(&self, f: &mut sp_std::fmt::Formatter<'_>) -> sp_std::fmt::Result {
		write!(f, "TrieBackend")
	}
}

impl<S: TrieBackendStorage<H>, H: Hasher> Backend<H> for TrieBackend<S, H>
where
	H::Out: Ord + Codec,
{
	type Error = crate::DefaultError;
	type Transaction = S::Overlay;
	type TrieBackendStorage = S;

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

	fn apply_to_key_values_while<F: FnMut(Vec<u8>, Vec<u8>) -> bool>(
		&self,
		child_info: Option<&ChildInfo>,
		prefix: Option<&[u8]>,
		start_at: Option<&[u8]>,
		f: F,
		allow_missing: bool,
	) -> Result<bool, Self::Error> {
		self.essence
			.apply_to_key_values_while(child_info, prefix, start_at, f, allow_missing)
	}

	fn apply_to_keys_while<F: FnMut(&[u8]) -> bool>(
		&self,
		child_info: Option<&ChildInfo>,
		prefix: Option<&[u8]>,
		f: F,
	) {
		self.essence.apply_to_keys_while(child_info, prefix, f)
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
			let trie = TrieDB::<H>::new(self.essence(), self.essence.root())?;
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
			},
		}
	}

	fn keys(&self, prefix: &[u8]) -> Vec<StorageKey> {
		let collect_all = || -> Result<_, Box<TrieError<H::Out>>> {
			let trie = TrieDB::<H>::new(self.essence(), self.essence.root())?;
			let mut v = Vec::new();
			for x in trie.iter()? {
				let (key, _) = x?;
				if key.starts_with(prefix) {
					v.push(key.to_vec());
				}
			}

			Ok(v)
		};

		collect_all()
			.map_err(|e| debug!(target: "trie", "Error extracting trie keys: {}", e))
			.unwrap_or_default()
	}

	fn storage_root<'a>(
		&self,
		delta: impl Iterator<Item = (&'a [u8], Option<&'a [u8]>)>,
		state_version: StateVersion,
	) -> (H::Out, Self::Transaction)
	where
		H::Out: Ord,
	{
		let mut write_overlay = S::Overlay::default();
		let mut root = *self.essence.root();

		{
			let mut eph = Ephemeral::new(self.essence.backend_storage(), &mut write_overlay);
			let res = match state_version {
				StateVersion::V0 =>
					delta_trie_root::<LayoutV0<H>, _, _, _, _, _>(&mut eph, root, delta),
				StateVersion::V1 =>
					delta_trie_root::<LayoutV1<H>, _, _, _, _, _>(&mut eph, root, delta),
			};

			match res {
				Ok(ret) => root = ret,
				Err(e) => warn!(target: "trie", "Failed to write to trie: {}", e),
			}
		}

		(root, write_overlay)
	}

	fn child_storage_root<'a>(
		&self,
		child_info: &ChildInfo,
		delta: impl Iterator<Item = (&'a [u8], Option<&'a [u8]>)>,
		state_version: StateVersion,
	) -> (H::Out, bool, Self::Transaction)
	where
		H::Out: Ord,
	{
		let default_root = match child_info.child_type() {
			ChildType::ParentKeyId => empty_child_trie_root::<LayoutV1<H>>(),
		};
		let mut write_overlay = S::Overlay::default();
		let prefixed_storage_key = child_info.prefixed_storage_key();
		let mut root = match self.storage(prefixed_storage_key.as_slice()) {
			Ok(value) => value
				.and_then(|r| Decode::decode(&mut &r[..]).ok())
				.unwrap_or_else(|| default_root.clone()),
			Err(e) => {
				warn!(target: "trie", "Failed to read child storage root: {}", e);
				default_root.clone()
			},
		};

		{
			let mut eph = Ephemeral::new(self.essence.backend_storage(), &mut write_overlay);
			match match state_version {
				StateVersion::V0 => child_delta_trie_root::<LayoutV0<H>, _, _, _, _, _, _>(
					child_info.keyspace(),
					&mut eph,
					root,
					delta,
				),
				StateVersion::V1 => child_delta_trie_root::<LayoutV1<H>, _, _, _, _, _, _>(
					child_info.keyspace(),
					&mut eph,
					root,
					delta,
				),
			} {
				Ok(ret) => root = ret,
				Err(e) => warn!(target: "trie", "Failed to write to trie: {}", e),
			}
		}

		let is_default = root == default_root;

		(root, is_default, write_overlay)
	}

	fn as_trie_backend(&self) -> Option<&TrieBackend<Self::TrieBackendStorage, H>> {
		Some(self)
	}

	fn register_overlay_stats(&self, _stats: &crate::stats::StateMachineStats) {}

	fn usage_info(&self) -> crate::UsageInfo {
		crate::UsageInfo::empty()
	}

	fn wipe(&self) -> Result<(), Self::Error> {
		Ok(())
	}
}

#[cfg(test)]
pub mod tests {
	use super::*;
	use codec::Encode;
	use sp_core::H256;
	use sp_runtime::traits::BlakeTwo256;
	use sp_trie::{
		trie_types::{TrieDBMutV0, TrieDBMutV1},
		KeySpacedDBMut, PrefixedMemoryDB, TrieMut,
	};
	use std::{collections::HashSet, iter};

	const CHILD_KEY_1: &[u8] = b"sub1";

	pub(crate) fn test_db(state_version: StateVersion) -> (PrefixedMemoryDB<BlakeTwo256>, H256) {
		let child_info = ChildInfo::new_default(CHILD_KEY_1);
		let mut root = H256::default();
		let mut mdb = PrefixedMemoryDB::<BlakeTwo256>::default();
		{
			let mut mdb = KeySpacedDBMut::new(&mut mdb, child_info.keyspace());
			match state_version {
				StateVersion::V0 => {
					let mut trie = TrieDBMutV0::new(&mut mdb, &mut root);
					trie.insert(b"value3", &[142; 33]).expect("insert failed");
					trie.insert(b"value4", &[124; 33]).expect("insert failed");
				},
				StateVersion::V1 => {
					let mut trie = TrieDBMutV1::new(&mut mdb, &mut root);
					trie.insert(b"value3", &[142; 33]).expect("insert failed");
					trie.insert(b"value4", &[124; 33]).expect("insert failed");
				},
			};
		};

		{
			let mut sub_root = Vec::new();
			root.encode_to(&mut sub_root);

			fn build<L: sp_trie::TrieLayout>(
				mut trie: sp_trie::TrieDBMut<L>,
				child_info: &ChildInfo,
				sub_root: &[u8],
			) {
				trie.insert(child_info.prefixed_storage_key().as_slice(), sub_root)
					.expect("insert failed");
				trie.insert(b"key", b"value").expect("insert failed");
				trie.insert(b"value1", &[42]).expect("insert failed");
				trie.insert(b"value2", &[24]).expect("insert failed");
				trie.insert(b":code", b"return 42").expect("insert failed");
				for i in 128u8..255u8 {
					trie.insert(&[i], &[i]).unwrap();
				}
			}

			match state_version {
				StateVersion::V0 => {
					let trie = TrieDBMutV0::new(&mut mdb, &mut root);
					build(trie, &child_info, &sub_root[..])
				},
				StateVersion::V1 => {
					let trie = TrieDBMutV1::new(&mut mdb, &mut root);
					build(trie, &child_info, &sub_root[..])
				},
			};
		}
		(mdb, root)
	}

	pub(crate) fn test_trie(
		hashed_value: StateVersion,
	) -> TrieBackend<PrefixedMemoryDB<BlakeTwo256>, BlakeTwo256> {
		let (mdb, root) = test_db(hashed_value);
		TrieBackend::new(mdb, root)
	}

	#[test]
	fn read_from_storage_returns_some() {
		read_from_storage_returns_some_inner(StateVersion::V0);
		read_from_storage_returns_some_inner(StateVersion::V1);
	}
	fn read_from_storage_returns_some_inner(state_version: StateVersion) {
		assert_eq!(test_trie(state_version).storage(b"key").unwrap(), Some(b"value".to_vec()));
	}

	#[test]
	fn read_from_child_storage_returns_some() {
		read_from_child_storage_returns_some_inner(StateVersion::V0);
		read_from_child_storage_returns_some_inner(StateVersion::V1);
	}
	fn read_from_child_storage_returns_some_inner(state_version: StateVersion) {
		let test_trie = test_trie(state_version);
		assert_eq!(
			test_trie
				.child_storage(&ChildInfo::new_default(CHILD_KEY_1), b"value3")
				.unwrap(),
			Some(vec![142u8; 33]),
		);
		// Change cache entry to check that caching is active.
		test_trie
			.essence
			.cache
			.write()
			.child_root
			.entry(b"sub1".to_vec())
			.and_modify(|value| {
				*value = None;
			});
		assert_eq!(
			test_trie
				.child_storage(&ChildInfo::new_default(CHILD_KEY_1), b"value3")
				.unwrap(),
			None,
		);
	}

	#[test]
	fn read_from_storage_returns_none() {
		read_from_storage_returns_none_inner(StateVersion::V0);
		read_from_storage_returns_none_inner(StateVersion::V1);
	}
	fn read_from_storage_returns_none_inner(state_version: StateVersion) {
		assert_eq!(test_trie(state_version).storage(b"non-existing-key").unwrap(), None);
	}

	#[test]
	fn pairs_are_not_empty_on_non_empty_storage() {
		pairs_are_not_empty_on_non_empty_storage_inner(StateVersion::V0);
		pairs_are_not_empty_on_non_empty_storage_inner(StateVersion::V1);
	}
	fn pairs_are_not_empty_on_non_empty_storage_inner(state_version: StateVersion) {
		assert!(!test_trie(state_version).pairs().is_empty());
	}

	#[test]
	fn pairs_are_empty_on_empty_storage() {
		assert!(TrieBackend::<PrefixedMemoryDB<BlakeTwo256>, BlakeTwo256>::new(
			PrefixedMemoryDB::default(),
			Default::default(),
		)
		.pairs()
		.is_empty());
	}

	#[test]
	fn storage_root_is_non_default() {
		storage_root_is_non_default_inner(StateVersion::V0);
		storage_root_is_non_default_inner(StateVersion::V1);
	}
	fn storage_root_is_non_default_inner(state_version: StateVersion) {
		assert!(
			test_trie(state_version).storage_root(iter::empty(), state_version).0 !=
				H256::repeat_byte(0)
		);
	}

	#[test]
	fn storage_root_transaction_is_non_empty() {
		storage_root_transaction_is_non_empty_inner(StateVersion::V0);
		storage_root_transaction_is_non_empty_inner(StateVersion::V1);
	}
	fn storage_root_transaction_is_non_empty_inner(state_version: StateVersion) {
		let (new_root, mut tx) = test_trie(state_version)
			.storage_root(iter::once((&b"new-key"[..], Some(&b"new-value"[..]))), state_version);
		assert!(!tx.drain().is_empty());
		assert!(new_root != test_trie(state_version).storage_root(iter::empty(), state_version).0);
	}

	#[test]
	fn prefix_walking_works() {
		prefix_walking_works_inner(StateVersion::V0);
		prefix_walking_works_inner(StateVersion::V1);
	}
	fn prefix_walking_works_inner(state_version: StateVersion) {
		let trie = test_trie(state_version);

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
