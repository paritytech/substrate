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
use sp_core::storage::{ChildInfo, ChildType};
use sp_core::state_version::StateVersion;
use sp_std::{boxed::Box, vec::Vec};
use sp_trie::{
	child_delta_trie_root, delta_trie_root, empty_child_trie_root,
	trie_types::{TrieDB, TrieError},
	Layout, Trie,
};

/// Patricia trie-based backend. Transaction type is an overlay of changes to commit.
pub struct TrieBackend<S: TrieBackendStorage<H>, H: Hasher> {
	pub(crate) essence: TrieBackendEssence<S, H>,
	state_version: StateVersion,
}

impl<S: TrieBackendStorage<H>, H: Hasher> TrieBackend<S, H>
where
	H::Out: Codec,
{
	/// Create new trie-based backend.
	pub fn new(storage: S, root: H::Out, state_version: StateVersion) -> Self {
		TrieBackend { essence: TrieBackendEssence::new(storage, root), state_version: state_version }
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
	) -> (H::Out, Self::Transaction)
	where
		H::Out: Ord,
	{
		let mut write_overlay = S::Overlay::default();
		let mut root = *self.essence.root();

		{
			let mut eph = Ephemeral::new(self.essence.backend_storage(), &mut write_overlay);
			let res = || {
				let layout = match self.state_version {
					StateVersion::V0 => {
						sp_trie::Layout::default()
					},
					StateVersion::V1{ threshold } => {
						sp_trie::Layout::with_alt_hashing(threshold)
					},
				};
				delta_trie_root::<Layout<H>, _, _, _, _, _>(&mut eph, root, delta, layout)
			};

			match res() {
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
	) -> (H::Out, bool, Self::Transaction)
	where
		H::Out: Ord,
	{
		let default_root = match child_info.child_type() {
			ChildType::ParentKeyId => empty_child_trie_root::<Layout<H>>(),
		};
		let layout = match self.state_version {
			StateVersion::V0 => {
				sp_trie::Layout::default()
			},
			StateVersion::V1{ threshold } => {
				sp_trie::Layout::with_alt_hashing(threshold)
			},
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

			match child_delta_trie_root::<Layout<H>, _, _, _, _, _, _>(
				child_info.keyspace(),
				&mut eph,
				root,
				delta,
				layout,
			) {
				Ok(ret) => root = ret,
				Err(e) => warn!(target: "trie", "Failed to write to trie: {}", e),
			}
		}

		let is_default = root == default_root;

		(root, is_default, write_overlay)
	}

	fn as_trie_backend(&mut self) -> Option<&TrieBackend<Self::TrieBackendStorage, H>> {
		Some(self)
	}

	fn register_overlay_stats(&self, _stats: &crate::stats::StateMachineStats) {}

	fn usage_info(&self) -> crate::UsageInfo {
		crate::UsageInfo::empty()
	}

	fn wipe(&self) -> Result<(), Self::Error> {
		Ok(())
	}

	fn state_version(&self) -> StateVersion {
		self.state_version.clone()
	}
}

#[cfg(test)]
pub mod tests {
	use super::*;
	use codec::Encode;
	use sp_core::{storage::TEST_DEFAULT_ALT_HASH_THRESHOLD as TRESHOLD, H256};
	use sp_runtime::traits::BlakeTwo256;
	use sp_trie::{trie_types::TrieDBMut, KeySpacedDBMut, PrefixedMemoryDB, TrieMut};
	use std::{collections::HashSet, iter};

	const CHILD_KEY_1: &[u8] = b"sub1";

	pub(crate) fn test_db(hashed_value: bool) -> (PrefixedMemoryDB<BlakeTwo256>, H256) {
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
			let mut trie = if hashed_value {
				let layout = Layout::with_alt_hashing(TRESHOLD);
				TrieDBMut::new_with_layout(&mut mdb, &mut root, layout)
			} else {
				TrieDBMut::new(&mut mdb, &mut root)
			};

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

	pub(crate) fn test_trie(
		hashed_value: bool,
	) -> TrieBackend<PrefixedMemoryDB<BlakeTwo256>, BlakeTwo256> {
		let (mdb, root) = test_db(hashed_value);
		TrieBackend::new(mdb, root, Default::default())
	}

	#[test]
	fn read_from_storage_returns_some() {
		read_from_storage_returns_some_inner(false);
		read_from_storage_returns_some_inner(true);
	}
	fn read_from_storage_returns_some_inner(flagged: bool) {
		assert_eq!(test_trie(flagged).storage(b"key").unwrap(), Some(b"value".to_vec()));
	}

	#[test]
	fn read_from_child_storage_returns_some() {
		read_from_child_storage_returns_some_inner(false);
		read_from_child_storage_returns_some_inner(true);
	}
	fn read_from_child_storage_returns_some_inner(flagged: bool) {
		let test_trie = test_trie(flagged);
		assert_eq!(
			test_trie
				.child_storage(&ChildInfo::new_default(CHILD_KEY_1), b"value3")
				.unwrap(),
			Some(vec![142u8]),
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
		read_from_storage_returns_none_inner(false);
		read_from_storage_returns_none_inner(true);
	}
	fn read_from_storage_returns_none_inner(flagged: bool) {
		assert_eq!(test_trie(flagged).storage(b"non-existing-key").unwrap(), None);
	}

	#[test]
	fn pairs_are_not_empty_on_non_empty_storage() {
		pairs_are_not_empty_on_non_empty_storage_inner(false);
		pairs_are_not_empty_on_non_empty_storage_inner(true);
	}
	fn pairs_are_not_empty_on_non_empty_storage_inner(flagged: bool) {
		assert!(!test_trie(flagged).pairs().is_empty());
	}

	#[test]
	fn pairs_are_empty_on_empty_storage() {
		assert!(TrieBackend::<PrefixedMemoryDB<BlakeTwo256>, BlakeTwo256>::new(
			PrefixedMemoryDB::default(),
			Default::default(),
			Default::default(),
		)
		.pairs()
		.is_empty());
	}

	#[test]
	fn storage_root_is_non_default() {
		storage_root_is_non_default_inner(false);
		storage_root_is_non_default_inner(true);
	}
	fn storage_root_is_non_default_inner(flagged: bool) {
		assert!(test_trie(flagged).storage_root(iter::empty()).0 != H256::repeat_byte(0));
	}

	#[test]
	fn storage_root_transaction_is_non_empty() {
		storage_root_transaction_is_non_empty_inner(false);
		storage_root_transaction_is_non_empty_inner(true);
	}
	fn storage_root_transaction_is_non_empty_inner(flagged: bool) {
		let (new_root, mut tx) =
			test_trie(flagged).storage_root(iter::once((&b"new-key"[..], Some(&b"new-value"[..]))));
		assert!(!tx.drain().is_empty());
		assert!(new_root != test_trie(false).storage_root(iter::empty()).0);
	}

	#[test]
	fn prefix_walking_works() {
		prefix_walking_works_inner(false);
		prefix_walking_works_inner(true);
	}
	fn prefix_walking_works_inner(flagged: bool) {
		let trie = test_trie(flagged);

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
