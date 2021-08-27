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
use sp_core::{
	state_version::StateVersion,
	storage::{ChildInfo, ChildType},
};
use sp_std::{boxed::Box, vec::Vec};
use sp_trie::{
	child_delta_trie_root, delta_trie_root, empty_child_trie_root,
	trie_types::{TrieDB, TrieError},
	Layout, Trie,
};
#[cfg(feature = "std")]
use log::info;

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
		TrieBackend { essence: TrieBackendEssence::new(storage, root), state_version }
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
					StateVersion::V0 => sp_trie::Layout::default(),
					StateVersion::V1 { threshold } => sp_trie::Layout::with_alt_hashing(threshold),
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
			StateVersion::V0 => sp_trie::Layout::default(),
			StateVersion::V1 { threshold } => sp_trie::Layout::with_alt_hashing(threshold),
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

	fn state_version(&self) -> StateVersion {
		self.state_version.clone()
	}
}

/// Migration progress.
pub struct MigrateProgress<H> {
	/// Next key to migrate for top.
	pub current_top: Option<Vec<u8>>,
	/// Current migrated root of top trie.
	pub root: Option<H>,
	/// Next key to migrate with current migrated root for a child
	/// trie.
	/// When defined, `current_top` always point to the
	/// child trie root top location.
	pub current_child: Option<(Vec<u8>, H)>,
}

/// Migration storage.
pub struct MigrateStorage<'a, S, H>
where
	H: Hasher,
{
	overlay: &'a mut sp_trie::PrefixedMemoryDB<H>,
	storage: &'a S,
}

use hash_db::{self, AsHashDB, HashDB, HashDBRef, Prefix};
use sp_trie::DBValue;

impl<'a, S: 'a + TrieBackendStorage<H>, H: Hasher> hash_db::HashDB<H, DBValue>
	for MigrateStorage<'a, S, H>
{
	fn get(&self, key: &H::Out, prefix: Prefix) -> Option<DBValue> {
		if let Some(val) = HashDB::get(self.overlay, key, prefix) {
			Some(val)
		} else {
			match self.storage.get(&key, prefix) {
				Ok(x) => x,
				Err(e) => {
					warn!(target: "trie", "Failed to read from DB: {}", e);
					None
				},
			}
		}
	}

	fn access_from(&self, key: &H::Out, _at: Option<&H::Out>) -> Option<DBValue> {
		// call back to storage even if the overlay was hit.
		self.storage.access_from(key);
		None
	}

	fn contains(&self, key: &H::Out, prefix: Prefix) -> bool {
		HashDB::get(self, key, prefix).is_some()
	}

	fn insert(&mut self, prefix: Prefix, value: &[u8]) -> H::Out {
		HashDB::insert(self.overlay, prefix, value)
	}

	fn emplace(&mut self, key: H::Out, prefix: Prefix, value: DBValue) {
		HashDB::emplace(self.overlay, key, prefix, value)
	}

	fn emplace_ref(&mut self, key: &H::Out, prefix: Prefix, value: &[u8]) {
		HashDB::emplace_ref(self.overlay, key, prefix, value)
	}

	fn remove(&mut self, key: &H::Out, prefix: Prefix) {
		HashDB::remove(self.overlay, key, prefix)
	}
}

impl<'a, S: 'a + TrieBackendStorage<H>, H: Hasher> HashDBRef<H, DBValue>
	for MigrateStorage<'a, S, H>
{
	fn get(&self, key: &H::Out, prefix: Prefix) -> Option<DBValue> {
		HashDB::get(self, key, prefix)
	}

	fn access_from(&self, key: &H::Out, at: Option<&H::Out>) -> Option<DBValue> {
		HashDB::access_from(self, key, at)
	}

	fn contains(&self, key: &H::Out, prefix: Prefix) -> bool {
		HashDB::contains(self, key, prefix)
	}
}

impl<'a, S: 'a + TrieBackendStorage<H>, H: 'a + Hasher> AsHashDB<H, DBValue>
	for MigrateStorage<'a, S, H>
{
	fn as_hash_db<'b>(&'b self) -> &'b (dyn HashDB<H, DBValue> + 'b) {
		self
	}
	fn as_hash_db_mut<'b>(&'b mut self) -> &'b mut (dyn HashDB<H, DBValue> + 'b) {
		self
	}
}

#[cfg(feature = "std")]
fn error_version() -> crate::DefaultError {
	"Cannot migrate for given state versions".into()
}

#[cfg(not(feature = "std"))]
fn error_version() -> crate::DefaultError {
	crate::DefaultError
}

#[cfg(feature = "std")]
fn trie_error<H: Hasher>(e: &sp_trie::TrieError<Layout<H>>) -> crate::DefaultError {
	format!("Migrate trieDB error: {}", e)
}

#[cfg(not(feature = "std"))]
fn trie_error<H: Hasher>(_e: &sp_trie::TrieError<Layout<H>>) -> crate::DefaultError {
	crate::DefaultError
}

impl<S: TrieBackendStorage<H>, H: Hasher> TrieBackend<S, H>
where
	H::Out: Ord + Codec,
{
	/// Execute a state migration, new and removed node are
	/// directly written in the db update.
	pub fn migrate(
		&self,
		migration_from: StateVersion,
		migration_to: StateVersion,
		mut limit_size: Option<u64>,
		mut limit_items: Option<u64>,
		do_update: Option<&mut sp_trie::PrefixedMemoryDB<H>>,
		previous_block_updates: (&crate::StorageCollection, &crate::ChildStorageCollection),
		mut progress: MigrateProgress<H::Out>,
	) -> Result<MigrateProgress<H::Out>, crate::DefaultError> {
		use sp_trie::{TrieDB, TrieDBIterator, TrieDBMut, TrieMut};
		let dest_threshold = match (migration_from, migration_to, self.state_version) {
			(StateVersion::V0, StateVersion::V1 { threshold }, StateVersion::V0) => threshold,
			_ => return Err(error_version()),
		};
		let empty_value = sp_std::vec![23u8; dest_threshold as usize];
		let empty_value2 = sp_std::vec![0u8; dest_threshold as usize];
		let dest_layout = Layout::with_alt_hashing(dest_threshold);
		let mut in_mem;
		let without_payload;
		let overlay = if let Some(change) = do_update {
			without_payload = false;
			change
		} else {
			without_payload = true;
			in_mem = sp_trie::PrefixedMemoryDB::default();
			&mut in_mem
		};
		// Using same db with remove node is ok, but require locking state pruning.
		let mut dest_db =
			MigrateStorage::<S, H> { overlay, storage: self.essence.backend_storage() };
		if progress.root.is_none() {
			progress.root = Some(self.essence.root().clone());
		}
		let dest_root = progress.root.as_mut().expect("Lazy init above.");
		let ori_root = self.essence.root().clone();
		let ori = TrieDB::new_with_layout(&self.essence, &ori_root, Layout::default())
			.map_err(|e| trie_error::<H>(&*e))?;
		let mut dest = TrieDBMut::from_existing_with_layout(&mut dest_db, dest_root, dest_layout)
			.map_err(|e| trie_error::<H>(&*e))?;

		let iter = TrieDBIterator::new_prefixed_then_seek(
			&ori,
			&[],
			progress.current_top.as_ref().map(|s| s.as_slice()).unwrap_or(&[]),
		)
		.map_err(|e| trie_error::<H>(&*e))?;

		let mut total_top_size = 0u64;
		let mut total_written_top_size = 0u64;
		let mut total_top_items = 0u64;
		let mut total_written_top_items = 0u64;
		for elt in iter {
			let (key, value) = elt.map_err(|e| trie_error::<H>(&*e))?;
			if let Some(limit_size) = limit_size.as_mut() {
				if *limit_size < value.len() as u64 {
					progress.current_top = Some(key);
					break
				}
				*limit_size -= value.len() as u64;
			}
			if let Some(limit_items) = limit_items.as_mut() {
				if *limit_items == 0 {
					progress.current_top = Some(key);
					break
				}
				*limit_items -= 1;
			}
			total_top_size += value.len() as u64;
			total_top_items += 1;
			if value.len() >= dest_threshold as usize {
				total_written_top_size += value.len() as u64;
				total_written_top_items += 1;
				// Force a change so triedbmut do not ignore
				// setting the same value.
				if value != empty_value {
					dest.insert(key.as_slice(), empty_value.as_slice())
						.map_err(|e| trie_error::<H>(&*e))?;
				} else {
					dest.insert(key.as_slice(), empty_value2.as_slice())
						.map_err(|e| trie_error::<H>(&*e))?;
				}
				dest.insert(key.as_slice(), value.as_slice())
					.map_err(|e| trie_error::<H>(&*e))?;
			}
		}

		// Set again changes from current block in dest (import may have overwrite them,
		// or may have change a previous block migration change).c
		for (key, value) in previous_block_updates.0.iter() {
			if let Some(value) = value.as_ref() {
				if without_payload || value.len() >= dest_threshold as usize {
					if progress.current_top.as_ref().map(|end| key < end).unwrap_or(true) {
						dest.insert(key.as_slice(), value.as_slice())
							.map_err(|e| trie_error::<H>(&*e))?;
					}
				}
			} else {
				if progress.current_top.as_ref().map(|end| key < end).unwrap_or(true) {
					// rerun all remove in case we import old. .
					dest.remove(key.as_slice())
						.map_err(|e| trie_error::<H>(&*e))?;
				}
			}
		}
		// TODO same for child
		sp_std::mem::drop(ori);
		sp_std::mem::drop(dest);
		#[cfg(feature = "std")]
		info!("\n  
		total_top_size: {},\n  
		total_written_top_size: {},\n  
		total_top_items: {}, \n  
		total_written_top_items: {}, \n  
		",
		total_top_size,
		total_written_top_size,
		total_top_items,
		total_written_top_items,
		);
	
		Ok(progress)
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
		let state_version = if hashed_value {
			StateVersion::V1 { threshold: sp_core::storage::TEST_DEFAULT_ALT_HASH_THRESHOLD }
		} else {
			StateVersion::V0
		};

		TrieBackend::new(mdb, root, state_version)
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
