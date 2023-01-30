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

//! Trie-based state machine backend.

#[cfg(feature = "std")]
use crate::backend::AsTrieBackend;
use crate::{
	trie_backend_essence::{TrieBackendEssence, TrieBackendStorage},
	Backend, StorageKey, StorageValue,
};
use codec::Codec;
#[cfg(feature = "std")]
use hash_db::HashDB;
use hash_db::Hasher;
use sp_core::storage::{ChildInfo, StateVersion};
use sp_std::vec::Vec;
#[cfg(feature = "std")]
use sp_trie::{cache::LocalTrieCache, recorder::Recorder};
#[cfg(feature = "std")]
use sp_trie::{MemoryDB, StorageProof};

/// Dummy type to be used in `no_std`.
///
/// This is required to have the type available for [`TrieBackendBuilder`] and [`TrieBackend`].
#[cfg(not(feature = "std"))]
pub struct LocalTrieCache<H>(sp_std::marker::PhantomData<H>);

/// Special trait to support taking the [`LocalTrieCache`] by value or by reference.
///
/// This trait is internal use only and to emphasize this, the trait is sealed.
pub trait AsLocalTrieCache<H: Hasher>: sealed::Sealed {
	/// Returns `self` as [`LocalTrieCache`].
	#[cfg(feature = "std")]
	fn as_local_trie_cache(&self) -> &LocalTrieCache<H>;
}

impl<H: Hasher> AsLocalTrieCache<H> for LocalTrieCache<H> {
	#[cfg(feature = "std")]
	fn as_local_trie_cache(&self) -> &LocalTrieCache<H> {
		self
	}
}

#[cfg(feature = "std")]
impl<H: Hasher> AsLocalTrieCache<H> for &LocalTrieCache<H> {
	fn as_local_trie_cache(&self) -> &LocalTrieCache<H> {
		self
	}
}

/// Special module that contains the `Sealed` trait.
mod sealed {
	use super::*;

	/// A special trait which prevents externals to implement the [`AsLocalTrieCache`] outside
	/// of this crate.
	pub trait Sealed {}

	impl<H: Hasher> Sealed for LocalTrieCache<H> {}
	impl<H: Hasher> Sealed for &LocalTrieCache<H> {}
}

/// Builder for creating a [`TrieBackend`].
pub struct TrieBackendBuilder<S: TrieBackendStorage<H>, H: Hasher, C = LocalTrieCache<H>> {
	storage: S,
	root: H::Out,
	#[cfg(feature = "std")]
	recorder: Option<Recorder<H>>,
	cache: Option<C>,
}

impl<S, H> TrieBackendBuilder<S, H, LocalTrieCache<H>>
where
	S: TrieBackendStorage<H>,
	H: Hasher,
{
	/// Create a new builder instance.
	pub fn new(storage: S, root: H::Out) -> Self {
		Self {
			storage,
			root,
			#[cfg(feature = "std")]
			recorder: None,
			cache: None,
		}
	}
}

impl<S, H, C> TrieBackendBuilder<S, H, C>
where
	S: TrieBackendStorage<H>,
	H: Hasher,
{
	/// Wrap the given [`TrieBackend`].
	///
	/// This can be used for example if all accesses to the trie should
	/// be recorded while some other functionality still uses the non-recording
	/// backend.
	///
	/// The backend storage and the cache will be taken from `other`.
	pub fn wrap(other: &TrieBackend<S, H, C>) -> TrieBackendBuilder<&S, H, &C> {
		TrieBackendBuilder {
			storage: other.essence.backend_storage(),
			root: *other.essence.root(),
			#[cfg(feature = "std")]
			recorder: None,
			#[cfg(feature = "std")]
			cache: other.essence.trie_node_cache.as_ref(),
			#[cfg(not(feature = "std"))]
			cache: None,
		}
	}

	/// Use the given optional `recorder` for the to be configured [`TrieBackend`].
	#[cfg(feature = "std")]
	pub fn with_optional_recorder(self, recorder: Option<Recorder<H>>) -> Self {
		Self { recorder, ..self }
	}

	/// Use the given `recorder` for the to be configured [`TrieBackend`].
	#[cfg(feature = "std")]
	pub fn with_recorder(self, recorder: Recorder<H>) -> Self {
		Self { recorder: Some(recorder), ..self }
	}

	/// Use the given optional `cache` for the to be configured [`TrieBackend`].
	#[cfg(feature = "std")]
	pub fn with_optional_cache<LC>(self, cache: Option<LC>) -> TrieBackendBuilder<S, H, LC> {
		TrieBackendBuilder {
			cache,
			root: self.root,
			storage: self.storage,
			recorder: self.recorder,
		}
	}

	/// Use the given `cache` for the to be configured [`TrieBackend`].
	#[cfg(feature = "std")]
	pub fn with_cache<LC>(self, cache: LC) -> TrieBackendBuilder<S, H, LC> {
		TrieBackendBuilder {
			cache: Some(cache),
			root: self.root,
			storage: self.storage,
			recorder: self.recorder,
		}
	}

	/// Build the configured [`TrieBackend`].
	#[cfg(feature = "std")]
	pub fn build(self) -> TrieBackend<S, H, C> {
		TrieBackend {
			essence: TrieBackendEssence::new_with_cache_and_recorder(
				self.storage,
				self.root,
				self.cache,
				self.recorder,
			),
		}
	}

	/// Build the configured [`TrieBackend`].
	#[cfg(not(feature = "std"))]
	pub fn build(self) -> TrieBackend<S, H, C> {
		let _ = self.cache;

		TrieBackend { essence: TrieBackendEssence::new(self.storage, self.root) }
	}
}

/// Patricia trie-based backend. Transaction type is an overlay of changes to commit.
pub struct TrieBackend<S: TrieBackendStorage<H>, H: Hasher, C = LocalTrieCache<H>> {
	pub(crate) essence: TrieBackendEssence<S, H, C>,
}

impl<S: TrieBackendStorage<H>, H: Hasher, C: AsLocalTrieCache<H> + Send + Sync> TrieBackend<S, H, C>
where
	H::Out: Codec,
{
	/// Get backend essence reference.
	pub fn essence(&self) -> &TrieBackendEssence<S, H, C> {
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

	/// Extract the [`StorageProof`].
	///
	/// This only returns `Some` when there was a recorder set.
	#[cfg(feature = "std")]
	pub fn extract_proof(mut self) -> Option<StorageProof> {
		self.essence.recorder.take().map(|r| r.drain_storage_proof())
	}
}

impl<S: TrieBackendStorage<H>, H: Hasher, C: AsLocalTrieCache<H>> sp_std::fmt::Debug
	for TrieBackend<S, H, C>
{
	fn fmt(&self, f: &mut sp_std::fmt::Formatter<'_>) -> sp_std::fmt::Result {
		write!(f, "TrieBackend")
	}
}

impl<S: TrieBackendStorage<H>, H: Hasher, C: AsLocalTrieCache<H> + Send + Sync> Backend<H>
	for TrieBackend<S, H, C>
where
	H::Out: Ord + Codec,
{
	type Error = crate::DefaultError;
	type Transaction = S::Overlay;
	type TrieBackendStorage = S;

	fn storage_hash(&self, key: &[u8]) -> Result<Option<H::Out>, Self::Error> {
		self.essence.storage_hash(key)
	}

	fn storage(&self, key: &[u8]) -> Result<Option<StorageValue>, Self::Error> {
		self.essence.storage(key)
	}

	fn child_storage_hash(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Result<Option<H::Out>, Self::Error> {
		self.essence.child_storage_hash(child_info, key)
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
		start_at: Option<&[u8]>,
		f: F,
	) {
		self.essence.apply_to_keys_while(child_info, prefix, start_at, f)
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
		self.essence.pairs()
	}

	fn keys(&self, prefix: &[u8]) -> Vec<StorageKey> {
		self.essence.keys(prefix)
	}

	fn storage_root<'a>(
		&self,
		delta: impl Iterator<Item = (&'a [u8], Option<&'a [u8]>)>,
		state_version: StateVersion,
	) -> (H::Out, Self::Transaction)
	where
		H::Out: Ord,
	{
		self.essence.storage_root(delta, state_version)
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
		self.essence.child_storage_root(child_info, delta, state_version)
	}

	fn register_overlay_stats(&self, _stats: &crate::stats::StateMachineStats) {}

	fn usage_info(&self) -> crate::UsageInfo {
		crate::UsageInfo::empty()
	}

	fn wipe(&self) -> Result<(), Self::Error> {
		Ok(())
	}
}

#[cfg(feature = "std")]
impl<S: TrieBackendStorage<H>, H: Hasher, C> AsTrieBackend<H, C> for TrieBackend<S, H, C> {
	type TrieBackendStorage = S;

	fn as_trie_backend(&self) -> &TrieBackend<S, H, C> {
		self
	}
}

/// Create a backend used for checking the proof, using `H` as hasher.
///
/// `proof` and `root` must match, i.e. `root` must be the correct root of `proof` nodes.
#[cfg(feature = "std")]
pub fn create_proof_check_backend<H>(
	root: H::Out,
	proof: StorageProof,
) -> Result<TrieBackend<MemoryDB<H>, H>, Box<dyn crate::Error>>
where
	H: Hasher,
	H::Out: Codec,
{
	let db = proof.into_memory_db();

	if db.contains(&root, hash_db::EMPTY_PREFIX) {
		Ok(TrieBackendBuilder::new(db, root).build())
	} else {
		Err(Box::new(crate::ExecutionError::InvalidProof))
	}
}

#[cfg(test)]
pub mod tests {
	use crate::{new_in_mem, InMemoryBackend};

	use super::*;
	use codec::Encode;
	use sp_core::H256;
	use sp_runtime::traits::BlakeTwo256;
	use sp_trie::{
		cache::{CacheSize, SharedTrieCache},
		trie_types::{TrieDBBuilder, TrieDBMutBuilderV0, TrieDBMutBuilderV1},
		KeySpacedDBMut, PrefixedKey, PrefixedMemoryDB, Trie, TrieCache, TrieMut,
	};
	use std::{collections::HashSet, iter};
	use trie_db::NodeCodec;

	const CHILD_KEY_1: &[u8] = b"sub1";

	type Recorder = sp_trie::recorder::Recorder<BlakeTwo256>;
	type Cache = LocalTrieCache<BlakeTwo256>;
	type SharedCache = SharedTrieCache<BlakeTwo256>;

	macro_rules! parameterized_test {
		($name:ident, $internal_name:ident) => {
			#[test]
			fn $name() {
				let parameters = vec![
					(StateVersion::V0, None, None),
					(StateVersion::V0, Some(SharedCache::new(CacheSize::unlimited())), None),
					(StateVersion::V0, None, Some(Recorder::default())),
					(
						StateVersion::V0,
						Some(SharedCache::new(CacheSize::unlimited())),
						Some(Recorder::default()),
					),
					(StateVersion::V1, None, None),
					(StateVersion::V1, Some(SharedCache::new(CacheSize::unlimited())), None),
					(StateVersion::V1, None, Some(Recorder::default())),
					(
						StateVersion::V1,
						Some(SharedCache::new(CacheSize::unlimited())),
						Some(Recorder::default()),
					),
				];

				for (version, cache, recorder) in parameters {
					eprintln!(
						"Running with version {:?}, cache enabled {} and recorder enabled {}",
						version,
						cache.is_some(),
						recorder.is_some()
					);

					let cache = cache.as_ref().map(|c| c.local_cache());

					$internal_name(version, cache, recorder.clone());
				}
			}
		};
	}

	pub(crate) fn test_db(state_version: StateVersion) -> (PrefixedMemoryDB<BlakeTwo256>, H256) {
		let child_info = ChildInfo::new_default(CHILD_KEY_1);
		let mut root = H256::default();
		let mut mdb = PrefixedMemoryDB::<BlakeTwo256>::default();
		{
			let mut mdb = KeySpacedDBMut::new(&mut mdb, child_info.keyspace());
			match state_version {
				StateVersion::V0 => {
					let mut trie = TrieDBMutBuilderV0::new(&mut mdb, &mut root).build();
					trie.insert(b"value3", &[142; 33]).expect("insert failed");
					trie.insert(b"value4", &[124; 33]).expect("insert failed");
				},
				StateVersion::V1 => {
					let mut trie = TrieDBMutBuilderV1::new(&mut mdb, &mut root).build();
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
					let trie = TrieDBMutBuilderV0::new(&mut mdb, &mut root).build();
					build(trie, &child_info, &sub_root[..])
				},
				StateVersion::V1 => {
					let trie = TrieDBMutBuilderV1::new(&mut mdb, &mut root).build();
					build(trie, &child_info, &sub_root[..])
				},
			};
		}
		(mdb, root)
	}

	pub(crate) fn test_trie(
		hashed_value: StateVersion,
		cache: Option<Cache>,
		recorder: Option<Recorder>,
	) -> TrieBackend<PrefixedMemoryDB<BlakeTwo256>, BlakeTwo256> {
		let (mdb, root) = test_db(hashed_value);

		TrieBackendBuilder::new(mdb, root)
			.with_optional_cache(cache)
			.with_optional_recorder(recorder)
			.build()
	}

	parameterized_test!(read_from_storage_returns_some, read_from_storage_returns_some_inner);
	fn read_from_storage_returns_some_inner(
		state_version: StateVersion,
		cache: Option<Cache>,
		recorder: Option<Recorder>,
	) {
		assert_eq!(
			test_trie(state_version, cache, recorder).storage(b"key").unwrap(),
			Some(b"value".to_vec())
		);
	}

	parameterized_test!(
		read_from_child_storage_returns_some,
		read_from_child_storage_returns_some_inner
	);
	fn read_from_child_storage_returns_some_inner(
		state_version: StateVersion,
		cache: Option<Cache>,
		recorder: Option<Recorder>,
	) {
		let test_trie = test_trie(state_version, cache, recorder);
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

	parameterized_test!(read_from_storage_returns_none, read_from_storage_returns_none_inner);
	fn read_from_storage_returns_none_inner(
		state_version: StateVersion,
		cache: Option<Cache>,
		recorder: Option<Recorder>,
	) {
		assert_eq!(
			test_trie(state_version, cache, recorder).storage(b"non-existing-key").unwrap(),
			None
		);
	}

	parameterized_test!(
		pairs_are_not_empty_on_non_empty_storage,
		pairs_are_not_empty_on_non_empty_storage_inner
	);
	fn pairs_are_not_empty_on_non_empty_storage_inner(
		state_version: StateVersion,
		cache: Option<Cache>,
		recorder: Option<Recorder>,
	) {
		assert!(!test_trie(state_version, cache, recorder).pairs().is_empty());
	}

	#[test]
	fn pairs_are_empty_on_empty_storage() {
		assert!(TrieBackendBuilder::<PrefixedMemoryDB<BlakeTwo256>, BlakeTwo256>::new(
			PrefixedMemoryDB::default(),
			Default::default(),
		)
		.build()
		.pairs()
		.is_empty());
	}

	parameterized_test!(storage_root_is_non_default, storage_root_is_non_default_inner);
	fn storage_root_is_non_default_inner(
		state_version: StateVersion,
		cache: Option<Cache>,
		recorder: Option<Recorder>,
	) {
		assert!(
			test_trie(state_version, cache, recorder)
				.storage_root(iter::empty(), state_version)
				.0 != H256::repeat_byte(0)
		);
	}

	parameterized_test!(
		storage_root_transaction_is_non_empty,
		storage_root_transaction_is_non_empty_inner
	);
	fn storage_root_transaction_is_non_empty_inner(
		state_version: StateVersion,
		cache: Option<Cache>,
		recorder: Option<Recorder>,
	) {
		let (new_root, mut tx) = test_trie(state_version, cache, recorder)
			.storage_root(iter::once((&b"new-key"[..], Some(&b"new-value"[..]))), state_version);
		assert!(!tx.drain().is_empty());
		assert!(
			new_root !=
				test_trie(state_version, None, None)
					.storage_root(iter::empty(), state_version)
					.0
		);
	}

	parameterized_test!(prefix_walking_works, prefix_walking_works_inner);
	fn prefix_walking_works_inner(
		state_version: StateVersion,
		cache: Option<Cache>,
		recorder: Option<Recorder>,
	) {
		let trie = test_trie(state_version, cache, recorder);

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

	parameterized_test!(
		keys_with_empty_prefix_returns_all_keys,
		keys_with_empty_prefix_returns_all_keys_inner
	);
	fn keys_with_empty_prefix_returns_all_keys_inner(
		state_version: StateVersion,
		cache: Option<Cache>,
		recorder: Option<Recorder>,
	) {
		let (test_db, test_root) = test_db(state_version);
		let expected = TrieDBBuilder::new(&test_db, &test_root)
			.build()
			.iter()
			.unwrap()
			.map(|d| d.unwrap().0.to_vec())
			.collect::<Vec<_>>();

		let trie = test_trie(state_version, cache, recorder);
		let keys = trie.keys(&[]);

		assert_eq!(expected, keys);
	}

	parameterized_test!(
		proof_is_empty_until_value_is_read,
		proof_is_empty_until_value_is_read_inner
	);
	fn proof_is_empty_until_value_is_read_inner(
		state_version: StateVersion,
		cache: Option<Cache>,
		recorder: Option<Recorder>,
	) {
		let trie_backend = test_trie(state_version, cache, recorder);
		assert!(TrieBackendBuilder::wrap(&trie_backend)
			.with_recorder(Recorder::default())
			.build()
			.extract_proof()
			.unwrap()
			.is_empty());
	}

	parameterized_test!(
		proof_is_non_empty_after_value_is_read,
		proof_is_non_empty_after_value_is_read_inner
	);
	fn proof_is_non_empty_after_value_is_read_inner(
		state_version: StateVersion,
		cache: Option<Cache>,
		recorder: Option<Recorder>,
	) {
		let trie_backend = test_trie(state_version, cache, recorder);
		let backend = TrieBackendBuilder::wrap(&trie_backend)
			.with_recorder(Recorder::default())
			.build();
		assert_eq!(backend.storage(b"key").unwrap(), Some(b"value".to_vec()));
		assert!(!backend.extract_proof().unwrap().is_empty());
	}

	#[test]
	fn proof_is_invalid_when_does_not_contains_root() {
		let result = create_proof_check_backend::<BlakeTwo256>(
			H256::from_low_u64_be(1),
			StorageProof::empty(),
		);
		assert!(result.is_err());
	}

	parameterized_test!(passes_through_backend_calls, passes_through_backend_calls_inner);
	fn passes_through_backend_calls_inner(
		state_version: StateVersion,
		cache: Option<Cache>,
		recorder: Option<Recorder>,
	) {
		let trie_backend = test_trie(state_version, cache, recorder);
		let proving_backend = TrieBackendBuilder::wrap(&trie_backend)
			.with_recorder(Recorder::default())
			.build();
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

		let trie = in_memory.as_trie_backend();
		let trie_root = trie.storage_root(std::iter::empty(), state_version).0;
		assert_eq!(in_memory_root, trie_root);
		value_range
			.clone()
			.for_each(|i| assert_eq!(trie.storage(&[i]).unwrap().unwrap(), vec![i; size_content]));

		for cache in [Some(SharedTrieCache::new(CacheSize::unlimited())), None] {
			// Run multiple times to have a different cache conditions.
			for i in 0..5 {
				if let Some(cache) = &cache {
					if i == 2 {
						cache.reset_node_cache();
					} else if i == 3 {
						cache.reset_value_cache();
					}
				}

				let proving = TrieBackendBuilder::wrap(&trie)
					.with_recorder(Recorder::default())
					.with_optional_cache(cache.as_ref().map(|c| c.local_cache()))
					.build();
				assert_eq!(proving.storage(&[42]).unwrap().unwrap(), vec![42; size_content]);

				let proof = proving.extract_proof().unwrap();

				let proof_check =
					create_proof_check_backend::<BlakeTwo256>(in_memory_root.into(), proof)
						.unwrap();
				assert_eq!(proof_check.storage(&[42]).unwrap().unwrap(), vec![42; size_content]);
			}
		}
	}

	#[test]
	fn proof_record_works_with_iter() {
		proof_record_works_with_iter_inner(StateVersion::V0);
		proof_record_works_with_iter_inner(StateVersion::V1);
	}
	fn proof_record_works_with_iter_inner(state_version: StateVersion) {
		for cache in [Some(SharedTrieCache::new(CacheSize::unlimited())), None] {
			// Run multiple times to have a different cache conditions.
			for i in 0..5 {
				if let Some(cache) = &cache {
					if i == 2 {
						cache.reset_node_cache();
					} else if i == 3 {
						cache.reset_value_cache();
					}
				}

				let contents = (0..64).map(|i| (vec![i], Some(vec![i]))).collect::<Vec<_>>();
				let in_memory = InMemoryBackend::<BlakeTwo256>::default();
				let in_memory = in_memory.update(vec![(None, contents)], state_version);
				let in_memory_root = in_memory.storage_root(std::iter::empty(), state_version).0;
				(0..64)
					.for_each(|i| assert_eq!(in_memory.storage(&[i]).unwrap().unwrap(), vec![i]));

				let trie = in_memory.as_trie_backend();
				let trie_root = trie.storage_root(std::iter::empty(), state_version).0;
				assert_eq!(in_memory_root, trie_root);
				(0..64).for_each(|i| assert_eq!(trie.storage(&[i]).unwrap().unwrap(), vec![i]));

				let proving = TrieBackendBuilder::wrap(&trie)
					.with_recorder(Recorder::default())
					.with_optional_cache(cache.as_ref().map(|c| c.local_cache()))
					.build();

				(0..63).for_each(|i| {
					assert_eq!(proving.next_storage_key(&[i]).unwrap(), Some(vec![i + 1]))
				});

				let proof = proving.extract_proof().unwrap();

				let proof_check =
					create_proof_check_backend::<BlakeTwo256>(in_memory_root.into(), proof)
						.unwrap();
				(0..63).for_each(|i| {
					assert_eq!(proof_check.next_storage_key(&[i]).unwrap(), Some(vec![i + 1]))
				});
			}
		}
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
		let in_memory = new_in_mem::<BlakeTwo256, PrefixedKey<BlakeTwo256>>();
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

		for cache in [Some(SharedTrieCache::new(CacheSize::unlimited())), None] {
			// Run multiple times to have a different cache conditions.
			for i in 0..5 {
				eprintln!("Running with cache {}, iteration {}", cache.is_some(), i);

				if let Some(cache) = &cache {
					if i == 2 {
						cache.reset_node_cache();
					} else if i == 3 {
						cache.reset_value_cache();
					}
				}

				let trie = in_memory.as_trie_backend();
				let trie_root = trie.storage_root(std::iter::empty(), state_version).0;
				assert_eq!(in_memory_root, trie_root);
				(0..64).for_each(|i| assert_eq!(trie.storage(&[i]).unwrap().unwrap(), vec![i]));

				let proving = TrieBackendBuilder::wrap(&trie)
					.with_recorder(Recorder::default())
					.with_optional_cache(cache.as_ref().map(|c| c.local_cache()))
					.build();
				assert_eq!(proving.storage(&[42]).unwrap().unwrap(), vec![42]);

				let proof = proving.extract_proof().unwrap();

				let proof_check =
					create_proof_check_backend::<BlakeTwo256>(in_memory_root.into(), proof)
						.unwrap();
				assert!(proof_check.storage(&[0]).is_err());
				assert_eq!(proof_check.storage(&[42]).unwrap().unwrap(), vec![42]);
				// note that it is include in root because proof close
				assert_eq!(proof_check.storage(&[41]).unwrap().unwrap(), vec![41]);
				assert_eq!(proof_check.storage(&[64]).unwrap(), None);

				let proving = TrieBackendBuilder::wrap(&trie)
					.with_recorder(Recorder::default())
					.with_optional_cache(cache.as_ref().map(|c| c.local_cache()))
					.build();
				assert_eq!(proving.child_storage(child_info_1, &[64]), Ok(Some(vec![64])));
				assert_eq!(proving.child_storage(child_info_1, &[25]), Ok(None));
				assert_eq!(proving.child_storage(child_info_2, &[14]), Ok(Some(vec![14])));
				assert_eq!(proving.child_storage(child_info_2, &[25]), Ok(None));

				let proof = proving.extract_proof().unwrap();
				let proof_check =
					create_proof_check_backend::<BlakeTwo256>(in_memory_root.into(), proof)
						.unwrap();
				assert_eq!(
					proof_check.child_storage(child_info_1, &[64]).unwrap().unwrap(),
					vec![64]
				);
				assert_eq!(proof_check.child_storage(child_info_1, &[25]).unwrap(), None);

				assert_eq!(
					proof_check.child_storage(child_info_2, &[14]).unwrap().unwrap(),
					vec![14]
				);
				assert_eq!(proof_check.child_storage(child_info_2, &[25]).unwrap(), None);
			}
		}
	}

	/// This tests an edge case when recording a child trie access with a cache.
	///
	/// The accessed value/node is in the cache, but not the nodes to get to this value. So,
	/// the recorder will need to traverse the trie to access these nodes from the backend when the
	/// storage proof is generated.
	#[test]
	fn child_proof_recording_with_edge_cases_works() {
		child_proof_recording_with_edge_cases_works_inner(StateVersion::V0);
		child_proof_recording_with_edge_cases_works_inner(StateVersion::V1);
	}
	fn child_proof_recording_with_edge_cases_works_inner(state_version: StateVersion) {
		let child_info_1 = ChildInfo::new_default(b"sub1");
		let child_info_1 = &child_info_1;
		let contents = vec![
			(None, (0..64).map(|i| (vec![i], Some(vec![i]))).collect::<Vec<_>>()),
			(
				Some(child_info_1.clone()),
				(28..65)
					.map(|i| (vec![i], Some(vec![i])))
					// Some big value to ensure we get a new node
					.chain(std::iter::once((vec![65], Some(vec![65; 128]))))
					.collect(),
			),
		];
		let in_memory = new_in_mem::<BlakeTwo256, PrefixedKey<BlakeTwo256>>();
		let in_memory = in_memory.update(contents, state_version);
		let child_storage_keys = vec![child_info_1.to_owned()];
		let in_memory_root = in_memory
			.full_storage_root(
				std::iter::empty(),
				child_storage_keys.iter().map(|k| (k, std::iter::empty())),
				state_version,
			)
			.0;

		let child_1_root =
			in_memory.child_storage_root(child_info_1, std::iter::empty(), state_version).0;
		let trie = in_memory.as_trie_backend();
		let nodes = {
			let backend = TrieBackendBuilder::wrap(trie).with_recorder(Default::default()).build();
			let value = backend.child_storage(child_info_1, &[65]).unwrap().unwrap();
			let value_hash = BlakeTwo256::hash(&value);
			assert_eq!(value, vec![65; 128]);

			let proof = backend.extract_proof().unwrap();

			let mut nodes = Vec::new();
			for node in proof.into_iter_nodes() {
				let hash = BlakeTwo256::hash(&node);
				// Only insert the node/value that contains the important data.
				if hash != value_hash {
					let node = sp_trie::NodeCodec::<BlakeTwo256>::decode(&node)
						.unwrap()
						.to_owned_node::<sp_trie::LayoutV1<BlakeTwo256>>()
						.unwrap();

					if let Some(data) = node.data() {
						if data == &vec![65; 128] {
							nodes.push((hash, node));
						}
					}
				} else if hash == value_hash {
					nodes.push((hash, trie_db::node::NodeOwned::Value(node.into(), hash)));
				}
			}

			nodes
		};

		let cache = SharedTrieCache::<BlakeTwo256>::new(CacheSize::unlimited());
		{
			let local_cache = cache.local_cache();
			let mut trie_cache = local_cache.as_trie_db_cache(child_1_root);

			// Put the value/node into the cache.
			for (hash, node) in nodes {
				trie_cache.get_or_insert_node(hash, &mut || Ok(node.clone())).unwrap();

				if let Some(data) = node.data() {
					trie_cache.cache_value_for_key(&[65], (data.clone(), hash).into());
				}
			}
		}

		{
			// Record the access
			let proving = TrieBackendBuilder::wrap(&trie)
				.with_recorder(Recorder::default())
				.with_cache(cache.local_cache())
				.build();
			assert_eq!(proving.child_storage(child_info_1, &[65]), Ok(Some(vec![65; 128])));

			let proof = proving.extract_proof().unwrap();
			// And check that we have a correct proof.
			let proof_check =
				create_proof_check_backend::<BlakeTwo256>(in_memory_root.into(), proof).unwrap();
			assert_eq!(
				proof_check.child_storage(child_info_1, &[65]).unwrap().unwrap(),
				vec![65; 128]
			);
		}
	}

	parameterized_test!(
		storage_proof_encoded_size_estimation_works,
		storage_proof_encoded_size_estimation_works_inner
	);
	fn storage_proof_encoded_size_estimation_works_inner(
		state_version: StateVersion,
		cache: Option<Cache>,
		recorder: Option<Recorder>,
	) {
		let has_cache = cache.is_some();
		let trie_backend = test_trie(state_version, cache, recorder);
		let keys = &[
			&b"key"[..],
			&b"value1"[..],
			&b"value2"[..],
			&b"doesnotexist"[..],
			&b"doesnotexist2"[..],
		];

		fn check_estimation(
			backend: TrieBackend<
				impl TrieBackendStorage<BlakeTwo256>,
				BlakeTwo256,
				&'_ LocalTrieCache<BlakeTwo256>,
			>,
			has_cache: bool,
		) {
			let estimation = backend.essence.recorder.as_ref().unwrap().estimate_encoded_size();
			let storage_proof = backend.extract_proof().unwrap();
			let storage_proof_size =
				storage_proof.into_nodes().into_iter().map(|n| n.encoded_size()).sum::<usize>();

			if has_cache {
				// Estimation is not entirely correct when we have values already cached.
				assert!(estimation >= storage_proof_size)
			} else {
				assert_eq!(storage_proof_size, estimation);
			}
		}

		for n in 0..keys.len() {
			let backend = TrieBackendBuilder::wrap(&trie_backend)
				.with_recorder(Recorder::default())
				.build();

			// Read n keys
			(0..n).for_each(|i| {
				backend.storage(keys[i]).unwrap();
			});

			// Check the estimation
			check_estimation(backend, has_cache);
		}
	}

	#[test]
	fn new_data_is_added_to_the_cache() {
		let shared_cache = SharedTrieCache::new(CacheSize::unlimited());
		let new_data = vec![
			(&b"new_data0"[..], Some(&b"0"[..])),
			(&b"new_data1"[..], Some(&b"1"[..])),
			(&b"new_data2"[..], Some(&b"2"[..])),
			(&b"new_data3"[..], Some(&b"3"[..])),
			(&b"new_data4"[..], Some(&b"4"[..])),
		];

		let new_root = {
			let trie = test_trie(StateVersion::V1, Some(shared_cache.local_cache()), None);
			trie.storage_root(new_data.clone().into_iter(), StateVersion::V1).0
		};

		let local_cache = shared_cache.local_cache();
		let mut cache = local_cache.as_trie_db_cache(new_root);
		// All the data should be cached now
		for (key, value) in new_data {
			assert_eq!(
				value.unwrap(),
				cache.lookup_value_for_key(key).unwrap().data().flatten().unwrap().as_ref()
			);
		}
	}

	/// Test to ensure that recording the same `key` for different tries works as expected.
	///
	/// Each trie stores a different value under the same key. The values are big enough to
	/// be not inlined with `StateVersion::V1`, this is important to test the expected behavior. The
	/// trie recorder is expected to differentiate key access based on the different storage roots
	/// of the tries.
	#[test]
	fn recording_same_key_access_in_different_tries() {
		recording_same_key_access_in_different_tries_inner(StateVersion::V0);
		recording_same_key_access_in_different_tries_inner(StateVersion::V1);
	}
	fn recording_same_key_access_in_different_tries_inner(state_version: StateVersion) {
		let key = b"test_key".to_vec();
		// Use some big values to ensure that we don't keep them inline
		let top_trie_val = vec![1; 1024];
		let child_trie_1_val = vec![2; 1024];
		let child_trie_2_val = vec![3; 1024];

		let child_info_1 = ChildInfo::new_default(b"sub1");
		let child_info_2 = ChildInfo::new_default(b"sub2");
		let child_info_1 = &child_info_1;
		let child_info_2 = &child_info_2;
		let contents = vec![
			(None, vec![(key.clone(), Some(top_trie_val.clone()))]),
			(Some(child_info_1.clone()), vec![(key.clone(), Some(child_trie_1_val.clone()))]),
			(Some(child_info_2.clone()), vec![(key.clone(), Some(child_trie_2_val.clone()))]),
		];
		let in_memory = new_in_mem::<BlakeTwo256, PrefixedKey<BlakeTwo256>>();
		let in_memory = in_memory.update(contents, state_version);
		let child_storage_keys = vec![child_info_1.to_owned(), child_info_2.to_owned()];
		let in_memory_root = in_memory
			.full_storage_root(
				std::iter::empty(),
				child_storage_keys.iter().map(|k| (k, std::iter::empty())),
				state_version,
			)
			.0;
		assert_eq!(in_memory.storage(&key).unwrap().unwrap(), top_trie_val);
		assert_eq!(in_memory.child_storage(child_info_1, &key).unwrap().unwrap(), child_trie_1_val);
		assert_eq!(in_memory.child_storage(child_info_2, &key).unwrap().unwrap(), child_trie_2_val);

		for cache in [Some(SharedTrieCache::new(CacheSize::unlimited())), None] {
			// Run multiple times to have a different cache conditions.
			for i in 0..5 {
				eprintln!("Running with cache {}, iteration {}", cache.is_some(), i);

				if let Some(cache) = &cache {
					if i == 2 {
						cache.reset_node_cache();
					} else if i == 3 {
						cache.reset_value_cache();
					}
				}

				let trie = in_memory.as_trie_backend();
				let trie_root = trie.storage_root(std::iter::empty(), state_version).0;
				assert_eq!(in_memory_root, trie_root);

				let proving = TrieBackendBuilder::wrap(&trie)
					.with_recorder(Recorder::default())
					.with_optional_cache(cache.as_ref().map(|c| c.local_cache()))
					.build();
				assert_eq!(proving.storage(&key).unwrap().unwrap(), top_trie_val);
				assert_eq!(
					proving.child_storage(child_info_1, &key).unwrap().unwrap(),
					child_trie_1_val
				);
				assert_eq!(
					proving.child_storage(child_info_2, &key).unwrap().unwrap(),
					child_trie_2_val
				);

				let proof = proving.extract_proof().unwrap();

				let proof_check =
					create_proof_check_backend::<BlakeTwo256>(in_memory_root.into(), proof)
						.unwrap();

				assert_eq!(proof_check.storage(&key).unwrap().unwrap(), top_trie_val);
				assert_eq!(
					proof_check.child_storage(child_info_1, &key).unwrap().unwrap(),
					child_trie_1_val
				);
				assert_eq!(
					proof_check.child_storage(child_info_2, &key).unwrap().unwrap(),
					child_trie_2_val
				);
			}
		}
	}
}
