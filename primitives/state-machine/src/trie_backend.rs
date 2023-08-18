// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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
	backend::{IterArgs, StorageIterator},
	trie_backend_essence::{RawIter, TrieBackendEssence, TrieBackendStorage},
	Backend, StorageKey, StorageValue,
};

use codec::Codec;
#[cfg(feature = "std")]
use hash_db::HashDB;
use hash_db::Hasher;
use sp_core::storage::{ChildInfo, StateVersion};
use sp_trie::PrefixedMemoryDB;
#[cfg(feature = "std")]
use sp_trie::{
	cache::{LocalTrieCache, TrieCache},
	recorder::Recorder,
	MemoryDB, StorageProof,
};
#[cfg(not(feature = "std"))]
use sp_trie::{Error, NodeCodec};
use trie_db::TrieCache as TrieCacheT;
#[cfg(not(feature = "std"))]
use trie_db::{node::NodeOwned, CachedValue};

/// A provider of trie caches that are compatible with [`trie_db::TrieDB`].
pub trait TrieCacheProvider<H: Hasher> {
	/// Cache type that implements [`trie_db::TrieCache`].
	type Cache<'a>: TrieCacheT<sp_trie::NodeCodec<H>> + 'a
	where
		Self: 'a;

	/// Return a [`trie_db::TrieDB`] compatible cache.
	///
	/// The `storage_root` parameter should be the storage root of the used trie.
	fn as_trie_db_cache(&self, storage_root: H::Out) -> Self::Cache<'_>;

	/// Returns a cache that can be used with a [`trie_db::TrieDBMut`].
	///
	/// When finished with the operation on the trie, it is required to call [`Self::merge`] to
	/// merge the cached items for the correct `storage_root`.
	fn as_trie_db_mut_cache(&self) -> Self::Cache<'_>;

	/// Merge the cached data in `other` into the provider using the given `new_root`.
	///
	/// This must be used for the cache returned by [`Self::as_trie_db_mut_cache`] as otherwise the
	/// cached data is just thrown away.
	fn merge<'a>(&'a self, other: Self::Cache<'a>, new_root: H::Out);
}

#[cfg(feature = "std")]
impl<H: Hasher> TrieCacheProvider<H> for LocalTrieCache<H> {
	type Cache<'a> = TrieCache<'a, H> where H: 'a;

	fn as_trie_db_cache(&self, storage_root: H::Out) -> Self::Cache<'_> {
		self.as_trie_db_cache(storage_root)
	}

	fn as_trie_db_mut_cache(&self) -> Self::Cache<'_> {
		self.as_trie_db_mut_cache()
	}

	fn merge<'a>(&'a self, other: Self::Cache<'a>, new_root: H::Out) {
		other.merge_into(self, new_root)
	}
}

#[cfg(feature = "std")]
impl<H: Hasher> TrieCacheProvider<H> for &LocalTrieCache<H> {
	type Cache<'a> = TrieCache<'a, H> where Self: 'a;

	fn as_trie_db_cache(&self, storage_root: H::Out) -> Self::Cache<'_> {
		(*self).as_trie_db_cache(storage_root)
	}

	fn as_trie_db_mut_cache(&self) -> Self::Cache<'_> {
		(*self).as_trie_db_mut_cache()
	}

	fn merge<'a>(&'a self, other: Self::Cache<'a>, new_root: H::Out) {
		other.merge_into(self, new_root)
	}
}

/// Cache provider that allows construction of a [`TrieBackend`] and satisfies the requirements, but
/// can never be instantiated.
#[cfg(not(feature = "std"))]
pub struct UnimplementedCacheProvider<H> {
	// Not strictly necessary, but the H bound allows to use this as a drop-in
	// replacement for the `LocalTrieCache` in no-std contexts.
	_phantom: core::marker::PhantomData<H>,
	// Statically prevents construction.
	_infallible: core::convert::Infallible,
}

#[cfg(not(feature = "std"))]
impl<H: Hasher> trie_db::TrieCache<NodeCodec<H>> for UnimplementedCacheProvider<H> {
	fn lookup_value_for_key(&mut self, _key: &[u8]) -> Option<&CachedValue<H::Out>> {
		unimplemented!()
	}

	fn cache_value_for_key(&mut self, _key: &[u8], _value: CachedValue<H::Out>) {
		unimplemented!()
	}

	fn get_or_insert_node(
		&mut self,
		_hash: H::Out,
		_fetch_node: &mut dyn FnMut() -> trie_db::Result<NodeOwned<H::Out>, H::Out, Error<H::Out>>,
	) -> trie_db::Result<&NodeOwned<H::Out>, H::Out, Error<H::Out>> {
		unimplemented!()
	}

	fn get_node(&mut self, _hash: &H::Out) -> Option<&NodeOwned<H::Out>> {
		unimplemented!()
	}
}

#[cfg(not(feature = "std"))]
impl<H: Hasher> TrieCacheProvider<H> for UnimplementedCacheProvider<H> {
	type Cache<'a> = UnimplementedCacheProvider<H> where H: 'a;

	fn as_trie_db_cache(&self, _storage_root: <H as Hasher>::Out) -> Self::Cache<'_> {
		unimplemented!()
	}

	fn as_trie_db_mut_cache(&self) -> Self::Cache<'_> {
		unimplemented!()
	}

	fn merge<'a>(&'a self, _other: Self::Cache<'a>, _new_root: <H as Hasher>::Out) {
		unimplemented!()
	}
}

#[cfg(feature = "std")]
type DefaultCache<H> = LocalTrieCache<H>;

#[cfg(not(feature = "std"))]
type DefaultCache<H> = UnimplementedCacheProvider<H>;

/// Builder for creating a [`TrieBackend`].
pub struct TrieBackendBuilder<S: TrieBackendStorage<H>, H: Hasher, C = DefaultCache<H>> {
	storage: S,
	root: H::Out,
	#[cfg(feature = "std")]
	recorder: Option<Recorder<H>>,
	cache: Option<C>,
}

impl<S, H> TrieBackendBuilder<S, H, DefaultCache<H>>
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
	/// Create a new builder instance.
	pub fn new_with_cache(storage: S, root: H::Out, cache: C) -> Self {
		Self {
			storage,
			root,
			#[cfg(feature = "std")]
			recorder: None,
			cache: Some(cache),
		}
	}
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
			cache: other.essence.trie_node_cache.as_ref(),
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
	pub fn with_optional_cache<LC>(self, cache: Option<LC>) -> TrieBackendBuilder<S, H, LC> {
		TrieBackendBuilder {
			cache,
			root: self.root,
			storage: self.storage,
			#[cfg(feature = "std")]
			recorder: self.recorder,
		}
	}

	/// Use the given `cache` for the to be configured [`TrieBackend`].
	pub fn with_cache<LC>(self, cache: LC) -> TrieBackendBuilder<S, H, LC> {
		TrieBackendBuilder {
			cache: Some(cache),
			root: self.root,
			storage: self.storage,
			#[cfg(feature = "std")]
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
			next_storage_key_cache: Default::default(),
		}
	}

	/// Build the configured [`TrieBackend`].
	#[cfg(not(feature = "std"))]
	pub fn build(self) -> TrieBackend<S, H, C> {
		TrieBackend {
			essence: TrieBackendEssence::new_with_cache(self.storage, self.root, self.cache),
			next_storage_key_cache: Default::default(),
		}
	}
}

/// A cached iterator.
struct CachedIter<S, H, C>
where
	H: Hasher,
{
	last_key: sp_std::vec::Vec<u8>,
	iter: RawIter<S, H, C>,
}

impl<S, H, C> Default for CachedIter<S, H, C>
where
	H: Hasher,
{
	fn default() -> Self {
		Self { last_key: Default::default(), iter: Default::default() }
	}
}

#[cfg(feature = "std")]
type CacheCell<T> = parking_lot::Mutex<T>;

#[cfg(not(feature = "std"))]
type CacheCell<T> = core::cell::RefCell<T>;

#[cfg(feature = "std")]
fn access_cache<T, R>(cell: &CacheCell<T>, callback: impl FnOnce(&mut T) -> R) -> R {
	callback(&mut *cell.lock())
}

#[cfg(not(feature = "std"))]
fn access_cache<T, R>(cell: &CacheCell<T>, callback: impl FnOnce(&mut T) -> R) -> R {
	callback(&mut *cell.borrow_mut())
}

/// Patricia trie-based backend. Transaction type is an overlay of changes to commit.
pub struct TrieBackend<S: TrieBackendStorage<H>, H: Hasher, C = DefaultCache<H>> {
	pub(crate) essence: TrieBackendEssence<S, H, C>,
	next_storage_key_cache: CacheCell<Option<CachedIter<S, H, C>>>,
}

impl<S: TrieBackendStorage<H>, H: Hasher, C: TrieCacheProvider<H> + Send + Sync>
	TrieBackend<S, H, C>
where
	H::Out: Codec,
{
	#[cfg(test)]
	pub(crate) fn from_essence(essence: TrieBackendEssence<S, H, C>) -> Self {
		Self { essence, next_storage_key_cache: Default::default() }
	}

	/// Get backend essence reference.
	pub fn essence(&self) -> &TrieBackendEssence<S, H, C> {
		&self.essence
	}

	/// Get backend storage reference.
	pub fn backend_storage_mut(&mut self) -> &mut S {
		self.essence.backend_storage_mut()
	}

	/// Get backend storage reference.
	pub fn backend_storage(&self) -> &S {
		self.essence.backend_storage()
	}

	/// Set trie root.
	pub fn set_root(&mut self, root: H::Out) {
		self.essence.set_root(root)
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

impl<S: TrieBackendStorage<H>, H: Hasher, C: TrieCacheProvider<H>> sp_std::fmt::Debug
	for TrieBackend<S, H, C>
{
	fn fmt(&self, f: &mut sp_std::fmt::Formatter<'_>) -> sp_std::fmt::Result {
		write!(f, "TrieBackend")
	}
}

impl<S: TrieBackendStorage<H>, H: Hasher, C: TrieCacheProvider<H> + Send + Sync> Backend<H>
	for TrieBackend<S, H, C>
where
	H::Out: Ord + Codec,
{
	type Error = crate::DefaultError;
	type TrieBackendStorage = S;
	type RawIter = crate::trie_backend_essence::RawIter<S, H, C>;

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
		let (is_cached, mut cache) = access_cache(&self.next_storage_key_cache, Option::take)
			.map(|cache| (cache.last_key == key, cache))
			.unwrap_or_default();

		if !is_cached {
			cache.iter = self.raw_iter(IterArgs {
				start_at: Some(key),
				start_at_exclusive: true,
				..IterArgs::default()
			})?
		};

		let next_key = match cache.iter.next_key(self) {
			None => return Ok(None),
			Some(Err(error)) => return Err(error),
			Some(Ok(next_key)) => next_key,
		};

		cache.last_key.clear();
		cache.last_key.extend_from_slice(&next_key);
		access_cache(&self.next_storage_key_cache, |cache_cell| cache_cell.replace(cache));

		#[cfg(debug_assertions)]
		debug_assert_eq!(
			self.essence
				.next_storage_key_slow(key)
				.expect(
					"fetching the next key through iterator didn't fail so this shouldn't either"
				)
				.as_ref(),
			Some(&next_key)
		);

		Ok(Some(next_key))
	}

	fn next_child_storage_key(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Result<Option<StorageKey>, Self::Error> {
		self.essence.next_child_storage_key(child_info, key)
	}

	fn raw_iter(&self, args: IterArgs) -> Result<Self::RawIter, Self::Error> {
		self.essence.raw_iter(args)
	}

	fn storage_root<'a>(
		&self,
		delta: impl Iterator<Item = (&'a [u8], Option<&'a [u8]>)>,
		state_version: StateVersion,
	) -> (H::Out, PrefixedMemoryDB<H>)
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
	) -> (H::Out, bool, PrefixedMemoryDB<H>)
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
		KeySpacedDBMut, PrefixedMemoryDB, Trie, TrieCache, TrieMut,
	};
	use std::iter;
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

	pub(crate) fn test_db_with_hex_keys(
		state_version: StateVersion,
		keys: &[&str],
	) -> (PrefixedMemoryDB<BlakeTwo256>, H256) {
		let mut root = H256::default();
		let mut mdb = PrefixedMemoryDB::<BlakeTwo256>::default();
		match state_version {
			StateVersion::V0 => {
				let mut trie = TrieDBMutBuilderV0::new(&mut mdb, &mut root).build();
				for (index, key) in keys.iter().enumerate() {
					trie.insert(&array_bytes::hex2bytes(key).unwrap(), &[index as u8]).unwrap();
				}
			},
			StateVersion::V1 => {
				let mut trie = TrieDBMutBuilderV1::new(&mut mdb, &mut root).build();
				for (index, key) in keys.iter().enumerate() {
					trie.insert(&array_bytes::hex2bytes(key).unwrap(), &[index as u8]).unwrap();
				}
			},
		};
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

	pub(crate) fn test_trie_with_hex_keys(
		hashed_value: StateVersion,
		cache: Option<Cache>,
		recorder: Option<Recorder>,
		keys: &[&str],
	) -> TrieBackend<PrefixedMemoryDB<BlakeTwo256>, BlakeTwo256> {
		let (mdb, root) = test_db_with_hex_keys(hashed_value, keys);

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
		assert!(!test_trie(state_version, cache, recorder)
			.pairs(Default::default())
			.unwrap()
			.next()
			.is_none());
	}

	#[test]
	fn pairs_are_empty_on_empty_storage() {
		assert!(TrieBackendBuilder::<PrefixedMemoryDB<BlakeTwo256>, BlakeTwo256>::new(
			PrefixedMemoryDB::default(),
			Default::default(),
		)
		.build()
		.pairs(Default::default())
		.unwrap()
		.next()
		.is_none());
	}

	parameterized_test!(storage_iteration_works, storage_iteration_works_inner);
	fn storage_iteration_works_inner(
		state_version: StateVersion,
		cache: Option<Cache>,
		recorder: Option<Recorder>,
	) {
		let trie = test_trie(state_version, cache, recorder);

		// Fetch everything.
		assert_eq!(
			trie.keys(Default::default())
				.unwrap()
				.map(|result| result.unwrap())
				.take(5)
				.collect::<Vec<_>>(),
			vec![
				b":child_storage:default:sub1".to_vec(),
				b":code".to_vec(),
				b"key".to_vec(),
				b"value1".to_vec(),
				b"value2".to_vec(),
			]
		);

		// Fetch starting at a given key (full key).
		assert_eq!(
			trie.keys(IterArgs { start_at: Some(b"key"), ..IterArgs::default() })
				.unwrap()
				.map(|result| result.unwrap())
				.take(3)
				.collect::<Vec<_>>(),
			vec![b"key".to_vec(), b"value1".to_vec(), b"value2".to_vec(),]
		);

		// Fetch starting at a given key (partial key).
		assert_eq!(
			trie.keys(IterArgs { start_at: Some(b"ke"), ..IterArgs::default() })
				.unwrap()
				.map(|result| result.unwrap())
				.take(3)
				.collect::<Vec<_>>(),
			vec![b"key".to_vec(), b"value1".to_vec(), b"value2".to_vec(),]
		);

		// Fetch starting at a given key (empty key).
		assert_eq!(
			trie.keys(IterArgs { start_at: Some(b""), ..IterArgs::default() })
				.unwrap()
				.map(|result| result.unwrap())
				.take(5)
				.collect::<Vec<_>>(),
			vec![
				b":child_storage:default:sub1".to_vec(),
				b":code".to_vec(),
				b"key".to_vec(),
				b"value1".to_vec(),
				b"value2".to_vec(),
			]
		);

		// Fetch starting at a given key and with prefix which doesn't match that key.
		// (Start *before* the prefix.)
		assert_eq!(
			trie.keys(IterArgs {
				prefix: Some(b"value"),
				start_at: Some(b"key"),
				..IterArgs::default()
			})
			.unwrap()
			.map(|result| result.unwrap())
			.collect::<Vec<_>>(),
			vec![b"value1".to_vec(), b"value2".to_vec(),]
		);

		// Fetch starting at a given key and with prefix which doesn't match that key.
		// (Start *after* the prefix.)
		assert!(trie
			.keys(IterArgs {
				prefix: Some(b"value"),
				start_at: Some(b"vblue"),
				..IterArgs::default()
			})
			.unwrap()
			.map(|result| result.unwrap())
			.next()
			.is_none());

		// Fetch starting at a given key and with prefix which does match that key.
		assert_eq!(
			trie.keys(IterArgs {
				prefix: Some(b"value"),
				start_at: Some(b"value"),
				..IterArgs::default()
			})
			.unwrap()
			.map(|result| result.unwrap())
			.collect::<Vec<_>>(),
			vec![b"value1".to_vec(), b"value2".to_vec(),]
		);
	}

	// This test reproduces an actual real-world issue: https://github.com/polkadot-js/apps/issues/9103
	parameterized_test!(
		storage_iter_does_not_return_out_of_prefix_keys,
		storage_iter_does_not_return_out_of_prefix_keys_inner
	);
	fn storage_iter_does_not_return_out_of_prefix_keys_inner(
		state_version: StateVersion,
		cache: Option<Cache>,
		recorder: Option<Recorder>,
	) {
		let trie = test_trie_with_hex_keys(state_version, cache, recorder, &[
			"6cf4040bbce30824850f1a4823d8c65faeefaa25a5bae16a431719647c1d99da",
			"6cf4040bbce30824850f1a4823d8c65ff536928ca5ba50039bc2766a48ddbbab",
			"70f943199f1a2dde80afdaf3f447db834e7b9012096b41c4eb3aaf947f6ea429",
			"7474449cca95dc5d0c00e71735a6d17d3cd15a3fd6e04e47bee3922dbfa92c8d007fc7effcb0c044a0c41fd8a77eb55d2133058a86d1f4d6f8e45612cd271eefd77f91caeaacfe011b8f41540e0a793b0fd51b245dae19382b45386570f2b545fab75e3277910f7324b55f47c29f9965e8298371404e50ac",
			"7474449cca95dc5d0c00e71735a6d17d3cd15a3fd6e04e47bee3922dbfa92c8d0179c23cd593c770fde9fc7aa8f84b3e401e654b8986c67728844da0080ec9ee222b41a85708a471a511548302870b53f40813d8354b6d2969e1b7ca9e083ecf96f9647e004ecb41c7f26f0110f778bdb3d9da31bef323d9",
			"7474449cca95dc5d0c00e71735a6d17d3cd15a3fd6e04e47bee3922dbfa92c8d024de296f88310247001277477f4ace4d0aa5685ea2928d518a807956e4806a656520d6520b8ac259f684aa0d91961d76f697716f04e6c997338d03560ab7d703829fe7b9d0e6d7eff8d8412fc428364c2f474a67b36586d",
			"7474449cca95dc5d0c00e71735a6d17d3cd15a3fd6e04e47bee3922dbfa92c8d13dc5d83f2361c14d05933eb3182a92ac14665718569703baf1da25c7d571843b6489f03d8549c87bfa5709836ba729443c319659e83ad5ee133e6f11af51d883e56216e9e1bbb1e2920c7c6120cbb55cd469b1f95b61601",
			"7474449cca95dc5d0c00e71735a6d17d3cd15a3fd6e04e47bee3922dbfa92c8d1786d20bbb4b91eb1f5765432d750bd0111a0807c8d04f05110ffaf73f4fa7b360422c13bc97efc3a2324d9fa8f954b424c0bcfce7236a2e8107dd31c2042a9860a964f8472fda49749dec3f146e81470b55aa0f3930d854",
			"7474449cca95dc5d0c00e71735a6d17d3cd15a3fd6e04e47bee3922dbfa92c8d18c246484ec5335a40903e7cd05771be7c0b8459333f1ae2925c3669fc3e5accd0f38c4711a15544bfa5709836ba729443c319659e83ad5ee133e6f11af51d883e56216e9e1bbb1e2920c7c6120cbb55cd469b1f95b61601",
			"7474449cca95dc5d0c00e71735a6d17d3cd15a3fd6e04e47bee3922dbfa92c8d1aca749033252ce75245528397430d14cb8e8c09248d81ee5de00b6ae93ee880b6d19a595e6dc106bfa5709836ba729443c319659e83ad5ee133e6f11af51d883e56216e9e1bbb1e2920c7c6120cbb55cd469b1f95b61601",
			"7474449cca95dc5d0c00e71735a6d17d3cd15a3fd6e04e47bee3922dbfa92c8d1d6bceb91bc07973e7b3296f83af9f1c4300ce9198cc3b44c54dafddb58f4a43aee44a9bef1a2e9dbfa5709836ba729443c319659e83ad5ee133e6f11af51d883e56216e9e1bbb1e2920c7c6120cbb55cd469b1f95b61601",
			"7474449cca95dc5d0c00e71735a6d17d3cd15a3fd6e04e47bee3922dbfa92c8d203383772f45721232139e1a8863b0f2f8d480bdc15bcc1f2033cf467e137059558da743838f6b58bfa5709836ba729443c319659e83ad5ee133e6f11af51d883e56216e9e1bbb1e2920c7c6120cbb55cd469b1f95b61601",
			"7474449cca95dc5d0c00e71735a6d17d3cd15a3fd6e04e47bee3922dbfa92c8d2197cc5c3eb3a6a67538e0dc3eaaf8c820d71310d377499c4a5d276381789e0a234475e69cddf709d207458083d6146d3a36fce7f1fe05b232702bf154096e5e3a8c378bdc237d7a27909acd663563917f0f70bb0e8e61a3",
			"7474449cca95dc5d0c00e71735a6d17d3cd15a3fd6e04e47bee3922dbfa92c8d4f19c117f2ea36100f753c4885aa8d63b4d65a0dc32106f829f89eeabd52c37105c9bdb75f752469729fa3f0e7d907c1d949192c8e264a1a510c32abe3a05ed50be2262d5bfb981673ec80a07fd2ce28c7f27cd0043a788c",
			"7474449cca95dc5d0c00e71735a6d17d3cd15a3fd6e04e47bee3922dbfa92c8d547d5aaa651bafa63d077560dfe823ac75665ebf1dcfd96a06e45499f03dda31282977706918d4821b8f41540e0a793b0fd51b245dae19382b45386570f2b545fab75e3277910f7324b55f47c29f9965e8298371404e50ac",
			"7474449cca95dc5d0c00e71735a6d17d3cd15a3fd6e04e47bee3922dbfa92c8d6037207d54d69a082ea225ab4a412e4b87d6f5612053b07c405cf05ea25e482a4908c0713be2998abfa5709836ba729443c319659e83ad5ee133e6f11af51d883e56216e9e1bbb1e2920c7c6120cbb55cd469b1f95b61601",
			"7474449cca95dc5d0c00e71735a6d17d3cd15a3fd6e04e47bee3922dbfa92c8d63d0920de0c7315ebaed1d639d926961d28af89461c31eca890441e449147d23bb7c9d4fc42d7c16bfa5709836ba729443c319659e83ad5ee133e6f11af51d883e56216e9e1bbb1e2920c7c6120cbb55cd469b1f95b61601",
			"7474449cca95dc5d0c00e71735a6d17d3cd15a3fd6e04e47bee3922dbfa92c8d7912c66be82a5972e5bc11c8d10551a296ba9aaff8ca6ab22a8cd1987974b87a97121c871f786d2e17e0a629acf01c38947f170b7e02a9ebb4ee60f83779acb99b71114c01a4f0a60694611a1502c399c77214ffa26e955b",
			"7474449cca95dc5d0c00e71735a6d17d3cd15a3fd6e04e47bee3922dbfa92c8d7aa00f217f3a374a2f1ca0f388719f84099e8157a8a83c5ccf54eae1617f93933fa976baa629e6febfa5709836ba729443c319659e83ad5ee133e6f11af51d883e56216e9e1bbb1e2920c7c6120cbb55cd469b1f95b61601",
			"7474449cca95dc5d0c00e71735a6d17d3cd15a3fd6e04e47bee3922dbfa92c8d9e1c3c8ab41943cf377b1aa724d7f518a3cfc96a732bdc4658155d09ed2bfc31b5ccbc6d8646b59f1b8f41540e0a793b0fd51b245dae19382b45386570f2b545fab75e3277910f7324b55f47c29f9965e8298371404e50ac",
			"7474449cca95dc5d0c00e71735a6d17d3cd15a3fd6e04e47bee3922dbfa92c8d9fb8d6d95d5214a3305a4fa07e344eb99fad4be3565d646c8ac5af85514d9c96702c9c207be234958dbdb9185f467d2be3b84e8b2f529f7ec3844b378a889afd6bd31a9b5ed22ffee2019ad82c6692f1736dd41c8bb85726",
			"7474449cca95dc5d0c00e71735a6d17d3cd15a3fd6e04e47bee3922dbfa92c8d9fb8d6d95d5214a3305a4fa07e344eb99fad4be3565d646c8ac5af85514d9c96702c9c207be23495ec1caa509591a36a8403684384ce40838c9bd7fc49d933a10d3b26e979273e2f17ebf0bf41cd90e4287e126a59d5a243",
			"7474449cca95dc5d0c00e71735a6d17d3cd15a3fd6e04e47bee3922dbfa92c8da7fc066aae2ffe03b36e9a72f9a39cb2befac7e47f320309f31f1c1676288d9596045807304b3d79bfa5709836ba729443c319659e83ad5ee133e6f11af51d883e56216e9e1bbb1e2920c7c6120cbb55cd469b1f95b61601",
			"7474449cca95dc5d0c00e71735a6d17d3cd15a3fd6e04e47bee3922dbfa92c8daf3c377b0fddf7c7ad6d390fab0ab45ac16c21645be880af5cab2fbbeb04820401a4c9f766c17bef9fc14a2e16ade86fe26ee81d4497dc6aab81cc5f5bb0458d6149a763ecb09aefec06950dd61db1ba025401d2a04e3b9d",
			"7474449cca95dc5d0c00e71735a6d17d3cd15a3fd6e04e47bee3922dbfa92c8daf3c377b0fddf7c7ad6d390fab0ab45ac16c21645be880af5cab2fbbeb04820401a4c9f766c17befbfa5709836ba729443c319659e83ad5ee133e6f11af51d883e56216e9e1bbb1e2920c7c6120cbb55cd469b1f95b61601",
			"7474449cca95dc5d0c00e71735a6d17d3cd15a3fd6e04e47bee3922dbfa92c8db60505ba8b77ef03ed805436d3242f26dc828084b12aaf4bcb96af468816a182b5360149398aad6b1dafe949b0918138ceef924f6393d1818a04842301294604972da17b24b31b155e4409a01273733b8d21a156c2e7eb71",
			"7474449cca95dc5d0c00e71735a6d17d3cd15a3fd6e04e47bee3922dbfa92c8dbd27136a6e028656073cc840bfabb48fe935880c4c4c990ee98458b2fed308e9765f7f7f717dd3b2862fa5361d3b55afa6040e582687403c852b2d065b24f253276cc581226991f8e1818a78fc64c39da7f0b383c6726e0f",
			"7474449cca95dc5d0c00e71735a6d17d3cd15a3fd6e04e47bee3922dbfa92c8dca40d91320edd326500f9e8b5a0b23a8bdf21549f98f0e014f66b6a18bdd78e337a6c05d670c80c88a55d4c7bb6fbae546e2d03ac9ab16e85fe11dad6adfd6a20618905477b831d7d48ca32d0bfd2bdc8dbeba26ffe2c710",
			"7474449cca95dc5d0c00e71735a6d17d3cd15a3fd6e04e47bee3922dbfa92c8dd27478512243ed62c1c1f7066021798a464d4cf9099546d5d9907b3369f1b9d7a5aa5d60ca845619bfa5709836ba729443c319659e83ad5ee133e6f11af51d883e56216e9e1bbb1e2920c7c6120cbb55cd469b1f95b61601",
			"7474449cca95dc5d0c00e71735a6d17d3cd15a3fd6e04e47bee3922dbfa92c8de6da5659cbbe1489abbe99c4d3a474f4d1e78edb55a9be68d8f52c6fe730388a298e6f6325db3da7bfa5709836ba729443c319659e83ad5ee133e6f11af51d883e56216e9e1bbb1e2920c7c6120cbb55cd469b1f95b61601",
			"7474449cca95dc5d0c00e71735a6d17d3cd15a3fd6e04e47bee3922dbfa92c8de6da5659cbbe1489abbe99c4d3a474f4d1e78edb55a9be68d8f52c6fe730388a298e6f6325db3da7e94ca3e8c297d82f71e232a2892992d1f6480475fb797ce64e58f773d8fafd9fbcee4bdf4b14f2a71b6d3a428cf9f24b",
			"7474449cca95dc5d0c00e71735a6d17d3cd15a3fd6e04e47bee3922dbfa92c8decdd1760c61ff7234f2876dbe817af803170233320d778b92043b2359e3de6d16c9e5359f6302da31c84d6f551ad2a831263ef956f0cdb3b4810cefcb2d0b57bcce7b82007016ae4fe752c31d1a01b589a7966cea03ec65c",
			"7474449cca95dc5d0c00e71735a6d17d3cd15a3fd6e04e47bee3922dbfa92c8df9981ee6b69eb7af2153af34f39ffc06e2daa5272c99798c8849091284dc8905f2a76b65754c2089bfa5709836ba729443c319659e83ad5ee133e6f11af51d883e56216e9e1bbb1e2920c7c6120cbb55cd469b1f95b61601",
			"7474449cca95dc5d0c00e71735a6d17d4e7b9012096b41c4eb3aaf947f6ea429",
			"89d139e01a5eb2256f222e5fc5dbe6b33c9c1284130706f5aea0c8b3d4c54d89",
			"89d139e01a5eb2256f222e5fc5dbe6b36254e9d55588784fa2a62b726696e2b1"
		]);

		let key = array_bytes::hex2bytes("7474449cca95dc5d0c00e71735a6d17d3cd15a3fd6e04e47bee3922dbfa92c8da7dad55cf08ffe8194efa962146801b0503092b1ed6a3fa6aee9107334aefd7965bbe568c3d24c6d").unwrap();

		assert_eq!(
			trie.keys(IterArgs {
				prefix: Some(&key),
				start_at: Some(&key),
				start_at_exclusive: true,
				..IterArgs::default()
			})
			.unwrap()
			.map(|result| result.unwrap())
			.collect::<Vec<_>>(),
			Vec::<Vec<u8>>::new()
		);
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
		let keys: Vec<_> =
			trie.keys(Default::default()).unwrap().map(|result| result.unwrap()).collect();

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
		assert_eq!(
			trie_backend
				.pairs(Default::default())
				.unwrap()
				.map(|result| result.unwrap())
				.collect::<Vec<_>>(),
			proving_backend
				.pairs(Default::default())
				.unwrap()
				.map(|result| result.unwrap())
				.collect::<Vec<_>>()
		);

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
		let in_memory = new_in_mem::<BlakeTwo256>();
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
		let in_memory = new_in_mem::<BlakeTwo256>();
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
		let in_memory = new_in_mem::<BlakeTwo256>();
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
