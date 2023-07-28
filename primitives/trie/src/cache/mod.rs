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

//! Trie Cache
//!
//! Provides an implementation of the [`TrieCache`](trie_db::TrieCache) trait.
//! The implementation is split into three types [`SharedTrieCache`], [`LocalTrieCache`] and
//! [`TrieCache`]. The [`SharedTrieCache`] is the instance that should be kept around for the entire
//! lifetime of the node. It will store all cached trie nodes and values on a global level. Then
//! there is the [`LocalTrieCache`] that should be kept around per state instance requested from the
//! backend. As there are very likely multiple accesses to the state per instance, this
//! [`LocalTrieCache`] is used to cache the nodes and the values before they are merged back to the
//! shared instance. Last but not least there is the [`TrieCache`] that is being used per access to
//! the state. It will use the [`SharedTrieCache`] and the [`LocalTrieCache`] to fulfill cache
//! requests. If both of them don't provide the requested data it will be inserted into the
//! [`LocalTrieCache`] and then later into the [`SharedTrieCache`].
//!
//! The [`SharedTrieCache`] is bound to some maximum number of bytes. It is ensured that it never
//! runs above this limit. However as long as data is cached inside a [`LocalTrieCache`] it isn't
//! taken into account when limiting the [`SharedTrieCache`]. This means that for the lifetime of a
//! [`LocalTrieCache`] the actual memory usage could be above the allowed maximum.

use crate::{Error, NodeCodec};
use hash_db::Hasher;
use nohash_hasher::BuildNoHashHasher;
use parking_lot::{Mutex, MutexGuard};
use schnellru::LruMap;
use shared_cache::{ValueCacheKey, ValueCacheRef};
use std::{
	collections::HashMap,
	sync::{
		atomic::{AtomicU64, Ordering},
		Arc,
	},
	time::Duration,
};
use trie_db::{node::NodeOwned, CachedValue};

mod shared_cache;

pub use shared_cache::SharedTrieCache;

use self::shared_cache::ValueCacheKeyHash;

const LOG_TARGET: &str = "trie-cache";

/// The maximum amount of time we'll wait trying to acquire the shared cache lock
/// when the local cache is dropped and synchronized with the share cache.
///
/// This is just a failsafe; normally this should never trigger.
const SHARED_CACHE_WRITE_LOCK_TIMEOUT: Duration = Duration::from_millis(100);

/// The maximum number of existing keys in the shared cache that a single local cache
/// can promote to the front of the LRU cache in one go.
///
/// If we have a big shared cache and the local cache hits all of those keys we don't
/// want to spend forever bumping all of them.
const SHARED_NODE_CACHE_MAX_PROMOTED_KEYS: u32 = 1792;
/// Same as [`SHARED_NODE_CACHE_MAX_PROMOTED_KEYS`].
const SHARED_VALUE_CACHE_MAX_PROMOTED_KEYS: u32 = 1792;

/// The maximum portion of the shared cache (in percent) that a single local
/// cache can replace in one go.
///
/// We don't want a single local cache instance to have the ability to replace
/// everything in the shared cache.
const SHARED_NODE_CACHE_MAX_REPLACE_PERCENT: usize = 33;
/// Same as [`SHARED_NODE_CACHE_MAX_REPLACE_PERCENT`].
const SHARED_VALUE_CACHE_MAX_REPLACE_PERCENT: usize = 33;

/// The maximum inline capacity of the local cache, in bytes.
///
/// This is just an upper limit; since the maps are resized in powers of two
/// their actual size will most likely not exactly match this.
const LOCAL_NODE_CACHE_MAX_INLINE_SIZE: usize = 512 * 1024;
/// Same as [`LOCAL_NODE_CACHE_MAX_INLINE_SIZE`].
const LOCAL_VALUE_CACHE_MAX_INLINE_SIZE: usize = 512 * 1024;

/// The maximum size of the memory allocated on the heap by the local cache, in bytes.
///
/// The size of the node cache should always be bigger than the value cache. The value
/// cache is only holding weak references to the actual values found in the nodes and
/// we account for the size of the node as part of the node cache.
const LOCAL_NODE_CACHE_MAX_HEAP_SIZE: usize = 8 * 1024 * 1024;
/// Same as [`LOCAL_NODE_CACHE_MAX_HEAP_SIZE`].
const LOCAL_VALUE_CACHE_MAX_HEAP_SIZE: usize = 2 * 1024 * 1024;

/// The size of the shared cache.
#[derive(Debug, Clone, Copy)]
pub struct CacheSize(usize);

impl CacheSize {
	/// An unlimited cache size.
	pub const fn unlimited() -> Self {
		CacheSize(usize::MAX)
	}

	/// A cache size `bytes` big.
	pub const fn new(bytes: usize) -> Self {
		CacheSize(bytes)
	}
}

/// A limiter for the local node cache. This makes sure the local cache doesn't grow too big.
#[derive(Default)]
pub struct LocalNodeCacheLimiter {
	/// The current size (in bytes) of data allocated by this cache on the heap.
	///
	/// This doesn't include the size of the map itself.
	current_heap_size: usize,
}

impl<H> schnellru::Limiter<H, NodeCached<H>> for LocalNodeCacheLimiter
where
	H: AsRef<[u8]> + std::fmt::Debug,
{
	type KeyToInsert<'a> = H;
	type LinkType = u32;

	#[inline]
	fn is_over_the_limit(&self, length: usize) -> bool {
		// Only enforce the limit if there's more than one element to make sure
		// we can always add a new element to the cache.
		if length <= 1 {
			return false
		}

		self.current_heap_size > LOCAL_NODE_CACHE_MAX_HEAP_SIZE
	}

	#[inline]
	fn on_insert<'a>(
		&mut self,
		_length: usize,
		key: H,
		cached_node: NodeCached<H>,
	) -> Option<(H, NodeCached<H>)> {
		self.current_heap_size += cached_node.heap_size();
		Some((key, cached_node))
	}

	#[inline]
	fn on_replace(
		&mut self,
		_length: usize,
		_old_key: &mut H,
		_new_key: H,
		old_node: &mut NodeCached<H>,
		new_node: &mut NodeCached<H>,
	) -> bool {
		debug_assert_eq!(_old_key.as_ref().len(), _new_key.as_ref().len());
		self.current_heap_size =
			self.current_heap_size + new_node.heap_size() - old_node.heap_size();
		true
	}

	#[inline]
	fn on_removed(&mut self, _key: &mut H, cached_node: &mut NodeCached<H>) {
		self.current_heap_size -= cached_node.heap_size();
	}

	#[inline]
	fn on_cleared(&mut self) {
		self.current_heap_size = 0;
	}

	#[inline]
	fn on_grow(&mut self, new_memory_usage: usize) -> bool {
		new_memory_usage <= LOCAL_NODE_CACHE_MAX_INLINE_SIZE
	}
}

/// A limiter for the local value cache. This makes sure the local cache doesn't grow too big.
#[derive(Default)]
pub struct LocalValueCacheLimiter {
	/// The current size (in bytes) of data allocated by this cache on the heap.
	///
	/// This doesn't include the size of the map itself.
	current_heap_size: usize,
}

impl<H> schnellru::Limiter<ValueCacheKey<H>, CachedValue<H>> for LocalValueCacheLimiter
where
	H: AsRef<[u8]>,
{
	type KeyToInsert<'a> = ValueCacheRef<'a, H>;
	type LinkType = u32;

	#[inline]
	fn is_over_the_limit(&self, length: usize) -> bool {
		// Only enforce the limit if there's more than one element to make sure
		// we can always add a new element to the cache.
		if length <= 1 {
			return false
		}

		self.current_heap_size > LOCAL_VALUE_CACHE_MAX_HEAP_SIZE
	}

	#[inline]
	fn on_insert(
		&mut self,
		_length: usize,
		key: Self::KeyToInsert<'_>,
		value: CachedValue<H>,
	) -> Option<(ValueCacheKey<H>, CachedValue<H>)> {
		self.current_heap_size += key.storage_key.len();
		Some((key.into(), value))
	}

	#[inline]
	fn on_replace(
		&mut self,
		_length: usize,
		_old_key: &mut ValueCacheKey<H>,
		_new_key: ValueCacheRef<H>,
		_old_value: &mut CachedValue<H>,
		_new_value: &mut CachedValue<H>,
	) -> bool {
		debug_assert_eq!(_old_key.storage_key.len(), _new_key.storage_key.len());
		true
	}

	#[inline]
	fn on_removed(&mut self, key: &mut ValueCacheKey<H>, _: &mut CachedValue<H>) {
		self.current_heap_size -= key.storage_key.len();
	}

	#[inline]
	fn on_cleared(&mut self) {
		self.current_heap_size = 0;
	}

	#[inline]
	fn on_grow(&mut self, new_memory_usage: usize) -> bool {
		new_memory_usage <= LOCAL_VALUE_CACHE_MAX_INLINE_SIZE
	}
}

/// A struct to gather hit/miss stats to aid in debugging the performance of the cache.
#[derive(Default)]
struct HitStats {
	shared_hits: AtomicU64,
	shared_fetch_attempts: AtomicU64,
	local_hits: AtomicU64,
	local_fetch_attempts: AtomicU64,
}

impl std::fmt::Display for HitStats {
	fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
		let shared_hits = self.shared_hits.load(Ordering::Relaxed);
		let shared_fetch_attempts = self.shared_fetch_attempts.load(Ordering::Relaxed);
		let local_hits = self.local_hits.load(Ordering::Relaxed);
		let local_fetch_attempts = self.local_fetch_attempts.load(Ordering::Relaxed);
		if shared_fetch_attempts == 0 && local_hits == 0 {
			write!(fmt, "empty")
		} else {
			let percent_local = (local_hits as f32 / local_fetch_attempts as f32) * 100.0;
			let percent_shared = (shared_hits as f32 / shared_fetch_attempts as f32) * 100.0;
			write!(
				fmt,
				"local hit rate = {}% [{}/{}], shared hit rate = {}% [{}/{}]",
				percent_local as u32,
				local_hits,
				local_fetch_attempts,
				percent_shared as u32,
				shared_hits,
				shared_fetch_attempts
			)
		}
	}
}

/// A struct to gather hit/miss stats for the node cache and the value cache.
#[derive(Default)]
struct TrieHitStats {
	node_cache: HitStats,
	value_cache: HitStats,
}

/// An internal struct to store the cached trie nodes.
pub(crate) struct NodeCached<H> {
	/// The cached node.
	pub node: NodeOwned<H>,
	/// Whether this node was fetched from the shared cache or not.
	pub is_from_shared_cache: bool,
}

impl<H> NodeCached<H> {
	/// Returns the number of bytes allocated on the heap by this node.
	fn heap_size(&self) -> usize {
		self.node.size_in_bytes() - std::mem::size_of::<NodeOwned<H>>()
	}
}

type NodeCacheMap<H> = LruMap<H, NodeCached<H>, LocalNodeCacheLimiter, schnellru::RandomState>;

type ValueCacheMap<H> = LruMap<
	ValueCacheKey<H>,
	CachedValue<H>,
	LocalValueCacheLimiter,
	BuildNoHashHasher<ValueCacheKey<H>>,
>;

type ValueAccessSet =
	LruMap<ValueCacheKeyHash, (), schnellru::ByLength, BuildNoHashHasher<ValueCacheKeyHash>>;

/// The local trie cache.
///
/// This cache should be used per state instance created by the backend. One state instance is
/// referring to the state of one block. It will cache all the accesses that are done to the state
/// which could not be fullfilled by the [`SharedTrieCache`]. These locally cached items are merged
/// back to the shared trie cache when this instance is dropped.
///
/// When using [`Self::as_trie_db_cache`] or [`Self::as_trie_db_mut_cache`], it will lock Mutexes.
/// So, it is important that these methods are not called multiple times, because they otherwise
/// deadlock.
pub struct LocalTrieCache<H: Hasher> {
	/// The shared trie cache that created this instance.
	shared: SharedTrieCache<H>,

	/// The local cache for the trie nodes.
	node_cache: Mutex<NodeCacheMap<H::Out>>,

	/// The local cache for the values.
	value_cache: Mutex<ValueCacheMap<H::Out>>,

	/// Keeps track of all values accessed in the shared cache.
	///
	/// This will be used to ensure that these nodes are brought to the front of the lru when this
	/// local instance is merged back to the shared cache. This can actually lead to collision when
	/// two [`ValueCacheKey`]s with different storage roots and keys map to the same hash. However,
	/// as we only use this set to update the lru position it is fine, even if we bring the wrong
	/// value to the top. The important part is that we always get the correct value from the value
	/// cache for a given key.
	shared_value_cache_access: Mutex<ValueAccessSet>,

	stats: TrieHitStats,
}

impl<H: Hasher> LocalTrieCache<H> {
	/// Return self as a [`TrieDB`](trie_db::TrieDB) compatible cache.
	///
	/// The given `storage_root` needs to be the storage root of the trie this cache is used for.
	pub fn as_trie_db_cache(&self, storage_root: H::Out) -> TrieCache<'_, H> {
		let value_cache = ValueCache::ForStorageRoot {
			storage_root,
			local_value_cache: self.value_cache.lock(),
			shared_value_cache_access: self.shared_value_cache_access.lock(),
			buffered_value: None,
		};

		TrieCache {
			shared_cache: self.shared.clone(),
			local_cache: self.node_cache.lock(),
			value_cache,
			stats: &self.stats,
		}
	}

	/// Return self as [`TrieDBMut`](trie_db::TrieDBMut) compatible cache.
	///
	/// After finishing all operations with [`TrieDBMut`](trie_db::TrieDBMut) and having obtained
	/// the new storage root, [`TrieCache::merge_into`] should be called to update this local
	/// cache instance. If the function is not called, cached data is just thrown away and not
	/// propagated to the shared cache. So, accessing these new items will be slower, but nothing
	/// would break because of this.
	pub fn as_trie_db_mut_cache(&self) -> TrieCache<'_, H> {
		TrieCache {
			shared_cache: self.shared.clone(),
			local_cache: self.node_cache.lock(),
			value_cache: ValueCache::Fresh(Default::default()),
			stats: &self.stats,
		}
	}
}

impl<H: Hasher> Drop for LocalTrieCache<H> {
	fn drop(&mut self) {
		tracing::debug!(
			target: LOG_TARGET,
			"Local node trie cache dropped: {}",
			self.stats.node_cache
		);

		tracing::debug!(
			target: LOG_TARGET,
			"Local value trie cache dropped: {}",
			self.stats.value_cache
		);

		let mut shared_inner = match self.shared.write_lock_inner() {
			Some(inner) => inner,
			None => {
				tracing::warn!(
					target: LOG_TARGET,
					"Timeout while trying to acquire a write lock for the shared trie cache"
				);
				return
			},
		};

		shared_inner.node_cache_mut().update(self.node_cache.get_mut().drain());

		shared_inner.value_cache_mut().update(
			self.value_cache.get_mut().drain(),
			self.shared_value_cache_access.get_mut().drain().map(|(key, ())| key),
		);
	}
}

/// The abstraction of the value cache for the [`TrieCache`].
enum ValueCache<'a, H: Hasher> {
	/// The value cache is fresh, aka not yet associated to any storage root.
	/// This is used for example when a new trie is being build, to cache new values.
	Fresh(HashMap<Arc<[u8]>, CachedValue<H::Out>>),
	/// The value cache is already bound to a specific storage root.
	ForStorageRoot {
		shared_value_cache_access: MutexGuard<'a, ValueAccessSet>,
		local_value_cache: MutexGuard<'a, ValueCacheMap<H::Out>>,
		storage_root: H::Out,
		// The shared value cache needs to be temporarily locked when reading from it
		// so we need to clone the value that is returned, but we need to be able to
		// return a reference to the value, so we just buffer it here.
		buffered_value: Option<CachedValue<H::Out>>,
	},
}

impl<H: Hasher> ValueCache<'_, H> {
	/// Get the value for the given `key`.
	fn get(
		&mut self,
		key: &[u8],
		shared_cache: &SharedTrieCache<H>,
		stats: &HitStats,
	) -> Option<&CachedValue<H::Out>> {
		stats.local_fetch_attempts.fetch_add(1, Ordering::Relaxed);

		match self {
			Self::Fresh(map) =>
				if let Some(value) = map.get(key) {
					stats.local_hits.fetch_add(1, Ordering::Relaxed);
					Some(value)
				} else {
					None
				},
			Self::ForStorageRoot {
				local_value_cache,
				shared_value_cache_access,
				storage_root,
				buffered_value,
			} => {
				// We first need to look up in the local cache and then the shared cache.
				// It can happen that some value is cached in the shared cache, but the
				// weak reference of the data can not be upgraded anymore. This for example
				// happens when the node is dropped that contains the strong reference to the data.
				//
				// So, the logic of the trie would lookup the data and the node and store both
				// in our local caches.

				let hash = ValueCacheKey::hash_data(key, storage_root);

				if let Some(value) = local_value_cache
					.peek_by_hash(hash.raw(), |existing_key, _| {
						existing_key.is_eq(storage_root, key)
					}) {
					stats.local_hits.fetch_add(1, Ordering::Relaxed);

					return Some(value)
				}

				stats.shared_fetch_attempts.fetch_add(1, Ordering::Relaxed);
				if let Some(value) = shared_cache.peek_value_by_hash(hash, storage_root, key) {
					stats.shared_hits.fetch_add(1, Ordering::Relaxed);
					shared_value_cache_access.insert(hash, ());
					*buffered_value = Some(value.clone());
					return buffered_value.as_ref()
				}

				None
			},
		}
	}

	/// Insert some new `value` under the given `key`.
	fn insert(&mut self, key: &[u8], value: CachedValue<H::Out>) {
		match self {
			Self::Fresh(map) => {
				map.insert(key.into(), value);
			},
			Self::ForStorageRoot { local_value_cache, storage_root, .. } => {
				local_value_cache.insert(ValueCacheRef::new(key, *storage_root), value);
			},
		}
	}
}

/// The actual [`TrieCache`](trie_db::TrieCache) implementation.
///
/// If this instance was created for using it with a [`TrieDBMut`](trie_db::TrieDBMut), it needs to
/// be merged back into the [`LocalTrieCache`] with [`Self::merge_into`] after all operations are
/// done.
pub struct TrieCache<'a, H: Hasher> {
	shared_cache: SharedTrieCache<H>,
	local_cache: MutexGuard<'a, NodeCacheMap<H::Out>>,
	value_cache: ValueCache<'a, H>,
	stats: &'a TrieHitStats,
}

impl<'a, H: Hasher> TrieCache<'a, H> {
	/// Merge this cache into the given [`LocalTrieCache`].
	///
	/// This function is only required to be called when this instance was created through
	/// [`LocalTrieCache::as_trie_db_mut_cache`], otherwise this method is a no-op. The given
	/// `storage_root` is the new storage root that was obtained after finishing all operations
	/// using the [`TrieDBMut`](trie_db::TrieDBMut).
	pub fn merge_into(self, local: &LocalTrieCache<H>, storage_root: H::Out) {
		let ValueCache::Fresh(cache) = self.value_cache else { return };

		if !cache.is_empty() {
			let mut value_cache = local.value_cache.lock();
			let partial_hash = ValueCacheKey::hash_partial_data(&storage_root);

			cache.into_iter().for_each(|(k, v)| {
				let hash = ValueCacheKeyHash::from_hasher_and_storage_key(partial_hash.clone(), &k);
				let k = ValueCacheRef { storage_root, storage_key: &k, hash };
				value_cache.insert(k, v);
			});
		}
	}
}

impl<'a, H: Hasher> trie_db::TrieCache<NodeCodec<H>> for TrieCache<'a, H> {
	fn get_or_insert_node(
		&mut self,
		hash: H::Out,
		fetch_node: &mut dyn FnMut() -> trie_db::Result<NodeOwned<H::Out>, H::Out, Error<H::Out>>,
	) -> trie_db::Result<&NodeOwned<H::Out>, H::Out, Error<H::Out>> {
		let mut is_local_cache_hit = true;
		self.stats.node_cache.local_fetch_attempts.fetch_add(1, Ordering::Relaxed);

		// First try to grab the node from the local cache.
		let node = self.local_cache.get_or_insert_fallible(hash, || {
			is_local_cache_hit = false;

			// It was not in the local cache; try the shared cache.
			self.stats.node_cache.shared_fetch_attempts.fetch_add(1, Ordering::Relaxed);
			if let Some(node) = self.shared_cache.peek_node(&hash) {
				self.stats.node_cache.shared_hits.fetch_add(1, Ordering::Relaxed);
				tracing::trace!(target: LOG_TARGET, ?hash, "Serving node from shared cache");

				return Ok(NodeCached::<H::Out> { node: node.clone(), is_from_shared_cache: true })
			}

			// It was not in the shared cache; try fetching it from the database.
			match fetch_node() {
				Ok(node) => {
					tracing::trace!(target: LOG_TARGET, ?hash, "Serving node from database");
					Ok(NodeCached::<H::Out> { node, is_from_shared_cache: false })
				},
				Err(error) => {
					tracing::trace!(target: LOG_TARGET, ?hash, "Serving node from database failed");
					Err(error)
				},
			}
		});

		if is_local_cache_hit {
			tracing::trace!(target: LOG_TARGET, ?hash, "Serving node from local cache");
			self.stats.node_cache.local_hits.fetch_add(1, Ordering::Relaxed);
		}

		Ok(&node?
			.expect("you can always insert at least one element into the local cache; qed")
			.node)
	}

	fn get_node(&mut self, hash: &H::Out) -> Option<&NodeOwned<H::Out>> {
		let mut is_local_cache_hit = true;
		self.stats.node_cache.local_fetch_attempts.fetch_add(1, Ordering::Relaxed);

		// First try to grab the node from the local cache.
		let cached_node = self.local_cache.get_or_insert_fallible(*hash, || {
			is_local_cache_hit = false;

			// It was not in the local cache; try the shared cache.
			self.stats.node_cache.shared_fetch_attempts.fetch_add(1, Ordering::Relaxed);
			if let Some(node) = self.shared_cache.peek_node(&hash) {
				self.stats.node_cache.shared_hits.fetch_add(1, Ordering::Relaxed);
				tracing::trace!(target: LOG_TARGET, ?hash, "Serving node from shared cache");

				Ok(NodeCached::<H::Out> { node: node.clone(), is_from_shared_cache: true })
			} else {
				tracing::trace!(target: LOG_TARGET, ?hash, "Serving node from cache failed");

				Err(())
			}
		});

		if is_local_cache_hit {
			tracing::trace!(target: LOG_TARGET, ?hash, "Serving node from local cache");
			self.stats.node_cache.local_hits.fetch_add(1, Ordering::Relaxed);
		}

		match cached_node {
			Ok(Some(cached_node)) => Some(&cached_node.node),
			Ok(None) => {
				unreachable!(
					"you can always insert at least one element into the local cache; qed"
				);
			},
			Err(()) => None,
		}
	}

	fn lookup_value_for_key(&mut self, key: &[u8]) -> Option<&CachedValue<H::Out>> {
		let res = self.value_cache.get(key, &self.shared_cache, &self.stats.value_cache);

		tracing::trace!(
			target: LOG_TARGET,
			key = ?sp_core::hexdisplay::HexDisplay::from(&key),
			found = res.is_some(),
			"Looked up value for key",
		);

		res
	}

	fn cache_value_for_key(&mut self, key: &[u8], data: CachedValue<H::Out>) {
		tracing::trace!(
			target: LOG_TARGET,
			key = ?sp_core::hexdisplay::HexDisplay::from(&key),
			"Caching value for key",
		);

		self.value_cache.insert(key, data);
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use trie_db::{Bytes, Trie, TrieDBBuilder, TrieDBMutBuilder, TrieHash, TrieMut};

	type MemoryDB = crate::MemoryDB<sp_core::Blake2Hasher>;
	type Layout = crate::LayoutV1<sp_core::Blake2Hasher>;
	type Cache = super::SharedTrieCache<sp_core::Blake2Hasher>;
	type Recorder = crate::recorder::Recorder<sp_core::Blake2Hasher>;

	const TEST_DATA: &[(&[u8], &[u8])] =
		&[(b"key1", b"val1"), (b"key2", &[2; 64]), (b"key3", b"val3"), (b"key4", &[4; 64])];
	const CACHE_SIZE_RAW: usize = 1024 * 10;
	const CACHE_SIZE: CacheSize = CacheSize::new(CACHE_SIZE_RAW);

	fn create_trie() -> (MemoryDB, TrieHash<Layout>) {
		let mut db = MemoryDB::default();
		let mut root = Default::default();

		{
			let mut trie = TrieDBMutBuilder::<Layout>::new(&mut db, &mut root).build();
			for (k, v) in TEST_DATA {
				trie.insert(k, v).expect("Inserts data");
			}
		}

		(db, root)
	}

	#[test]
	fn basic_cache_works() {
		let (db, root) = create_trie();

		let shared_cache = Cache::new(CACHE_SIZE);
		let local_cache = shared_cache.local_cache();

		{
			let mut cache = local_cache.as_trie_db_cache(root);
			let trie = TrieDBBuilder::<Layout>::new(&db, &root).with_cache(&mut cache).build();
			assert_eq!(TEST_DATA[0].1.to_vec(), trie.get(TEST_DATA[0].0).unwrap().unwrap());
		}

		// Local cache wasn't dropped yet, so there should nothing in the shared caches.
		assert!(shared_cache.read_lock_inner().value_cache().lru.is_empty());
		assert!(shared_cache.read_lock_inner().node_cache().lru.is_empty());

		drop(local_cache);

		// Now we should have the cached items in the shared cache.
		assert!(shared_cache.read_lock_inner().node_cache().lru.len() >= 1);
		let cached_data = shared_cache
			.read_lock_inner()
			.value_cache()
			.lru
			.peek(&ValueCacheKey::new_value(TEST_DATA[0].0, root))
			.unwrap()
			.clone();
		assert_eq!(Bytes::from(TEST_DATA[0].1.to_vec()), cached_data.data().flatten().unwrap());

		let fake_data = Bytes::from(&b"fake_data"[..]);

		let local_cache = shared_cache.local_cache();
		shared_cache.write_lock_inner().unwrap().value_cache_mut().lru.insert(
			ValueCacheKey::new_value(TEST_DATA[1].0, root),
			(fake_data.clone(), Default::default()).into(),
		);

		{
			let mut cache = local_cache.as_trie_db_cache(root);
			let trie = TrieDBBuilder::<Layout>::new(&db, &root).with_cache(&mut cache).build();

			// We should now get the "fake_data", because we inserted this manually to the cache.
			assert_eq!(b"fake_data".to_vec(), trie.get(TEST_DATA[1].0).unwrap().unwrap());
		}
	}

	#[test]
	fn trie_db_mut_cache_works() {
		let (mut db, root) = create_trie();

		let new_key = b"new_key".to_vec();
		// Use some long value to not have it inlined
		let new_value = vec![23; 64];

		let shared_cache = Cache::new(CACHE_SIZE);
		let mut new_root = root;

		{
			let local_cache = shared_cache.local_cache();

			let mut cache = local_cache.as_trie_db_mut_cache();

			{
				let mut trie = TrieDBMutBuilder::<Layout>::from_existing(&mut db, &mut new_root)
					.with_cache(&mut cache)
					.build();

				trie.insert(&new_key, &new_value).unwrap();
			}

			cache.merge_into(&local_cache, new_root);
		}

		// After the local cache is dropped, all changes should have been merged back to the shared
		// cache.
		let cached_data = shared_cache
			.read_lock_inner()
			.value_cache()
			.lru
			.peek(&ValueCacheKey::new_value(new_key, new_root))
			.unwrap()
			.clone();
		assert_eq!(Bytes::from(new_value), cached_data.data().flatten().unwrap());
	}

	#[test]
	fn trie_db_cache_and_recorder_work_together() {
		let (db, root) = create_trie();

		let shared_cache = Cache::new(CACHE_SIZE);

		for i in 0..5 {
			// Clear some of the caches.
			if i == 2 {
				shared_cache.reset_node_cache();
			} else if i == 3 {
				shared_cache.reset_value_cache();
			}

			let local_cache = shared_cache.local_cache();
			let recorder = Recorder::default();

			{
				let mut cache = local_cache.as_trie_db_cache(root);
				let mut recorder = recorder.as_trie_recorder(root);
				let trie = TrieDBBuilder::<Layout>::new(&db, &root)
					.with_cache(&mut cache)
					.with_recorder(&mut recorder)
					.build();

				for (key, value) in TEST_DATA {
					assert_eq!(*value, trie.get(&key).unwrap().unwrap());
				}
			}

			let storage_proof = recorder.drain_storage_proof();
			let memory_db: MemoryDB = storage_proof.into_memory_db();

			{
				let trie = TrieDBBuilder::<Layout>::new(&memory_db, &root).build();

				for (key, value) in TEST_DATA {
					assert_eq!(*value, trie.get(&key).unwrap().unwrap());
				}
			}
		}
	}

	#[test]
	fn trie_db_mut_cache_and_recorder_work_together() {
		const DATA_TO_ADD: &[(&[u8], &[u8])] = &[(b"key11", &[45; 78]), (b"key33", &[78; 89])];

		let (db, root) = create_trie();

		let shared_cache = Cache::new(CACHE_SIZE);

		// Run this twice so that we use the data cache in the second run.
		for i in 0..5 {
			// Clear some of the caches.
			if i == 2 {
				shared_cache.reset_node_cache();
			} else if i == 3 {
				shared_cache.reset_value_cache();
			}

			let recorder = Recorder::default();
			let local_cache = shared_cache.local_cache();
			let mut new_root = root;

			{
				let mut db = db.clone();
				let mut cache = local_cache.as_trie_db_cache(root);
				let mut recorder = recorder.as_trie_recorder(root);
				let mut trie = TrieDBMutBuilder::<Layout>::from_existing(&mut db, &mut new_root)
					.with_cache(&mut cache)
					.with_recorder(&mut recorder)
					.build();

				for (key, value) in DATA_TO_ADD {
					trie.insert(key, value).unwrap();
				}
			}

			let storage_proof = recorder.drain_storage_proof();
			let mut memory_db: MemoryDB = storage_proof.into_memory_db();
			let mut proof_root = root;

			{
				let mut trie =
					TrieDBMutBuilder::<Layout>::from_existing(&mut memory_db, &mut proof_root)
						.build();

				for (key, value) in DATA_TO_ADD {
					trie.insert(key, value).unwrap();
				}
			}

			assert_eq!(new_root, proof_root)
		}
	}

	#[test]
	fn cache_lru_works() {
		let (db, root) = create_trie();

		let shared_cache = Cache::new(CACHE_SIZE);

		{
			let local_cache = shared_cache.local_cache();

			let mut cache = local_cache.as_trie_db_cache(root);
			let trie = TrieDBBuilder::<Layout>::new(&db, &root).with_cache(&mut cache).build();

			for (k, _) in TEST_DATA {
				trie.get(k).unwrap().unwrap();
			}
		}

		// Check that all items are there.
		assert!(shared_cache
			.read_lock_inner()
			.value_cache()
			.lru
			.iter()
			.map(|d| d.0)
			.all(|l| TEST_DATA.iter().any(|d| &*l.storage_key == d.0)));

		// Run this in a loop. The first time we check that with the filled value cache,
		// the expected values are at the top of the LRU.
		// The second run is using an empty value cache to ensure that we access the nodes.
		for _ in 0..2 {
			{
				let local_cache = shared_cache.local_cache();

				let mut cache = local_cache.as_trie_db_cache(root);
				let trie = TrieDBBuilder::<Layout>::new(&db, &root).with_cache(&mut cache).build();

				for (k, _) in TEST_DATA.iter().take(2) {
					trie.get(k).unwrap().unwrap();
				}
			}

			// Ensure that the accessed items are most recently used items of the shared value
			// cache.
			assert!(shared_cache
				.read_lock_inner()
				.value_cache()
				.lru
				.iter()
				.take(2)
				.map(|d| d.0)
				.all(|l| { TEST_DATA.iter().take(2).any(|d| &*l.storage_key == d.0) }));

			// Delete the value cache, so that we access the nodes.
			shared_cache.reset_value_cache();
		}

		let most_recently_used_nodes = shared_cache
			.read_lock_inner()
			.node_cache()
			.lru
			.iter()
			.map(|d| *d.0)
			.collect::<Vec<_>>();

		{
			let local_cache = shared_cache.local_cache();

			let mut cache = local_cache.as_trie_db_cache(root);
			let trie = TrieDBBuilder::<Layout>::new(&db, &root).with_cache(&mut cache).build();

			for (k, _) in TEST_DATA.iter().skip(2) {
				trie.get(k).unwrap().unwrap();
			}
		}

		// Ensure that the most recently used nodes changed as well.
		assert_ne!(
			most_recently_used_nodes,
			shared_cache
				.read_lock_inner()
				.node_cache()
				.lru
				.iter()
				.map(|d| *d.0)
				.collect::<Vec<_>>()
		);
	}

	#[test]
	fn cache_respects_bounds() {
		let (mut db, root) = create_trie();

		let shared_cache = Cache::new(CACHE_SIZE);
		{
			let local_cache = shared_cache.local_cache();

			let mut new_root = root;

			{
				let mut cache = local_cache.as_trie_db_cache(root);
				{
					let mut trie =
						TrieDBMutBuilder::<Layout>::from_existing(&mut db, &mut new_root)
							.with_cache(&mut cache)
							.build();

					let value = vec![10u8; 100];
					// Ensure we add enough data that would overflow the cache.
					for i in 0..CACHE_SIZE_RAW / 100 * 2 {
						trie.insert(format!("key{}", i).as_bytes(), &value).unwrap();
					}
				}

				cache.merge_into(&local_cache, new_root);
			}
		}

		assert!(shared_cache.used_memory_size() < CACHE_SIZE_RAW);
	}
}
