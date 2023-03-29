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

///! Provides the [`SharedNodeCache`], the [`SharedValueCache`] and the [`SharedTrieCache`]
///! that combines both caches and is exported to the outside.
use super::{CacheSize, NodeCached};
use hash_db::Hasher;
use hashbrown::{hash_set::Entry as SetEntry, HashSet};
use nohash_hasher::BuildNoHashHasher;
use parking_lot::{Mutex, RwLock, RwLockWriteGuard};
use schnellru::LruMap;
use std::{
	hash::{BuildHasher, Hasher as _},
	sync::Arc,
};
use trie_db::{node::NodeOwned, CachedValue};

lazy_static::lazy_static! {
	static ref RANDOM_STATE: ahash::RandomState = ahash::RandomState::default();
}

pub struct SharedNodeCacheLimiter {
	/// The maximum size (in bytes) the cache can hold inline.
	///
	/// This space is always consumed whether there are any items in the map or not.
	max_inline_size: usize,

	/// The maximum size (in bytes) the cache can hold on the heap.
	max_heap_size: usize,

	/// The current size (in bytes) of data allocated by this cache on the heap.
	///
	/// This doesn't include the size of the map itself.
	heap_size: usize,

	/// A counter with the number of elements that got evicted from the cache.
	///
	/// Reset to zero before every update.
	items_evicted: usize,

	/// The maximum number of elements that we allow to be evicted.
	///
	/// Reset on every update.
	max_items_evicted: usize,
}

impl<H> schnellru::Limiter<H, NodeOwned<H>> for SharedNodeCacheLimiter
where
	H: AsRef<[u8]>,
{
	type KeyToInsert<'a> = H;
	type LinkType = u32;

	#[inline]
	fn is_over_the_limit(&self, _length: usize) -> bool {
		// Once we hit the limit of max items evicted this will return `false` and prevent
		// any further evictions, but this is fine because the outer loop which inserts
		// items into this cache will just detect this and stop inserting new items.
		self.items_evicted <= self.max_items_evicted && self.heap_size > self.max_heap_size
	}

	#[inline]
	fn on_insert(
		&mut self,
		_length: usize,
		key: Self::KeyToInsert<'_>,
		node: NodeOwned<H>,
	) -> Option<(H, NodeOwned<H>)> {
		let new_item_heap_size = node.size_in_bytes() - std::mem::size_of::<NodeOwned<H>>();
		if new_item_heap_size > self.max_heap_size {
			// Item's too big to add even if the cache's empty; bail.
			return None
		}

		self.heap_size += new_item_heap_size;
		Some((key, node))
	}

	#[inline]
	fn on_replace(
		&mut self,
		_length: usize,
		_old_key: &mut H,
		_new_key: H,
		old_node: &mut NodeOwned<H>,
		new_node: &mut NodeOwned<H>,
	) -> bool {
		debug_assert_eq!(_old_key.as_ref(), _new_key.as_ref());

		let new_item_heap_size = new_node.size_in_bytes() - std::mem::size_of::<NodeOwned<H>>();
		if new_item_heap_size > self.max_heap_size {
			// Item's too big to add even if the cache's empty; bail.
			return false
		}

		let old_item_heap_size = old_node.size_in_bytes() - std::mem::size_of::<NodeOwned<H>>();
		self.heap_size = self.heap_size - old_item_heap_size + new_item_heap_size;
		true
	}

	#[inline]
	fn on_cleared(&mut self) {
		self.heap_size = 0;
	}

	#[inline]
	fn on_removed(&mut self, _: &mut H, node: &mut NodeOwned<H>) {
		self.heap_size -= node.size_in_bytes() - std::mem::size_of::<NodeOwned<H>>();
		self.items_evicted += 1;
	}

	#[inline]
	fn on_grow(&mut self, new_memory_usage: usize) -> bool {
		new_memory_usage <= self.max_inline_size
	}
}

pub struct SharedValueCacheLimiter {
	/// The maximum size (in bytes) the cache can hold inline.
	///
	/// This space is always consumed whether there are any items in the map or not.
	max_inline_size: usize,

	/// The maximum size (in bytes) the cache can hold on the heap.
	max_heap_size: usize,

	/// The current size (in bytes) of data allocated by this cache on the heap.
	///
	/// This doesn't include the size of the map itself.
	heap_size: usize,

	/// A set with all of the keys deduplicated to save on memory.
	known_storage_keys: HashSet<Arc<[u8]>>,

	/// A counter with the number of elements that got evicted from the cache.
	///
	/// Reset to zero before every update.
	items_evicted: usize,

	/// The maximum number of elements that we allow to be evicted.
	///
	/// Reset on every update.
	max_items_evicted: usize,
}

impl<H> schnellru::Limiter<ValueCacheKey<H>, CachedValue<H>> for SharedValueCacheLimiter
where
	H: AsRef<[u8]>,
{
	type KeyToInsert<'a> = ValueCacheKey<H>;
	type LinkType = u32;

	#[inline]
	fn is_over_the_limit(&self, _length: usize) -> bool {
		self.items_evicted <= self.max_items_evicted && self.heap_size > self.max_heap_size
	}

	#[inline]
	fn on_insert(
		&mut self,
		_length: usize,
		mut key: Self::KeyToInsert<'_>,
		value: CachedValue<H>,
	) -> Option<(ValueCacheKey<H>, CachedValue<H>)> {
		match self.known_storage_keys.entry(key.storage_key.clone()) {
			SetEntry::Vacant(entry) => {
				let new_item_heap_size = key.storage_key.len();
				if new_item_heap_size > self.max_heap_size {
					// Item's too big to add even if the cache's empty; bail.
					return None
				}

				self.heap_size += new_item_heap_size;
				entry.insert();
			},
			SetEntry::Occupied(entry) => {
				key.storage_key = entry.get().clone();
			},
		}

		Some((key, value))
	}

	#[inline]
	fn on_replace(
		&mut self,
		_length: usize,
		_old_key: &mut ValueCacheKey<H>,
		_new_key: ValueCacheKey<H>,
		_old_value: &mut CachedValue<H>,
		_new_value: &mut CachedValue<H>,
	) -> bool {
		debug_assert_eq!(_new_key.storage_key, _old_key.storage_key);
		true
	}

	#[inline]
	fn on_removed(&mut self, key: &mut ValueCacheKey<H>, _: &mut CachedValue<H>) {
		if Arc::strong_count(&key.storage_key) == 2 {
			// There are only two instances of this key:
			//   1) one memoized in `known_storage_keys`,
			//   2) one inside the map.
			//
			// This means that after this remove goes through the `Arc` will be deallocated.
			self.heap_size -= key.storage_key.len();
			self.known_storage_keys.remove(&key.storage_key);
		}
		self.items_evicted += 1;
	}

	#[inline]
	fn on_cleared(&mut self) {
		self.heap_size = 0;
		self.known_storage_keys.clear();
	}

	#[inline]
	fn on_grow(&mut self, new_memory_usage: usize) -> bool {
		new_memory_usage <= self.max_inline_size
	}
}

type SharedNodeCacheMap<H> =
	LruMap<H, NodeOwned<H>, SharedNodeCacheLimiter, schnellru::RandomState>;

/// The shared node cache.
///
/// Internally this stores all cached nodes in a [`LruMap`]. It ensures that when updating the
/// cache, that the cache stays within its allowed bounds.
pub(super) struct SharedNodeCache<H>
where
	H: AsRef<[u8]>,
{
	/// The cached nodes, ordered by least recently used.
	pub(super) lru: SharedNodeCacheMap<H>,
}

impl<H: AsRef<[u8]> + Eq + std::hash::Hash> SharedNodeCache<H> {
	/// Create a new instance.
	fn new(max_inline_size: usize, max_heap_size: usize) -> Self {
		Self {
			lru: LruMap::new(SharedNodeCacheLimiter {
				max_inline_size,
				max_heap_size,
				heap_size: 0,
				items_evicted: 0,
				max_items_evicted: 0, // Will be set during `update`.
			}),
		}
	}

	/// Update the cache with the `list` of nodes which were either newly added or accessed.
	pub fn update(&mut self, list: impl IntoIterator<Item = (H, NodeCached<H>)>) {
		let mut access_count = 0;
		let mut add_count = 0;

		self.lru.limiter_mut().items_evicted = 0;
		self.lru.limiter_mut().max_items_evicted =
			self.lru.len() * 100 / super::SHARED_NODE_CACHE_MAX_REPLACE_PERCENT;

		for (key, cached_node) in list {
			if cached_node.is_from_shared_cache {
				if self.lru.get(&key).is_some() {
					access_count += 1;

					if access_count >= super::SHARED_NODE_CACHE_MAX_PROMOTED_KEYS {
						// Stop when we've promoted a large enough number of items.
						break
					}

					continue
				}
			}

			self.lru.insert(key, cached_node.node);
			add_count += 1;

			if self.lru.limiter().items_evicted > self.lru.limiter().max_items_evicted {
				// Stop when we've evicted a big enough chunk of the shared cache.
				break
			}
		}

		tracing::debug!(
			target: super::LOG_TARGET,
			"Updated the shared node cache: {} accesses, {} new values, {}/{} evicted (length = {}, inline size={}/{}, heap size={}/{})",
			access_count,
			add_count,
			self.lru.limiter().items_evicted,
			self.lru.limiter().max_items_evicted,
			self.lru.len(),
			self.lru.memory_usage(),
			self.lru.limiter().max_inline_size,
			self.lru.limiter().heap_size,
			self.lru.limiter().max_heap_size,
		);
	}

	/// Reset the cache.
	fn reset(&mut self) {
		self.lru.clear();
	}
}

/// The hash of [`ValueCacheKey`].
#[derive(PartialEq, Eq, Clone, Copy, Hash)]
#[repr(transparent)]
pub struct ValueCacheKeyHash(u64);

impl ValueCacheKeyHash {
	pub fn raw(self) -> u64 {
		self.0
	}
}

impl ValueCacheKeyHash {
	pub fn from_hasher_and_storage_key(
		mut hasher: impl std::hash::Hasher,
		storage_key: &[u8],
	) -> Self {
		hasher.write(storage_key);

		Self(hasher.finish())
	}
}

impl nohash_hasher::IsEnabled for ValueCacheKeyHash {}

/// The key type that is being used to address a [`CachedValue`].
#[derive(Eq)]
pub(super) struct ValueCacheKey<H> {
	/// The storage root of the trie this key belongs to.
	pub storage_root: H,
	/// The key to access the value in the storage.
	pub storage_key: Arc<[u8]>,
	/// The hash that identifies this instance of `storage_root` and `storage_key`.
	pub hash: ValueCacheKeyHash,
}

/// A borrowed variant of [`ValueCacheKey`].
pub(super) struct ValueCacheRef<'a, H> {
	/// The storage root of the trie this key belongs to.
	pub storage_root: H,
	/// The key to access the value in the storage.
	pub storage_key: &'a [u8],
	/// The hash that identifies this instance of `storage_root` and `storage_key`.
	pub hash: ValueCacheKeyHash,
}

impl<'a, H> ValueCacheRef<'a, H> {
	pub fn new(storage_key: &'a [u8], storage_root: H) -> Self
	where
		H: AsRef<[u8]>,
	{
		let hash = ValueCacheKey::<H>::hash_data(&storage_key, &storage_root);
		Self { storage_root, storage_key, hash }
	}
}

impl<'a, H> From<ValueCacheRef<'a, H>> for ValueCacheKey<H> {
	fn from(value: ValueCacheRef<'a, H>) -> Self {
		ValueCacheKey {
			storage_root: value.storage_root,
			storage_key: value.storage_key.into(),
			hash: value.hash,
		}
	}
}

impl<'a, H: std::hash::Hash> std::hash::Hash for ValueCacheRef<'a, H> {
	fn hash<Hasher: std::hash::Hasher>(&self, state: &mut Hasher) {
		self.hash.hash(state)
	}
}

impl<'a, H> PartialEq<ValueCacheKey<H>> for ValueCacheRef<'a, H>
where
	H: AsRef<[u8]>,
{
	fn eq(&self, rhs: &ValueCacheKey<H>) -> bool {
		self.storage_root.as_ref() == rhs.storage_root.as_ref() &&
			self.storage_key == &*rhs.storage_key
	}
}

impl<H> ValueCacheKey<H> {
	/// Constructs [`Self::Value`].
	#[cfg(test)] // Only used in tests.
	pub fn new_value(storage_key: impl Into<Arc<[u8]>>, storage_root: H) -> Self
	where
		H: AsRef<[u8]>,
	{
		let storage_key = storage_key.into();
		let hash = Self::hash_data(&storage_key, &storage_root);
		Self { storage_root, storage_key, hash }
	}

	/// Returns a hasher prepared to build the final hash to identify [`Self`].
	///
	/// See [`Self::hash_data`] for building the hash directly.
	pub fn hash_partial_data(storage_root: &H) -> impl std::hash::Hasher + Clone
	where
		H: AsRef<[u8]>,
	{
		let mut hasher = RANDOM_STATE.build_hasher();
		hasher.write(storage_root.as_ref());
		hasher
	}

	/// Hash the `key` and `storage_root` that identify [`Self`].
	///
	/// Returns a `u64` which represents the unique hash for the given inputs.
	pub fn hash_data(key: &[u8], storage_root: &H) -> ValueCacheKeyHash
	where
		H: AsRef<[u8]>,
	{
		let hasher = Self::hash_partial_data(storage_root);

		ValueCacheKeyHash::from_hasher_and_storage_key(hasher, key)
	}

	/// Checks whether the key is equal to the given `storage_key` and `storage_root`.
	#[inline]
	pub fn is_eq(&self, storage_root: &H, storage_key: &[u8]) -> bool
	where
		H: PartialEq,
	{
		self.storage_root == *storage_root && *self.storage_key == *storage_key
	}
}

// Implement manually so that only `hash` is accessed.
impl<H: std::hash::Hash> std::hash::Hash for ValueCacheKey<H> {
	fn hash<Hasher: std::hash::Hasher>(&self, state: &mut Hasher) {
		self.hash.hash(state)
	}
}

impl<H> nohash_hasher::IsEnabled for ValueCacheKey<H> {}

// Implement manually to not have to compare `hash`.
impl<H: PartialEq> PartialEq for ValueCacheKey<H> {
	#[inline]
	fn eq(&self, other: &Self) -> bool {
		self.is_eq(&other.storage_root, &other.storage_key)
	}
}

type SharedValueCacheMap<H> = schnellru::LruMap<
	ValueCacheKey<H>,
	CachedValue<H>,
	SharedValueCacheLimiter,
	BuildNoHashHasher<ValueCacheKey<H>>,
>;

/// The shared value cache.
///
/// The cache ensures that it stays in the configured size bounds.
pub(super) struct SharedValueCache<H>
where
	H: AsRef<[u8]>,
{
	/// The cached nodes, ordered by least recently used.
	pub(super) lru: SharedValueCacheMap<H>,
}

impl<H: Eq + std::hash::Hash + Clone + Copy + AsRef<[u8]>> SharedValueCache<H> {
	/// Create a new instance.
	fn new(max_inline_size: usize, max_heap_size: usize) -> Self {
		Self {
			lru: schnellru::LruMap::with_hasher(
				SharedValueCacheLimiter {
					max_inline_size,
					max_heap_size,
					heap_size: 0,
					known_storage_keys: Default::default(),
					items_evicted: 0,
					max_items_evicted: 0, // Will be set during `update`.
				},
				Default::default(),
			),
		}
	}

	/// Update the cache with the `added` values and the `accessed` values.
	///
	/// The `added` values are the ones that have been collected by doing operations on the trie and
	/// now should be stored in the shared cache. The `accessed` values are only referenced by the
	/// [`ValueCacheKeyHash`] and represent the values that were retrieved from this shared cache.
	/// These `accessed` values are being put to the front of the internal [`LruMap`] like the
	/// `added` ones.
	pub fn update(
		&mut self,
		added: impl IntoIterator<Item = (ValueCacheKey<H>, CachedValue<H>)>,
		accessed: impl IntoIterator<Item = ValueCacheKeyHash>,
	) {
		let mut access_count = 0;
		let mut add_count = 0;

		for hash in accessed {
			// Access every node in the map to put it to the front.
			//
			// Since we are only comparing the hashes here it may lead us to promoting the wrong
			// values as the most recently accessed ones. However this is harmless as the only
			// consequence is that we may accidentally prune a recently used value too early.
			self.lru.get_by_hash(hash.raw(), |existing_key, _| existing_key.hash == hash);
			access_count += 1;
		}

		// Insert all of the new items which were *not* found in the shared cache.
		//
		// Limit how many items we'll replace in the shared cache in one go so that
		// we don't evict the whole shared cache nor we keep spinning our wheels
		// evicting items which we've added ourselves in previous iterations of this loop.

		self.lru.limiter_mut().items_evicted = 0;
		self.lru.limiter_mut().max_items_evicted =
			self.lru.len() * 100 / super::SHARED_VALUE_CACHE_MAX_REPLACE_PERCENT;

		for (key, value) in added {
			self.lru.insert(key, value);
			add_count += 1;

			if self.lru.limiter().items_evicted > self.lru.limiter().max_items_evicted {
				// Stop when we've evicted a big enough chunk of the shared cache.
				break
			}
		}

		tracing::debug!(
			target: super::LOG_TARGET,
			"Updated the shared value cache: {} accesses, {} new values, {}/{} evicted (length = {}, known_storage_keys = {}, inline size={}/{}, heap size={}/{})",
			access_count,
			add_count,
			self.lru.limiter().items_evicted,
			self.lru.limiter().max_items_evicted,
			self.lru.len(),
			self.lru.limiter().known_storage_keys.len(),
			self.lru.memory_usage(),
			self.lru.limiter().max_inline_size,
			self.lru.limiter().heap_size,
			self.lru.limiter().max_heap_size
		);
	}

	/// Reset the cache.
	fn reset(&mut self) {
		self.lru.clear();
	}
}

/// The inner of [`SharedTrieCache`].
pub(super) struct SharedTrieCacheInner<H: Hasher> {
	node_cache: SharedNodeCache<H::Out>,
	value_cache: SharedValueCache<H::Out>,
}

impl<H: Hasher> SharedTrieCacheInner<H> {
	/// Returns a reference to the [`SharedValueCache`].
	#[cfg(test)]
	pub(super) fn value_cache(&self) -> &SharedValueCache<H::Out> {
		&self.value_cache
	}

	/// Returns a mutable reference to the [`SharedValueCache`].
	pub(super) fn value_cache_mut(&mut self) -> &mut SharedValueCache<H::Out> {
		&mut self.value_cache
	}

	/// Returns a reference to the [`SharedNodeCache`].
	#[cfg(test)]
	pub(super) fn node_cache(&self) -> &SharedNodeCache<H::Out> {
		&self.node_cache
	}

	/// Returns a mutable reference to the [`SharedNodeCache`].
	pub(super) fn node_cache_mut(&mut self) -> &mut SharedNodeCache<H::Out> {
		&mut self.node_cache
	}
}

/// The shared trie cache.
///
/// It should be instantiated once per node. It will hold the trie nodes and values of all
/// operations to the state. To not use all available memory it will ensure to stay in the
/// bounds given via the [`CacheSize`] at startup.
///
/// The instance of this object can be shared between multiple threads.
pub struct SharedTrieCache<H: Hasher> {
	inner: Arc<RwLock<SharedTrieCacheInner<H>>>,
}

impl<H: Hasher> Clone for SharedTrieCache<H> {
	fn clone(&self) -> Self {
		Self { inner: self.inner.clone() }
	}
}

impl<H: Hasher> SharedTrieCache<H> {
	/// Create a new [`SharedTrieCache`].
	pub fn new(cache_size: CacheSize) -> Self {
		let total_budget = cache_size.0;

		// Split our memory budget between the two types of caches.
		let value_cache_budget = (total_budget as f32 * 0.20) as usize; // 20% for the value cache
		let node_cache_budget = total_budget - value_cache_budget; // 80% for the node cache

		// Split our memory budget between what we'll be holding inline in the map,
		// and what we'll be holding on the heap.
		let value_cache_inline_budget = (value_cache_budget as f32 * 0.70) as usize;
		let node_cache_inline_budget = (node_cache_budget as f32 * 0.70) as usize;

		// Calculate how much memory the maps will be allowed to hold inline given our budget.
		let value_cache_max_inline_size =
			SharedValueCacheMap::<H::Out>::memory_usage_for_memory_budget(
				value_cache_inline_budget,
			);

		let node_cache_max_inline_size =
			SharedNodeCacheMap::<H::Out>::memory_usage_for_memory_budget(node_cache_inline_budget);

		// And this is how much data we'll at most keep on the heap for each cache.
		let value_cache_max_heap_size = value_cache_budget - value_cache_max_inline_size;
		let node_cache_max_heap_size = node_cache_budget - node_cache_max_inline_size;

		tracing::debug!(
			target: super::LOG_TARGET,
			"Configured a shared trie cache with a budget of ~{} bytes (node_cache_max_inline_size = {}, node_cache_max_heap_size = {}, value_cache_max_inline_size = {}, value_cache_max_heap_size = {})",
			total_budget,
			node_cache_max_inline_size,
			node_cache_max_heap_size,
			value_cache_max_inline_size,
			value_cache_max_heap_size,
		);

		Self {
			inner: Arc::new(RwLock::new(SharedTrieCacheInner {
				node_cache: SharedNodeCache::new(
					node_cache_max_inline_size,
					node_cache_max_heap_size,
				),
				value_cache: SharedValueCache::new(
					value_cache_max_inline_size,
					value_cache_max_heap_size,
				),
			})),
		}
	}

	/// Create a new [`LocalTrieCache`](super::LocalTrieCache) instance from this shared cache.
	pub fn local_cache(&self) -> super::LocalTrieCache<H> {
		super::LocalTrieCache {
			shared: self.clone(),
			node_cache: Default::default(),
			value_cache: Default::default(),
			shared_value_cache_access: Mutex::new(super::ValueAccessSet::with_hasher(
				schnellru::ByLength::new(super::SHARED_VALUE_CACHE_MAX_PROMOTED_KEYS),
				Default::default(),
			)),
			stats: Default::default(),
		}
	}

	/// Get a copy of the node for `key`.
	///
	/// This will temporarily lock the shared cache for reading.
	///
	/// This doesn't change the least recently order in the internal [`LruMap`].
	#[inline]
	pub fn peek_node(&self, key: &H::Out) -> Option<NodeOwned<H::Out>> {
		self.inner.read().node_cache.lru.peek(key).cloned()
	}

	/// Get a copy of the [`CachedValue`] for `key`.
	///
	/// This will temporarily lock the shared cache for reading.
	///
	/// This doesn't reorder any of the elements in the internal [`LruMap`].
	pub fn peek_value_by_hash(
		&self,
		hash: ValueCacheKeyHash,
		storage_root: &H::Out,
		storage_key: &[u8],
	) -> Option<CachedValue<H::Out>> {
		self.inner
			.read()
			.value_cache
			.lru
			.peek_by_hash(hash.0, |existing_key, _| existing_key.is_eq(storage_root, storage_key))
			.cloned()
	}

	/// Returns the used memory size of this cache in bytes.
	pub fn used_memory_size(&self) -> usize {
		let inner = self.inner.read();
		let value_cache_size =
			inner.value_cache.lru.memory_usage() + inner.value_cache.lru.limiter().heap_size;
		let node_cache_size =
			inner.node_cache.lru.memory_usage() + inner.node_cache.lru.limiter().heap_size;

		node_cache_size + value_cache_size
	}

	/// Reset the node cache.
	pub fn reset_node_cache(&self) {
		self.inner.write().node_cache.reset();
	}

	/// Reset the value cache.
	pub fn reset_value_cache(&self) {
		self.inner.write().value_cache.reset();
	}

	/// Reset the entire cache.
	pub fn reset(&self) {
		self.reset_node_cache();
		self.reset_value_cache();
	}

	/// Returns the read locked inner.
	#[cfg(test)]
	pub(super) fn read_lock_inner(
		&self,
	) -> parking_lot::RwLockReadGuard<'_, SharedTrieCacheInner<H>> {
		self.inner.read()
	}

	/// Returns the write locked inner.
	pub(super) fn write_lock_inner(&self) -> Option<RwLockWriteGuard<'_, SharedTrieCacheInner<H>>> {
		// This should never happen, but we *really* don't want to deadlock. So let's have it
		// timeout, just in case. At worst it'll do nothing, and at best it'll avert a catastrophe
		// and notify us that there's a problem.
		self.inner.try_write_for(super::SHARED_CACHE_WRITE_LOCK_TIMEOUT)
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use sp_core::H256 as Hash;

	#[test]
	fn shared_value_cache_works() {
		let mut cache = SharedValueCache::<sp_core::H256>::new(usize::MAX, 10 * 10);

		let key = vec![0; 10];

		let root0 = Hash::repeat_byte(1);
		let root1 = Hash::repeat_byte(2);

		cache.update(
			vec![
				(ValueCacheKey::new_value(&key[..], root0), CachedValue::NonExisting),
				(ValueCacheKey::new_value(&key[..], root1), CachedValue::NonExisting),
			],
			vec![],
		);

		// Ensure that the basics are working
		assert_eq!(1, cache.lru.limiter_mut().known_storage_keys.len());
		assert_eq!(
			3, // Two instances inside the cache + one extra in `known_storage_keys`.
			Arc::strong_count(cache.lru.limiter_mut().known_storage_keys.get(&key[..]).unwrap())
		);
		assert_eq!(key.len(), cache.lru.limiter().heap_size);
		assert_eq!(cache.lru.len(), 2);
		assert_eq!(cache.lru.peek_newest().unwrap().0.storage_root, root1);
		assert_eq!(cache.lru.peek_oldest().unwrap().0.storage_root, root0);
		assert!(cache.lru.limiter().heap_size <= cache.lru.limiter().max_heap_size);
		assert_eq!(cache.lru.limiter().heap_size, 10);

		// Just accessing a key should not change anything on the size and number of entries.
		cache.update(vec![], vec![ValueCacheKey::hash_data(&key[..], &root0)]);
		assert_eq!(1, cache.lru.limiter_mut().known_storage_keys.len());
		assert_eq!(
			3,
			Arc::strong_count(cache.lru.limiter_mut().known_storage_keys.get(&key[..]).unwrap())
		);
		assert_eq!(key.len(), cache.lru.limiter().heap_size);
		assert_eq!(cache.lru.len(), 2);
		assert_eq!(cache.lru.peek_newest().unwrap().0.storage_root, root0);
		assert_eq!(cache.lru.peek_oldest().unwrap().0.storage_root, root1);
		assert!(cache.lru.limiter().heap_size <= cache.lru.limiter().max_heap_size);
		assert_eq!(cache.lru.limiter().heap_size, 10);

		// Updating the cache again with exactly the same data should not change anything.
		cache.update(
			vec![
				(ValueCacheKey::new_value(&key[..], root1), CachedValue::NonExisting),
				(ValueCacheKey::new_value(&key[..], root0), CachedValue::NonExisting),
			],
			vec![],
		);
		assert_eq!(1, cache.lru.limiter_mut().known_storage_keys.len());
		assert_eq!(
			3,
			Arc::strong_count(cache.lru.limiter_mut().known_storage_keys.get(&key[..]).unwrap())
		);
		assert_eq!(key.len(), cache.lru.limiter().heap_size);
		assert_eq!(cache.lru.len(), 2);
		assert_eq!(cache.lru.peek_newest().unwrap().0.storage_root, root0);
		assert_eq!(cache.lru.peek_oldest().unwrap().0.storage_root, root1);
		assert!(cache.lru.limiter().heap_size <= cache.lru.limiter().max_heap_size);
		assert_eq!(cache.lru.limiter().items_evicted, 0);
		assert_eq!(cache.lru.limiter().heap_size, 10);

		// Add 10 other entries and this should move out two of the initial entries.
		cache.update(
			(1..11)
				.map(|i| vec![i; 10])
				.map(|key| (ValueCacheKey::new_value(&key[..], root0), CachedValue::NonExisting)),
			vec![],
		);

		assert_eq!(cache.lru.limiter().items_evicted, 2);
		assert_eq!(10, cache.lru.len());
		assert_eq!(10, cache.lru.limiter_mut().known_storage_keys.len());
		assert!(cache.lru.limiter_mut().known_storage_keys.get(&key[..]).is_none());
		assert_eq!(key.len() * 10, cache.lru.limiter().heap_size);
		assert_eq!(cache.lru.len(), 10);
		assert!(cache.lru.limiter().heap_size <= cache.lru.limiter().max_heap_size);
		assert_eq!(cache.lru.limiter().heap_size, 100);

		assert!(matches!(
			cache.lru.peek(&ValueCacheKey::new_value(&[1; 10][..], root0)).unwrap(),
			CachedValue::<Hash>::NonExisting
		));

		assert!(cache.lru.peek(&ValueCacheKey::new_value(&[1; 10][..], root1)).is_none(),);

		assert!(cache.lru.peek(&ValueCacheKey::new_value(&key[..], root0)).is_none());
		assert!(cache.lru.peek(&ValueCacheKey::new_value(&key[..], root1)).is_none());

		cache.update(
			vec![(ValueCacheKey::new_value(vec![10; 10], root0), CachedValue::NonExisting)],
			vec![],
		);

		assert!(cache.lru.limiter_mut().known_storage_keys.get(&key[..]).is_none());
	}
}
