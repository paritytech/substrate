// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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
use hashbrown::HashSet;
use nohash_hasher::BuildNoHashHasher;
use parking_lot::{Mutex, MutexGuard, RwLockReadGuard};
use shared_cache::{SharedValueCache, ValueCacheKey};
use std::{
	collections::{hash_map::Entry as MapEntry, HashMap},
	sync::Arc,
};
use trie_db::{node::NodeOwned, CachedValue};

mod shared_cache;

pub use shared_cache::SharedTrieCache;

use self::shared_cache::{SharedTrieCacheInner, ValueCacheKeyHash};

const LOG_TARGET: &str = "trie-cache";

/// The size of the cache.
#[derive(Debug, Clone, Copy)]
pub enum CacheSize {
	/// Do not limit the cache size.
	Unlimited,
	/// Let the cache in maximum use the given amount of bytes.
	Maximum(usize),
}

impl CacheSize {
	/// Returns `true` if the `current_size` exceeds the allowed size.
	fn exceeds(&self, current_size: usize) -> bool {
		match self {
			Self::Unlimited => false,
			Self::Maximum(max) => *max < current_size,
		}
	}
}

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
	node_cache: Mutex<HashMap<H::Out, NodeOwned<H::Out>>>,
	/// Keeps track of all the trie nodes accessed in the shared cache.
	///
	/// This will be used to ensure that these nodes are brought to the front of the lru when this
	/// local instance is merged back to the shared cache.
	shared_node_cache_access: Mutex<HashSet<H::Out>>,
	/// The local cache for the values.
	value_cache: Mutex<
		HashMap<
			ValueCacheKey<'static, H::Out>,
			CachedValue<H::Out>,
			BuildNoHashHasher<ValueCacheKey<'static, H::Out>>,
		>,
	>,
	/// Keeps track of all values accessed in the shared cache.
	///
	/// This will be used to ensure that these nodes are brought to the front of the lru when this
	/// local instance is merged back to the shared cache. This can actually lead to collision when
	/// two [`ValueCacheKey`]s with different storage roots and keys map to the same hash. However,
	/// as we only use this set to update the lru position it is fine, even if we bring the wrong
	/// value to the top. The important part is that we always get the correct value from the value
	/// cache for a given key.
	shared_value_cache_access:
		Mutex<HashSet<ValueCacheKeyHash, BuildNoHashHasher<ValueCacheKeyHash>>>,
}

impl<H: Hasher> LocalTrieCache<H> {
	/// Return self as a [`TrieDB`](trie_db::TrieDB) compatible cache.
	///
	/// The given `storage_root` needs to be the storage root of the trie this cache is used for.
	pub fn as_trie_db_cache(&self, storage_root: H::Out) -> TrieCache<'_, H> {
		let shared_inner = self.shared.read_lock_inner();

		let value_cache = ValueCache::ForStorageRoot {
			storage_root,
			local_value_cache: self.value_cache.lock(),
			shared_value_cache_access: self.shared_value_cache_access.lock(),
		};

		TrieCache {
			shared_inner,
			local_cache: self.node_cache.lock(),
			value_cache,
			shared_node_cache_access: self.shared_node_cache_access.lock(),
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
			shared_inner: self.shared.read_lock_inner(),
			local_cache: self.node_cache.lock(),
			value_cache: ValueCache::Fresh(Default::default()),
			shared_node_cache_access: self.shared_node_cache_access.lock(),
		}
	}
}

impl<H: Hasher> Drop for LocalTrieCache<H> {
	fn drop(&mut self) {
		let mut shared_inner = self.shared.write_lock_inner();

		shared_inner
			.node_cache_mut()
			.update(self.node_cache.lock().drain(), self.shared_node_cache_access.lock().drain());

		shared_inner
			.value_cache_mut()
			.update(self.value_cache.lock().drain(), self.shared_value_cache_access.lock().drain());
	}
}

/// The abstraction of the value cache for the [`TrieCache`].
enum ValueCache<'a, H> {
	/// The value cache is fresh, aka not yet associated to any storage root.
	/// This is used for example when a new trie is being build, to cache new values.
	Fresh(HashMap<Arc<[u8]>, CachedValue<H>>),
	/// The value cache is already bound to a specific storage root.
	ForStorageRoot {
		shared_value_cache_access: MutexGuard<
			'a,
			HashSet<ValueCacheKeyHash, nohash_hasher::BuildNoHashHasher<ValueCacheKeyHash>>,
		>,
		local_value_cache: MutexGuard<
			'a,
			HashMap<
				ValueCacheKey<'static, H>,
				CachedValue<H>,
				nohash_hasher::BuildNoHashHasher<ValueCacheKey<'static, H>>,
			>,
		>,
		storage_root: H,
	},
}

impl<H: AsRef<[u8]> + std::hash::Hash + Eq + Clone + Copy> ValueCache<'_, H> {
	/// Get the value for the given `key`.
	fn get<'a>(
		&'a mut self,
		key: &[u8],
		shared_value_cache: &'a SharedValueCache<H>,
	) -> Option<&CachedValue<H>> {
		match self {
			Self::Fresh(map) => map.get(key),
			Self::ForStorageRoot { local_value_cache, shared_value_cache_access, storage_root } => {
				let key = ValueCacheKey::new_ref(key, *storage_root);

				// We first need to look up in the local cache and then the shared cache.
				// It can happen that some value is cached in the shared cache, but the
				// weak reference of the data can not be upgraded anymore. This for example
				// happens when the node is dropped that contains the strong reference to the data.
				//
				// So, the logic of the trie would lookup the data and the node and store both
				// in our local caches.
				local_value_cache
					.get(unsafe {
						// SAFETY
						//
						// We need to convert the lifetime to make the compiler happy. However, as
						// we only use the `key` to looking up the value this lifetime conversion is
						// safe.
						std::mem::transmute::<&ValueCacheKey<'_, H>, &ValueCacheKey<'static, H>>(
							&key,
						)
					})
					.or_else(|| {
						shared_value_cache.get(&key).map(|v| {
							shared_value_cache_access.insert(key.get_hash());
							v
						})
					})
			},
		}
	}

	/// Insert some new `value` under the given `key`.
	fn insert(&mut self, key: &[u8], value: CachedValue<H>) {
		match self {
			Self::Fresh(map) => {
				map.insert(key.into(), value);
			},
			Self::ForStorageRoot { local_value_cache, storage_root, .. } => {
				local_value_cache.insert(ValueCacheKey::new_value(key, *storage_root), value);
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
	shared_inner: RwLockReadGuard<'a, SharedTrieCacheInner<H>>,
	shared_node_cache_access: MutexGuard<'a, HashSet<H::Out>>,
	local_cache: MutexGuard<'a, HashMap<H::Out, NodeOwned<H::Out>>>,
	value_cache: ValueCache<'a, H::Out>,
}

impl<'a, H: Hasher> TrieCache<'a, H> {
	/// Merge this cache into the given [`LocalTrieCache`].
	///
	/// This function is only required to be called when this instance was created through
	/// [`LocalTrieCache::as_trie_db_mut_cache`], otherwise this method is a no-op. The given
	/// `storage_root` is the new storage root that was obtained after finishing all operations
	/// using the [`TrieDBMut`](trie_db::TrieDBMut).
	pub fn merge_into(self, local: &LocalTrieCache<H>, storage_root: H::Out) {
		let cache = if let ValueCache::Fresh(cache) = self.value_cache { cache } else { return };

		if !cache.is_empty() {
			let mut value_cache = local.value_cache.lock();
			let partial_hash = ValueCacheKey::hash_partial_data(&storage_root);

			cache
				.into_iter()
				.map(|(k, v)| {
					let hash =
						ValueCacheKeyHash::from_hasher_and_storage_key(partial_hash.clone(), &k);
					(ValueCacheKey::Value { storage_key: k, storage_root, hash }, v)
				})
				.for_each(|(k, v)| {
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
		if let Some(res) = self.shared_inner.node_cache().get(&hash) {
			tracing::trace!(target: LOG_TARGET, ?hash, "Serving node from shared cache");
			self.shared_node_cache_access.insert(hash);
			return Ok(res)
		}

		match self.local_cache.entry(hash) {
			MapEntry::Occupied(res) => {
				tracing::trace!(target: LOG_TARGET, ?hash, "Serving node from local cache");
				Ok(res.into_mut())
			},
			MapEntry::Vacant(vacant) => {
				let node = (*fetch_node)();

				tracing::trace!(
					target: LOG_TARGET,
					?hash,
					fetch_successful = node.is_ok(),
					"Node not found, needed to fetch it."
				);

				Ok(vacant.insert(node?))
			},
		}
	}

	fn get_node(&mut self, hash: &H::Out) -> Option<&NodeOwned<H::Out>> {
		if let Some(node) = self.shared_inner.node_cache().get(hash) {
			tracing::trace!(target: LOG_TARGET, ?hash, "Getting node from shared cache");
			self.shared_node_cache_access.insert(*hash);
			return Some(node)
		}

		let res = self.local_cache.get(hash);

		tracing::trace!(
			target: LOG_TARGET,
			?hash,
			found = res.is_some(),
			"Getting node from local cache"
		);

		res
	}

	fn lookup_value_for_key(&mut self, key: &[u8]) -> Option<&CachedValue<H::Out>> {
		let res = self.value_cache.get(key, self.shared_inner.value_cache());

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

		self.value_cache.insert(key.into(), data);
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
	const CACHE_SIZE: CacheSize = CacheSize::Maximum(CACHE_SIZE_RAW);

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
		shared_cache.write_lock_inner().value_cache_mut().lru.put(
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
				let mut recorder = recorder.as_trie_recorder();
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
				let mut recorder = recorder.as_trie_recorder();
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
			.all(|l| TEST_DATA.iter().any(|d| l.storage_key().unwrap() == d.0)));

		{
			let local_cache = shared_cache.local_cache();

			let mut cache = local_cache.as_trie_db_cache(root);
			let trie = TrieDBBuilder::<Layout>::new(&db, &root).with_cache(&mut cache).build();

			for (k, _) in TEST_DATA.iter().take(2) {
				trie.get(k).unwrap().unwrap();
			}
		}

		// Ensure that the accessed items are most recently used items of the shared value cache.
		assert!(shared_cache
			.read_lock_inner()
			.value_cache()
			.lru
			.iter()
			.take(2)
			.map(|d| d.0)
			.all(|l| { TEST_DATA.iter().take(2).any(|d| l.storage_key().unwrap() == d.0) }));

		let most_recently_used_nodes = shared_cache
			.read_lock_inner()
			.node_cache()
			.lru
			.iter()
			.map(|d| *d.0)
			.collect::<Vec<_>>();

		// Delete the value cache, so that we access the nodes.
		shared_cache.reset_value_cache();

		{
			let local_cache = shared_cache.local_cache();

			let mut cache = local_cache.as_trie_db_cache(root);
			let trie = TrieDBBuilder::<Layout>::new(&db, &root).with_cache(&mut cache).build();

			for (k, _) in TEST_DATA.iter().take(2) {
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

		let node_cache_size = shared_cache.read_lock_inner().node_cache().size_in_bytes;
		let value_cache_size = shared_cache.read_lock_inner().value_cache().size_in_bytes;

		assert!(node_cache_size + value_cache_size < CACHE_SIZE_RAW);
	}
}
