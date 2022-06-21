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
use lru::LruCache;
use nohash_hasher::{BuildNoHashHasher, IntMap, IntSet};
use parking_lot::{Mutex, MutexGuard, RwLock, RwLockReadGuard};
use std::{
	collections::{hash_map::Entry, HashMap, HashSet},
	hash::{BuildHasher, Hasher as _},
	mem,
	sync::Arc,
};
use trie_db::{node::NodeOwned, CachedValue};

const LOG_TARGET: &str = "trie-cache";

lazy_static::lazy_static! {
	static ref RANDOM_STATE: ahash::RandomState = ahash::RandomState::default();
}

/// No hashing [`LruCache`].
///
/// The key is an `u64` that is expected to be unique.
type NoHashingLruCache<T> = lru::LruCache<u64, T, BuildNoHashHasher<u64>>;

/// Returns a hasher prepared to build the final value cache key.
///
/// To build the final hash the storage key still needs to be added to the hasher.
/// If you are only interested in the full value cache key, you can directly use
/// [`value_cache_get_key`].
fn value_cache_partial_hash(storage_root: &impl AsRef<[u8]>) -> impl std::hash::Hasher + Clone {
	let mut hasher = RANDOM_STATE.build_hasher();
	hasher.write(storage_root.as_ref());
	hasher
}

/// Get the key for the value cache.
///
/// The key is build by hashing the actual storage `key` and the `storage_root`.
fn value_cache_get_key(key: &[u8], storage_root: &impl AsRef<[u8]>) -> u64 {
	let mut hasher = value_cache_partial_hash(storage_root);
	hasher.write(key);
	hasher.finish()
}

/// The shared node cache.
///
/// Internally this stores all cached nodes in a [`LruCache`]. It ensures that when updating the
/// cache, that the cache stays within its allowed bounds.
struct SharedNodeCache<H: Hasher> {
	/// The cached nodes, ordered by least recently used.
	lru: LruCache<H::Out, NodeOwned<H::Out>>,
	/// The size of [`Self::lru`] in bytes.
	size_in_bytes: usize,
	/// The maximum cache size of [`Self::lru`].
	cache_size: CacheSize,
}

impl<H: Hasher> SharedNodeCache<H> {
	/// Create a new instance.
	fn new(cache_size: CacheSize) -> Self {
		Self { lru: LruCache::unbounded(), size_in_bytes: 0, cache_size }
	}

	/// Get the node for `key`.
	///
	/// This doesn't change the least recently order in the internal [`LruCache`].
	fn get(&self, key: &H::Out) -> Option<&NodeOwned<H::Out>> {
		self.lru.peek(key)
	}

	/// Update the cache with the `added` nodes and the `accessed` nodes.
	///
	/// The `added` nodes are the ones that have been collected by doing operations on the trie and
	/// now should be stored in the shared cache. The `accessed` nodes are only referenced by hash
	/// and represent the nodes that were retrieved from this shared cache through [`Self::get`].
	/// These `accessed` nodes are being put to the front of the internal [`LruCache`] like the
	/// `added` ones.
	///
	/// After the internal [`LruCache`] was updated, it is ensured that the internal [`LruCache`] is
	/// inside its bounds ([`Self::maximum_size_in_bytes`]).
	fn update(
		&mut self,
		added: impl IntoIterator<Item = (H::Out, NodeOwned<H::Out>)>,
		accessed: impl IntoIterator<Item = H::Out>,
	) {
		let update_size_in_bytes =
			|size_in_bytes: &mut usize, key: &H::Out, node: &NodeOwned<H::Out>| {
				if let Some(new_size_in_bytes) =
					size_in_bytes.checked_sub(key.as_ref().len() + node.size_in_bytes())
				{
					*size_in_bytes = new_size_in_bytes;
				} else {
					*size_in_bytes = 0;
					tracing::error!(target: LOG_TARGET, "Trie cache underflow detected!",);
				}
			};

		accessed.into_iter().for_each(|key| {
			// Access every node in the lru to put it to the front.
			self.lru.get(&key);
		});
		added.into_iter().for_each(|(key, node)| {
			self.size_in_bytes += key.as_ref().len() + node.size_in_bytes();

			if let Some((r_key, r_node)) = self.lru.push(key, node) {
				update_size_in_bytes(&mut self.size_in_bytes, &r_key, &r_node);
			}

			// Directly ensure that we respect the maximum size. By doing it directly here we ensure
			// that the internal map of the [`LruCache`] doesn't grow too much.
			while self.cache_size.exceeds(self.size_in_bytes) {
				// This should always be `Some(_)`, otherwise something is wrong!
				if let Some((key, node)) = self.lru.pop_lru() {
					update_size_in_bytes(&mut self.size_in_bytes, &key, &node);
				}
			}
		});
	}

	/// Reset the cache.
	fn reset(&mut self) {
		self.size_in_bytes = 0;
		self.lru.clear();
	}
}

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

/// The shared trie cache.
///
/// It should be instantiated once per node. It will hold the trie nodes and values of all
/// operations to the state. To not use all available memory it will ensure to stay in the
/// bounds given via the [`CacheSize`] at startup.
///
/// The instance of this object can be shared between multiple threads.
pub struct SharedTrieCache<H: Hasher> {
	node_cache: Arc<RwLock<SharedNodeCache<H>>>,
	/// The key to lookup a [`CachedValue`] is build using [`value_cache_get_key`].
	///
	/// We use this custom key generation function to use one [`LruCache`] over all different
	/// state tries. As the storage key can be the same for different state tries, we need to
	/// incorporate the storage root of the trie to get an unique key.
	value_cache: Arc<RwLock<NoHashingLruCache<CachedValue<H::Out>>>>,
}

impl<H: Hasher> Clone for SharedTrieCache<H> {
	fn clone(&self) -> Self {
		Self { node_cache: self.node_cache.clone(), value_cache: self.value_cache.clone() }
	}
}

impl<H: Hasher> SharedTrieCache<H> {
	/// Returns the size of one element in the value cache.
	fn value_cache_element_size() -> usize {
		// key + value
		mem::size_of::<u64>() + mem::size_of::<CachedValue<H::Out>>()
	}

	/// Create a new [`SharedTrieCache`].
	pub fn new(cache_size: CacheSize) -> Self {
		let (node_cache_size, value_cache) = match cache_size {
			CacheSize::Maximum(max) => {
				// The value cache element size isn't that huge, roughly around 50 bytes (mainly
				// depending on the hash size). Thus, we only give it 5% of the overall cache size.
				let value_cache_size_in_bytes = (max as f32 * 0.05) as usize;

				(
					CacheSize::Maximum(max - value_cache_size_in_bytes),
					NoHashingLruCache::with_hasher(
						value_cache_size_in_bytes / Self::value_cache_element_size(),
						Default::default(),
					),
				)
			},
			CacheSize::Unlimited =>
				(CacheSize::Unlimited, NoHashingLruCache::unbounded_with_hasher(Default::default())),
		};

		Self {
			node_cache: Arc::new(RwLock::new(SharedNodeCache::new(node_cache_size))),
			value_cache: Arc::new(RwLock::new(value_cache)),
		}
	}

	/// Create a new [`LocalTrieCache`] instance from this shared cache.
	pub fn local_cache(&self) -> LocalTrieCache<H> {
		LocalTrieCache {
			shared: self.clone(),
			node_cache: Default::default(),
			value_cache: Default::default(),
			shared_node_cache_access: Default::default(),
			shared_value_cache_access: Default::default(),
		}
	}

	/// Returns the used memory size of this cache in bytes.
	pub fn used_memory_size(&self) -> usize {
		let value_cache_size = self.value_cache.read().len() * Self::value_cache_element_size();
		let node_cache_size = self.node_cache.read().size_in_bytes;

		node_cache_size + value_cache_size
	}

	/// Reset the node cache.
	pub fn reset_node_cache(&self) {
		self.node_cache.write().reset();
	}

	/// Reset the value cache.
	pub fn reset_value_cache(&self) {
		self.value_cache.write().clear();
	}

	/// Reset the entire cache.
	pub fn reset(&self) {
		self.reset_node_cache();
		self.reset_value_cache();
	}
}

/// The local trie cache.
///
/// This cache should be used per state instance created by the backend. One state instance is
/// referring to the state of one block. It will cache all the accesses that are done to the state
/// which could not be fullfilled by the [`SharedTrieCache`]. These locally cached items are merged
/// back to the shared trie cache when this instance is dropped.
///
/// When using [`Self::as_trie_db_cache`] or [`Self::as_trie_db_mut_cache`], it will lock mutexes.
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
	value_cache: Mutex<IntMap<u64, CachedValue<H::Out>>>,
	/// Keeps track of all values accessed in the shared cache.
	///
	/// This will be used to ensure that these nodes are brought to the front of the lru when this
	/// local instance is merged back to the shared cache.
	shared_value_cache_access: Mutex<IntSet<u64>>,
}

impl<H: Hasher> LocalTrieCache<H> {
	/// Return self as a [`TrieDB`](trie_db::TrieDB) compatible cache.
	///
	/// The given `storage_root` needs to be the storage root of the trie this cache is used for.
	pub fn as_trie_db_cache<'a>(&'a self, storage_root: H::Out) -> TrieCache<'a, H> {
		let value_cache = ValueCache::ForStorageRoot {
			storage_root,
			local_value_cache: self.value_cache.lock(),
			shared_value_cache: self.shared.value_cache.read(),
			shared_value_cache_access: self.shared_value_cache_access.lock(),
		};

		TrieCache {
			shared_node_cache: self.shared.node_cache.read(),
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
	pub fn as_trie_db_mut_cache<'a>(&'a self) -> TrieCache<'a, H> {
		TrieCache {
			shared_node_cache: self.shared.node_cache.read(),
			local_cache: self.node_cache.lock(),
			value_cache: ValueCache::Fresh(Default::default()),
			shared_node_cache_access: self.shared_node_cache_access.lock(),
		}
	}
}

impl<H: Hasher> Drop for LocalTrieCache<H> {
	fn drop(&mut self) {
		self.shared
			.node_cache
			.write()
			.update(self.node_cache.lock().drain(), self.shared_node_cache_access.lock().drain());

		let mut shared_value_cache = self.shared.value_cache.write();
		let mut shared_value_cache_access = self.shared_value_cache_access.lock();

		// First write the new values that were cached here locally
		self.value_cache.lock().drain().for_each(|(k, v)| {
			shared_value_cache_access.remove(&k);
			shared_value_cache.put(k, v);
		});
		// Then only touch the ones that we have read from the global cache, to bring them
		// up in the lru.
		shared_value_cache_access.drain().for_each(|k| {
			shared_value_cache.get(&k);
		});
	}
}

/// The abstraction of the value cache for the [`TrieCache`].
enum ValueCache<'a, H> {
	/// The value cache is fresh, aka not yet associated to any storage root.
	/// This is used for example when a new trie is being build, to cache new values.
	Fresh(HashMap<Vec<u8>, CachedValue<H>>),
	/// The value cache is already bound to a specific storage root.
	ForStorageRoot {
		shared_value_cache: RwLockReadGuard<'a, NoHashingLruCache<CachedValue<H>>>,
		shared_value_cache_access: MutexGuard<'a, IntSet<u64>>,
		local_value_cache: MutexGuard<'a, IntMap<u64, CachedValue<H>>>,
		storage_root: H,
	},
}

impl<H: AsRef<[u8]>> ValueCache<'_, H> {
	/// Get the value for the given `key`.
	fn get(&mut self, key: &[u8]) -> Option<&CachedValue<H>> {
		match self {
			Self::Fresh(map) => map.get(key),
			Self::ForStorageRoot {
				local_value_cache,
				shared_value_cache,
				shared_value_cache_access,
				storage_root,
			} => {
				let key = value_cache_get_key(key, &storage_root);

				// We first need to look up in the local cache and then the shared cache.
				// It can happen that some value is cached in the shared cache, but the
				// weak reference of the data can not be upgraded anymore. This for example
				// happens when the node is dropped that contains the strong reference to the data.
				//
				// So, the logic of the trie would lookup the data and the node and store both
				// in our local caches.
				local_value_cache.get(&key).or_else(|| {
					shared_value_cache.peek(&key).map(|v| {
						shared_value_cache_access.insert(key);
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
				let key = value_cache_get_key(key, &storage_root);
				local_value_cache.insert(key, value);
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
	shared_node_cache: RwLockReadGuard<'a, SharedNodeCache<H>>,
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

		let mut value_cache = local.shared.value_cache.write();

		if !cache.is_empty() {
			let hasher = value_cache_partial_hash(&storage_root);

			cache
				.into_iter()
				.map(|(k, v)| {
					let mut hasher = hasher.clone();
					hasher.write(&k);
					(hasher.finish(), v)
				})
				.for_each(|(k, v)| {
					value_cache.push(k, v);
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
		if let Some(res) = self.shared_node_cache.get(&hash) {
			tracing::trace!(target: LOG_TARGET, ?hash, "Serving node from shared cache");
			self.shared_node_cache_access.insert(hash);
			return Ok(res)
		}

		match self.local_cache.entry(hash) {
			Entry::Occupied(res) => {
				tracing::trace!(target: LOG_TARGET, ?hash, "Serving node from local cache");
				Ok(res.into_mut())
			},
			Entry::Vacant(vacant) => {
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
		if let Some(node) = self.shared_node_cache.get(hash) {
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
		let res = self.value_cache.get(key);

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

	use crate::cache::value_cache_get_key;

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
		assert!(shared_cache.value_cache.read().is_empty());
		assert!(shared_cache.node_cache.read().lru.is_empty());

		drop(local_cache);

		// Now we should have the cached items in the shared cache.
		assert!(shared_cache.node_cache.read().lru.len() >= 1);
		let cached_data = shared_cache
			.value_cache
			.read()
			.peek(&value_cache_get_key(TEST_DATA[0].0, &root))
			.unwrap()
			.clone();
		assert_eq!(Bytes::from(TEST_DATA[0].1.to_vec()), cached_data.data().flatten().unwrap());

		let fake_data = Bytes::from(&b"fake_data"[..]);

		let local_cache = shared_cache.local_cache();
		shared_cache.value_cache.write().put(
			value_cache_get_key(TEST_DATA[1].0, &root),
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
		let local_cache = shared_cache.local_cache();

		let mut new_root = root;
		let mut cache = local_cache.as_trie_db_mut_cache();

		{
			let mut trie = TrieDBMutBuilder::<Layout>::from_existing(&mut db, &mut new_root)
				.with_cache(&mut cache)
				.build();

			trie.insert(&new_key, &new_value).unwrap();
		}

		cache.merge_into(&local_cache, new_root);

		let cached_data = shared_cache
			.value_cache
			.read()
			.peek(&value_cache_get_key(&new_key, &new_root))
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
				shared_cache.node_cache.write().reset();
			} else if i == 3 {
				shared_cache.value_cache.write().clear();
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
				shared_cache.node_cache.write().reset();
			} else if i == 3 {
				shared_cache.value_cache.write().clear();
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
			let mut proof_root = root.clone();

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
			.value_cache
			.read()
			.iter()
			.map(|d| d.0)
			.all(|l| TEST_DATA.iter().any(|d| *l == value_cache_get_key(&d.0, &root))));

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
			.value_cache
			.read()
			.iter()
			.take(2)
			.map(|d| d.0)
			.all(|l| { TEST_DATA.iter().take(2).any(|d| *l == value_cache_get_key(&d.0, &root)) }));

		let most_recently_used_nodes = shared_cache
			.node_cache
			.read()
			.lru
			.iter()
			.map(|d| d.0.clone())
			.collect::<Vec<_>>();

		// Delete the value cache, so that we access the nodes.
		shared_cache.value_cache.write().clear();

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
				.node_cache
				.read()
				.lru
				.iter()
				.map(|d| d.0.clone())
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

		let node_cache_size = shared_cache
			.node_cache
			.read()
			.lru
			.iter()
			.map(|(k, v)| k.as_ref().len() + v.size_in_bytes())
			.sum::<usize>();
		let value_cache_size = shared_cache.value_cache.read().len() *
			(mem::size_of::<u64>() + mem::size_of::<CachedValue<sp_core::H256>>());

		assert!(node_cache_size + value_cache_size < CACHE_SIZE_RAW);
	}
}
