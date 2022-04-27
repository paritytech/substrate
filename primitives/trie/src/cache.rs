// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
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

use crate::{Error, NodeCodec};
use hash_db::Hasher;
use lru::LruCache;
use nohash_hasher::{BuildNoHashHasher, IntMap, IntSet};
use parking_lot::{Mutex, MutexGuard, RwLock, RwLockReadGuard};
use std::{
	collections::{
		hash_map::{DefaultHasher, Entry},
		HashMap, HashSet,
	},
	hash::Hasher as _,
	sync::Arc,
};
use trie_db::{node::NodeOwned, CachedValue};

/// No hashing [`lru::LruCache`].
///
/// The key is an `u64` that is expected to be unique.
type NoHashingLruCache<T> = lru::LruCache<u64, T, BuildNoHashHasher<u64>>;

/// Get the key for the value cache.
///
/// The key is build by hashing the actual storage `key` and the `storage_root`.
fn value_cache_get_key(key: &[u8], storage_root: &impl AsRef<[u8]>) -> u64 {
	let mut hasher = DefaultHasher::default();
	hasher.write(key);
	hasher.write(storage_root.as_ref());
	hasher.finish()
}

pub struct SharedTrieNodeCache<H: Hasher> {
	node_cache: Arc<RwLock<LruCache<H::Out, NodeOwned<H::Out>>>>,
	value_cache: Arc<RwLock<NoHashingLruCache<CachedValue<H::Out>>>>,
}

impl<H: Hasher> Clone for SharedTrieNodeCache<H> {
	fn clone(&self) -> Self {
		Self { node_cache: self.node_cache.clone(), value_cache: self.value_cache.clone() }
	}
}

impl<H: Hasher> SharedTrieNodeCache<H> {
	/// Create a new [`SharedTrieNodeCache`].
	pub fn new() -> Self {
		Self {
			node_cache: Arc::new(RwLock::new(LruCache::unbounded())),
			value_cache: Arc::new(RwLock::new(NoHashingLruCache::unbounded_with_hasher(
				Default::default(),
			))),
		}
	}

	/// Create a new [`LocalTrieNodeCache`] instance from this shared cache.
	pub fn local_cache(&self) -> LocalTrieNodeCache<H> {
		LocalTrieNodeCache {
			shared: self.clone(),
			node_cache: Default::default(),
			value_cache: Default::default(),
			shared_node_cache_access: Default::default(),
			shared_value_cache_access: Default::default(),
		}
	}
}

pub struct LocalTrieNodeCache<H: Hasher> {
	shared: SharedTrieNodeCache<H>,
	node_cache: Mutex<HashMap<H::Out, NodeOwned<H::Out>>>,
	shared_node_cache_access: Mutex<HashSet<H::Out>>,
	value_cache: Mutex<IntMap<u64, CachedValue<H::Out>>>,
	shared_value_cache_access: Mutex<IntSet<u64>>,
}

impl<H: Hasher> LocalTrieNodeCache<H> {
	/// Return self as a [`TrieDB`](trie_db::TrieDB) compatible cache.
	///
	/// The given `storage_root` needs to be the storage root of the trie this cache is used for.
	pub fn as_trie_db_cache<'a>(&'a self, storage_root: H::Out) -> TrieNodeCache<'a, H> {
		let value_cache = ValueCache::ForStorageRoot {
			storage_root,
			local_value_cache: self.value_cache.lock(),
			shared_value_cache: self.shared.value_cache.read(),
			shared_value_cache_access: self.shared_value_cache_access.lock(),
		};

		TrieNodeCache {
			shared_cache: self.shared.node_cache.read(),
			local_cache: self.node_cache.lock(),
			value_cache,
			shared_node_cache_access: self.shared_node_cache_access.lock(),
		}
	}

	/// Return self as [`TrieDBMut`](trie_db::TrieDBMut) compatible cache.
	///
	/// After finishing all operations with [`TrieDBMut`](trie_db::TrieDBMut) and having obtained
	/// the new storage root, [`TrieNodeCache::merge_into`] should be called to update this local
	/// cache instance. If the function is not called, cached data is just thrown away and not
	/// propagated to the shared cache. So, accessing these new items will be slower, but nothing
	/// would break because of this.
	pub fn as_trie_db_mut_cache<'a>(&'a self) -> TrieNodeCache<'a, H> {
		TrieNodeCache {
			shared_cache: self.shared.node_cache.read(),
			local_cache: self.node_cache.lock(),
			value_cache: ValueCache::Fresh(Default::default()),
			shared_node_cache_access: self.shared_node_cache_access.lock(),
		}
	}
}

impl<H: Hasher> Drop for LocalTrieNodeCache<H> {
	fn drop(&mut self) {
		let mut shared_node_cache = self.shared.node_cache.write();
		let mut shared_node_cache_access = self.shared_node_cache_access.lock();
		self.node_cache.lock().drain().for_each(|(k, v)| {
			shared_node_cache_access.remove(&k);
			shared_node_cache.put(k, v);
		});
		shared_node_cache_access.drain().for_each(|k| {
			shared_node_cache.get(&k);
		});

		let mut shared_value_cache = self.shared.value_cache.write();
		let mut shared_value_cache_access = self.shared_value_cache_access.lock();

		self.value_cache.lock().drain().for_each(|(k, v)| {
			shared_value_cache_access.remove(&k);
			shared_value_cache.put(k, v);
		});
		shared_value_cache_access.drain().for_each(|k| {
			shared_value_cache.get(&k);
		});
	}
}

/// The abstraction of the value cache for the [`TrieNodeCache`].
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

pub struct TrieNodeCache<'a, H: Hasher> {
	shared_cache: RwLockReadGuard<'a, LruCache<H::Out, NodeOwned<H::Out>>>,
	shared_node_cache_access: MutexGuard<'a, HashSet<H::Out>>,
	local_cache: MutexGuard<'a, HashMap<H::Out, NodeOwned<H::Out>>>,
	value_cache: ValueCache<'a, H::Out>,
}

impl<'a, H: Hasher> TrieNodeCache<'a, H> {
	/// Merge this cache into the given [`LocalTrieNodeCache`].
	///
	/// This function is only required to be called when this instance was created through
	/// [`LocalTrieNodeCache::as_trie_db_mut_cache`], otherwise this method is a no-op. The given
	/// `storage_root` is the new storage root that was obtained after finishing all operations
	/// using the [`TrieDBMut`](trie_db::TrieDBMut).
	pub fn merge_into(self, local: &LocalTrieNodeCache<H>, storage_root: H::Out) {
		let cache = if let ValueCache::Fresh(cache) = self.value_cache { cache } else { return };

		let mut value_cache = local.shared.value_cache.write();
		cache
			.into_iter()
			.map(|(k, v)| (value_cache_get_key(&k, &storage_root), v))
			.for_each(|(k, v)| {
				value_cache.push(k, v);
			});
	}
}

impl<'a, H: Hasher> trie_db::TrieCache<NodeCodec<H>> for TrieNodeCache<'a, H> {
	fn get_or_insert_node(
		&mut self,
		hash: H::Out,
		fetch_node: &mut dyn FnMut() -> trie_db::Result<NodeOwned<H::Out>, H::Out, Error<H::Out>>,
	) -> trie_db::Result<&NodeOwned<H::Out>, H::Out, Error<H::Out>> {
		if let Some(res) = self.shared_cache.peek(&hash) {
			self.shared_node_cache_access.insert(hash);
			return Ok(res)
		}

		match self.local_cache.entry(hash) {
			Entry::Occupied(res) => Ok(res.into_mut()),
			Entry::Vacant(vacant) => {
				let node = (*fetch_node)()?;
				Ok(vacant.insert(node))
			},
		}
	}

	fn insert_node(&mut self, hash: H::Out, node: NodeOwned<H::Out>) {
		self.local_cache.insert(hash, node);
	}

	fn get_node(&mut self, hash: &H::Out) -> Option<&NodeOwned<H::Out>> {
		if let Some(node) = self.shared_cache.peek(hash) {
			self.shared_node_cache_access.insert(*hash);
			return Some(node)
		}

		self.local_cache.get(hash)
	}

	fn lookup_value_for_key(&mut self, key: &[u8]) -> Option<&CachedValue<H::Out>> {
		self.value_cache.get(key)
	}

	fn cache_value_for_key(&mut self, key: &[u8], data: CachedValue<H::Out>) {
		self.value_cache.insert(key.into(), data);
	}
}

#[cfg(test)]
mod tests {
	use trie_db::{Bytes, Trie, TrieDBBuilder, TrieDBMutBuilder, TrieHash, TrieMut};

	use crate::cache::value_cache_get_key;

	type MemoryDB = crate::MemoryDB<sp_core::Blake2Hasher>;
	type Layout = crate::LayoutV1<sp_core::Blake2Hasher>;
	type Cache = super::SharedTrieNodeCache<sp_core::Blake2Hasher>;
	type Recorder = crate::recorder::Recorder<sp_core::Blake2Hasher>;

	const TEST_DATA: &[(&[u8], &[u8])] =
		&[(b"key1", b"val1"), (b"key2", &[2; 64]), (b"key3", b"val3"), (b"key4", &[4; 64])];

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

		let shared_cache = Cache::new();
		let local_cache = shared_cache.local_cache();

		{
			let mut cache = local_cache.as_trie_db_cache(root);
			let trie = TrieDBBuilder::<Layout>::new(&db, &root).with_cache(&mut cache).build();
			assert_eq!(TEST_DATA[0].1.to_vec(), trie.get(TEST_DATA[0].0).unwrap().unwrap());
		}

		// Local cache wasn't dropped yet, so there should nothing in the shared caches.
		assert!(shared_cache.value_cache.read().is_empty());
		assert!(shared_cache.node_cache.read().is_empty());

		drop(local_cache);

		// Now we should have the cached items in the shared cache.
		assert!(shared_cache.node_cache.read().len() >= 1);
		let cached_data = shared_cache
			.value_cache
			.read()
			.peek(&value_cache_get_key(TEST_DATA[0].0, &root))
			.unwrap()
			.clone();
		assert_eq!(Bytes::from(TEST_DATA[0].1.to_vec()), cached_data.data().unwrap());

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

		let shared_cache = Cache::new();
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
		assert_eq!(Bytes::from(new_value), cached_data.data().unwrap());
	}

	#[test]
	fn trie_db_cache_and_recorder_work_together() {
		let (db, root) = create_trie();

		let shared_cache = Cache::new();
		let local_cache = shared_cache.local_cache();

		// Run this twice so that we use the data cache in the second run.
		for _ in 0..2 {
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

			let storage_proof = recorder
				.into_storage_proof::<Layout>(
					&root,
					&db,
					Some(&mut local_cache.as_trie_db_cache(root)),
				)
				.unwrap();
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

		let shared_cache = Cache::new();
		let local_cache = shared_cache.local_cache();

		// Run this twice so that we use the data cache in the second run.
		for _ in 0..2 {
			let recorder = Recorder::default();
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

			let storage_proof = recorder
				.into_storage_proof::<Layout>(
					&root,
					&db,
					Some(&mut local_cache.as_trie_db_cache(root)),
				)
				.unwrap();
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

		let shared_cache = Cache::new();

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

		let most_recently_used_nodes =
			shared_cache.node_cache.read().iter().map(|d| d.0.clone()).collect::<Vec<_>>();

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
			shared_cache.node_cache.read().iter().map(|d| d.0.clone()).collect::<Vec<_>>()
		);
	}
}
