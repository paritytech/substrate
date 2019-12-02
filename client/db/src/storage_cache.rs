// Copyright 2019 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Global cache state.

use std::collections::{VecDeque, HashSet, HashMap};
use std::sync::Arc;
use parking_lot::{Mutex, RwLock, RwLockUpgradableReadGuard};
use linked_hash_map::{LinkedHashMap, Entry};
use hash_db::Hasher;
use sp_runtime::traits::{Block as BlockT, Header};
use primitives::hexdisplay::HexDisplay;
use state_machine::{backend::Backend as StateBackend, TrieBackend};
use log::trace;
use client_api::backend::{StorageCollection, ChildStorageCollection};
use std::hash::Hash as StdHash;

const STATE_CACHE_BLOCKS: usize = 12;

type StorageKey = Vec<u8>;
type ChildStorageKey = (Vec<u8>, Vec<u8>);
type StorageValue = Vec<u8>;

/// Shared canonical state cache.
pub struct Cache<B: BlockT, H: Hasher> {
	/// Storage cache. `None` indicates that key is known to be missing.
	lru_storage: LRUMap<StorageKey, Option<StorageValue>>,
	/// Storage hashes cache. `None` indicates that key is known to be missing.
	lru_hashes: LRUMap<StorageKey, OptionHOut<H::Out>>,
	/// Storage cache for child trie. `None` indicates that key is known to be missing.
	lru_child_storage: LRUMap<ChildStorageKey, Option<StorageValue>>,
	/// Information on the modifications in recently committed blocks; specifically which keys
	/// changed in which block. Ordered by block number.
	modifications: VecDeque<BlockChanges<B::Header>>,
}

struct LRUMap<K, V>(LinkedHashMap<K, V>, usize, usize);

/// Internal trait similar to `heapsize` but using
/// a simply estimation.
///
/// This should not be made public, it is implementation
/// detail trait. If it need to become public please
/// consider using `malloc_size_of`.
trait EstimateSize {
	/// Return a size estimation of additional size needed
	/// to cache this struct (in bytes).
	fn estimate_size(&self) -> usize;
}

impl EstimateSize for Vec<u8> {
	fn estimate_size(&self) -> usize {
		self.capacity()
	}
}

impl EstimateSize for Option<Vec<u8>> {
	fn estimate_size(&self) -> usize {
		self.as_ref().map(|v|v.capacity()).unwrap_or(0)
	}
}

struct OptionHOut<T: AsRef<[u8]>>(Option<T>);

impl<T: AsRef<[u8]>> EstimateSize for OptionHOut<T> {
	fn estimate_size(&self) -> usize {
		// capacity would be better
		self.0.as_ref().map(|v|v.as_ref().len()).unwrap_or(0)
	}
}

impl<T: EstimateSize> EstimateSize for (T, T) {
	fn estimate_size(&self) -> usize {
		self.0.estimate_size() + self.1.estimate_size()
	}
}

impl<K: EstimateSize + Eq + StdHash, V: EstimateSize> LRUMap<K, V> {
	fn remove(&mut self, k: &K) {
		let map = &mut self.0;
		let storage_used_size = &mut self.1;
		if let Some(v) = map.remove(k) {
			*storage_used_size -= k.estimate_size();
			*storage_used_size -= v.estimate_size();
		}
	}

	fn add(&mut self, k: K, v: V) {
		let lmap = &mut self.0;
		let storage_used_size = &mut self.1;
		let limit = self.2;
		let klen = k.estimate_size();
		*storage_used_size += v.estimate_size();
		// TODO assert k v size fit into limit?? to avoid insert remove?
		match lmap.entry(k) {
			Entry::Occupied(mut entry) => {
				// note that in this case we are not running pure lru as
				// it would require to remove first
				*storage_used_size -= entry.get().estimate_size();
				entry.insert(v);
			},
			Entry::Vacant(entry) => {
				*storage_used_size += klen;
				entry.insert(v);
			},
		};

		while *storage_used_size > limit {
			if let Some((k,v)) = lmap.pop_front() {
				*storage_used_size -= k.estimate_size();
				*storage_used_size -= v.estimate_size();
			} else {
				// can happen fairly often as we get value from multiple lru
				// and only remove from a single lru
				break;
			}
		}
	}

	fn get<Q:?Sized>(&mut self, k: &Q) -> Option<&mut V>
		where K: std::borrow::Borrow<Q>,
			Q: StdHash + Eq {
		self.0.get_refresh(k)
	}

	fn used_size(&self) -> usize {
		self.1
	}
	fn clear(&mut self) {
		self.0.clear();
		self.1 = 0;
	}

}

impl<B: BlockT, H: Hasher> Cache<B, H> {
	/// Returns the used memory size of the storage cache in bytes.
	pub fn used_storage_cache_size(&self) -> usize {
		self.lru_storage.used_size()
			+ self.lru_child_storage.used_size()
			//  ignore small hashes storage and self.lru_hashes.used_size()
	}

	/// Synchronize the shared cache with the best block state.
	///
	/// This function updates the shared cache by removing entries
	/// that are invalidated by chain reorganization. It should be called
	/// externally when chain reorg happens without importing a new block.
	pub fn sync(&mut self, enacted: &[B::Hash], retracted: &[B::Hash]) {
		trace!("Syncing shared cache, enacted = {:?}, retracted = {:?}", enacted, retracted);

		// Purge changes from re-enacted and retracted blocks.
		let mut clear = false;
		for block in enacted {
			clear = clear || {
				if let Some(m) = self.modifications.iter_mut().find(|m| &m.hash == block) {
					trace!("Reverting enacted block {:?}", block);
					m.is_canon = true;
					for a in &m.storage {
						trace!("Reverting enacted key {:?}", HexDisplay::from(a));
						self.lru_storage.remove(a);
					}
					for a in &m.child_storage {
						trace!("Reverting enacted child key {:?}", a);
						self.lru_child_storage.remove(a);
					}
					false
				} else {
					true
				}
			};
		}

		for block in retracted {
			clear = clear || {
				if let Some(m) = self.modifications.iter_mut().find(|m| &m.hash == block) {
					trace!("Retracting block {:?}", block);
					m.is_canon = false;
					for a in &m.storage {
						trace!("Retracted key {:?}", HexDisplay::from(a));
						self.lru_storage.remove(a);
					}
					for a in &m.child_storage {
						trace!("Retracted child key {:?}", a);
						self.lru_child_storage.remove(a);
					}
					false
				} else {
					true
				}
			};
		}
		if clear {
			// We don't know anything about the block; clear everything
			trace!("Wiping cache");
			self.lru_storage.clear();
			self.lru_child_storage.clear();
			self.lru_hashes.clear();
			self.modifications.clear();
		}
	}
}

pub type SharedCache<B, H> = Arc<Mutex<Cache<B, H>>>;

/// Fix lru storage size for hash (small 64ko).
const FIX_LRU_HASH_SIZE: usize = 65_536;

/// Create a new shared cache instance with given max memory usage.
pub fn new_shared_cache<B: BlockT, H: Hasher>(
	shared_cache_size: usize,
	child_ratio: (usize, usize),
) -> SharedCache<B, H> {
	let top = child_ratio.1.saturating_sub(child_ratio.0);
	Arc::new(Mutex::new(Cache {
		lru_storage: LRUMap(LinkedHashMap::new(), 0,
			shared_cache_size * top / child_ratio.1),
		lru_hashes: LRUMap(LinkedHashMap::new(), 0, FIX_LRU_HASH_SIZE),
		lru_child_storage: LRUMap(LinkedHashMap::new(), 0,
			shared_cache_size * child_ratio.0 / child_ratio.1),
		modifications: VecDeque::new(),
	}))
}

#[derive(Debug)]
/// Accumulates a list of storage changed in a block.
struct BlockChanges<B: Header> {
	/// Block number.
	number: B::Number,
	/// Block hash.
	hash: B::Hash,
	/// Parent block hash.
	parent: B::Hash,
	/// A set of modified storage keys.
	storage: HashSet<StorageKey>,
	/// A set of modified child storage keys.
	child_storage: HashSet<ChildStorageKey>,
	/// Block is part of the canonical chain.
	is_canon: bool,
}

/// Cached values specific to a state.
struct LocalCache<H: Hasher> {
	/// Storage cache.
	///
	/// `None` indicates that key is known to be missing.
	storage: HashMap<StorageKey, Option<StorageValue>>,
	/// Storage hashes cache.
	///
	/// `None` indicates that key is known to be missing.
	hashes: HashMap<StorageKey, Option<H::Out>>,
	/// Child storage cache.
	///
	/// `None` indicates that key is known to be missing.
	child_storage: HashMap<ChildStorageKey, Option<StorageValue>>,
}

/// Cache changes.
pub struct CacheChanges<H: Hasher, B: BlockT> {
	/// Shared canonical state cache.
	shared_cache: SharedCache<B, H>,
	/// Local cache of values for this state.
	local_cache: RwLock<LocalCache<H>>,
	/// Hash of the block on top of which this instance was created or
	/// `None` if cache is disabled
	pub parent_hash: Option<B::Hash>,
}

/// State cache abstraction.
///
/// Manages shared global state cache which reflects the canonical
/// state as it is on the disk.
///
/// A instance of `CachingState` may be created as canonical or not.
/// For canonical instances local cache is accumulated and applied
/// in `sync_cache` along with the change overlay.
/// For non-canonical clones local cache and changes are dropped.
pub struct CachingState<H: Hasher, S: StateBackend<H>, B: BlockT> {
	/// Backing state.
	state: S,
	/// Cache data.
	pub cache: CacheChanges<H, B>
}

impl<H: Hasher, S: StateBackend<H>, B: BlockT> std::fmt::Debug for CachingState<H, S, B> {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "Block {:?}", self.cache.parent_hash)
	}
}

impl<H: Hasher, B: BlockT> CacheChanges<H, B> {
	/// Propagate local cache into the shared cache and synchronize
	/// the shared cache with the best block state.
	///
	/// This function updates the shared cache by removing entries
	/// that are invalidated by chain reorganization. `sync_cache`
	/// should be called after the block has been committed and the
	/// blockchain route has been calculated.
	pub fn sync_cache(
		&mut self,
		enacted: &[B::Hash],
		retracted: &[B::Hash],
		changes: StorageCollection,
		child_changes: ChildStorageCollection,
		commit_hash: Option<B::Hash>,
		commit_number: Option<<B::Header as Header>::Number>,
		is_best: bool,
	) {
		let mut cache = self.shared_cache.lock();
		trace!("Syncing cache, id = (#{:?}, {:?}), parent={:?}, best={}", commit_number, commit_hash, self.parent_hash, is_best);
		let cache = &mut *cache;
		// Filter out commiting block if any.
		let enacted: Vec<_> = enacted
			.iter()
			.filter(|h| commit_hash.as_ref().map_or(true, |p| *h != p))
			.cloned()
			.collect();
		cache.sync(&enacted, retracted);
		// Propagate cache only if committing on top of the latest canonical state
		// blocks are ordered by number and only one block with a given number is marked as canonical
		// (contributed to canonical state cache)
		if let Some(_) = self.parent_hash {
			let mut local_cache = self.local_cache.write();
			if is_best {
				trace!(
					"Committing {} local, {} hashes, {} modified root entries, {} modified child entries",
					local_cache.storage.len(),
					local_cache.hashes.len(),
					changes.len(),
					child_changes.iter().map(|v|v.1.len()).sum::<usize>(),
				);
				for (k, v) in local_cache.storage.drain() {
					cache.lru_storage.add(k, v);
				}
				for (k, v) in local_cache.child_storage.drain() {
					cache.lru_child_storage.add(k, v);
				}
				for (k, v) in local_cache.hashes.drain() {
					cache.lru_hashes.add(k, OptionHOut(v));
				}
			}
		}

		if let (
			Some(ref number), Some(ref hash), Some(ref parent))
				= (commit_number, commit_hash, self.parent_hash)
		{
			if cache.modifications.len() == STATE_CACHE_BLOCKS {
				cache.modifications.pop_back();
			}
			let mut modifications = HashSet::new();
			let mut child_modifications = HashSet::new();
			child_changes.into_iter().for_each(|(sk, changes)|
				for (k, v) in changes.into_iter() {
					let k = (sk.clone(), k);
					if is_best {
						cache.lru_child_storage.add(k.clone(), v);
					}
					child_modifications.insert(k);
				}
			);
			for (k, v) in changes.into_iter() {
				if is_best {
					cache.lru_hashes.remove(&k);
					cache.lru_storage.add(k.clone(), v);
				}
				modifications.insert(k);
			}

			// Save modified storage. These are ordered by the block number in reverse.
			let block_changes = BlockChanges {
				storage: modifications,
				child_storage: child_modifications,
				number: *number,
				hash: hash.clone(),
				is_canon: is_best,
				parent: parent.clone(),
			};
			let insert_at = cache.modifications.iter()
				.enumerate()
				.find(|(_, m)| m.number < *number)
				.map(|(i, _)| i);
			trace!("Inserting modifications at {:?}", insert_at);
			if let Some(insert_at) = insert_at {
				cache.modifications.insert(insert_at, block_changes);
			} else {
				cache.modifications.push_back(block_changes);
			}
		}
	}

}

impl<H: Hasher, S: StateBackend<H>, B: BlockT> CachingState<H, S, B> {
	/// Create a new instance wrapping generic State and shared cache.
	pub fn new(state: S, shared_cache: SharedCache<B, H>, parent_hash: Option<B::Hash>) -> CachingState<H, S, B> {
		CachingState {
			state,
			cache: CacheChanges {
				shared_cache,
				local_cache: RwLock::new(LocalCache {
					storage: Default::default(),
					hashes: Default::default(),
					child_storage: Default::default(),
				}),
				parent_hash: parent_hash,
			},
		}
	}

	/// Check if the key can be returned from cache by matching current block parent hash against canonical
	/// state and filtering out entries modified in later blocks.
	fn is_allowed(
		key: Option<&[u8]>,
		child_key: Option<&ChildStorageKey>,
		parent_hash: &Option<B::Hash>,
		modifications: &VecDeque<BlockChanges<B::Header>>
	) -> bool
	{
		let mut parent = match *parent_hash {
			None => {
				trace!("Cache lookup skipped for {:?}: no parent hash", key.as_ref().map(HexDisplay::from));
				return false;
			}
			Some(ref parent) => parent,
		};
		// Ignore all storage entries modified in later blocks.
		// Modifications contains block ordered by the number
		// We search for our parent in that list first and then for
		// all its parents until we hit the canonical block,
		// checking against all the intermediate modifications.
		for m in modifications {
			if &m.hash == parent {
				if m.is_canon {
					return true;
				}
				parent = &m.parent;
			}
			if let Some(key) = key {
				if m.storage.contains(key) {
					trace!("Cache lookup skipped for {:?}: modified in a later block", HexDisplay::from(&key));
					return false;
				}
			}
			if let Some(child_key) = child_key {
				if m.child_storage.contains(child_key) {
					trace!("Cache lookup skipped for {:?}: modified in a later block", child_key);
					return false;
				}
			}
		}
		trace!("Cache lookup skipped for {:?}: parent hash is unknown", key.as_ref().map(HexDisplay::from));
		false
	}

	/// Dispose state and return cache data.
	pub fn release(self) -> CacheChanges<H, B> {
		self.cache
	}
}

impl<H: Hasher, S: StateBackend<H>, B: BlockT> StateBackend<H> for CachingState<H, S, B> {
	type Error = S::Error;
	type Transaction = S::Transaction;
	type TrieBackendStorage = S::TrieBackendStorage;

	fn storage(&self, key: &[u8]) -> Result<Option<Vec<u8>>, Self::Error> {
		let local_cache = self.cache.local_cache.upgradable_read();
		// Note that local cache makes that lru is not refreshed
		if let Some(entry) = local_cache.storage.get(key).cloned() {
			trace!("Found in local cache: {:?}", HexDisplay::from(&key));
			return Ok(entry)
		}
		let mut cache = self.cache.shared_cache.lock();
		if Self::is_allowed(Some(key), None, &self.cache.parent_hash, &cache.modifications) {
			if let Some(entry) = cache.lru_storage.get(key).map(|a| a.clone()) {
				trace!("Found in shared cache: {:?}", HexDisplay::from(&key));
				return Ok(entry)
			}
		}
		trace!("Cache miss: {:?}", HexDisplay::from(&key));
		let value = self.state.storage(key)?;
		RwLockUpgradableReadGuard::upgrade(local_cache).storage.insert(key.to_vec(), value.clone());
		Ok(value)
	}

	fn storage_hash(&self, key: &[u8]) -> Result<Option<H::Out>, Self::Error> {
		let local_cache = self.cache.local_cache.upgradable_read();
		if let Some(entry) = local_cache.hashes.get(key).cloned() {
			trace!("Found hash in local cache: {:?}", HexDisplay::from(&key));
			return Ok(entry)
		}
		let mut cache = self.cache.shared_cache.lock();
		if Self::is_allowed(Some(key), None, &self.cache.parent_hash, &cache.modifications) {
			if let Some(entry) = cache.lru_hashes.get(key).map(|a| a.0.clone()) {
				trace!("Found hash in shared cache: {:?}", HexDisplay::from(&key));
				return Ok(entry)
			}
		}
		trace!("Cache hash miss: {:?}", HexDisplay::from(&key));
		let hash = self.state.storage_hash(key)?;
		RwLockUpgradableReadGuard::upgrade(local_cache).hashes.insert(key.to_vec(), hash);
		Ok(hash)
	}

	fn child_storage(&self, storage_key: &[u8], key: &[u8]) -> Result<Option<Vec<u8>>, Self::Error> {
		let key = (storage_key.to_vec(), key.to_vec());
		let local_cache = self.cache.local_cache.upgradable_read();
		if let Some(entry) = local_cache.child_storage.get(&key).cloned() {
			trace!("Found in local cache: {:?}", key);
			return Ok(entry)
		}
		let mut cache = self.cache.shared_cache.lock();
		if Self::is_allowed(None, Some(&key), &self.cache.parent_hash, &cache.modifications) {
			if let Some(entry) = cache.lru_child_storage.get(&key).map(|a| a.clone()) {
				trace!("Found in shared cache: {:?}", key);
				return Ok(entry)
			}
		}
		trace!("Cache miss: {:?}", key);
		let value = self.state.child_storage(storage_key, &key.1[..])?;
		RwLockUpgradableReadGuard::upgrade(local_cache).child_storage.insert(key, value.clone());
		Ok(value)
	}

	fn exists_storage(&self, key: &[u8]) -> Result<bool, Self::Error> {
		Ok(self.storage(key)?.is_some())
	}

	fn exists_child_storage(&self, storage_key: &[u8], key: &[u8]) -> Result<bool, Self::Error> {
		self.state.exists_child_storage(storage_key, key)
	}

	fn for_keys_in_child_storage<F: FnMut(&[u8])>(&self, storage_key: &[u8], f: F) {
		self.state.for_keys_in_child_storage(storage_key, f)
	}

	fn for_keys_with_prefix<F: FnMut(&[u8])>(&self, prefix: &[u8], f: F) {
		self.state.for_keys_with_prefix(prefix, f)
	}

	fn for_key_values_with_prefix<F: FnMut(&[u8], &[u8])>(&self, prefix: &[u8], f: F) {
		self.state.for_key_values_with_prefix(prefix, f)
	}

	fn for_child_keys_with_prefix<F: FnMut(&[u8])>(&self, storage_key: &[u8], prefix: &[u8], f: F) {
		self.state.for_child_keys_with_prefix(storage_key, prefix, f)
	}

	fn storage_root<I>(&self, delta: I) -> (H::Out, Self::Transaction)
		where
			I: IntoIterator<Item=(Vec<u8>, Option<Vec<u8>>)>,
			H::Out: Ord
	{
		self.state.storage_root(delta)
	}

	fn child_storage_root<I>(&self, storage_key: &[u8], delta: I) -> (H::Out, bool, Self::Transaction)
		where
			I: IntoIterator<Item=(Vec<u8>, Option<Vec<u8>>)>,
			H::Out: Ord
	{
		self.state.child_storage_root(storage_key, delta)
	}

	fn pairs(&self) -> Vec<(Vec<u8>, Vec<u8>)> {
		self.state.pairs()
	}

	fn keys(&self, prefix: &[u8]) -> Vec<Vec<u8>> {
		self.state.keys(prefix)
	}

	fn child_keys(&self, child_key: &[u8], prefix: &[u8]) -> Vec<Vec<u8>> {
		self.state.child_keys(child_key, prefix)
	}

	fn as_trie_backend(&mut self) -> Option<&TrieBackend<Self::TrieBackendStorage, H>> {
		self.state.as_trie_backend()
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use sp_runtime::testing::{H256, Block as RawBlock, ExtrinsicWrapper};
	use state_machine::backend::InMemory;
	use primitives::Blake2Hasher;

	type Block = RawBlock<ExtrinsicWrapper<u32>>;

	#[test]
	fn smoke() {
		//init_log();
		let root_parent = H256::random();
		let key = H256::random()[..].to_vec();
		let h0 = H256::random();
		let h1a = H256::random();
		let h1b = H256::random();
		let h2a = H256::random();
		let h2b = H256::random();
		let h3a = H256::random();
		let h3b = H256::random();

		let shared = new_shared_cache::<Block, Blake2Hasher>(256*1024, (0,1));

		// blocks  [ 3a(c) 2a(c) 2b 1b 1a(c) 0 ]
		// state   [ 5     5     4  3  2     2 ]
		let mut s = CachingState::new(InMemory::<Blake2Hasher>::default(), shared.clone(), Some(root_parent));
		s.cache.sync_cache(&[], &[], vec![(key.clone(), Some(vec![2]))], vec![], Some(h0), Some(0), true);

		let mut s = CachingState::new(InMemory::<Blake2Hasher>::default(), shared.clone(), Some(h0));
		s.cache.sync_cache(&[], &[], vec![], vec![], Some(h1a), Some(1), true);

		let mut s = CachingState::new(InMemory::<Blake2Hasher>::default(), shared.clone(), Some(h0));
		s.cache.sync_cache(&[], &[], vec![(key.clone(), Some(vec![3]))], vec![], Some(h1b), Some(1), false);

		let mut s = CachingState::new(InMemory::<Blake2Hasher>::default(), shared.clone(), Some(h1b.clone()));
		s.cache.sync_cache(&[], &[], vec![(key.clone(), Some(vec![4]))], vec![], Some(h2b), Some(2), false);

		let mut s = CachingState::new(InMemory::<Blake2Hasher>::default(), shared.clone(), Some(h1a.clone()));
		s.cache.sync_cache(&[], &[], vec![(key.clone(), Some(vec![5]))], vec![], Some(h2a), Some(2), true);

		let mut s = CachingState::new(InMemory::<Blake2Hasher>::default(), shared.clone(), Some(h2a));
		s.cache.sync_cache(&[], &[], vec![], vec![], Some(h3a), Some(3), true);

		let s = CachingState::new(InMemory::<Blake2Hasher>::default(), shared.clone(), Some(h3a));
		assert_eq!(s.storage(&key).unwrap().unwrap(), vec![5]);

		let s = CachingState::new(InMemory::<Blake2Hasher>::default(), shared.clone(), Some(h1a));
		assert!(s.storage(&key).unwrap().is_none());

		let s = CachingState::new(InMemory::<Blake2Hasher>::default(), shared.clone(), Some(h2b));
		assert!(s.storage(&key).unwrap().is_none());

		let s = CachingState::new(InMemory::<Blake2Hasher>::default(), shared.clone(), Some(h1b));
		assert!(s.storage(&key).unwrap().is_none());

		// reorg to 3b
		// blocks  [ 3b(c) 3a 2a 2b(c) 1b 1a 0 ]
		let mut s = CachingState::new(InMemory::<Blake2Hasher>::default(), shared.clone(), Some(h2b));
		s.cache.sync_cache(
			&[h1b, h2b, h3b],
			&[h1a, h2a, h3a],
			vec![],
			vec![],
			Some(h3b),
			Some(3),
			true,
		);
		let s = CachingState::new(InMemory::<Blake2Hasher>::default(), shared.clone(), Some(h3a));
		assert!(s.storage(&key).unwrap().is_none());
	}

	#[test]
	fn simple_fork() {
		let _ = ::env_logger::try_init();

		let root_parent = H256::random();
		let key = H256::random()[..].to_vec();
		let h1 = H256::random();
		let h2a = H256::random();
		let h2b = H256::random();
		let h3b = H256::random();

		let shared = new_shared_cache::<Block, Blake2Hasher>(256*1024, (0,1));

		let mut s = CachingState::new(InMemory::<Blake2Hasher>::default(), shared.clone(), Some(root_parent));
		s.cache.sync_cache(&[], &[], vec![(key.clone(), Some(vec![2]))], vec![], Some(h1), Some(1), true);

		let mut s = CachingState::new(InMemory::<Blake2Hasher>::default(), shared.clone(), Some(h1));
		s.cache.sync_cache(&[], &[], vec![], vec![], Some(h2a), Some(2), true);

		let mut s = CachingState::new(InMemory::<Blake2Hasher>::default(), shared.clone(), Some(h1));
		s.cache.sync_cache(&[], &[], vec![(key.clone(), Some(vec![3]))], vec![], Some(h2b), Some(2), false);

		let mut s = CachingState::new(InMemory::<Blake2Hasher>::default(), shared.clone(), Some(h2b));
		s.cache.sync_cache(&[], &[], vec![(key.clone(), Some(vec![3]))], vec![], Some(h3b), Some(2), false);

		let s = CachingState::new(InMemory::<Blake2Hasher>::default(), shared.clone(), Some(h2a));
		assert_eq!(s.storage(&key).unwrap().unwrap(), vec![2]);
	}

	#[test]
	fn double_fork() {
		let root_parent = H256::random();
		let key = H256::random()[..].to_vec();
		let h1 = H256::random();
		let h2a = H256::random();
		let h2b = H256::random();
		let h3a = H256::random();
		let h3b = H256::random();

		let shared = new_shared_cache::<Block, Blake2Hasher>(256*1024, (0,1));

		let mut s = CachingState::new(InMemory::<Blake2Hasher>::default(), shared.clone(), Some(root_parent));
		s.cache.sync_cache(&[], &[], vec![], vec![], Some(h1), Some(1), true);

		let mut s = CachingState::new(InMemory::<Blake2Hasher>::default(), shared.clone(), Some(h1));
		s.cache.sync_cache(&[], &[], vec![], vec![], Some(h2a), Some(2), true);

		let mut s = CachingState::new(InMemory::<Blake2Hasher>::default(), shared.clone(), Some(h2a));
		s.cache.sync_cache(&[], &[], vec![(key.clone(), Some(vec![2]))], vec![], Some(h3a), Some(3), true);

		let mut s = CachingState::new(InMemory::<Blake2Hasher>::default(), shared.clone(), Some(h1));
		s.cache.sync_cache(&[], &[], vec![], vec![], Some(h2b), Some(2), false);

		let mut s = CachingState::new(InMemory::<Blake2Hasher>::default(), shared.clone(), Some(h2b));
		s.cache.sync_cache(&[], &[], vec![(key.clone(), Some(vec![3]))], vec![], Some(h3b), Some(3), false);

		let s = CachingState::new(InMemory::<Blake2Hasher>::default(), shared.clone(), Some(h3a));
		assert_eq!(s.storage(&key).unwrap().unwrap(), vec![2]);
	}

	#[test]
	fn should_track_used_size_correctly() {
		let root_parent = H256::random();
		let shared = new_shared_cache::<Block, Blake2Hasher>(109, ((109-36), 109));
		let h0 = H256::random();

		let mut s = CachingState::new(InMemory::<Blake2Hasher>::default(), shared.clone(), Some(root_parent));

		let key = H256::random()[..].to_vec();
		let s_key = H256::random()[..].to_vec();
		s.cache.sync_cache(
			&[],
			&[],
			vec![(key.clone(), Some(vec![1, 2, 3]))],
			vec![],
			Some(h0),
			Some(0),
			true,
		);
		// 32 key, 3 byte size
		assert_eq!(shared.lock().used_storage_cache_size(), 35 /* bytes */);

		let key = H256::random()[..].to_vec();
		s.cache.sync_cache(
			&[],
			&[],
			vec![],
			vec![(s_key.clone(), vec![(key.clone(), Some(vec![1, 2]))])],
			Some(h0),
			Some(0),
			true,
		);
		// 35 + (2 * 32) key, 2 byte size
		assert_eq!(shared.lock().used_storage_cache_size(), 101 /* bytes */);
	}

	#[test]
	fn should_remove_lru_items_based_on_tracking_used_size() {
		let root_parent = H256::random();
		let shared = new_shared_cache::<Block, Blake2Hasher>(36*3, (2,3));
		let h0 = H256::random();

		let mut s = CachingState::new(InMemory::<Blake2Hasher>::default(), shared.clone(), Some(root_parent));

		let key = H256::random()[..].to_vec();
		s.cache.sync_cache(
			&[],
			&[],
			vec![(key.clone(), Some(vec![1, 2, 3, 4]))],
			vec![],
			Some(h0),
			Some(0),
			true,
		);
		// 32 key, 4 byte size
		assert_eq!(shared.lock().used_storage_cache_size(), 36 /* bytes */);

		let key = H256::random()[..].to_vec();
		s.cache.sync_cache(
			&[],
			&[],
			vec![(key.clone(), Some(vec![1, 2]))],
			vec![],
			Some(h0),
			Some(0),
			true,
		);
		// 32 key, 2 byte size
		assert_eq!(shared.lock().used_storage_cache_size(), 34 /* bytes */);
	}

	#[test]
	fn fix_storage_mismatch_issue() {
		let _ = ::env_logger::try_init();
		let root_parent = H256::random();

		let key = H256::random()[..].to_vec();

		let h0 = H256::random();
		let h1 = H256::random();

		let shared = new_shared_cache::<Block, Blake2Hasher>(256*1024, (0, 1));
		let mut s = CachingState::new(InMemory::<Blake2Hasher>::default(), shared.clone(), Some(root_parent));
		s.cache.sync_cache(&[], &[], vec![(key.clone(), Some(vec![2]))], vec![], Some(h0), Some(0), true);

		let mut s = CachingState::new(InMemory::<Blake2Hasher>::default(), shared.clone(), Some(h0));
		s.cache.sync_cache(&[], &[], vec![(key.clone(), Some(vec![3]))], vec![], Some(h1), Some(1), true);

		let mut s = CachingState::new(InMemory::<Blake2Hasher>::default(), shared.clone(), Some(h1));
		assert_eq!(s.storage(&key).unwrap(), Some(vec![3]));

		// Restart (or unknown block?), clear caches.
		{
			let mut cache = s.cache.shared_cache.lock();
			let cache = &mut *cache;
			cache.lru_storage.clear();
			cache.lru_hashes.clear();
			cache.lru_child_storage.clear();
			cache.modifications.clear();
		}

		// New value is written because of cache miss.
		s.cache.local_cache.write().storage.insert(key.clone(), Some(vec![42]));

		// New value is propagated.
		s.cache.sync_cache(&[], &[], vec![], vec![], None, None, true);

		let s = CachingState::new(InMemory::<Blake2Hasher>::default(), shared.clone(), Some(h1));
		assert_eq!(s.storage(&key).unwrap(), None);
	}
}

#[cfg(test)]
mod qc {
	use std::collections::{HashMap, hash_map::Entry};

	use quickcheck::{quickcheck, TestResult, Arbitrary};

	use super::*;
	use sp_runtime::testing::{H256, Block as RawBlock, ExtrinsicWrapper};
	use state_machine::backend::InMemory;
	use primitives::Blake2Hasher;

	type Block = RawBlock<ExtrinsicWrapper<u32>>;

	type KeySet = Vec<(Vec<u8>, Option<Vec<u8>>)>;

	type KeyMap = HashMap<Vec<u8>, Option<Vec<u8>>>;

	#[derive(Debug, Clone)]
	struct Node {
		hash: H256,
		parent: H256,
		state: KeyMap,
		changes: KeySet,
	}

	impl Node {
		fn new_next(&self, hash: H256, changes: KeySet) -> Self {
			let mut state = self.state.clone();

			for (k, v) in self.state.iter() { state.insert(k.clone(), v.clone()); }
			for (k, v) in changes.clone().into_iter() { state.insert(k, v); }

			Self {
				hash,
				parent: self.hash,
				changes,
				state,
			}
		}

		fn new(hash: H256, parent: H256, changes: KeySet) -> Self {
			let mut state = KeyMap::new();

			for (k, v) in changes.clone().into_iter() { state.insert(k, v); }

			Self {
				hash,
				parent,
				state,
				changes,
			}
		}

		fn purge(&mut self, other_changes: &KeySet) {
			for (k, _) in other_changes.iter() {
				self.state.remove(k);
			}
		}
	}

	#[derive(Debug, Clone)]
	enum Action {
		Next { hash: H256, changes: KeySet },
		Fork { depth: usize, hash: H256, changes: KeySet },
		ReorgWithImport { depth: usize, hash: H256 },
		FinalizationReorg { fork_depth: usize, depth: usize },
	}

	impl Arbitrary for Action {
		fn arbitrary<G: quickcheck::Gen>(gen: &mut G) -> Self {
			let path = gen.next_u32() as u8;
			let mut buf = [0u8; 32];

			match path {
				0..=175 => {
					gen.fill_bytes(&mut buf[..]);
					Action::Next {
						hash: H256::from(&buf),
						changes: {
							let mut set = Vec::new();
							for _ in 0..gen.next_u32()/(64*256*256*256) {
								set.push((vec![gen.next_u32() as u8], Some(vec![gen.next_u32() as u8])));
							}
							set
						}
					}
				},
				176..=220 => {
					gen.fill_bytes(&mut buf[..]);
					Action::Fork {
						hash: H256::from(&buf),
						depth: ((gen.next_u32() as u8) / 32) as usize,
						changes: {
							let mut set = Vec::new();
							for _ in 0..gen.next_u32()/(64*256*256*256) {
								set.push((vec![gen.next_u32() as u8], Some(vec![gen.next_u32() as u8])));
							}
							set
						}
					}
				},
				221..=240 => {
					gen.fill_bytes(&mut buf[..]);
					Action::ReorgWithImport {
						hash: H256::from(&buf),
						depth: ((gen.next_u32() as u8) / 32) as usize, // 0-7
					}
				},
				_ => {
					gen.fill_bytes(&mut buf[..]);
					Action::FinalizationReorg {
						fork_depth: ((gen.next_u32() as u8) / 32) as usize, // 0-7
						depth: ((gen.next_u32() as u8) / 64) as usize, // 0-3
					}
				},
			}
		}
	}

	struct Mutator {
		shared: SharedCache<Block, Blake2Hasher>,
		canon: Vec<Node>,
		forks: HashMap<H256, Vec<Node>>,
	}

	impl Mutator {
		fn new_empty() -> Self {
			let shared = new_shared_cache::<Block, Blake2Hasher>(256*1024, (0,1));

			Self {
				shared,
				canon: vec![],
				forks: HashMap::new(),
			}
		}

		fn head_state(&self, hash: H256) -> CachingState<Blake2Hasher, InMemory<Blake2Hasher>, Block> {
			CachingState::new(
				InMemory::<Blake2Hasher>::default(),
				self.shared.clone(),
				Some(hash)
			)
		}

		fn canon_head_state(&self) -> CachingState<Blake2Hasher, InMemory<Blake2Hasher>, Block> {
			self.head_state(self.canon.last().expect("Expected to be one commit").hash)
		}

		fn mutate_static(&mut self, action: Action) -> CachingState<Blake2Hasher, InMemory<Blake2Hasher>, Block> {
			self.mutate(action).expect("Expected to provide only valid actions to the mutate_static")
		}

		fn canon_len(&self) -> usize {
			return self.canon.len();
		}

		fn head_storage_ref(&self) -> &KeyMap {
			&self.canon.last().expect("Expected to be one commit").state
		}

		fn key_permutations() -> Vec<Vec<u8>> {
			(0u8..255).map(|x| vec![x]).collect()
		}

		fn mutate(&mut self, action: Action) -> Result<CachingState<Blake2Hasher, InMemory<Blake2Hasher>, Block>, ()> {
			let state = match action {
				Action::Fork { depth, hash, changes } => {
					let pos = self.canon.len() as isize - depth as isize;
					if pos < 0 || self.canon.len() == 0 || pos >= (self.canon.len()-1) as isize
					// no fork on top also, thus len-1
					{
						return Err(());
					}

					let pos = pos as usize;

					let fork_at = self.canon[pos].hash;

					let (total_h, parent) = match self.forks.entry(fork_at) {
						Entry::Occupied(occupied) => {
							let chain = occupied.into_mut();
							let parent = chain.last().expect("No empty forks are ever created").clone();
							let mut node = parent.new_next(hash, changes.clone());

							for earlier in chain.iter() {
								node.purge(&earlier.changes.clone());
							}

							chain.push(node);

							(pos + chain.len(), parent.hash)
						},
						Entry::Vacant(vacant) => {
							let canon_parent = &self.canon[pos];
							vacant.insert(vec![canon_parent.new_next(hash, changes.clone())]);

							(pos + 1, fork_at)
						}
					};

					let mut state = CachingState::new(
						InMemory::<Blake2Hasher>::default(),
						self.shared.clone(),
						Some(parent)
					);

					state.cache.sync_cache(
						&[],
						&[],
						changes,
						vec![],
						Some(hash),
						Some(total_h as u64),
						false,
					);

					state
				},
				Action::Next { hash, changes } => {
					let (next, parent_hash) = match self.canon.last() {
						None => {
							let parent_hash = H256::from(&[0u8; 32]);
							(Node::new(hash, parent_hash, changes.clone()), parent_hash)
						},
						Some(parent) => {
							(parent.new_next(hash, changes.clone()), parent.hash)
						}
					};

					// delete cache entries for earlier
					for node in self.canon.iter_mut() {
						node.purge(&next.changes);
						if let Some(fork) = self.forks.get_mut(&node.hash) {
							for node in fork.iter_mut() {
								node.purge(&next.changes);
							}
						}
					}

					let mut state = CachingState::new(
						InMemory::<Blake2Hasher>::default(),
						self.shared.clone(),
						Some(parent_hash)
					);

					state.cache.sync_cache(
						&[],
						&[],
						next.changes.clone(),
						vec![],
						Some(hash),
						Some(self.canon.len() as u64 + 1),
						true,
					);

					self.canon.push(next);

					state
				},
				Action::ReorgWithImport { depth, hash } => {
					let pos = self.canon.len() as isize - depth as isize;
					if pos < 0 || pos+1 >= self.canon.len() as isize { return Err(()); }
					let fork_at = self.canon[pos as usize].hash;
					let pos = pos as usize;

					match self.forks.get_mut(&fork_at) {
						Some(chain) => {
							let mut new_fork = self.canon.drain(pos+1..).collect::<Vec<Node>>();

							let retracted: Vec<H256> = new_fork.iter().map(|node| node.hash).collect();
							let enacted: Vec<H256> = chain.iter().map(|node| node.hash).collect();

							std::mem::swap(chain, &mut new_fork);

							let mut node = new_fork.last().map(
								|node| node.new_next(hash, vec![])
							).expect("No empty fork ever created!");

							for invalidators in chain.iter().chain(new_fork.iter()) {
								node.purge(&invalidators.changes);
							}

							self.canon.extend(new_fork.into_iter());

							self.canon.push(node);

							let mut state = CachingState::new(
								InMemory::<Blake2Hasher>::default(),
								self.shared.clone(),
								Some(fork_at)
							);

							let height = pos as u64 + enacted.len() as u64 + 2;
							state.cache.sync_cache(
								&enacted[..],
								&retracted[..],
								vec![],
								vec![],
								Some(hash),
								Some(height),
								true,
							);

							state
						}
						None => {
							return Err(()); // no reorg without a fork atm!
						},
					}
				},
				Action::FinalizationReorg { fork_depth, depth } => {
					let pos = self.canon.len() as isize - fork_depth as isize;
					if pos < 0 || pos+1 >= self.canon.len() as isize { return Err(()); }
					let fork_at = self.canon[pos as usize].hash;
					let pos = pos as usize;

					match self.forks.get_mut(&fork_at) {
						Some(fork_chain) => {
							let sync_pos = fork_chain.len() as isize - fork_chain.len() as isize - depth as isize;
							if sync_pos < 0 || sync_pos >= fork_chain.len() as isize { return Err (()); }
							let sync_pos = sync_pos as usize;

							let mut new_fork = self.canon.drain(pos+1..).collect::<Vec<Node>>();

							let retracted: Vec<H256> = new_fork.iter().map(|node| node.hash).collect();
							let enacted: Vec<H256> = fork_chain.iter().take(sync_pos+1).map(|node| node.hash).collect();

							std::mem::swap(fork_chain, &mut new_fork);

							self.shared.lock().sync(&retracted, &enacted);

							self.head_state(
								self.canon.last()
								.expect("wasn't forking to emptiness so there shoud be one!")
								.hash
							)
						},
						None => {
							return Err(()); // no reorg to nothing pls!
						}
					}

				},
			};

			Ok(state)
		}
	}

	#[test]
	fn smoke() {
		let key = H256::random()[..].to_vec();
		let h0 = H256::random();
		let h1a = H256::random();
		let h1b = H256::random();
		let h2a = H256::random();
		let h2b = H256::random();
		let h3a = H256::random();
		let h3b = H256::random();

		let mut mutator = Mutator::new_empty();
		mutator.mutate_static(Action::Next { hash: h0, changes: vec![(key.clone(), Some(vec![2]))] });
		mutator.mutate_static(Action::Next { hash: h1a, changes: vec![] });
		mutator.mutate_static(Action::Fork { depth: 2, hash: h1b, changes: vec![(key.clone(), Some(vec![3]))] });
		mutator.mutate_static(Action::Fork { depth: 2, hash: h2b, changes: vec![(key.clone(), Some(vec![4]))] });
		mutator.mutate_static(Action::Next { hash: h2a, changes: vec![(key.clone(), Some(vec![5]))] });
		mutator.mutate_static(Action::Next { hash: h3a, changes: vec![] });

		assert_eq!(mutator.head_state(h3a).storage(&key).unwrap().expect("there should be a value"), vec![5]);
		assert!(mutator.head_state(h1a).storage(&key).unwrap().is_none());
		assert!(mutator.head_state(h2b).storage(&key).unwrap().is_none());
		assert!(mutator.head_state(h1b).storage(&key).unwrap().is_none());

		mutator.mutate_static(Action::ReorgWithImport { depth: 4, hash: h3b });
		assert!(mutator.head_state(h3a).storage(&key).unwrap().is_none());
	}

	fn is_head_match(mutator: &Mutator) -> bool {
		let head_state = mutator.canon_head_state();

		for key in Mutator::key_permutations() {
			match (head_state.storage(&key).unwrap(), mutator.head_storage_ref().get(&key)) {
				(Some(x), Some(y)) => {
					if Some(&x) != y.as_ref() {
						eprintln!("{:?} != {:?}", x, y);
						return false;
					}
				},
				(None, Some(_y)) => {
					// TODO: cache miss is not tracked atm
				},
				(Some(x), None) => {
					eprintln!("{:?} != <missing>", x);
					return false;
				},
				_ => continue,
			}
		}
		true
	}

	fn is_canon_match(mutator: &Mutator) -> bool {
		for node in mutator.canon.iter() {
			let head_state = mutator.head_state(node.hash);
			for key in Mutator::key_permutations() {
				match (head_state.storage(&key).unwrap(), node.state.get(&key)) {
					(Some(x), Some(y)) => {
						if Some(&x) != y.as_ref() {
							eprintln!("at [{}]: {:?} != {:?}", node.hash, x, y);
							return false;
						}
					},
					(None, Some(_y)) => {
						// cache miss is not tracked atm
					},
					(Some(x), None) => {
						eprintln!("at [{}]: {:?} != <missing>", node.hash, x);
						return false;
					},
					_ => continue,
				}
			}
		}
		true
	}

	#[test]
	fn reorg() {
		let key = H256::random()[..].to_vec();
		let h0 = H256::random();
		let h1 = H256::random();
		let h2 = H256::random();
		let h1b = H256::random();
		let h2b = H256::random();

		let mut mutator = Mutator::new_empty();
		mutator.mutate_static(Action::Next { hash: h0, changes: vec![] });
		mutator.mutate_static(Action::Next { hash: h1, changes: vec![] });
		mutator.mutate_static(Action::Next { hash: h2, changes: vec![(key.clone(), Some(vec![2]))] });
		mutator.mutate_static(Action::Fork { depth: 2, hash: h1b, changes: vec![(key.clone(), Some(vec![3]))] });
		mutator.mutate_static(Action::ReorgWithImport { depth: 2, hash: h2b });

		assert!(is_head_match(&mutator))
	}

	fn key(k: u8) -> Vec<u8> { vec![k] }
	fn val(v: u8) -> Option<Vec<u8>> { Some(vec![v]) }
	fn keyval(k: u8, v: u8) -> KeySet { vec![(key(k), val(v))] }

	#[test]
	fn reorg2() {
		let h0 = H256::random();
		let h1a = H256::random();
		let h1b = H256::random();
		let h2b = H256::random();
		let h2a = H256::random();
		let h3a = H256::random();

		let mut mutator = Mutator::new_empty();
		mutator.mutate_static(Action::Next { hash: h0, changes: keyval(1, 1) });
		mutator.mutate_static(Action::Next { hash: h1a, changes: keyval(1, 1) });
		mutator.mutate_static(Action::Fork { depth: 2, hash: h1b, changes: keyval(2, 2 ) });

		mutator.mutate_static(Action::Next { hash: h2a, changes: keyval(3, 3) });
		mutator.mutate_static(Action::Next { hash: h3a, changes: keyval(4, 4) });
		mutator.mutate_static(Action::ReorgWithImport { depth: 4, hash: h2b });

		assert!(is_head_match(&mutator))
	}

	#[test]
	fn fork2() {
		let h1 = H256::random();
		let h2a = H256::random();
		let h2b = H256::random();
		let h3a = H256::random();
		let h3b = H256::random();

		let mut mutator = Mutator::new_empty();
		mutator.mutate_static(Action::Next { hash: h1, changes: vec![] });
		mutator.mutate_static(Action::Next { hash: h2a, changes: vec![] });
		mutator.mutate_static(Action::Next { hash: h3a, changes: keyval(1, 1) });

		mutator.mutate_static(Action::Fork { depth: 2, hash: h2b, changes: vec![] });
		mutator.mutate_static(Action::Fork { depth: 2, hash: h3b, changes: keyval(1, 2) });

		assert!(is_head_match(&mutator))
	}

	#[test]
	fn fork3() {
		let h1 = H256::random();
		let h2a = H256::random();
		let h2b = H256::random();
		let h3a = H256::random();

		let mut mutator = Mutator::new_empty();
		mutator.mutate_static(Action::Next { hash: h1, changes: keyval(1, 1) });
		mutator.mutate_static(Action::Next { hash: h2a, changes: keyval(2, 2) });
		mutator.mutate_static(Action::Next { hash: h3a, changes: keyval(3, 3) });

		mutator.mutate_static(Action::Fork { depth: 2, hash: h2b, changes: keyval(1, 3) });

		assert!(is_canon_match(&mutator))
	}

	quickcheck! {
		fn head_complete(actions: Vec<Action>) -> TestResult {
			let mut mutator = Mutator::new_empty();

			for action in actions.into_iter() {
				if let Err(_) = mutator.mutate(action) {
					return TestResult::discard();
				}
			}

			if mutator.canon_len() == 0 {
				return TestResult::discard();
			}

			TestResult::from_bool(is_head_match(&mutator))
		}

		fn canon_complete(actions: Vec<Action>) -> TestResult {
			let mut mutator = Mutator::new_empty();

			for action in actions.into_iter() {
				if let Err(_) = mutator.mutate(action) {
					return TestResult::discard();
				}
			}

			if mutator.canon_len() == 0 {
				return TestResult::discard();
			}

			TestResult::from_bool(is_canon_match(&mutator))
		}
	}
}
