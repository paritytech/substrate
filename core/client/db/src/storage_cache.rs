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
use lru_cache::LruCache;
use hash_db::Hasher;
use runtime_primitives::traits::{Block, Header};
use state_machine::{backend::Backend as StateBackend, TrieBackend};
use log::trace;

const STATE_CACHE_BLOCKS: usize = 12;

type StorageKey = Vec<u8>;
type StorageValue = Vec<u8>;

/// Shared canonical state cache.
pub struct Cache<B: Block, H: Hasher> {
	/// Storage cache. `None` indicates that key is known to be missing.
	storage: LruCache<StorageKey, Option<StorageValue>>,
	/// Storage hashes cache. `None` indicates that key is known to be missing.
	hashes: LruCache<StorageKey, Option<H::Out>>,
	/// Information on the modifications in recently committed blocks; specifically which keys
	/// changed in which block. Ordered by block number.
	modifications: VecDeque<BlockChanges<B::Header>>,
	/// Maximum cache size available, in Bytes.
	shared_cache_size: usize,
	/// Used storage size, in Bytes.
	storage_used_size: usize,
}

impl<B: Block, H: Hasher> Cache<B, H> {
	/// Returns the used memory size of the storage cache in bytes.
	pub fn used_storage_cache_size(&self) -> usize {
		self.storage_used_size
	}
}

pub type SharedCache<B, H> = Arc<Mutex<Cache<B, H>>>;

/// Create new shared cache instance with given max memory usage.
pub fn new_shared_cache<B: Block, H: Hasher>(shared_cache_size: usize) -> SharedCache<B, H> {
	// we need to supply a max capacity to `LruCache`, but since
	// we don't have any idea how large the size of each item
	// that is stored will be we can't calculate the max amount
	// of items properly from `shared_cache_size`.
	//
	// what we do instead is to supply `shared_cache_size` as the
	// max upper bound capacity (this would only be reached if each
	// item would be one byte).
	// each time we store to the storage cache we verify the memory
	// constraint and pop the lru item if space needs to be freed.

	Arc::new(Mutex::new(Cache {
		storage: LruCache::new(shared_cache_size),
		hashes: LruCache::new(shared_cache_size),
		modifications: VecDeque::new(),
		shared_cache_size: shared_cache_size,
		storage_used_size: 0,
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
	/// Block is part of the canonical chain.
	is_canon: bool,
}

/// Cached values specific to a state.
struct LocalCache<H: Hasher> {
	/// Storage cache. `None` indicates that key is known to be missing.
	storage: HashMap<StorageKey, Option<StorageValue>>,
	/// Storage hashes cache. `None` indicates that key is known to be missing.
	hashes: HashMap<StorageKey, Option<H::Out>>,
}

/// State abstraction.
/// Manages shared global state cache which reflects the canonical
/// state as it is on the disk.
/// A instance of `CachingState` may be created as canonical or not.
/// For canonical instances local cache is accumulated and applied
/// in `sync_cache` along with the change overlay.
/// For non-canonical clones local cache and changes are dropped.
pub struct CachingState<H: Hasher, S: StateBackend<H>, B: Block> {
	/// Backing state.
	state: S,
	/// Shared canonical state cache.
	shared_cache: SharedCache<B, H>,
	/// Local cache of values for this state.
	local_cache: RwLock<LocalCache<H>>,
	/// Hash of the block on top of which this instance was created or
	/// `None` if cache is disabled
	pub parent_hash: Option<B::Hash>,
}

impl<H: Hasher, S: StateBackend<H>, B: Block> CachingState<H, S, B> {
	/// Create a new instance wrapping generic State and shared cache.
	pub fn new(state: S, shared_cache: SharedCache<B, H>, parent_hash: Option<B::Hash>) -> CachingState<H, S, B> {
		CachingState {
			state,
			shared_cache,
			local_cache: RwLock::new(LocalCache {
				storage: Default::default(),
				hashes: Default::default(),
			}),
			parent_hash: parent_hash,
		}
	}

	fn storage_insert(cache: &mut Cache<B, H>, k: StorageValue, v: Option<StorageValue>) {
		if let Some(v_) = &v {
			while cache.storage_used_size + v_.len() > cache.shared_cache_size {
				// pop until space constraint satisfied
				match cache.storage.remove_lru() {
					Some((_, Some(popped_v))) =>
						cache.storage_used_size = cache.storage_used_size - popped_v.len(),
					Some((_, None)) => continue,
					None => break,
				};
			}
			cache.storage_used_size = cache.storage_used_size + v_.len();
		}
		cache.storage.insert(k, v);
	}

	fn storage_remove(
		storage: &mut LruCache<StorageKey, Option<StorageValue>>,
		k: &StorageKey,
		storage_used_size: &mut usize,
	) {
		let v = storage.remove(k);
		if let Some(Some(v_)) = v {
			*storage_used_size = *storage_used_size - v_.len();
		}
	}

	/// Propagate local cache into the shared cache and synchronize
	/// the shared cache with the best block state.
	/// This function updates the shared cache by removing entries
	/// that are invalidated by chain reorganization. `sync_cache`
	/// should be called after the block has been committed and the
	/// blockchain route has been calculated.
	pub fn sync_cache<F: FnOnce() -> bool> (
		&mut self,
		enacted: &[B::Hash],
		retracted: &[B::Hash],
		changes: Vec<(StorageKey, Option<StorageValue>)>,
		commit_hash: Option<B::Hash>,
		commit_number: Option<<B::Header as Header>::Number>,
		is_best: F,
	) {
		let mut cache = self.shared_cache.lock();
		let is_best = is_best();
		trace!("Syncing cache, id = (#{:?}, {:?}), parent={:?}, best={}", commit_number, commit_hash, self.parent_hash, is_best);
		let cache = &mut *cache;

		// Purge changes from re-enacted and retracted blocks.
		// Filter out commiting block if any.
		let mut clear = false;
		for block in enacted.iter().filter(|h| commit_hash.as_ref().map_or(true, |p| *h != p)) {
			clear = clear || {
				if let Some(ref mut m) = cache.modifications.iter_mut().find(|m| &m.hash == block) {
					trace!("Reverting enacted block {:?}", block);
					m.is_canon = true;
					for a in &m.storage {
						trace!("Reverting enacted key {:?}", a);
						CachingState::<H, S, B>::storage_remove(&mut cache.storage, a, &mut cache.storage_used_size);
					}
					false
				} else {
					true
				}
			};
		}

		for block in retracted {
			clear = clear || {
				if let Some(ref mut m) = cache.modifications.iter_mut().find(|m| &m.hash == block) {
					trace!("Retracting block {:?}", block);
					m.is_canon = false;
					for a in &m.storage {
						trace!("Retracted key {:?}", a);
						CachingState::<H, S, B>::storage_remove(&mut cache.storage, a, &mut cache.storage_used_size);
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
			cache.storage.clear();
			cache.modifications.clear();
		}

		// Propagate cache only if committing on top of the latest canonical state
		// blocks are ordered by number and only one block with a given number is marked as canonical
		// (contributed to canonical state cache)
		if let Some(_) = self.parent_hash {
			let mut local_cache = self.local_cache.write();
			if is_best {
				trace!("Committing {} local, {} hashes, {} modified entries", local_cache.storage.len(), local_cache.hashes.len(), changes.len());
				for (k, v) in local_cache.storage.drain() {
					CachingState::<H, S, B>::storage_insert(cache, k, v);
				}
				for (k, v) in local_cache.hashes.drain() {
					cache.hashes.insert(k, v);
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
			for (k, v) in changes.into_iter() {
				modifications.insert(k.clone());
				if is_best {
					cache.hashes.remove(&k);
					CachingState::<H, S, B>::storage_insert(cache, k, v);
				}
			}
			// Save modified storage. These are ordered by the block number.
			let block_changes = BlockChanges {
				storage: modifications,
				number: *number,
				hash: hash.clone(),
				is_canon: is_best,
				parent: parent.clone(),
			};
			let insert_at = cache.modifications.iter()
				.enumerate()
				.find(|&(_, m)| m.number < *number)
				.map(|(i, _)| i);
			trace!("Inserting modifications at {:?}", insert_at);
			if let Some(insert_at) = insert_at {
				cache.modifications.insert(insert_at, block_changes);
			} else {
				cache.modifications.push_back(block_changes);
			}
		}
	}

	/// Check if the key can be returned from cache by matching current block parent hash against canonical
	/// state and filtering out entries modified in later blocks.
	fn is_allowed(
		key: &[u8],
		parent_hash: &Option<B::Hash>,
		modifications:
		&VecDeque<BlockChanges<B::Header>>
	) -> bool
	{
		let mut parent = match *parent_hash {
			None => {
				trace!("Cache lookup skipped for {:?}: no parent hash", key);
				return false;
			}
			Some(ref parent) => parent,
		};
		if modifications.is_empty() {
			trace!("Cache lookup allowed for {:?}", key);
			return true;
		}
		// Ignore all storage modified in later blocks
		// Modifications contains block ordered by the number
		// We search for our parent in that list first and then for
		// all its parent until we hit the canonical block,
		// checking against all the intermediate modifications.
		for m in modifications {
			if &m.hash == parent {
				if m.is_canon {
					return true;
				}
				parent = &m.parent;
			}
			if m.storage.contains(key) {
				trace!("Cache lookup skipped for {:?}: modified in a later block", key);
				return false;
			}
		}
		trace!("Cache lookup skipped for {:?}: parent hash is unknown", key);
		false
	}
}

impl<H: Hasher, S: StateBackend<H>, B:Block> StateBackend<H> for CachingState<H, S, B> {
	type Error =  S::Error;
	type Transaction = S::Transaction;
	type TrieBackendStorage = S::TrieBackendStorage;

	fn storage(&self, key: &[u8]) -> Result<Option<Vec<u8>>, Self::Error> {
		let local_cache = self.local_cache.upgradable_read();
		if let Some(entry) = local_cache.storage.get(key).cloned() {
			trace!("Found in local cache: {:?}", key);
			return Ok(entry)
		}
		let mut cache = self.shared_cache.lock();
		if Self::is_allowed(key, &self.parent_hash, &cache.modifications) {
			if let Some(entry) = cache.storage.get_mut(key).map(|a| a.clone()) {
				trace!("Found in shared cache: {:?}", key);
				return Ok(entry)
			}
		}
		trace!("Cache miss: {:?}", key);
		let value = self.state.storage(key)?;
		RwLockUpgradableReadGuard::upgrade(local_cache).storage.insert(key.to_vec(), value.clone());
		Ok(value)
	}

	fn storage_hash(&self, key: &[u8]) -> Result<Option<H::Out>, Self::Error> {
		let local_cache = self.local_cache.upgradable_read();
		if let Some(entry) = local_cache.hashes.get(key).cloned() {
			trace!("Found hash in local cache: {:?}", key);
			return Ok(entry)
		}
		let mut cache = self.shared_cache.lock();
		if Self::is_allowed(key, &self.parent_hash, &cache.modifications) {
			if let Some(entry) = cache.hashes.get_mut(key).map(|a| a.clone()) {
				trace!("Found hash in shared cache: {:?}", key);
				return Ok(entry)
			}
		}
		trace!("Cache hash miss: {:?}", key);
		let hash = self.state.storage_hash(key)?;
		RwLockUpgradableReadGuard::upgrade(local_cache).hashes.insert(key.to_vec(), hash.clone());
		Ok(hash)
	}

	fn child_storage(&self, storage_key: &[u8], key: &[u8]) -> Result<Option<Vec<u8>>, Self::Error> {
		self.state.child_storage(storage_key, key)
	}

	fn exists_storage(&self, key: &[u8]) -> Result<bool, Self::Error> {
		Ok(self.storage(key)?.is_some())
	}

	fn exists_child_storage(&self, storage_key: &[u8], key: &[u8]) -> Result<bool, Self::Error> {
		self.state.exists_child_storage(storage_key, key)
	}

	fn for_keys_with_prefix<F: FnMut(&[u8])>(&self, prefix: &[u8], f: F) {
		self.state.for_keys_with_prefix(prefix, f)
	}

	fn for_keys_in_child_storage<F: FnMut(&[u8])>(&self, storage_key: &[u8], f: F) {
		self.state.for_keys_in_child_storage(storage_key, f)
	}

	fn storage_root<I>(&self, delta: I) -> (H::Out, Self::Transaction)
		where
			I: IntoIterator<Item=(Vec<u8>, Option<Vec<u8>>)>,
			H::Out: Ord
	{
		self.state.storage_root(delta)
	}

	fn child_storage_root<I>(&self, storage_key: &[u8], delta: I) -> (Vec<u8>, bool, Self::Transaction)
		where
			I: IntoIterator<Item=(Vec<u8>, Option<Vec<u8>>)>,
			H::Out: Ord
	{
		self.state.child_storage_root(storage_key, delta)
	}

	fn pairs(&self) -> Vec<(Vec<u8>, Vec<u8>)> {
		self.state.pairs()
	}

	fn keys(&self, prefix: &Vec<u8>) -> Vec<Vec<u8>> {
		self.state.keys(prefix)
	}

	fn try_into_trie_backend(self) -> Option<TrieBackend<Self::TrieBackendStorage, H>> {
		self.state.try_into_trie_backend()
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use runtime_primitives::testing::{H256, Block as RawBlock, ExtrinsicWrapper};
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

		let shared = new_shared_cache::<Block, Blake2Hasher>(256*1024);

		// blocks  [ 3a(c) 2a(c) 2b 1b 1a(c) 0 ]
		// state   [ 5     5     4  3  2     2 ]
		let mut s = CachingState::new(InMemory::<Blake2Hasher>::default(), shared.clone(), Some(root_parent.clone()));
		s.sync_cache(&[], &[], vec![(key.clone(), Some(vec![2]))], Some(h0.clone()), Some(0), || true);

		let mut s = CachingState::new(InMemory::<Blake2Hasher>::default(), shared.clone(), Some(h0.clone()));
		s.sync_cache(&[], &[], vec![], Some(h1a.clone()), Some(1), || true);

		let mut s = CachingState::new(InMemory::<Blake2Hasher>::default(), shared.clone(), Some(h0.clone()));
		s.sync_cache(&[], &[], vec![(key.clone(), Some(vec![3]))], Some(h1b.clone()), Some(1), || false);

		let mut s = CachingState::new(InMemory::<Blake2Hasher>::default(), shared.clone(), Some(h1b.clone()));
		s.sync_cache(&[], &[], vec![(key.clone(), Some(vec![4]))], Some(h2b.clone()), Some(2), || false);

		let mut s = CachingState::new(InMemory::<Blake2Hasher>::default(), shared.clone(), Some(h1a.clone()));
		s.sync_cache(&[], &[], vec![(key.clone(), Some(vec![5]))], Some(h2a.clone()), Some(2), || true);

		let mut s = CachingState::new(InMemory::<Blake2Hasher>::default(), shared.clone(), Some(h2a.clone()));
		s.sync_cache(&[], &[], vec![], Some(h3a.clone()), Some(3), || true);

		let s = CachingState::new(InMemory::<Blake2Hasher>::default(), shared.clone(), Some(h3a.clone()));
		assert_eq!(s.storage(&key).unwrap().unwrap(), vec![5]);

		let s = CachingState::new(InMemory::<Blake2Hasher>::default(), shared.clone(), Some(h1a.clone()));
		assert!(s.storage(&key).unwrap().is_none());

		let s = CachingState::new(InMemory::<Blake2Hasher>::default(), shared.clone(), Some(h2b.clone()));
		assert!(s.storage(&key).unwrap().is_none());

		let s = CachingState::new(InMemory::<Blake2Hasher>::default(), shared.clone(), Some(h1b.clone()));
		assert!(s.storage(&key).unwrap().is_none());

		// reorg to 3b
		// blocks  [ 3b(c) 3a 2a 2b(c) 1b 1a 0 ]
		let mut s = CachingState::new(InMemory::<Blake2Hasher>::default(), shared.clone(), Some(h2b.clone()));
		s.sync_cache(&[h1b.clone(), h2b.clone(), h3b.clone()], &[h1a.clone(), h2a.clone(), h3a.clone()], vec![], Some(h3b.clone()), Some(3), || true);
		let s = CachingState::new(InMemory::<Blake2Hasher>::default(), shared.clone(), Some(h3a.clone()));
		assert!(s.storage(&key).unwrap().is_none());
	}

	#[test]
	fn should_track_used_size_correctly() {
		let root_parent = H256::random();
		let shared = new_shared_cache::<Block, Blake2Hasher>(5);
		let h0 = H256::random();

		let mut s = CachingState::new(InMemory::<Blake2Hasher>::default(), shared.clone(), Some(root_parent.clone()));

		let key = H256::random()[..].to_vec();
		s.sync_cache(&[], &[], vec![(key.clone(), Some(vec![1, 2, 3]))], Some(h0.clone()), Some(0), || true);
		assert_eq!(shared.lock().used_storage_cache_size(), 3 /* bytes */);

		let key = H256::random()[..].to_vec();
		s.sync_cache(&[], &[], vec![(key.clone(), Some(vec![1, 2]))], Some(h0.clone()), Some(0), || true);
		assert_eq!(shared.lock().used_storage_cache_size(), 5 /* bytes */);
	}

	#[test]
	fn should_remove_lru_items_based_on_tracking_used_size() {
		let root_parent = H256::random();
		let shared = new_shared_cache::<Block, Blake2Hasher>(5);
		let h0 = H256::random();

		let mut s = CachingState::new(InMemory::<Blake2Hasher>::default(), shared.clone(), Some(root_parent.clone()));

		let key = H256::random()[..].to_vec();
		s.sync_cache(&[], &[], vec![(key.clone(), Some(vec![1, 2, 3, 4]))], Some(h0.clone()), Some(0), || true);
		assert_eq!(shared.lock().used_storage_cache_size(), 4 /* bytes */);

		let key = H256::random()[..].to_vec();
		s.sync_cache(&[], &[], vec![(key.clone(), Some(vec![1, 2]))], Some(h0.clone()), Some(0), || true);
		assert_eq!(shared.lock().used_storage_cache_size(), 2 /* bytes */);
	}
}
