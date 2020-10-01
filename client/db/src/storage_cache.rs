// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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

use historied_db::{
	StateDBRef, InMemoryStateDBRef, StateDB, ManagementRef, Management,
	ForkableManagement, Latest, UpdateResult,
	historied::{InMemoryValue, Value},
	historied::tree::Tree,
	management::tree::{Tree as TreeMgmt, TreeManagement, ForkPlan},
};
use std::collections::{VecDeque, HashSet, HashMap, BTreeSet};
use std::sync::Arc;
use std::hash::Hash as StdHash;
use parking_lot::{Mutex, RwLock, RwLockUpgradableReadGuard};
use linked_hash_map::{LinkedHashMap, Entry, IterMut};
use hash_db::Hasher;
use sp_runtime::traits::{Block as BlockT, Header, HashFor, NumberFor};
use sp_core::hexdisplay::HexDisplay;
use sp_core::storage::ChildInfo;
use sp_state_machine::{
	backend::Backend as StateBackend, TrieBackend, StorageKey, StorageValue,
	StorageCollection, ChildStorageCollection,
};
use log::trace;
use log::warn;
use crate::{utils::Meta, stats::StateUsageStats};
use std::marker::PhantomData;
use sc_client_api::ExpCacheConf;

const STATE_CACHE_BLOCKS: usize = 12;

type ChildStorageKey = (Vec<u8>, Vec<u8>);

type HistoriedTreeBackend = historied_db::backend::in_memory::MemoryOnly<
	historied_db::historied::linear::Linear<Option<Vec<u8>>, u32, HistoriedLinearBackend>,
	u32,
>;
type HistoriedLinearBackend = historied_db::backend::in_memory::MemoryOnly<Option<Vec<u8>>, u32>;

/// Shared canonical state cache.
pub struct Cache<B: BlockT> {
	/// Storage cache. `None` indicates that key is known to be missing.
	lru_storage: LRUMap<StorageKey, Option<StorageValue>, B>,
	/// Storage hashes cache. `None` indicates that key is known to be missing.
	lru_hashes: LRUMap<StorageKey, OptionHOut<B::Hash>, B>,
	/// Storage cache for child trie. `None` indicates that key is known to be missing.
	lru_child_storage: LRUMap<ChildStorageKey, Option<StorageValue>, B>,
	/// Information on the modifications in recently committed blocks; specifically which keys
	/// changed in which block. Ordered by block number.
	modifications: VecDeque<BlockChanges<B::Header>>,
}

// TODO remove (useless) -> make the ExperimentalCache
impl<B: BlockT> StateDBRef<StorageKey, Option<StorageValue>> for SyncExperimentalCache<B> {
	type S = ForkPlan<u32, u32>;

	fn get(&self, key: &StorageKey, at: &Self::S) -> Option<Option<StorageValue>> {
		use historied_db::historied::ValueRef;
		self.0.write().lru_storage.get(key).and_then(|history| history.get(at))
	}

	fn contains(&self, key: &StorageKey, at: &Self::S) -> bool {
		self.get(key, at).is_some()
	}
}

impl<B: BlockT> StateDBRef<StorageKey, Option<StorageValue>> for ExperimentalCache<B> {
	type S = ForkPlan<u32, u32>;
	fn get(&self, key: &StorageKey, at: &Self::S) -> Option<Option<StorageValue>> {
		unreachable!("dummy implementation for state db implementation")
	}
	fn contains(&self, key: &StorageKey, at: &Self::S) -> bool {
		unreachable!("dummy implementation for state db implementation")
	}
}

/* cannot return ref behind a lock and lru require mut access
impl<B: BlockT> InMemoryStateDBRef<StorageKey, Option<StorageValue>> for SyncExperimentalCache<B> {
	fn get_ref(&self, key: &StorageKey, at: &Self::S) -> Option<&Option<StorageValue>> {
		use historied_db::historied::InMemoryValueRef;
		self.0.write().lru_storage.get(key).and_then(|history| history.get_ref(at))
	}
}
*/
impl<B: BlockT> StateDB<StorageKey, Option<StorageValue>> for ExperimentalCache<B> {
	type SE = Latest<(u32, u32)>;
	// not needed as ExperimentalCache also implement management
	type GC = ();
	// not needed as ExperimentalCache also implement management
	type Migrate = ();

	fn emplace(&mut self, key: StorageKey, value: Option<StorageValue>, at: &Self::SE) {
		use historied_db::historied::Value;
		if let Some(history) = self.lru_storage.get(&key) {
			let mut additional_size = value.as_ref().map(|v| v.estimate_size());
			match history.set_mut(value, at) {
				UpdateResult::Changed(Some(v)) | UpdateResult::Cleared(Some(v)) => {
					let size = v.estimate_size();
					self.lru_storage.lru_decrease_size(size);
				},
				UpdateResult::Unchanged => {
					additional_size = None;
				},
				_ => (),
			}
			if let Some(size) = additional_size {
				if self.lru_storage.lru_increase_size(size) {
					self.gc(&mut ());
				}
			}
		} else {
			let history = Tree::new(value, at, ((), ()));
			if self.lru_storage.add_no_resize(key, history) {
				self.gc(&mut ());
			}
		}
	}

	fn remove(&mut self, key: &StorageKey, at: &Self::SE) {
		unimplemented!()
	}

	fn gc(&mut self, _gc: &Self::GC) {
		match self.clean_mode {
			ExpCacheConf::None => (),
			ExpCacheConf::LRUOnly(nb) => {
				if self.did_gc == 0 {
					self.clear();
					debug_assert!(self.did_gc == nb);
				} else {
					self.did_gc -= 1;
				}
			},
			ExpCacheConf::GCRetracted => {
				// TODO it can use a migrate (for now gc is implemented)
				let mut change = false;
				for retracted in std::mem::replace(&mut self.retracted, Default::default()) {
					let chain_remove_mapping = false; // because we run over all retracted anyway.
					// Those change should use trait method: here we use internals TODO EMCH + put
					// state back to private in management
					if let Some(state) = self.management.get_db_state_for_fork(&retracted) {
						change = true;
						self.management.apply_drop_state(&state, chain_remove_mapping, None);
					}
				}

				if change {
					let mut to_rem = Vec::new();
					let mut decrease = 0;
					if let Some(gc) = self.management.get_gc() {
						for (k, v) in self.lru_storage.iter_mut() {
							let initial_size = v.estimate_size();
							match v.gc(gc.as_ref()) {
								UpdateResult::Cleared(_) => {
									decrease += initial_size;
									to_rem.push(k.clone());
								},
								UpdateResult::Changed(_) => {
									let new_size = v.estimate_size();
									decrease += initial_size - new_size;
								},
								UpdateResult::Unchanged => (),
							}
						}
						for k in to_rem.iter() {
							self.lru_storage.remove(k);
						}
						self.lru_storage.lru_decrease_size(decrease);
					}
				}
			},
			ExpCacheConf::GCRange(width) => {
				if self.management.apply_drop_from_latest(width) {
					let mut to_rem = Vec::new();
					let mut decrease = 0;
					if let Some(gc) = self.management.get_gc() {
						for (k, v) in self.lru_storage.iter_mut() {
							let initial_size = v.estimate_size();
							match v.gc(gc.as_ref()) {
								UpdateResult::Cleared(_) => {
									decrease += initial_size;
									to_rem.push(k.clone());
								},
								UpdateResult::Changed(_) => {
									let new_size = v.estimate_size();
									decrease += initial_size - new_size;
								},
								UpdateResult::Unchanged => (),
							}
						}
						for k in to_rem.iter() {
							self.lru_storage.remove(k);
						}
						self.lru_storage.lru_decrease_size(decrease);
					}
				}
			},
		}

		self.lru_storage.lru_resize();
	}

	fn migrate(&mut self, _mig: &mut Self::Migrate) {
		// nice migration strategy
		self.clear();
	}
}

struct LRUMap<K, V, B>(LinkedHashMap<K, V>, usize, usize, PhantomData<B>);

/// TODO replace second usize index by actual B::blocknumber
pub struct ExperimentalCache<B: BlockT>{
	lru_storage: LRUMap<StorageKey, Tree<u32, u32, Option<StorageValue>, HistoriedTreeBackend, HistoriedLinearBackend>, B>,
	management: TreeManagement<B::Hash, u32, u32, Option<StorageValue>, ()>,
	/// since retracted branch could potentially be enacted back we do not put it
	/// in management directly.
	/// TODO Note that we only need lower branch number block, but will also
	/// store the other to avoid querying enacted blocks.
	/// Also note that gc cannot be done on retracted because it can be enacted back (unless
	/// invalidate cache on enacted back).
	/// TODO this should only be needed for retracted clean mode and we can allow fail insert(or
	///  don't insert at all when confident it is not needed).
	retracted: BTreeSet<B::Hash>,
	clean_mode: ExpCacheConf,
	/// store if gc did happen.
	did_gc: usize,
}

impl<B: BlockT> ExperimentalCache<B> {
	pub fn sync(
		&mut self,
		pivot: Option<&B::Hash>,
		enacted: &[B::Hash],
		retracted: &[B::Hash],
		commit_hash: Option<&B::Hash>,
		parent_hash: Option<&B::Hash>, // TODO just for debugging, remove
		experimental_query_plan: Option<&ForkPlan<u32, u32>>,
	) -> Option<(ForkPlan<u32, u32>, Latest<(u32, u32)>)> {
		trace!("Syncing experimental cache, pivot = {:?}, enacted = {:?}, retracted = {:?}", pivot, enacted, retracted);
			warn!("Syncing = {:?}", (pivot, enacted, retracted));
		for h in retracted {
			self.retracted.insert(h.clone());
		}
		let mut got_all_enacted = true;
		let pivot = if enacted.last().is_some() {
			enacted.last()
		} else {
			pivot
		};
		// TODO EMCH make it debug assert + it break tests -> TODO ignore pivot uses debug parent_hash
/*		assert!(if parent_hash.is_some() && pivot.is_some() {
			parent_hash == pivot
		} else { true });*/

		let state = if let Some(state) = pivot.and_then(|pivot| self.management.get_db_state_for_fork(pivot)) {
			for h in enacted {
				if self.retracted.remove(h) {
					continue;
				}
				// TODO debug_assert
				assert!(self.management.get_db_state_for_fork(h).is_some());
			}
			state
		} else {
			for h in enacted {
				if !self.retracted.remove(h) {
					got_all_enacted = false;
				}
			}

			let result = experimental_query_plan
				.map(|qp| self.management.ref_state_fork(qp))
				.unwrap_or_else(|| {
					warn!("#####Using init state fork for a new branch");
					self.management.init_state_fork()
				});
//			assert!(result.latest() == &Default::default()); // missing something in mgmt trait here
			result
		};

		if let ExpCacheConf::GCRetracted = self.clean_mode {
			if !got_all_enacted && self.did_gc > 0 {
				// invalidate cache since a gc can have removed those value: TODO EMCH do it only if a gc did
				// run or if eager gc on access
				self.clear();
			}
		}

		if let Some(h) = commit_hash {
			warn!("actual append at = {:?} for {:?} parent {:?}", commit_hash, state, parent_hash);
			// TODO EMCH make it debug assert + it breaks test so make it a conditional
//			assert!(self.management.get_db_state_for_fork(h).is_none());
			// TODO returning both state on this call???
			let state_mut =	self.management.append_external_state(h.clone(), &state)
					.expect("correct state resolution");
			Some((
				self.management.get_db_state(&h)
					.expect("correct state resolution"),
				state_mut,
			))
		} else {
			None
		}
	}

	fn clear(&mut self) {
		self.management = TreeManagement::default();
		self.lru_storage.clear();
		self.retracted.clear();
		self.did_gc = self.clean_mode.did_gc_init();
	}
}


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

impl EstimateSize for Tree<u32, u32, Option<StorageValue>, HistoriedTreeBackend, HistoriedLinearBackend> {
	fn estimate_size(&self) -> usize {
		self.temp_size()
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

impl<K: EstimateSize + Eq + StdHash, V: EstimateSize, B> LRUMap<K, V, B> {
	fn remove(&mut self, k: &K) {
		let map = &mut self.0;
		let storage_used_size = &mut self.1;
		if let Some(v) = map.remove(k) {
			*storage_used_size -= k.estimate_size();
			*storage_used_size -= v.estimate_size();
		}
	}

	fn add(&mut self, k: K, v: V) {
		if self.add_no_resize(k, v) {
			self.lru_resize()
		}
	}

	///  return true if need resize
	fn add_no_resize(&mut self, k: K, v: V) -> bool {
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
		*storage_used_size > limit
	}

	fn lru_resize(&mut self) {
		let lmap = &mut self.0;
		let storage_used_size = &mut self.1;
		while *storage_used_size > self.2 {
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

	fn lru_decrease_size(&mut self, size: usize) {
		let storage_used_size = &mut self.1;
		debug_assert!(*storage_used_size >= size);
		*storage_used_size -= size;
	}

	fn lru_increase_size(&mut self, size: usize) -> bool {
		let storage_used_size = &mut self.1;
		*storage_used_size += size;
		*storage_used_size > self.2
	}

	fn get<Q:?Sized>(&mut self, k: &Q) -> Option<&mut V>
		where K: std::borrow::Borrow<Q>,
			Q: StdHash + Eq {
		self.0.get_refresh(k)
	}

	fn used_size(&self) -> usize {
		self.1
	}

	fn iter_mut(&mut self) -> IterMut<K, V> {
		self.0.iter_mut()
	}

	fn clear(&mut self) {
		self.0.clear();
		self.1 = 0;
	}

}

impl<B: BlockT> Cache<B> {
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

pub type SharedCache<B> = Arc<Mutex<Cache<B>>>;

#[derive(Clone)]
pub struct SyncExperimentalCache<B: BlockT>(pub Arc<RwLock<ExperimentalCache<B>>>);

/// Fix lru storage size for hash (small 64ko).
const FIX_LRU_HASH_SIZE: usize = 65_536;

/// Create a new shared cache instance with given max memory usage.
pub fn new_shared_cache<B: BlockT>(
	shared_cache_size: usize,
	child_ratio: (usize, usize),
	experimental: ExpCacheConf,
) -> (SharedCache<B>, Option<SyncExperimentalCache<B>>) {
	let top = child_ratio.1.saturating_sub(child_ratio.0);
	(Arc::new(
		Mutex::new(
			Cache {
				lru_storage: LRUMap(
					LinkedHashMap::new(), 0, shared_cache_size * top / child_ratio.1, PhantomData
				),
				lru_hashes: LRUMap(LinkedHashMap::new(), 0, FIX_LRU_HASH_SIZE, PhantomData),
				lru_child_storage: LRUMap(
					LinkedHashMap::new(), 0, shared_cache_size * child_ratio.0 / child_ratio.1, PhantomData
				),
				modifications: VecDeque::new(),
			}
		)
	), if experimental.use_exp_cache() {
			// TODO Mutex or RwLock
			Some(SyncExperimentalCache(Arc::new(RwLock::new(ExperimentalCache {
				lru_storage: LRUMap(
					LinkedHashMap::new(), 0, shared_cache_size * top / child_ratio.1, PhantomData
				),
				management: TreeManagement::default(),
				retracted: Default::default(),
				did_gc: experimental.did_gc_init(),
				clean_mode: experimental,
			}))))
		} else {
			None
		})
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
pub struct CacheChanges<B: BlockT> {
	/// Shared canonical state cache.
	shared_cache: SharedCache<B>,
	/// Local cache of values for this state.
	local_cache: RwLock<LocalCache<HashFor<B>>>,
	/// experimental only for root to test then put in its own SharedCache variant
	experimental_cache: Option<SyncExperimentalCache<B>>,
	/// Hash of the block on top of which this instance was created or
	/// `None` if cache is disabled
	pub parent_hash: Option<B::Hash>,
	pub experimental_query_plan: Option<ForkPlan<u32, u32>>,
	// TODO rather unused as we update on hresh fork.
	pub experimental_update: Option<Latest<(u32, u32)>>,
	/// disable checking experimental cache value
	pub no_assert: bool,
	/// avoid doing assert against backend result (no backend in qc test)
	pub qc: bool,
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
pub struct CachingState<S, B: BlockT> {
	/// Usage statistics
	usage: StateUsageStats,
	/// State machine registered stats
	overlay_stats: sp_state_machine::StateMachineStats,
	/// Backing state.
	state: S,
	/// Cache data.
	cache: CacheChanges<B>,
}

impl<S, B: BlockT> std::fmt::Debug for CachingState<S, B> {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "Block {:?}", self.cache.parent_hash)
	}
}

impl<B: BlockT> CacheChanges<B> {
	/// Propagate local cache into the shared cache and synchronize
	/// the shared cache with the best block state.
	///
	/// This function updates the shared cache by removing entries
	/// that are invalidated by chain reorganization. `sync_cache`
	/// should be called after the block has been committed and the
	/// blockchain route has been calculated.
	pub fn sync_cache(
		&mut self,
		pivot: Option<&B::Hash>,
		enacted: &[B::Hash],
		retracted: &[B::Hash],
		changes: StorageCollection,
		child_changes: ChildStorageCollection,
		commit_hash: Option<B::Hash>,
		commit_number: Option<NumberFor<B>>,
		is_best: bool,
	) {
		// This is also protect a race on experimental cache where
		// we add a state when a previous state did not commit entirely.
		let mut shared_cache = self.shared_cache.lock();
		let cache = &mut *shared_cache;

		if let Some(cache) = self.experimental_cache.as_ref() {
			let mut cache = cache.0.write();
			if let Some((qp, eu)) = cache.sync(pivot, enacted, retracted, commit_hash.as_ref(), self.parent_hash.as_ref(), self.experimental_query_plan.as_ref()) {
				self.experimental_query_plan = Some(qp);
				self.experimental_update = Some(eu);
			}
		}// else { TODO EMCH do not sync when exp -> warn need to extract some exp udate from sync cache default fn
		

		trace!(
			"Syncing cache, id = (#{:?}, {:?}), parent={:?}, best={}",
			commit_number,
			commit_hash,
			self.parent_hash,
			is_best,
		);
		// Filter out committing block if any.
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
			warn!("isbest: {:?}", is_best);
				let eu = &self.experimental_update;
				let mut exp_cache = self.experimental_cache.as_mut().map(|c| c.0.write())
					.and_then(|c| eu.as_ref().map(|eu| (c, eu)));
				trace!(
					"Committing {} local, {} hashes, {} modified root entries, {} modified child entries",
					local_cache.storage.len(),
					local_cache.hashes.len(),
					changes.len(),
					child_changes.iter().map(|v|v.1.len()).sum::<usize>(),
				);
				for (k, v) in local_cache.storage.drain() {
		if k == [28, 182, 243, 110, 2, 122, 187, 32, 145, 207, 181, 17, 10, 181, 8, 127, 6, 21, 91, 60, 217, 168, 201, 229, 233, 162, 63, 213, 220, 19, 165, 237] {

			warn!("write k = {:?}", v);
		}
	
					// This bring some read query of unchanged values.
					// The queries will be written at latest block index when
					// they are not: this caching writes somewhat invalid
					// positional when you consider real state change.
					// With a strict historied backend we could have values
					// with right change index, here it is not (never write
					// this content to a backend).
					exp_cache.as_mut().map(|(exp_cache, eu)| {

		if k == [28, 182, 243, 110, 2, 122, 187, 32, 145, 207, 181, 17, 10, 181, 8, 127, 6, 21, 91, 60, 217, 168, 201, 229, 233, 162, 63, 213, 220, 19, 165, 237] {

			warn!("write k = {:?} at {:?}", v, eu);
		}
						exp_cache.emplace(k.clone(), v.clone(), eu); // debug here??
					});
			if is_best {
					cache.lru_storage.add(k, v);
			}
				}
			if is_best {
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
			let mut exp_cache = {
				let eu = &self.experimental_update;
				self.experimental_cache.as_mut().map(|c| c.0.write())
					.and_then(|c| eu.as_ref().map(|eu| (c, eu)))
			};
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
			warn!("isbest2: {:?}", is_best);
			for (k, v) in changes.into_iter() {
		if k == [28, 182, 243, 110, 2, 122, 187, 32, 145, 207, 181, 17, 10, 181, 8, 127, 6, 21, 91, 60, 217, 168, 201, 229, 233, 162, 63, 213, 220, 19, 165, 237] {

			warn!("write k = {:?} ", v);
		}
	
					exp_cache.as_mut().map(|(exp_cache, eu)| {
		if k == [28, 182, 243, 110, 2, 122, 187, 32, 145, 207, 181, 17, 10, 181, 8, 127, 6, 21, 91, 60, 217, 168, 201, 229, 233, 162, 63, 213, 220, 19, 165, 237] {

			warn!("write k = {:?} at {:?}", v, eu);
		}
						exp_cache.emplace(k.clone(), v.clone(), eu);
					});

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

impl<S: StateBackend<HashFor<B>>, B: BlockT> CachingState<S, B> {
	#[cfg(test)]
	pub(crate) fn qc_new(
		state: S,
		shared_cache: SharedCache<B>,
		experimental_cache: Option<SyncExperimentalCache<B>>,
		parent_hash: Option<B::Hash>,
	) -> Self {
		let mut result = Self::new(state, shared_cache, experimental_cache, parent_hash);
		result.cache.qc = true;
		result
	}

	/// Create a new instance wrapping generic State and shared cache.
	pub(crate) fn new(
		state: S,
		shared_cache: SharedCache<B>,
		experimental_cache: Option<SyncExperimentalCache<B>>,
		parent_hash: Option<B::Hash>,
	) -> Self {
		let experimental_query_plan = parent_hash.as_ref().and_then(|ph|
				experimental_cache.as_ref().and_then(|ec| {
					let mut cache = ec.0.write();
					cache.management.get_db_state(ph)
				}));
		// TODO factor with previous exp, ok for now
		let experimental_update = parent_hash.as_ref().and_then(|ph|
				experimental_cache.as_ref().and_then(|ec| {
					let mut cache = ec.0.write();
					cache.management.get_db_state_mut(ph)
				}));

		if experimental_query_plan.is_none() && parent_hash.is_some() {
			warn!("No query plan for cache {:?}", parent_hash);
		}
		experimental_query_plan.as_ref().map(|qp|
			warn!("Query plan for new cache = {:?}", qp)
		);
		experimental_update.as_ref().map(|eu|
			warn!("Update at for new cache = {:?}", eu)
		);
		CachingState {
			usage: StateUsageStats::new(),
			overlay_stats: sp_state_machine::StateMachineStats::default(),
			state,
			cache: CacheChanges {
				shared_cache,
				experimental_cache,
				local_cache: RwLock::new(LocalCache {
					storage: Default::default(),
					hashes: Default::default(),
					child_storage: Default::default(),
				}),
				parent_hash,
				experimental_query_plan,
				experimental_update,
				no_assert: false,
				qc: false,
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
	) -> bool {
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
		trace!(
			"Cache lookup skipped for {:?}: parent hash is unknown",
			key.as_ref().map(HexDisplay::from),
		);
		false
	}
}

static cache_hits_counter: std::sync::atomic::AtomicIsize = std::sync::atomic::AtomicIsize::new(0);

impl<S: StateBackend<HashFor<B>>, B: BlockT> StateBackend<HashFor<B>> for CachingState<S, B> {
	type Error = S::Error;
	type Transaction = S::Transaction;
	type TrieBackendStorage = S::TrieBackendStorage;

	fn storage(&self, key: &[u8]) -> Result<Option<Vec<u8>>, Self::Error> {
		/* experimental cache need to use local cache (upgrade and drop is not
		 * doable with a shared state). Generally, I think this local cache
		 * should move into the overlay layer (most of the evaluation requires it
		 * and we would not need the RWLock.
		*/
		let local_cache = self.cache.local_cache.upgradable_read();
		// Note that local cache makes that lru is not refreshed
		if let Some(entry) = local_cache.storage.get(key).cloned() {
			trace!("Found in local cache: {:?}", HexDisplay::from(&key));
			self.usage.tally_key_read(key, entry.as_ref(), true);

			return Ok(entry)
		}

		let exp_v = if let Some(cache) = self.cache.experimental_cache.as_ref() {
			self.cache.experimental_query_plan.as_ref().and_then(|qp| {
				// TODO change trait to borrow to avoid alloc
				cache.get(&key.to_vec(), qp)
			})
		} else {
			None
		}; // TODO elsify then non cache

		let mut cache = self.cache.shared_cache.lock();
		if Self::is_allowed(Some(key), None, &self.cache.parent_hash, &cache.modifications) {
			if let Some(entry) = cache.lru_storage.get(key).map(|a| a.clone()) {
				trace!("Found in shared cache: {:?}", HexDisplay::from(&key));
				self.usage.tally_key_read(key, entry.as_ref(), true);
if !self.cache.no_assert {
	if let Some(exp_v) = exp_v {
		assert_eq!(entry, exp_v, "k: {:?}, {:?}, qp {:?} h {:?}", key, self.state.storage(key), self.cache.experimental_query_plan, self.cache.parent_hash);
	}
} else {
	let nb = cache_hits_counter.fetch_sub(1, std::sync::atomic::Ordering::Relaxed);
	warn!("Std cache it when no experimental cache it {}", nb - 1);
}
	
				return Ok(entry)
			}
		}
if exp_v.is_some() {
	let nb = cache_hits_counter.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
	warn!("Experimental cache it when no std cache it {}", nb + 1);
}
		trace!("Cache miss: {:?}", HexDisplay::from(&key));
		let value = self.state.storage(key)?;
if !self.cache.qc && !self.cache.no_assert {
	if let Some(exp_v) = exp_v {
		assert_eq!(value, exp_v, "k: {:?}, qb {:?} h {:?}", key, self.cache.experimental_query_plan, self.cache.parent_hash);
	}
}

		RwLockUpgradableReadGuard::upgrade(local_cache).storage.insert(key.to_vec(), value.clone());
		self.usage.tally_key_read(key, value.as_ref(), false);
		Ok(value)

/*	  let result = self.storage_inner(key)?;
		if let Some(exp_v) = exp_v {
			assert_eq!(result, exp_v);
		} else {
			if let Some(cache) = self.cache.experimental_cache.as_ref() {
				self.cache.experimental_update.as_ref().map(|eu| {
					// TODO change trait to borrow to avoid alloc
					cache.0.write().emplace(key.to_vec(), result.clone(), eu);
				});
			}
		}

		Ok(result)*/
	}

	fn storage_hash(&self, key: &[u8]) -> Result<Option<B::Hash>, Self::Error> {
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

	fn child_storage(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Result<Option<Vec<u8>>, Self::Error> {
		let key = (child_info.storage_key().to_vec(), key.to_vec());
		let local_cache = self.cache.local_cache.upgradable_read();
		if let Some(entry) = local_cache.child_storage.get(&key).cloned() {
			trace!("Found in local cache: {:?}", key);
			return Ok(
				self.usage.tally_child_key_read(&key, entry, true)
			)
		}
		let mut cache = self.cache.shared_cache.lock();
		if Self::is_allowed(None, Some(&key), &self.cache.parent_hash, &cache.modifications) {
			if let Some(entry) = cache.lru_child_storage.get(&key).map(|a| a.clone()) {
				trace!("Found in shared cache: {:?}", key);
				return Ok(
					self.usage.tally_child_key_read(&key, entry, true)
				)
			}
		}
		trace!("Cache miss: {:?}", key);
		let value = self.state.child_storage(child_info, &key.1[..])?;

		// just pass it through the usage counter
		let value =	self.usage.tally_child_key_read(&key, value, false);

		RwLockUpgradableReadGuard::upgrade(local_cache).child_storage.insert(key, value.clone());
		Ok(value)
	}

	fn exists_storage(&self, key: &[u8]) -> Result<bool, Self::Error> {
		Ok(self.storage(key)?.is_some())
	}

	fn exists_child_storage(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Result<bool, Self::Error> {
		self.state.exists_child_storage(child_info, key)
	}

	fn for_keys_in_child_storage<F: FnMut(&[u8])>(
		&self,
		child_info: &ChildInfo,
		f: F,
	) {
		self.state.for_keys_in_child_storage(child_info, f)
	}

	fn next_storage_key(&self, key: &[u8]) -> Result<Option<Vec<u8>>, Self::Error> {
		self.state.next_storage_key(key)
	}

	fn next_child_storage_key(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Result<Option<Vec<u8>>, Self::Error> {
		self.state.next_child_storage_key(child_info, key)
	}

	fn for_keys_with_prefix<F: FnMut(&[u8])>(&self, prefix: &[u8], f: F) {
		self.state.for_keys_with_prefix(prefix, f)
	}

	fn for_key_values_with_prefix<F: FnMut(&[u8], &[u8])>(&self, prefix: &[u8], f: F) {
		self.state.for_key_values_with_prefix(prefix, f)
	}

	fn for_child_keys_with_prefix<F: FnMut(&[u8])>(
		&self,
		child_info: &ChildInfo,
		prefix: &[u8],
		f: F,
	) {
		self.state.for_child_keys_with_prefix(child_info, prefix, f)
	}

	fn storage_root<'a>(
		&self,
		delta: impl Iterator<Item=(&'a [u8], Option<&'a [u8]>)>,
	) -> (B::Hash, Self::Transaction) where B::Hash: Ord {
		self.state.storage_root(delta)
	}

	fn child_storage_root<'a>(
		&self,
		child_info: &ChildInfo,
		delta: impl Iterator<Item=(&'a [u8], Option<&'a [u8]>)>,
	) -> (B::Hash, bool, Self::Transaction) where B::Hash: Ord {
		self.state.child_storage_root(child_info, delta)
	}

	fn pairs(&self) -> Vec<(Vec<u8>, Vec<u8>)> {
		self.state.pairs()
	}

	fn keys(&self, prefix: &[u8]) -> Vec<Vec<u8>> {
		self.state.keys(prefix)
	}

	fn child_keys(
		&self,
		child_info: &ChildInfo,
		prefix: &[u8],
	) -> Vec<Vec<u8>> {
		self.state.child_keys(child_info, prefix)
	}

	fn as_trie_backend(&mut self) -> Option<&TrieBackend<Self::TrieBackendStorage, HashFor<B>>> {
		self.state.as_trie_backend()
	}

	fn register_overlay_stats(&mut self, stats: &sp_state_machine::StateMachineStats) {
		self.overlay_stats.add(stats);
	}

	fn usage_info(&self) -> sp_state_machine::UsageInfo {
		let mut info = self.usage.take();
		info.include_state_machine_states(&self.overlay_stats);
		info
	}
}

/// Extended [`CachingState`] that will sync the caches on drop.
pub struct SyncingCachingState<S, Block: BlockT> {
	/// The usage statistics of the backend. These will be updated on drop.
	state_usage: Arc<StateUsageStats>,
	/// Reference to the meta db.
	meta: Arc<RwLock<Meta<NumberFor<Block>, Block::Hash>>>,
	/// Mutex to lock get exlusive access to the backend.
	lock: Arc<RwLock<()>>,
	/// The wrapped caching state.
	///
	/// This is required to be a `Option`, because sometimes we want to extract
	/// the cache changes and Rust does not allow to move fields from types that
	/// implement `Drop`.
	caching_state: Option<CachingState<S, Block>>,
	/// Disable syncing of the cache. This is by default always `false`. However,
	/// we need to disable syncing when this is a state in a
	/// [`BlockImportOperation`](crate::BlockImportOperation). The import operation
	/// takes care to sync the cache and more importantly we want to prevent a dead
	/// lock.
	disable_syncing: bool,
}

impl<S, B: BlockT> SyncingCachingState<S, B> {
	/// Create new automatic syncing state.
	pub fn new(
		caching_state: CachingState<S, B>,
		state_usage: Arc<StateUsageStats>,
		meta: Arc<RwLock<Meta<NumberFor<B>, B::Hash>>>,
		lock: Arc<RwLock<()>>,
	) -> Self {
		Self {
			caching_state: Some(caching_state),
			state_usage,
			meta,
			lock,
			disable_syncing: false,
		}
	}

	/// Returns the reference to the internal [`CachingState`].
	fn caching_state(&self) -> &CachingState<S, B> {
		self.caching_state
			.as_ref()
			.expect("`caching_state` is always valid for the lifetime of the object; qed")
	}

	/// Convert `Self` into the cache changes.
	pub fn into_cache_changes(mut self) -> CacheChanges<B> {
		self.caching_state
			.take()
			.expect("`caching_state` is always valid for the lifetime of the object; qed")
			.cache
	}

	/// Disable syncing the cache on drop.
	pub fn disable_syncing(&mut self) {
		self.disable_syncing = true;
	}
}

impl<S, B: BlockT> std::fmt::Debug for SyncingCachingState<S, B> {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		self.caching_state().fmt(f)
	}
}

impl<S: StateBackend<HashFor<B>>, B: BlockT> StateBackend<HashFor<B>> for SyncingCachingState<S, B> {
	type Error = S::Error;
	type Transaction = S::Transaction;
	type TrieBackendStorage = S::TrieBackendStorage;

	fn storage(&self, key: &[u8]) -> Result<Option<Vec<u8>>, Self::Error> {
		self.caching_state().storage(key)
	}

	fn storage_hash(&self, key: &[u8]) -> Result<Option<B::Hash>, Self::Error> {
		self.caching_state().storage_hash(key)
	}

	fn child_storage(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Result<Option<Vec<u8>>, Self::Error> {
		self.caching_state().child_storage(child_info, key)
	}

	fn exists_storage(&self, key: &[u8]) -> Result<bool, Self::Error> {
		self.caching_state().exists_storage(key)
	}

	fn exists_child_storage(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Result<bool, Self::Error> {
		self.caching_state().exists_child_storage(child_info, key)
	}

	fn for_keys_in_child_storage<F: FnMut(&[u8])>(
		&self,
		child_info: &ChildInfo,
		f: F,
	) {
		self.caching_state().for_keys_in_child_storage(child_info, f)
	}

	fn next_storage_key(&self, key: &[u8]) -> Result<Option<Vec<u8>>, Self::Error> {
		self.caching_state().next_storage_key(key)
	}

	fn next_child_storage_key(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Result<Option<Vec<u8>>, Self::Error> {
		self.caching_state().next_child_storage_key(child_info, key)
	}

	fn for_keys_with_prefix<F: FnMut(&[u8])>(&self, prefix: &[u8], f: F) {
		self.caching_state().for_keys_with_prefix(prefix, f)
	}

	fn for_key_values_with_prefix<F: FnMut(&[u8], &[u8])>(&self, prefix: &[u8], f: F) {
		self.caching_state().for_key_values_with_prefix(prefix, f)
	}

	fn for_child_keys_with_prefix<F: FnMut(&[u8])>(
		&self,
		child_info: &ChildInfo,
		prefix: &[u8],
		f: F,
	) {
		self.caching_state().for_child_keys_with_prefix(child_info, prefix, f)
	}

	fn storage_root<'a>(
		&self,
		delta: impl Iterator<Item=(&'a [u8], Option<&'a [u8]>)>,
	) -> (B::Hash, Self::Transaction) where B::Hash: Ord {
		self.caching_state().storage_root(delta)
	}

	fn child_storage_root<'a>(
		&self,
		child_info: &ChildInfo,
		delta: impl Iterator<Item=(&'a [u8], Option<&'a [u8]>)>,
	) -> (B::Hash, bool, Self::Transaction) where B::Hash: Ord {
		self.caching_state().child_storage_root(child_info, delta)
	}

	fn pairs(&self) -> Vec<(Vec<u8>, Vec<u8>)> {
		self.caching_state().pairs()
	}

	fn keys(&self, prefix: &[u8]) -> Vec<Vec<u8>> {
		self.caching_state().keys(prefix)
	}

	fn child_keys(
		&self,
		child_info: &ChildInfo,
		prefix: &[u8],
	) -> Vec<Vec<u8>> {
		self.caching_state().child_keys(child_info, prefix)
	}

	fn as_trie_backend(&mut self) -> Option<&TrieBackend<Self::TrieBackendStorage, HashFor<B>>> {
		self.caching_state
			.as_mut()
			.expect("`caching_state` is valid for the lifetime of the object; qed")
			.as_trie_backend()
	}

	fn register_overlay_stats(&mut self, stats: &sp_state_machine::StateMachineStats) {
		self.caching_state().register_overlay_stats(stats);
	}

	fn usage_info(&self) -> sp_state_machine::UsageInfo {
		self.caching_state().usage_info()
	}
}

impl<S, B: BlockT> Drop for SyncingCachingState<S, B> {
	fn drop(&mut self) {
		if self.disable_syncing {
			return;
		}

		if let Some(mut caching_state) = self.caching_state.take() {
			let _lock = self.lock.read();

			self.state_usage.merge_sm(caching_state.usage.take());
			if let Some(hash) = caching_state.cache.parent_hash.clone() {
				let is_best = self.meta.read().best_hash == hash;
				caching_state.cache.sync_cache(None, &[], &[], vec![], vec![], None, None, is_best);
			}
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use sp_runtime::{
		traits::BlakeTwo256,
		testing::{H256, Block as RawBlock, ExtrinsicWrapper},
	};
	use sp_state_machine::InMemoryBackend;

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

		let (shared, experimental) = new_shared_cache::<Block>(256 * 1024, (0, 1), Default::default());

		// blocks  [ 3a(c) 2a(c) 2b 1b 1a(c) 0 ]
		// state   [ 5     5     4  3  2     2 ]
		let mut s = CachingState::qc_new(
			InMemoryBackend::<BlakeTwo256>::default(),
			shared.clone(),
			experimental.clone(),
			Some(root_parent),
		);
		s.cache.sync_cache(
			None,
			&[],
			&[],
			vec![(key.clone(), Some(vec![2]))],
			vec![],
			Some(h0),
			Some(0),
			true,
		);

		let mut s = CachingState::qc_new(
			InMemoryBackend::<BlakeTwo256>::default(),
			shared.clone(),
			experimental.clone(),
			Some(h0),
		);
		s.cache.sync_cache(None, &[], &[], vec![], vec![], Some(h1a), Some(1), true);

		let mut s = CachingState::qc_new(
			InMemoryBackend::<BlakeTwo256>::default(),
			shared.clone(),
			experimental.clone(),
			Some(h0),
		);
		s.cache.sync_cache(
			None,
			&[],
			&[],
			vec![(key.clone(), Some(vec![3]))],
			vec![],
			Some(h1b),
			Some(1),
			false,
		);

		let mut s = CachingState::qc_new(
			InMemoryBackend::<BlakeTwo256>::default(),
			shared.clone(),
			experimental.clone(),
			Some(h1b),
		);
		s.cache.sync_cache(
			None,
			&[],
			&[],
			vec![(key.clone(), Some(vec![4]))],
			vec![],
			Some(h2b),
			Some(2),
			false,
		);

		let mut s = CachingState::qc_new(
			InMemoryBackend::<BlakeTwo256>::default(),
			shared.clone(),
			experimental.clone(),
			Some(h1a),
		);
		s.cache.sync_cache(
			None,
			&[],
			&[],
			vec![(key.clone(), Some(vec![5]))],
			vec![],
			Some(h2a),
			Some(2),
			true,
		);

		let mut s = CachingState::qc_new(
			InMemoryBackend::<BlakeTwo256>::default(),
			shared.clone(),
			experimental.clone(),
			Some(h2a),
		);
		s.cache.sync_cache(None, &[], &[], vec![], vec![], Some(h3a), Some(3), true);

		let s = CachingState::qc_new(
			InMemoryBackend::<BlakeTwo256>::default(),
			shared.clone(),
			experimental.clone(),
			Some(h3a),
		);
		assert_eq!(s.storage(&key).unwrap().unwrap(), vec![5]);

		let s = CachingState::qc_new(
			InMemoryBackend::<BlakeTwo256>::default(),
			shared.clone(),
			experimental.clone(),
			Some(h1a),
		);
		assert!(s.storage(&key).unwrap().is_none());

		let s = CachingState::qc_new(
			InMemoryBackend::<BlakeTwo256>::default(),
			shared.clone(),
			experimental.clone(),
			Some(h2b),
		);
		assert!(s.storage(&key).unwrap().is_none());

		let s = CachingState::qc_new(
			InMemoryBackend::<BlakeTwo256>::default(),
			shared.clone(),
			experimental.clone(),
			Some(h1b),
		);
		assert!(s.storage(&key).unwrap().is_none());

		// reorg to 3b
		// blocks  [ 3b(c) 3a 2a 2b(c) 1b 1a 0 ]
		let mut s = CachingState::qc_new(
			InMemoryBackend::<BlakeTwo256>::default(),
			shared.clone(),
			experimental.clone(),
			Some(h2b),
		);
		s.cache.sync_cache(
			Some(&h0),
			&[h1b, h2b, h3b],
			&[h1a, h2a, h3a],
			vec![],
			vec![],
			Some(h3b),
			Some(3),
			true,
		);
		let s = CachingState::qc_new(
			InMemoryBackend::<BlakeTwo256>::default(),
			shared.clone(),
			experimental.clone(),
			Some(h3a),
		);
		assert!(s.storage(&key).unwrap().is_none());
	}

	#[test]
	fn simple_fork() {
		sp_tracing::try_init_simple();

		let root_parent = H256::random();
		let key = H256::random()[..].to_vec();
		let h1 = H256::random();
		let h2a = H256::random();
		let h2b = H256::random();
		let h3b = H256::random();

		let (shared, experimental) = new_shared_cache::<Block>(256*1024, (0,1), Default::default());

		let mut s = CachingState::qc_new(
			InMemoryBackend::<BlakeTwo256>::default(),
			shared.clone(),
			experimental.clone(),
			Some(root_parent),
		);
		s.cache.sync_cache(
			None,
			&[],
			&[],
			vec![(key.clone(), Some(vec![2]))],
			vec![],
			Some(h1),
			Some(1),
			true,
		);

		let mut s = CachingState::qc_new(
			InMemoryBackend::<BlakeTwo256>::default(),
			shared.clone(),
			experimental.clone(),
			Some(h1),
		);
		s.cache.sync_cache(None, &[], &[], vec![], vec![], Some(h2a), Some(2), true);

		let mut s = CachingState::qc_new(
			InMemoryBackend::<BlakeTwo256>::default(),
			shared.clone(),
			experimental.clone(),
			Some(h1),
		);
		s.cache.sync_cache(
			None,
			&[],
			&[],
			vec![(key.clone(), Some(vec![3]))],
			vec![],
			Some(h2b),
			Some(2),
			false,
		);

		let mut s = CachingState::qc_new(
			InMemoryBackend::<BlakeTwo256>::default(),
			shared.clone(),
			experimental.clone(),
			Some(h2b),
		);
		s.cache.sync_cache(
			None,
			&[],
			&[],
			vec![(key.clone(), Some(vec![3]))],
			vec![],
			Some(h3b),
			Some(2),
			false,
		);

		let s = CachingState::qc_new(
			InMemoryBackend::<BlakeTwo256>::default(),
			shared.clone(),
			experimental.clone(),
			Some(h2a),
		);
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

		let (shared, experimental) = new_shared_cache::<Block>(256*1024, (0,1), Default::default());

		let mut s = CachingState::qc_new(
			InMemoryBackend::<BlakeTwo256>::default(),
			shared.clone(),
			experimental.clone(),
			Some(root_parent),
		);
		s.cache.sync_cache(None, &[], &[], vec![], vec![], Some(h1), Some(1), true);

		let mut s = CachingState::qc_new(
			InMemoryBackend::<BlakeTwo256>::default(),
			shared.clone(),
			experimental.clone(),
			Some(h1),
		);
		s.cache.sync_cache(None, &[], &[], vec![], vec![], Some(h2a), Some(2), true);

		let mut s = CachingState::qc_new(
			InMemoryBackend::<BlakeTwo256>::default(),
			shared.clone(),
			experimental.clone(),
			Some(h2a),
		);
		s.cache.sync_cache(
			None,
			&[],
			&[],
			vec![(key.clone(), Some(vec![2]))],
			vec![],
			Some(h3a),
			Some(3),
			true,
		);

		let mut s = CachingState::qc_new(
			InMemoryBackend::<BlakeTwo256>::default(),
			shared.clone(),
			experimental.clone(),
			Some(h1),
		);
		s.cache.sync_cache(None, &[], &[], vec![], vec![], Some(h2b), Some(2), false);

		let mut s = CachingState::qc_new(
			InMemoryBackend::<BlakeTwo256>::default(),
			shared.clone(),
			experimental.clone(),
			Some(h2b),
		);
		s.cache.sync_cache(
			None,
			&[],
			&[],
			vec![(key.clone(), Some(vec![3]))],
			vec![],
			Some(h3b),
			Some(3),
			false,
		);

		let s = CachingState::qc_new(
			InMemoryBackend::<BlakeTwo256>::default(),
			shared.clone(),
			experimental.clone(),
			Some(h3a),
		);
		assert_eq!(s.storage(&key).unwrap().unwrap(), vec![2]);
	}

	#[test]
	fn should_track_used_size_correctly() {
		let root_parent = H256::random();
		let (shared, experimental) = new_shared_cache::<Block>(109, ((109-36), 109), Default::default());
		let h0 = H256::random();

		let mut s = CachingState::qc_new(
			InMemoryBackend::<BlakeTwo256>::default(),
			shared.clone(),
			experimental.clone(),
			Some(root_parent.clone()),
		);

		let key = H256::random()[..].to_vec();
		let s_key = H256::random()[..].to_vec();
		s.cache.sync_cache(
			None,
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
			None,
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
		let (shared, experimental) = new_shared_cache::<Block>(36*3, (2,3), Default::default());
		let h0 = H256::random();

		let mut s = CachingState::qc_new(
			InMemoryBackend::<BlakeTwo256>::default(),
			shared.clone(),
			experimental.clone(),
			Some(root_parent),
		);

		let key = H256::random()[..].to_vec();
		s.cache.sync_cache(
			None,
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
			None,
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
		sp_tracing::try_init_simple();
		let root_parent = H256::random();

		let key = H256::random()[..].to_vec();

		let h0 = H256::random();
		let h1 = H256::random();

		let (shared, experimental) = new_shared_cache::<Block>(256 * 1024, (0, 1), Default::default());
		let mut s = CachingState::qc_new(
			InMemoryBackend::<BlakeTwo256>::default(),
			shared.clone(),
			experimental.clone(),
			Some(root_parent.clone()),
		);
		s.cache.sync_cache(
			None,
			&[],
			&[],
			vec![(key.clone(), Some(vec![2]))],
			vec![],
			Some(h0.clone()),
			Some(0),
			true,
		);

		let mut s = CachingState::qc_new(
			InMemoryBackend::<BlakeTwo256>::default(),
			shared.clone(),
			experimental.clone(),
			Some(h0),
		);
		s.cache.sync_cache(
			None,
			&[],
			&[],
			vec![(key.clone(), Some(vec![3]))],
			vec![],
			Some(h1),
			Some(1),
			true,
		);

		let mut s = CachingState::qc_new(
			InMemoryBackend::<BlakeTwo256>::default(),
			shared.clone(),
			experimental.clone(),
			Some(h1),
		);
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
		s.cache.sync_cache(None, &[], &[], vec![], vec![], None, None, true);

		let s = CachingState::qc_new(
			InMemoryBackend::<BlakeTwo256>::default(),
			shared.clone(),
			experimental.clone(),
			Some(h1),
		);
		assert_eq!(s.storage(&key).unwrap(), None);
	}
}

#[cfg(test)]
mod qc {
	use std::collections::{HashMap, hash_map::Entry};

	use quickcheck::{quickcheck, TestResult, Arbitrary};

	use super::*;
	use sp_runtime::{
		traits::BlakeTwo256,
		testing::{H256, Block as RawBlock, ExtrinsicWrapper},
	};
	use sp_state_machine::InMemoryBackend;

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
		shared: SharedCache<Block>,
		experimental: Option<SyncExperimentalCache<Block>>,
		canon: Vec<Node>,
		forks: HashMap<H256, Vec<Node>>,
	}

	impl Mutator {
		fn new_empty() -> Self {
			let (shared, experimental) = new_shared_cache::<Block>(256*1024, (0,1), Default::default());

			Self {
				shared,
				experimental,
				canon: vec![],
				forks: HashMap::new(),
			}
		}

		fn head_state(&self, hash: H256) -> CachingState<InMemoryBackend<BlakeTwo256>, Block> {
			CachingState::qc_new(
				InMemoryBackend::<BlakeTwo256>::default(),
				self.shared.clone(),
				self.experimental.clone(),
				Some(hash),
			)
		}

		fn canon_head_state(&self) -> CachingState<InMemoryBackend<BlakeTwo256>, Block> {
			self.head_state(self.canon.last().expect("Expected to be one commit").hash)
		}

		fn mutate_static(
			&mut self,
			action: Action,
		) -> CachingState<InMemoryBackend<BlakeTwo256>, Block> {
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

		fn mutate(
			&mut self,
			action: Action,
		) -> Result<CachingState<InMemoryBackend<BlakeTwo256>, Block>, ()> {
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

					let mut state = CachingState::qc_new(
						InMemoryBackend::<BlakeTwo256>::default(),
						self.shared.clone(),
						self.experimental.clone(),
						Some(parent),
					);

					state.cache.sync_cache(
						None,
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

					let mut state = CachingState::qc_new(
						InMemoryBackend::<BlakeTwo256>::default(),
						self.shared.clone(),
						self.experimental.clone(),
						Some(parent_hash),
					);

					state.cache.sync_cache(
						None,
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

							let pivot = self.canon.last().map(|node| node.hash);
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

							let mut state = CachingState::qc_new(
								InMemoryBackend::<BlakeTwo256>::default(),
								self.shared.clone(),
								self.experimental.clone(),
								Some(fork_at),
							);

							let height = pos as u64 + enacted.len() as u64 + 2;
							state.cache.sync_cache(
								pivot.as_ref(),
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
								.expect("wasn't forking to emptiness so there should be one!")
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
