// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! State backend that's useful for benchmarking

use crate::{DbState, DbStateBuilder};
use hash_db::{Hasher, Prefix};
use kvdb::{DBTransaction, KeyValueDB};
use linked_hash_map::LinkedHashMap;
use parking_lot::Mutex;
use sp_core::{
	hexdisplay::HexDisplay,
	storage::{ChildInfo, TrackedStorageKey},
};
use sp_runtime::{
	traits::{Block as BlockT, HashingFor},
	StateVersion, Storage,
};
use sp_state_machine::{
	backend::Backend as StateBackend, BackendTransaction, ChildStorageCollection, DBValue,
	IterArgs, StorageCollection, StorageIterator, StorageKey, StorageValue,
};
use sp_trie::{
	cache::{CacheSize, SharedTrieCache},
	prefixed_key, MemoryDB,
};
use std::{
	cell::{Cell, RefCell},
	collections::HashMap,
	sync::Arc,
};

type State<B> = DbState<B>;

struct StorageDb<Block: BlockT> {
	db: Arc<dyn KeyValueDB>,
	_block: std::marker::PhantomData<Block>,
}

impl<Block: BlockT> sp_state_machine::Storage<HashingFor<Block>> for StorageDb<Block> {
	fn get(&self, key: &Block::Hash, prefix: Prefix) -> Result<Option<DBValue>, String> {
		let prefixed_key = prefixed_key::<HashingFor<Block>>(key, prefix);
		self.db
			.get(0, &prefixed_key)
			.map_err(|e| format!("Database backend error: {:?}", e))
	}
}

struct KeyTracker {
	enable_tracking: bool,
	/// Key tracker for keys in the main trie.
	/// We track the total number of reads and writes to these keys,
	/// not de-duplicated for repeats.
	main_keys: LinkedHashMap<Vec<u8>, TrackedStorageKey>,
	/// Key tracker for keys in a child trie.
	/// Child trie are identified by their storage key (i.e. `ChildInfo::storage_key()`)
	/// We track the total number of reads and writes to these keys,
	/// not de-duplicated for repeats.
	child_keys: LinkedHashMap<Vec<u8>, LinkedHashMap<Vec<u8>, TrackedStorageKey>>,
}

/// State that manages the backend database reference. Allows runtime to control the database.
pub struct BenchmarkingState<B: BlockT> {
	root: Cell<B::Hash>,
	genesis_root: B::Hash,
	state: RefCell<Option<State<B>>>,
	db: Cell<Option<Arc<dyn KeyValueDB>>>,
	genesis: HashMap<Vec<u8>, (Vec<u8>, i32)>,
	record: Cell<Vec<Vec<u8>>>,
	key_tracker: Arc<Mutex<KeyTracker>>,
	whitelist: RefCell<Vec<TrackedStorageKey>>,
	proof_recorder: Option<sp_trie::recorder::Recorder<HashingFor<B>>>,
	proof_recorder_root: Cell<B::Hash>,
	shared_trie_cache: SharedTrieCache<HashingFor<B>>,
}

/// A raw iterator over the `BenchmarkingState`.
pub struct RawIter<B: BlockT> {
	inner: <DbState<B> as StateBackend<HashingFor<B>>>::RawIter,
	child_trie: Option<Vec<u8>>,
	key_tracker: Arc<Mutex<KeyTracker>>,
}

impl<B: BlockT> StorageIterator<HashingFor<B>> for RawIter<B> {
	type Backend = BenchmarkingState<B>;
	type Error = String;

	fn next_key(&mut self, backend: &Self::Backend) -> Option<Result<StorageKey, Self::Error>> {
		match self.inner.next_key(backend.state.borrow().as_ref()?) {
			Some(Ok(key)) => {
				self.key_tracker.lock().add_read_key(self.child_trie.as_deref(), &key);
				Some(Ok(key))
			},
			result => result,
		}
	}

	fn next_pair(
		&mut self,
		backend: &Self::Backend,
	) -> Option<Result<(StorageKey, StorageValue), Self::Error>> {
		match self.inner.next_pair(backend.state.borrow().as_ref()?) {
			Some(Ok((key, value))) => {
				self.key_tracker.lock().add_read_key(self.child_trie.as_deref(), &key);
				Some(Ok((key, value)))
			},
			result => result,
		}
	}

	fn was_complete(&self) -> bool {
		self.inner.was_complete()
	}
}

impl<B: BlockT> BenchmarkingState<B> {
	/// Create a new instance that creates a database in a temporary dir.
	pub fn new(
		genesis: Storage,
		_cache_size_mb: Option<usize>,
		record_proof: bool,
		enable_tracking: bool,
	) -> Result<Self, String> {
		let state_version = sp_runtime::StateVersion::default();
		let mut root = B::Hash::default();
		let mut mdb = MemoryDB::<HashingFor<B>>::default();
		sp_trie::trie_types::TrieDBMutBuilderV1::<HashingFor<B>>::new(&mut mdb, &mut root).build();

		let mut state = BenchmarkingState {
			state: RefCell::new(None),
			db: Cell::new(None),
			root: Cell::new(root),
			genesis: Default::default(),
			genesis_root: Default::default(),
			record: Default::default(),
			key_tracker: Arc::new(Mutex::new(KeyTracker {
				main_keys: Default::default(),
				child_keys: Default::default(),
				enable_tracking,
			})),
			whitelist: Default::default(),
			proof_recorder: record_proof.then(Default::default),
			proof_recorder_root: Cell::new(root),
			// Enable the cache, but do not sync anything to the shared state.
			shared_trie_cache: SharedTrieCache::new(CacheSize::new(0)),
		};

		state.add_whitelist_to_tracker();

		state.reopen()?;
		let child_delta = genesis.children_default.values().map(|child_content| {
			(
				&child_content.child_info,
				child_content.data.iter().map(|(k, v)| (k.as_ref(), Some(v.as_ref()))),
			)
		});
		let (root, transaction): (B::Hash, _) =
			state.state.borrow().as_ref().unwrap().full_storage_root(
				genesis.top.iter().map(|(k, v)| (k.as_ref(), Some(v.as_ref()))),
				child_delta,
				state_version,
			);
		state.genesis = transaction.clone().drain();
		state.genesis_root = root;
		state.commit(root, transaction, Vec::new(), Vec::new())?;
		state.record.take();
		Ok(state)
	}

	fn reopen(&self) -> Result<(), String> {
		*self.state.borrow_mut() = None;
		let db = match self.db.take() {
			Some(db) => db,
			None => Arc::new(kvdb_memorydb::create(1)),
		};
		self.db.set(Some(db.clone()));
		if let Some(recorder) = &self.proof_recorder {
			recorder.reset();
			self.proof_recorder_root.set(self.root.get());
		}
		let storage_db = Arc::new(StorageDb::<B> { db, _block: Default::default() });
		*self.state.borrow_mut() = Some(
			DbStateBuilder::<B>::new(storage_db, self.root.get())
				.with_optional_recorder(self.proof_recorder.clone())
				.with_cache(self.shared_trie_cache.local_cache())
				.build(),
		);
		Ok(())
	}

	fn add_whitelist_to_tracker(&self) {
		self.key_tracker.lock().add_whitelist(&self.whitelist.borrow());
	}

	fn wipe_tracker(&self) {
		let mut key_tracker = self.key_tracker.lock();
		key_tracker.main_keys = LinkedHashMap::new();
		key_tracker.child_keys = LinkedHashMap::new();
		key_tracker.add_whitelist(&self.whitelist.borrow());
	}

	fn add_read_key(&self, childtrie: Option<&[u8]>, key: &[u8]) {
		self.key_tracker.lock().add_read_key(childtrie, key);
	}

	fn add_write_key(&self, childtrie: Option<&[u8]>, key: &[u8]) {
		self.key_tracker.lock().add_write_key(childtrie, key);
	}

	fn all_trackers(&self) -> Vec<TrackedStorageKey> {
		self.key_tracker.lock().all_trackers()
	}
}

impl KeyTracker {
	fn add_whitelist(&mut self, whitelist: &[TrackedStorageKey]) {
		whitelist.iter().for_each(|key| {
			let mut whitelisted = TrackedStorageKey::new(key.key.clone());
			whitelisted.whitelist();
			self.main_keys.insert(key.key.clone(), whitelisted);
		});
	}

	// Childtrie is identified by its storage key (i.e. `ChildInfo::storage_key`)
	fn add_read_key(&mut self, childtrie: Option<&[u8]>, key: &[u8]) {
		if !self.enable_tracking {
			return
		}

		let child_key_tracker = &mut self.child_keys;
		let main_key_tracker = &mut self.main_keys;

		let key_tracker = if let Some(childtrie) = childtrie {
			child_key_tracker.entry(childtrie.to_vec()).or_insert_with(LinkedHashMap::new)
		} else {
			main_key_tracker
		};

		let should_log = match key_tracker.get_mut(key) {
			None => {
				let mut has_been_read = TrackedStorageKey::new(key.to_vec());
				has_been_read.add_read();
				key_tracker.insert(key.to_vec(), has_been_read);
				true
			},
			Some(tracker) => {
				let should_log = !tracker.has_been_read();
				tracker.add_read();
				should_log
			},
		};

		if should_log {
			if let Some(childtrie) = childtrie {
				log::trace!(
					target: "benchmark",
					"Childtrie Read: {} {}", HexDisplay::from(&childtrie), HexDisplay::from(&key)
				);
			} else {
				log::trace!(target: "benchmark", "Read: {}", HexDisplay::from(&key));
			}
		}
	}

	// Childtrie is identified by its storage key (i.e. `ChildInfo::storage_key`)
	fn add_write_key(&mut self, childtrie: Option<&[u8]>, key: &[u8]) {
		if !self.enable_tracking {
			return
		}

		let child_key_tracker = &mut self.child_keys;
		let main_key_tracker = &mut self.main_keys;

		let key_tracker = if let Some(childtrie) = childtrie {
			child_key_tracker.entry(childtrie.to_vec()).or_insert_with(LinkedHashMap::new)
		} else {
			main_key_tracker
		};

		// If we have written to the key, we also consider that we have read from it.
		let should_log = match key_tracker.get_mut(key) {
			None => {
				let mut has_been_written = TrackedStorageKey::new(key.to_vec());
				has_been_written.add_write();
				key_tracker.insert(key.to_vec(), has_been_written);
				true
			},
			Some(tracker) => {
				let should_log = !tracker.has_been_written();
				tracker.add_write();
				should_log
			},
		};

		if should_log {
			if let Some(childtrie) = childtrie {
				log::trace!(
					target: "benchmark",
					"Childtrie Write: {} {}", HexDisplay::from(&childtrie), HexDisplay::from(&key)
				);
			} else {
				log::trace!(target: "benchmark", "Write: {}", HexDisplay::from(&key));
			}
		}
	}

	// Return all the tracked storage keys among main and child trie.
	fn all_trackers(&self) -> Vec<TrackedStorageKey> {
		let mut all_trackers = Vec::new();

		self.main_keys.iter().for_each(|(_, tracker)| {
			all_trackers.push(tracker.clone());
		});

		self.child_keys.iter().for_each(|(_, child_tracker)| {
			child_tracker.iter().for_each(|(_, tracker)| {
				all_trackers.push(tracker.clone());
			});
		});

		all_trackers
	}
}

fn state_err() -> String {
	"State is not open".into()
}

impl<B: BlockT> StateBackend<HashingFor<B>> for BenchmarkingState<B> {
	type Error = <DbState<B> as StateBackend<HashingFor<B>>>::Error;
	type TrieBackendStorage = <DbState<B> as StateBackend<HashingFor<B>>>::TrieBackendStorage;
	type RawIter = RawIter<B>;

	fn storage(&self, key: &[u8]) -> Result<Option<Vec<u8>>, Self::Error> {
		self.add_read_key(None, key);
		self.state.borrow().as_ref().ok_or_else(state_err)?.storage(key)
	}

	fn storage_hash(&self, key: &[u8]) -> Result<Option<B::Hash>, Self::Error> {
		self.add_read_key(None, key);
		self.state.borrow().as_ref().ok_or_else(state_err)?.storage_hash(key)
	}

	fn child_storage(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Result<Option<Vec<u8>>, Self::Error> {
		self.add_read_key(Some(child_info.storage_key()), key);
		self.state
			.borrow()
			.as_ref()
			.ok_or_else(state_err)?
			.child_storage(child_info, key)
	}

	fn child_storage_hash(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Result<Option<B::Hash>, Self::Error> {
		self.add_read_key(Some(child_info.storage_key()), key);
		self.state
			.borrow()
			.as_ref()
			.ok_or_else(state_err)?
			.child_storage_hash(child_info, key)
	}

	fn exists_storage(&self, key: &[u8]) -> Result<bool, Self::Error> {
		self.add_read_key(None, key);
		self.state.borrow().as_ref().ok_or_else(state_err)?.exists_storage(key)
	}

	fn exists_child_storage(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Result<bool, Self::Error> {
		self.add_read_key(Some(child_info.storage_key()), key);
		self.state
			.borrow()
			.as_ref()
			.ok_or_else(state_err)?
			.exists_child_storage(child_info, key)
	}

	fn next_storage_key(&self, key: &[u8]) -> Result<Option<Vec<u8>>, Self::Error> {
		self.add_read_key(None, key);
		self.state.borrow().as_ref().ok_or_else(state_err)?.next_storage_key(key)
	}

	fn next_child_storage_key(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Result<Option<Vec<u8>>, Self::Error> {
		self.add_read_key(Some(child_info.storage_key()), key);
		self.state
			.borrow()
			.as_ref()
			.ok_or_else(state_err)?
			.next_child_storage_key(child_info, key)
	}

	fn storage_root<'a>(
		&self,
		delta: impl Iterator<Item = (&'a [u8], Option<&'a [u8]>)>,
		state_version: StateVersion,
	) -> (B::Hash, BackendTransaction<HashingFor<B>>) {
		self.state
			.borrow()
			.as_ref()
			.map_or(Default::default(), |s| s.storage_root(delta, state_version))
	}

	fn child_storage_root<'a>(
		&self,
		child_info: &ChildInfo,
		delta: impl Iterator<Item = (&'a [u8], Option<&'a [u8]>)>,
		state_version: StateVersion,
	) -> (B::Hash, bool, BackendTransaction<HashingFor<B>>) {
		self.state
			.borrow()
			.as_ref()
			.map_or(Default::default(), |s| s.child_storage_root(child_info, delta, state_version))
	}

	fn raw_iter(&self, args: IterArgs) -> Result<Self::RawIter, Self::Error> {
		let child_trie =
			args.child_info.as_ref().map(|child_info| child_info.storage_key().to_vec());
		self.state
			.borrow()
			.as_ref()
			.map(|s| s.raw_iter(args))
			.unwrap_or(Ok(Default::default()))
			.map(|raw_iter| RawIter {
				inner: raw_iter,
				key_tracker: self.key_tracker.clone(),
				child_trie,
			})
	}

	fn commit(
		&self,
		storage_root: <HashingFor<B> as Hasher>::Out,
		mut transaction: BackendTransaction<HashingFor<B>>,
		main_storage_changes: StorageCollection,
		child_storage_changes: ChildStorageCollection,
	) -> Result<(), Self::Error> {
		if let Some(db) = self.db.take() {
			let mut db_transaction = DBTransaction::new();
			let changes = transaction.drain();
			let mut keys = Vec::with_capacity(changes.len());
			for (key, (val, rc)) in changes {
				if rc > 0 {
					db_transaction.put(0, &key, &val);
				} else if rc < 0 {
					db_transaction.delete(0, &key);
				}
				keys.push(key);
			}
			let mut record = self.record.take();
			record.extend(keys);
			self.record.set(record);
			db.write(db_transaction)
				.map_err(|_| String::from("Error committing transaction"))?;
			self.root.set(storage_root);
			self.db.set(Some(db));

			// Track DB Writes
			main_storage_changes.iter().for_each(|(key, _)| {
				self.add_write_key(None, key);
			});
			child_storage_changes.iter().for_each(|(child_storage_key, storage_changes)| {
				storage_changes.iter().for_each(|(key, _)| {
					self.add_write_key(Some(child_storage_key), key);
				})
			});
		} else {
			return Err("Trying to commit to a closed db".into())
		}
		self.reopen()
	}

	fn wipe(&self) -> Result<(), Self::Error> {
		// Restore to genesis
		let record = self.record.take();
		if let Some(db) = self.db.take() {
			let mut db_transaction = DBTransaction::new();
			for key in record {
				match self.genesis.get(&key) {
					Some((v, _)) => db_transaction.put(0, &key, v),
					None => db_transaction.delete(0, &key),
				}
			}
			db.write(db_transaction)
				.map_err(|_| String::from("Error committing transaction"))?;
			self.db.set(Some(db));
		}

		self.root.set(self.genesis_root);
		self.reopen()?;
		self.wipe_tracker();
		Ok(())
	}

	/// Get the key tracking information for the state db.
	/// 1. `reads` - Total number of DB reads.
	/// 2. `repeat_reads` - Total number of in-memory reads.
	/// 3. `writes` - Total number of DB writes.
	/// 4. `repeat_writes` - Total number of in-memory writes.
	fn read_write_count(&self) -> (u32, u32, u32, u32) {
		let mut reads = 0;
		let mut repeat_reads = 0;
		let mut writes = 0;
		let mut repeat_writes = 0;

		self.all_trackers().iter().for_each(|tracker| {
			if !tracker.whitelisted {
				if tracker.reads > 0 {
					reads += 1;
					repeat_reads += tracker.reads - 1;
				}

				if tracker.writes > 0 {
					writes += 1;
					repeat_writes += tracker.writes - 1;
				}
			}
		});
		(reads, repeat_reads, writes, repeat_writes)
	}

	/// Reset the key tracking information for the state db.
	fn reset_read_write_count(&self) {
		self.wipe_tracker()
	}

	fn get_whitelist(&self) -> Vec<TrackedStorageKey> {
		self.whitelist.borrow().to_vec()
	}

	fn set_whitelist(&self, new: Vec<TrackedStorageKey>) {
		*self.whitelist.borrow_mut() = new;
	}

	fn get_read_and_written_keys(&self) -> Vec<(Vec<u8>, u32, u32, bool)> {
		// We only track at the level of a key-prefix and not whitelisted for now for memory size.
		// TODO: Refactor to enable full storage key transparency, where we can remove the
		// `prefix_key_tracker`.
		let mut prefix_key_tracker = LinkedHashMap::<Vec<u8>, (u32, u32, bool)>::new();
		self.all_trackers().iter().for_each(|tracker| {
			if !tracker.whitelisted {
				let prefix_length = tracker.key.len().min(32);
				let prefix = tracker.key[0..prefix_length].to_vec();
				// each read / write of a specific key is counted at most one time, since
				// additional reads / writes happen in the memory overlay.
				let reads = tracker.reads.min(1);
				let writes = tracker.writes.min(1);
				if let Some(prefix_tracker) = prefix_key_tracker.get_mut(&prefix) {
					prefix_tracker.0 += reads;
					prefix_tracker.1 += writes;
				} else {
					prefix_key_tracker.insert(prefix, (reads, writes, tracker.whitelisted));
				}
			}
		});

		prefix_key_tracker
			.iter()
			.map(|(key, tracker)| -> (Vec<u8>, u32, u32, bool) {
				(key.to_vec(), tracker.0, tracker.1, tracker.2)
			})
			.collect::<Vec<_>>()
	}

	fn register_overlay_stats(&self, stats: &sp_state_machine::StateMachineStats) {
		self.state.borrow().as_ref().map(|s| s.register_overlay_stats(stats));
	}

	fn usage_info(&self) -> sp_state_machine::UsageInfo {
		self.state
			.borrow()
			.as_ref()
			.map_or(sp_state_machine::UsageInfo::empty(), |s| s.usage_info())
	}

	fn proof_size(&self) -> Option<u32> {
		self.proof_recorder.as_ref().map(|recorder| {
			let proof_size = recorder.estimate_encoded_size() as u32;

			let proof = recorder.to_storage_proof();

			let proof_recorder_root = self.proof_recorder_root.get();
			if proof_recorder_root == Default::default() || proof_size == 1 {
				// empty trie
				log::debug!(target: "benchmark", "Some proof size: {}", &proof_size);
				proof_size
			} else {
				if let Some(size) = proof.encoded_compact_size::<HashingFor<B>>(proof_recorder_root)
				{
					size as u32
				} else if proof_recorder_root == self.root.get() {
					log::debug!(target: "benchmark", "No changes - no proof");
					0
				} else {
					panic!(
						"proof rec root {:?}, root {:?}, genesis {:?}, rec_len {:?}",
						self.proof_recorder_root.get(),
						self.root.get(),
						self.genesis_root,
						proof_size,
					);
				}
			}
		})
	}
}

impl<Block: BlockT> std::fmt::Debug for BenchmarkingState<Block> {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "Bench DB")
	}
}

#[cfg(test)]
mod test {
	use crate::bench::BenchmarkingState;
	use sp_state_machine::backend::Backend as _;

	fn hex(hex: &str) -> Vec<u8> {
		array_bytes::hex2bytes(hex).unwrap()
	}

	#[test]
	fn iteration_is_also_counted_in_rw_counts() {
		let storage = sp_runtime::Storage {
			top: vec![(
				hex("ce6e1397e668c7fcf47744350dc59688455a2c2dbd2e2a649df4e55d93cd7158"),
				hex("0102030405060708"),
			)]
			.into_iter()
			.collect(),
			..sp_runtime::Storage::default()
		};
		let bench_state =
			BenchmarkingState::<crate::tests::Block>::new(storage, None, false, true).unwrap();

		assert_eq!(bench_state.read_write_count(), (0, 0, 0, 0));
		assert_eq!(bench_state.keys(Default::default()).unwrap().count(), 1);
		assert_eq!(bench_state.read_write_count(), (1, 0, 0, 0));
	}

	#[test]
	fn read_to_main_and_child_tries() {
		let bench_state =
			BenchmarkingState::<crate::tests::Block>::new(Default::default(), None, false, true)
				.unwrap();

		for _ in 0..2 {
			let child1 = sp_core::storage::ChildInfo::new_default(b"child1");
			let child2 = sp_core::storage::ChildInfo::new_default(b"child2");

			bench_state.storage(b"foo").unwrap();
			bench_state.child_storage(&child1, b"foo").unwrap();
			bench_state.child_storage(&child2, b"foo").unwrap();

			bench_state.storage(b"bar").unwrap();
			bench_state.child_storage(&child1, b"bar").unwrap();
			bench_state.child_storage(&child2, b"bar").unwrap();

			bench_state
				.commit(
					Default::default(),
					Default::default(),
					vec![("foo".as_bytes().to_vec(), None)],
					vec![("child1".as_bytes().to_vec(), vec![("foo".as_bytes().to_vec(), None)])],
				)
				.unwrap();

			let rw_tracker = bench_state.read_write_count();
			assert_eq!(rw_tracker.0, 6);
			assert_eq!(rw_tracker.1, 0);
			assert_eq!(rw_tracker.2, 2);
			assert_eq!(rw_tracker.3, 0);
			bench_state.wipe().unwrap();
		}
	}
}
