// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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

//! Pruning window.
//!
//! For each block we maintain a list of nodes pending deletion.
//! There is also a global index of node key to block number.
//! If a node is re-inserted into the window it gets removed from
//! the death list.
//! The changes are journaled in the DB.

use crate::{noncanonical::LAST_CANONICAL, to_meta_key, CommitSet, Error, Hash, MetaDb};
use codec::{Decode, Encode};
use log::{trace, warn};
use std::{
	cmp,
	collections::{HashMap, HashSet, VecDeque},
};

const LAST_PRUNED: &[u8] = b"last_pruned";
const PRUNING_JOURNAL: &[u8] = b"pruning_journal";
// Default pruning window size plus a magic number keep most common ops in cache
const CACHE_BATCH_SIZE: usize = 256 + 10;

/// See module documentation.
#[derive(parity_util_mem_derive::MallocSizeOf)]
pub struct RefWindow<BlockHash: Hash, Key: Hash, D: MetaDb> {
	/// A queue of blocks keep tracking keys that should be deleted for each block in the
	/// pruning window.
	queue: DeathRowQueue<BlockHash, Key, D>,
	/// Block number that corresponds to the front of `death_rows`.
	pending_number: u64,
	/// Number of call of `note_canonical` after
	/// last call `apply_pending` or `revert_pending`
	pending_canonicalizations: usize,
	/// Number of calls of `prune_one` after
	/// last call `apply_pending` or `revert_pending`
	pending_prunings: usize,
}

/// `DeathRowQueue` used to keep track of blocks in the pruning window, there are two flavors:
/// - `Mem`, used when the backend database do not supports reference counting, keep all
/// 	blocks in memory, and keep track of re-inserted keys to not delete them when pruning
/// - `DbBacked`, used when the backend database supports reference counting, only keep
/// 	a few number of blocks in memory and load more blocks on demand, it also keep all the
/// 	block's hash in memory for checking block existence
#[derive(parity_util_mem_derive::MallocSizeOf)]
enum DeathRowQueue<BlockHash: Hash, Key: Hash, D: MetaDb> {
	Mem {
		/// A queue of keys that should be deleted for each block in the pruning window.
		death_rows: VecDeque<DeathRow<BlockHash, Key>>,
		/// An index that maps each key from `death_rows` to block number.
		death_index: HashMap<Key, u64>,
	},
	DbBacked {
		// The backend database
		db: D,
		/// A queue of keys that should be deleted for each block in the pruning window.
		/// Only caching the first fews blocks of the pruning window, blocks inside are
		/// successive and ordered by block number
		cache: VecDeque<DeathRow<BlockHash, Key>>,
		/// The number of blocks that not loaded into `cache`
		unload_blocks: usize,
	},
}

impl<BlockHash: Hash, Key: Hash, D: MetaDb> DeathRowQueue<BlockHash, Key, D> {
	/// Return a `DeathRowQueue` that all blocks are keep in memory
	fn new_mem(db: &D, base: u64) -> Result<DeathRowQueue<BlockHash, Key, D>, Error<D::Error>> {
		let mut block = base;
		let mut queue = DeathRowQueue::<BlockHash, Key, D>::Mem {
			death_rows: VecDeque::new(),
			death_index: HashMap::new(),
		};
		// read the journal
		trace!(target: "state-db", "Reading pruning journal for the memory queue. Pending #{}", base);
		loop {
			let journal_key = to_journal_key(block);
			match db.get_meta(&journal_key).map_err(Error::Db)? {
				Some(record) => {
					let record: JournalRecord<BlockHash, Key> =
						Decode::decode(&mut record.as_slice())?;
					trace!(target: "state-db", "Pruning journal entry {} ({} inserted, {} deleted)", block, record.inserted.len(), record.deleted.len());
					queue.import(base, record);
				},
				None => break,
			}
			block += 1;
		}
		Ok(queue)
	}

	/// Return a `DeathRowQueue` that backed by an database, and only keep a few number
	/// of blocks in memory
	fn new_db_backed(
		db: D,
		base: u64,
		mut unload_blocks: usize,
	) -> Result<DeathRowQueue<BlockHash, Key, D>, Error<D::Error>> {
		let mut cache = VecDeque::with_capacity(CACHE_BATCH_SIZE);
		trace!(target: "state-db", "Reading pruning journal for the database-backed queue. Pending #{}", base);
		// Load block from db
		DeathRowQueue::load_batch_from_db(&db, &mut unload_blocks, &mut cache, base)?;
		Ok(DeathRowQueue::DbBacked { db, cache, unload_blocks })
	}

	/// import a new block to the back of the queue
	fn import(&mut self, base: u64, journal_record: JournalRecord<BlockHash, Key>) {
		let JournalRecord { hash, inserted, deleted } = journal_record;
		match self {
			DeathRowQueue::DbBacked { unload_blocks, cache, .. } => {
				// `unload_blocks` is zero means currently all block are loaded into `cache`
				// thus if `cache` is not full, load the next block into `cache` too
				if *unload_blocks == 0 && cache.len() < CACHE_BATCH_SIZE {
					cache.push_back(DeathRow { hash, deleted: deleted.into_iter().collect() });
				} else {
					*unload_blocks += 1;
				}
			},
			DeathRowQueue::Mem { death_rows, death_index } => {
				// remove all re-inserted keys from death rows
				for k in inserted {
					if let Some(block) = death_index.remove(&k) {
						death_rows[(block - base) as usize].deleted.remove(&k);
					}
				}
				// add new keys
				let imported_block = base + death_rows.len() as u64;
				for k in deleted.iter() {
					death_index.insert(k.clone(), imported_block);
				}
				death_rows.push_back(DeathRow { hash, deleted: deleted.into_iter().collect() });
			},
		}
	}

	/// Pop out one block from the front of the queue, `base` is the block number
	/// of the first block of the queue
	fn pop_front(
		&mut self,
		base: u64,
	) -> Result<Option<DeathRow<BlockHash, Key>>, Error<D::Error>> {
		match self {
			DeathRowQueue::DbBacked { db, unload_blocks, cache } => {
				if cache.is_empty() && *unload_blocks != 0 {
					// load more blocks from db since there are still blocks in it
					DeathRowQueue::load_batch_from_db(db, unload_blocks, cache, base)?;
				}
				Ok(cache.pop_front())
			},
			DeathRowQueue::Mem { death_rows, death_index } => match death_rows.pop_front() {
				Some(row) => {
					for k in row.deleted.iter() {
						death_index.remove(k);
					}
					Ok(Some(row))
				},
				None => Ok(None),
			},
		}
	}

	/// Revert recent additions to the queue, namely remove `amount` number of blocks from the back
	/// of the queue, `base` is the block number of the first block of the queue
	fn revert_recent_add(&mut self, base: u64, amout: usize) {
		debug_assert!(amout <= self.len());
		match self {
			DeathRowQueue::DbBacked { unload_blocks, cache, .. } => {
				// remove from `unload_blocks` if it can cover
				if *unload_blocks >= amout {
					*unload_blocks -= amout;
					return
				}
				// clear `hashs` and remove remain blocks from `cache`
				let remain = amout - *unload_blocks;
				*unload_blocks = 0;
				cache.truncate(cache.len() - remain);
			},
			DeathRowQueue::Mem { death_rows, death_index } => {
				// Revert recent addition to the queue
				// Note that pending insertions might cause some existing deletions to be removed
				// from `death_index` We don't bother to track and revert that for now. This means
				// that a few nodes might end up no being deleted in case transaction fails and
				// `revert_pending` is called.
				death_rows.truncate(death_rows.len() - amout);
				let new_max_block = death_rows.len() as u64 + base;
				death_index.retain(|_, block| *block < new_max_block);
			},
		}
	}

	/// Load a batch of blocks from the backend database into `cache`, start from (and include) the
	/// next block followe the last block of `cache`, `base` is the block number of the first block
	/// of the queue
	fn load_batch_from_db(
		db: &D,
		unload_blocks: &mut usize,
		cache: &mut VecDeque<DeathRow<BlockHash, Key>>,
		base: u64,
	) -> Result<(), Error<D::Error>> {
		// return if all blocks already loaded into `cache` and there are no other
		// blocks in the backend database
		if *unload_blocks == 0 {
			return Ok(())
		}
		let start = base + cache.len() as u64;
		let batch_size = cmp::min(*unload_blocks, CACHE_BATCH_SIZE);
		let mut loaded = 0;
		for i in 0..batch_size as u64 {
			match load_death_row_from_db::<BlockHash, Key, D>(db, start + i)? {
				Some(row) => {
					cache.push_back(row);
					loaded += 1;
				},
				None => break,
			}
		}
		// `loaded` should be the same as what we expect, if there are missing blocks
		// `load_death_row_from_db` should return a db error
		debug_assert_eq!(batch_size, loaded);
		*unload_blocks -= loaded;
		Ok(())
	}

	/// Get the block in the given index of the queue, `base` is the block number of the
	/// first block of the queue
	fn get(
		&mut self,
		base: u64,
		index: usize,
	) -> Result<Option<DeathRow<BlockHash, Key>>, Error<D::Error>> {
		match self {
			DeathRowQueue::DbBacked { db, unload_blocks, cache } => {
				// check if `index` target a block reside on disk
				if index >= cache.len() && index < cache.len() + *unload_blocks {
					// if `index` target the next batch of `DeathRow`, load a batch from db
					if index - cache.len() < cmp::min(*unload_blocks, CACHE_BATCH_SIZE) {
						DeathRowQueue::load_batch_from_db(db, unload_blocks, cache, base)?;
					} else {
						// load a single `DeathRow` from db, but do not insert it to `cache`
						// because `cache` is a queue of successive `DeathRow`
						// NOTE: this branch should not be entered because blocks are visited
						// in successive increasing order, just keeping it for robustness
						return load_death_row_from_db(db, base + index as u64)
					}
				}
				Ok(cache.get(index).cloned())
			},
			DeathRowQueue::Mem { death_rows, .. } => Ok(death_rows.get(index).cloned()),
		}
	}

	/// Get the hash of the block at the given `index` of the queue  
	fn get_hash(&mut self, base: u64, index: usize) -> Result<Option<BlockHash>, Error<D::Error>> {
		match self {
			DeathRowQueue::DbBacked { cache, .. } =>
				if index < cache.len() {
					Ok(cache.get(index).map(|r| r.hash.clone()))
				} else {
					self.get(base, index).map(|r| r.map(|r| r.hash))
				},
			DeathRowQueue::Mem { death_rows, .. } =>
				Ok(death_rows.get(index).map(|r| r.hash.clone())),
		}
	}

	/// Return the number of block in the pruning window
	fn len(&self) -> usize {
		match self {
			DeathRowQueue::DbBacked { unload_blocks, cache, .. } => cache.len() + *unload_blocks,
			DeathRowQueue::Mem { death_rows, .. } => death_rows.len(),
		}
	}

	#[cfg(test)]
	fn get_mem_queue_state(
		&self,
	) -> Option<(&VecDeque<DeathRow<BlockHash, Key>>, &HashMap<Key, u64>)> {
		match self {
			DeathRowQueue::DbBacked { .. } => None,
			DeathRowQueue::Mem { death_rows, death_index } => Some((death_rows, death_index)),
		}
	}

	#[cfg(test)]
	fn get_db_backed_queue_state(&self) -> Option<(&VecDeque<DeathRow<BlockHash, Key>>, usize)> {
		match self {
			DeathRowQueue::DbBacked { cache, unload_blocks, .. } => Some((cache, *unload_blocks)),
			DeathRowQueue::Mem { .. } => None,
		}
	}

	#[cfg(test)]
	fn get_db(&mut self) -> Option<&mut D> {
		match self {
			DeathRowQueue::DbBacked { db, .. } => Some(db),
			DeathRowQueue::Mem { .. } => None,
		}
	}
}

fn load_death_row_from_db<BlockHash: Hash, Key: Hash, D: MetaDb>(
	db: &D,
	block: u64,
) -> Result<Option<DeathRow<BlockHash, Key>>, Error<D::Error>> {
	let journal_key = to_journal_key(block);
	match db.get_meta(&journal_key).map_err(Error::Db)? {
		Some(record) => {
			let JournalRecord { hash, deleted, .. } = Decode::decode(&mut record.as_slice())?;
			Ok(Some(DeathRow { hash, deleted: deleted.into_iter().collect() }))
		},
		None => Ok(None),
	}
}

#[derive(Clone, Debug, PartialEq, Eq, parity_util_mem_derive::MallocSizeOf)]
struct DeathRow<BlockHash: Hash, Key: Hash> {
	hash: BlockHash,
	deleted: HashSet<Key>,
}

#[derive(Encode, Decode)]
struct JournalRecord<BlockHash: Hash, Key: Hash> {
	hash: BlockHash,
	inserted: Vec<Key>,
	deleted: Vec<Key>,
}

fn to_journal_key(block: u64) -> Vec<u8> {
	to_meta_key(PRUNING_JOURNAL, &block)
}

impl<BlockHash: Hash, Key: Hash, D: MetaDb> RefWindow<BlockHash, Key, D> {
	pub fn new(
		db: &D,
		count_insertions: bool,
	) -> Result<RefWindow<BlockHash, Key, D>, Error<D::Error>> {
		// the block number of the first block in the queue
		let pending_number = match db.get_meta(&to_meta_key(LAST_PRUNED, &())).map_err(Error::Db)? {
			Some(buffer) => u64::decode(&mut buffer.as_slice())? + 1,
			None => 0,
		};
		// the block number of the last block in the queue
		let last_canonicalized_number =
			match db.get_meta(&to_meta_key(LAST_CANONICAL, &())).map_err(Error::Db)? {
				Some(buffer) => Some(<(BlockHash, u64)>::decode(&mut buffer.as_slice())?.1),
				None => None,
			};

		let queue = if count_insertions {
			DeathRowQueue::new_mem(db, pending_number)?
		} else {
			let unload = match last_canonicalized_number {
				Some(last_canonicalized_number) => {
					debug_assert!(last_canonicalized_number >= pending_number);
					last_canonicalized_number - pending_number + 1
				},
				// None means `LAST_CANONICAL` is never been wrote, since the pruning journals are
				// in the same `CommitSet` as `LAST_CANONICAL`, it means no pruning journal have
				// ever been committed to the db, thus set `unload` to zero
				None => 0,
			};
			DeathRowQueue::new_db_backed(db.clone(), pending_number, unload as usize)?
		};

		Ok(RefWindow { queue, pending_number, pending_canonicalizations: 0, pending_prunings: 0 })
	}

	pub fn window_size(&self) -> u64 {
		(self.queue.len() - self.pending_prunings) as u64
	}

	pub fn next_hash(&mut self) -> Result<Option<BlockHash>, Error<D::Error>> {
		self.queue.get_hash(self.pending_number, self.pending_prunings)
	}

	pub fn mem_used(&self) -> usize {
		0
	}

	// Return the block number of the first block that not been pending pruned
	pub fn pending(&self) -> u64 {
		self.pending_number + self.pending_prunings as u64
	}

	// Return true if a canonicalized block is in the window and not be pruned yet
	pub fn have_block(&self, number: u64) -> bool {
		number >= self.pending() && number < self.pending_number + self.queue.len() as u64
	}

	/// Prune next block. Expects at least one block in the window. Adds changes to `commit`.
	pub fn prune_one(&mut self, commit: &mut CommitSet<Key>) -> Result<(), Error<D::Error>> {
		if let Some(pruned) = self.queue.get(self.pending_number, self.pending_prunings)? {
			trace!(target: "state-db", "Pruning {:?} ({} deleted)", pruned.hash, pruned.deleted.len());
			let index = self.pending_number + self.pending_prunings as u64;
			commit.data.deleted.extend(pruned.deleted.into_iter());
			commit.meta.inserted.push((to_meta_key(LAST_PRUNED, &()), index.encode()));
			commit
				.meta
				.deleted
				.push(to_journal_key(self.pending_number + self.pending_prunings as u64));
			self.pending_prunings += 1;
		} else {
			warn!(target: "state-db", "Trying to prune when there's nothing to prune");
		}
		Ok(())
	}

	/// Add a change set to the window. Creates a journal record and pushes it to `commit`
	pub fn note_canonical(&mut self, hash: &BlockHash, commit: &mut CommitSet<Key>) {
		trace!(target: "state-db", "Adding to pruning window: {:?} ({} inserted, {} deleted)", hash, commit.data.inserted.len(), commit.data.deleted.len());
		let inserted = if matches!(self.queue, DeathRowQueue::Mem { .. }) {
			commit.data.inserted.iter().map(|(k, _)| k.clone()).collect()
		} else {
			Default::default()
		};
		let deleted = ::std::mem::take(&mut commit.data.deleted);
		let journal_record = JournalRecord { hash: hash.clone(), inserted, deleted };
		let block = self.pending_number + self.queue.len() as u64;
		commit.meta.inserted.push((to_journal_key(block), journal_record.encode()));
		self.queue.import(self.pending_number, journal_record);
		self.pending_canonicalizations += 1;
	}

	/// Apply all pending changes
	pub fn apply_pending(&mut self) {
		self.pending_canonicalizations = 0;
		for _ in 0..self.pending_prunings {
			let pruned = self
				.queue
				.pop_front(self.pending_number)
				// NOTE: `pop_front` should not return `MetaDb::Error` because blocks are visited
				// by `RefWindow::prune_one` first then `RefWindow::apply_pending` and
				// `DeathRowQueue::get` should load the blocks into cache already
				.expect("block must loaded in cache thus no MetaDb::Error")
				.expect("pending_prunings is always < queue.len()");
			trace!(target: "state-db", "Applying pruning {:?} ({} deleted)", pruned.hash, pruned.deleted.len());
			self.pending_number += 1;
		}
		self.pending_prunings = 0;
	}

	/// Revert all pending changes
	pub fn revert_pending(&mut self) {
		self.queue
			.revert_recent_add(self.pending_number, self.pending_canonicalizations);
		self.pending_canonicalizations = 0;
		self.pending_prunings = 0;
	}
}

#[cfg(test)]
mod tests {
	use super::{DeathRowQueue, RefWindow, CACHE_BATCH_SIZE};
	use crate::{
		noncanonical::LAST_CANONICAL,
		test::{make_commit, make_db, TestDb},
		to_meta_key, CommitSet, Hash,
	};
	use codec::Encode;
	use sp_core::H256;

	fn check_journal(pruning: &RefWindow<H256, H256, TestDb>, db: &TestDb) {
		let count_insertions = matches!(pruning.queue, DeathRowQueue::Mem { .. });
		let restored: RefWindow<H256, H256, TestDb> = RefWindow::new(db, count_insertions).unwrap();
		assert_eq!(pruning.pending_number, restored.pending_number);
		assert_eq!(pruning.queue.get_mem_queue_state(), restored.queue.get_mem_queue_state());
	}

	#[test]
	fn created_from_empty_db() {
		let db = make_db(&[]);
		let pruning: RefWindow<H256, H256, TestDb> = RefWindow::new(&db, true).unwrap();
		assert_eq!(pruning.pending_number, 0);
		let (death_rows, death_index) = pruning.queue.get_mem_queue_state().unwrap();
		assert!(death_rows.is_empty());
		assert!(death_index.is_empty());
	}

	#[test]
	fn prune_empty() {
		let db = make_db(&[]);
		let mut pruning: RefWindow<H256, H256, TestDb> = RefWindow::new(&db, true).unwrap();
		let mut commit = CommitSet::default();
		pruning.prune_one(&mut commit).unwrap();
		assert_eq!(pruning.pending_number, 0);
		let (death_rows, death_index) = pruning.queue.get_mem_queue_state().unwrap();
		assert!(death_rows.is_empty());
		assert!(death_index.is_empty());
		assert!(pruning.pending_prunings == 0);
		assert!(pruning.pending_canonicalizations == 0);
	}

	#[test]
	fn prune_one() {
		let mut db = make_db(&[1, 2, 3]);
		let mut pruning: RefWindow<H256, H256, TestDb> = RefWindow::new(&db, true).unwrap();
		let mut commit = make_commit(&[4, 5], &[1, 3]);
		pruning.note_canonical(&H256::random(), &mut commit);
		db.commit(&commit);
		assert!(pruning.have_block(0));
		pruning.apply_pending();
		assert!(pruning.have_block(0));
		assert!(commit.data.deleted.is_empty());
		let (death_rows, death_index) = pruning.queue.get_mem_queue_state().unwrap();
		assert_eq!(death_rows.len(), 1);
		assert_eq!(death_index.len(), 2);
		assert!(db.data_eq(&make_db(&[1, 2, 3, 4, 5])));
		check_journal(&pruning, &db);

		let mut commit = CommitSet::default();
		pruning.prune_one(&mut commit).unwrap();
		assert!(!pruning.have_block(0));
		db.commit(&commit);
		pruning.apply_pending();
		assert!(!pruning.have_block(0));
		assert!(db.data_eq(&make_db(&[2, 4, 5])));
		let (death_rows, death_index) = pruning.queue.get_mem_queue_state().unwrap();
		assert!(death_rows.is_empty());
		assert!(death_index.is_empty());
		assert_eq!(pruning.pending_number, 1);
	}

	#[test]
	fn prune_two() {
		let mut db = make_db(&[1, 2, 3]);
		let mut pruning: RefWindow<H256, H256, TestDb> = RefWindow::new(&db, true).unwrap();
		let mut commit = make_commit(&[4], &[1]);
		pruning.note_canonical(&H256::random(), &mut commit);
		db.commit(&commit);
		let mut commit = make_commit(&[5], &[2]);
		pruning.note_canonical(&H256::random(), &mut commit);
		db.commit(&commit);
		pruning.apply_pending();
		assert!(db.data_eq(&make_db(&[1, 2, 3, 4, 5])));

		check_journal(&pruning, &db);

		let mut commit = CommitSet::default();
		pruning.prune_one(&mut commit).unwrap();
		db.commit(&commit);
		pruning.apply_pending();
		assert!(db.data_eq(&make_db(&[2, 3, 4, 5])));
		let mut commit = CommitSet::default();
		pruning.prune_one(&mut commit).unwrap();
		db.commit(&commit);
		pruning.apply_pending();
		assert!(db.data_eq(&make_db(&[3, 4, 5])));
		assert_eq!(pruning.pending_number, 2);
	}

	#[test]
	fn prune_two_pending() {
		let mut db = make_db(&[1, 2, 3]);
		let mut pruning: RefWindow<H256, H256, TestDb> = RefWindow::new(&db, true).unwrap();
		let mut commit = make_commit(&[4], &[1]);
		pruning.note_canonical(&H256::random(), &mut commit);
		db.commit(&commit);
		let mut commit = make_commit(&[5], &[2]);
		pruning.note_canonical(&H256::random(), &mut commit);
		db.commit(&commit);
		assert!(db.data_eq(&make_db(&[1, 2, 3, 4, 5])));
		let mut commit = CommitSet::default();
		pruning.prune_one(&mut commit).unwrap();
		db.commit(&commit);
		assert!(db.data_eq(&make_db(&[2, 3, 4, 5])));
		let mut commit = CommitSet::default();
		pruning.prune_one(&mut commit).unwrap();
		db.commit(&commit);
		pruning.apply_pending();
		assert!(db.data_eq(&make_db(&[3, 4, 5])));
		assert_eq!(pruning.pending_number, 2);
	}

	#[test]
	fn reinserted_survives() {
		let mut db = make_db(&[1, 2, 3]);
		let mut pruning: RefWindow<H256, H256, TestDb> = RefWindow::new(&db, true).unwrap();
		let mut commit = make_commit(&[], &[2]);
		pruning.note_canonical(&H256::random(), &mut commit);
		db.commit(&commit);
		let mut commit = make_commit(&[2], &[]);
		pruning.note_canonical(&H256::random(), &mut commit);
		db.commit(&commit);
		let mut commit = make_commit(&[], &[2]);
		pruning.note_canonical(&H256::random(), &mut commit);
		db.commit(&commit);
		assert!(db.data_eq(&make_db(&[1, 2, 3])));
		pruning.apply_pending();

		check_journal(&pruning, &db);

		let mut commit = CommitSet::default();
		pruning.prune_one(&mut commit).unwrap();
		db.commit(&commit);
		assert!(db.data_eq(&make_db(&[1, 2, 3])));
		let mut commit = CommitSet::default();
		pruning.prune_one(&mut commit).unwrap();
		db.commit(&commit);
		assert!(db.data_eq(&make_db(&[1, 2, 3])));
		pruning.prune_one(&mut commit).unwrap();
		db.commit(&commit);
		assert!(db.data_eq(&make_db(&[1, 3])));
		pruning.apply_pending();
		assert_eq!(pruning.pending_number, 3);
	}

	#[test]
	fn reinserted_survive_pending() {
		let mut db = make_db(&[1, 2, 3]);
		let mut pruning: RefWindow<H256, H256, TestDb> = RefWindow::new(&db, true).unwrap();
		let mut commit = make_commit(&[], &[2]);
		pruning.note_canonical(&H256::random(), &mut commit);
		db.commit(&commit);
		let mut commit = make_commit(&[2], &[]);
		pruning.note_canonical(&H256::random(), &mut commit);
		db.commit(&commit);
		let mut commit = make_commit(&[], &[2]);
		pruning.note_canonical(&H256::random(), &mut commit);
		db.commit(&commit);
		assert!(db.data_eq(&make_db(&[1, 2, 3])));

		let mut commit = CommitSet::default();
		pruning.prune_one(&mut commit).unwrap();
		db.commit(&commit);
		assert!(db.data_eq(&make_db(&[1, 2, 3])));
		let mut commit = CommitSet::default();
		pruning.prune_one(&mut commit).unwrap();
		db.commit(&commit);
		assert!(db.data_eq(&make_db(&[1, 2, 3])));
		pruning.prune_one(&mut commit).unwrap();
		db.commit(&commit);
		assert!(db.data_eq(&make_db(&[1, 3])));
		pruning.apply_pending();
		assert_eq!(pruning.pending_number, 3);
	}

	#[test]
	fn reinserted_ignores() {
		let mut db = make_db(&[1, 2, 3]);
		let mut pruning: RefWindow<H256, H256, TestDb> = RefWindow::new(&db, false).unwrap();
		let mut commit = make_commit(&[], &[2]);
		pruning.note_canonical(&H256::random(), &mut commit);
		db.commit(&commit);
		let mut commit = make_commit(&[2], &[]);
		pruning.note_canonical(&H256::random(), &mut commit);
		db.commit(&commit);
		let mut commit = make_commit(&[], &[2]);
		pruning.note_canonical(&H256::random(), &mut commit);
		db.commit(&commit);
		assert!(db.data_eq(&make_db(&[1, 2, 3])));
		pruning.apply_pending();

		check_journal(&pruning, &db);

		let mut commit = CommitSet::default();
		pruning.prune_one(&mut commit).unwrap();
		db.commit(&commit);
		assert!(db.data_eq(&make_db(&[1, 3])));
	}

	fn push_last_canonicalized<H: Hash>(block: u64, commit: &mut CommitSet<H>) {
		commit
			.meta
			.inserted
			.push((to_meta_key(LAST_CANONICAL, &()), (block, block).encode()));
	}

	#[test]
	fn db_backed_queue() {
		let mut pruning: RefWindow<u64, H256, TestDb> =
			RefWindow::new(&make_db(&[]), false).unwrap();

		// start as an empty queue
		let (cache, unload_blocks) = pruning.queue.get_db_backed_queue_state().unwrap();
		assert_eq!(cache.len(), 0);
		assert_eq!(unload_blocks, 0);

		// import blocks
		// queue size and content should match
		for i in 0..(CACHE_BATCH_SIZE + 10) {
			let mut commit = make_commit(&[], &[]);
			pruning.note_canonical(&(i as u64), &mut commit);
			push_last_canonicalized(i as u64, &mut commit);
			pruning.queue.get_db().unwrap().commit(&commit);
			// block will fill in cache first
			let (cache, unload_blocks) = pruning.queue.get_db_backed_queue_state().unwrap();
			if i < CACHE_BATCH_SIZE {
				assert_eq!(cache.len(), i + 1);
				assert_eq!(unload_blocks, 0);
			} else {
				assert_eq!(cache.len(), CACHE_BATCH_SIZE);
				assert_eq!(unload_blocks, i - CACHE_BATCH_SIZE + 1);
			}
		}
		pruning.apply_pending();
		assert_eq!(pruning.queue.len(), CACHE_BATCH_SIZE + 10);
		let (cache, unload_blocks) = pruning.queue.get_db_backed_queue_state().unwrap();
		assert_eq!(cache.len(), CACHE_BATCH_SIZE);
		assert_eq!(unload_blocks, 10);
		for i in 0..CACHE_BATCH_SIZE {
			assert_eq!(cache[i].hash, i as u64);
		}

		// import a new block to the end of the queue
		// won't keep the new block in memory
		let mut commit = CommitSet::default();
		pruning.note_canonical(&(CACHE_BATCH_SIZE as u64 + 10), &mut commit);
		assert_eq!(pruning.queue.len(), CACHE_BATCH_SIZE + 11);
		let (cache, unload_blocks) = pruning.queue.get_db_backed_queue_state().unwrap();
		assert_eq!(cache.len(), CACHE_BATCH_SIZE);
		assert_eq!(unload_blocks, 11);

		// revert the last add that no apply yet
		// NOTE: do not commit the previous `CommitSet` to db
		pruning.queue.revert_recent_add(0, 1);
		assert_eq!(pruning.queue.len(), CACHE_BATCH_SIZE + 10);
		let (cache, unload_blocks) = pruning.queue.get_db_backed_queue_state().unwrap();
		assert_eq!(cache.len(), CACHE_BATCH_SIZE);
		assert_eq!(unload_blocks, 10);

		// remove one block from the start of the queue
		// block is removed from the head of cache
		let mut commit = CommitSet::default();
		pruning.prune_one(&mut commit).unwrap();
		pruning.queue.get_db().unwrap().commit(&commit);
		pruning.apply_pending();
		assert_eq!(pruning.queue.len(), CACHE_BATCH_SIZE + 9);
		let (cache, unload_blocks) = pruning.queue.get_db_backed_queue_state().unwrap();
		assert_eq!(cache.len(), CACHE_BATCH_SIZE - 1);
		assert_eq!(unload_blocks, 10);
		for i in 0..(CACHE_BATCH_SIZE - 1) {
			assert_eq!(cache[i].hash, (i + 1) as u64);
		}

		// load a new queue from db
		// `cache` is full again but the content of the queue should be the same
		let pruning: RefWindow<u64, H256, TestDb> =
			RefWindow::new(pruning.queue.get_db().unwrap(), false).unwrap();
		assert_eq!(pruning.queue.len(), CACHE_BATCH_SIZE + 9);
		let (cache, unload_blocks) = pruning.queue.get_db_backed_queue_state().unwrap();
		assert_eq!(cache.len(), CACHE_BATCH_SIZE);
		assert_eq!(unload_blocks, 9);
		for i in 0..CACHE_BATCH_SIZE {
			assert_eq!(cache[i].hash, (i + 1) as u64);
		}
	}

	#[test]
	fn load_block_from_db() {
		let mut pruning: RefWindow<u64, H256, TestDb> =
			RefWindow::new(&make_db(&[]), false).unwrap();

		// import blocks
		for i in 0..(CACHE_BATCH_SIZE as u64 * 2 + 10) {
			let mut commit = make_commit(&[], &[]);
			pruning.note_canonical(&i, &mut commit);
			push_last_canonicalized(i as u64, &mut commit);
			pruning.queue.get_db().unwrap().commit(&commit);
		}

		// the following operations won't triger loading block from db:
		// - getting block in cache
		// - getting block not in the queue
		let index = CACHE_BATCH_SIZE;
		assert_eq!(
			pruning.queue.get(0, index - 1).unwrap().unwrap().hash,
			CACHE_BATCH_SIZE as u64 - 1
		);
		assert_eq!(pruning.queue.get(0, CACHE_BATCH_SIZE * 2 + 10).unwrap(), None);
		let (cache, unload_blocks) = pruning.queue.get_db_backed_queue_state().unwrap();
		assert_eq!(cache.len(), CACHE_BATCH_SIZE);
		assert_eq!(unload_blocks, CACHE_BATCH_SIZE + 10);

		// getting a block not in cache will triger loading block from db
		assert_eq!(pruning.queue.get(0, index).unwrap().unwrap().hash, CACHE_BATCH_SIZE as u64);
		let (cache, unload_blocks) = pruning.queue.get_db_backed_queue_state().unwrap();
		assert_eq!(cache.len(), CACHE_BATCH_SIZE * 2);
		assert_eq!(unload_blocks, 10);

		// clear all block loaded in cache
		for _ in 0..CACHE_BATCH_SIZE * 2 {
			let mut commit = CommitSet::default();
			pruning.prune_one(&mut commit).unwrap();
			pruning.queue.get_db().unwrap().commit(&commit);
		}
		pruning.apply_pending();
		let (cache, unload_blocks) = pruning.queue.get_db_backed_queue_state().unwrap();
		assert!(cache.is_empty());
		assert_eq!(unload_blocks, 10);

		// getting the hash of block that not in cache will also triger loading
		// the remaining blocks from db
		assert_eq!(
			pruning.queue.get(pruning.pending_number, 0).unwrap().unwrap().hash,
			(CACHE_BATCH_SIZE * 2) as u64
		);
		let (cache, unload_blocks) = pruning.queue.get_db_backed_queue_state().unwrap();
		assert_eq!(cache.len(), 10);
		assert_eq!(unload_blocks, 0);

		// load a new queue from db
		// `cache` should be the same
		let pruning: RefWindow<u64, H256, TestDb> =
			RefWindow::new(pruning.queue.get_db().unwrap(), false).unwrap();
		assert_eq!(pruning.queue.len(), 10);
		let (cache, unload_blocks) = pruning.queue.get_db_backed_queue_state().unwrap();
		assert_eq!(cache.len(), 10);
		assert_eq!(unload_blocks, 0);
		for i in 0..10 {
			assert_eq!(cache[i].hash, (CACHE_BATCH_SIZE * 2 + i) as u64);
		}
	}
}
