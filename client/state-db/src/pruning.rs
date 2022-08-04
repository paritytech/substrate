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

use crate::{to_meta_key, CommitSet, Error, Hash, MetaDb};
use codec::{Decode, Encode};
use log::{trace, warn};
use std::{
	cmp,
	collections::{HashMap, HashSet, VecDeque},
};

const LAST_PRUNED: &[u8] = b"last_pruned";
const PRUNING_JOURNAL: &[u8] = b"pruning_journal";
// default pruning window size plus a magic number keep most common ops in cache
const CACHE_BATCH_SIZE: usize = 256 + 10;

/// See module documentation.
#[derive(parity_util_mem_derive::MallocSizeOf)]
pub struct RefWindow<BlockHash: Hash, Key: Hash, D: MetaDb> {
	/// A queue of blocks keep tracking keys that should be deleted for each block in the
	/// pruning window.
	death_rows_queue: DeathRowQueue<BlockHash, Key, D>,
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
/// - `MemQueue`, used when the backend database do not supports reference counting, keep all
/// 	blocks in memory, and keep track of re-inserted keys to not delete them when pruning
/// - `DbBackedQueue`, used when the backend database supports reference counting, only keep
/// 	a few number of blocks in memory and load more blocks on demand, it also keep all the
/// 	block's hash in memory for checking block existence
#[derive(parity_util_mem_derive::MallocSizeOf)]
enum DeathRowQueue<BlockHash: Hash, Key: Hash, D: MetaDb> {
	MemQueue {
		/// A queue of keys that should be deleted for each block in the pruning window.
		death_rows: VecDeque<DeathRow<BlockHash, Key>>,
		/// An index that maps each key from `death_rows` to block number.
		death_index: HashMap<Key, u64>,
	},
	DbBackedQueue {
		// The backend database
		db: D,
		/// A queue of keys that should be deleted for each block in the pruning window.
		/// Only caching the first fews blocks of the pruning window, blocks inside are
		/// successive and ordered by block number
		cache: VecDeque<DeathRow<BlockHash, Key>>,
		/// A queue of hashs of all the blocks that not loaded into cache, the first hash of
		/// the queue followe the last block of `cache`, namely `block_numer(hashs[0])` ==
		/// `block_numer(cache.last()) + 1`, hashs inside are successive and ordered by block
		/// number
		hashs: VecDeque<BlockHash>,
	},
}

impl<BlockHash: Hash, Key: Hash, D: MetaDb> DeathRowQueue<BlockHash, Key, D> {
	fn new(db: Option<D>) -> DeathRowQueue<BlockHash, Key, D> {
		match db {
			Some(db) => DeathRowQueue::DbBackedQueue {
				db,
				hashs: VecDeque::new(),
				cache: VecDeque::with_capacity(CACHE_BATCH_SIZE),
			},
			None =>
				DeathRowQueue::MemQueue { death_rows: VecDeque::new(), death_index: HashMap::new() },
		}
	}

	/// import a new block to the back of the queue
	fn import(&mut self, base: u64, hash: BlockHash, inserted: Vec<Key>, deleted: Vec<Key>) {
		match self {
			DeathRowQueue::DbBackedQueue { hashs, cache, .. } => {
				// `hashs` is empty means currently all block are loaded into `cache`
				// thus if `cache` is not full, load the next block into `cache` too
				if hashs.is_empty() && cache.len() < CACHE_BATCH_SIZE {
					cache.push_back(DeathRow { hash, deleted: deleted.into_iter().collect() });
				} else {
					hashs.push_back(hash);
				}
			},
			DeathRowQueue::MemQueue { death_rows, death_index } => {
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
			DeathRowQueue::DbBackedQueue { db, hashs, cache, .. } => {
				if cache.is_empty() && !hashs.is_empty() {
					// load more blocks from db since there are still blocks in it
					DeathRowQueue::load_batch_from_db(db, hashs, cache, base)?;
				}
				Ok(cache.pop_front())
			},
			DeathRowQueue::MemQueue { death_rows, death_index } => match death_rows.pop_front() {
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

	fn has_block(&self, hash: &BlockHash, skip: usize) -> bool {
		// TODO: if the pruning window is set to large, this may hurt performance
		match self {
			DeathRowQueue::DbBackedQueue { hashs, cache, .. } => cache
				.iter()
				.map(|row| &row.hash)
				.chain(hashs.iter())
				.skip(skip)
				.any(|h| h == hash),
			DeathRowQueue::MemQueue { death_rows, .. } =>
				death_rows.iter().map(|row| &row.hash).skip(skip).any(|h| h == hash),
		}
	}

	/// Revert recent additions to the queue, namely remove `amount` number of blocks from the back
	/// of the queue, `base` is the block number of the first block of the queue
	fn revert_recent_add(&mut self, base: u64, amout: usize) {
		debug_assert!(amout <= self.len());
		match self {
			DeathRowQueue::DbBackedQueue { hashs, cache, .. } => {
				// remove from `hashs` if it can cover
				if hashs.len() >= amout {
					hashs.truncate(hashs.len() - amout);
					return
				}
				// clear `hashs` and remove remain blocks from `cache`
				let remain = amout - hashs.len();
				hashs.clear();
				cache.truncate(cache.len() - remain);
			},
			DeathRowQueue::MemQueue { death_rows, death_index } => {
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
		hashs: &mut VecDeque<BlockHash>,
		cache: &mut VecDeque<DeathRow<BlockHash, Key>>,
		base: u64,
	) -> Result<(), Error<D::Error>> {
		// return if all blocks already loaded into `cache` and there are no other
		// blocks in the backend database
		if hashs.len() == 0 {
			return Ok(())
		}
		let start = base + cache.len() as u64;
		let batch_size = cmp::min(hashs.len(), CACHE_BATCH_SIZE);
		let mut loaded = 0;
		for i in 0..batch_size as u64 {
			match load_death_row_from_db::<BlockHash, _, _>(db, start + i)? {
				Some(row) => {
					// the incoming block's hash should be the same as the first hash of
					// `hashs`, if there are corrupted data `load_death_row_from_db` should
					// return a db error
					debug_assert_eq!(Some(row.hash.clone()), hashs.pop_front());
					cache.push_back(row);
					loaded += 1;
				},
				None => break,
			}
		}
		// `loaded` should be the same as what we expect, if there are missing blocks
		// `load_death_row_from_db` should return a db error
		debug_assert_eq!(batch_size, loaded);
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
			DeathRowQueue::DbBackedQueue { db, hashs, cache } => {
				// check if `index` target a block reside on disk
				if index >= cache.len() && index < cache.len() + hashs.len() {
					// if `index` target the next batch of `DeathRow`, load a batch from db
					if index - cache.len() < cmp::min(hashs.len(), CACHE_BATCH_SIZE) {
						DeathRowQueue::load_batch_from_db(db, hashs, cache, base)?;
					} else {
						// load a single `DeathRow` from db, but do not insert it to `cache`
						// because `cache` is a queue of successive `DeathRow`
						// NOTE: this branch should not be entered because blocks are visited
						// in successive increasing order, just keeping it for robustness
						return Ok(load_death_row_from_db(db, base + index as u64)?)
					}
				}
				Ok(cache.get(index).cloned())
			},
			DeathRowQueue::MemQueue { death_rows, .. } => Ok(death_rows.get(index).cloned()),
		}
	}

	/// Get the hash of the block at the given `index` of the queue  
	fn get_hash(&self, index: usize) -> Option<BlockHash> {
		match self {
			DeathRowQueue::DbBackedQueue { cache, hashs, .. } =>
				if index < cache.len() {
					cache.get(index).map(|r| r.hash.clone())
				} else {
					hashs.get(index - cache.len()).cloned()
				},
			DeathRowQueue::MemQueue { death_rows, .. } =>
				death_rows.get(index).map(|r| r.hash.clone()),
		}
	}

	/// Return the number of block in the pruning window
	fn len(&self) -> usize {
		match self {
			DeathRowQueue::DbBackedQueue { hashs, cache, .. } => cache.len() + hashs.len(),
			DeathRowQueue::MemQueue { death_rows, .. } => death_rows.len(),
		}
	}

	#[cfg(test)]
	fn get_mem_queue_state(
		&self,
	) -> Option<(&VecDeque<DeathRow<BlockHash, Key>>, &HashMap<Key, u64>)> {
		match self {
			DeathRowQueue::DbBackedQueue { .. } => None,
			DeathRowQueue::MemQueue { death_rows, death_index } => Some((death_rows, death_index)),
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
		let last_pruned = db.get_meta(&to_meta_key(LAST_PRUNED, &())).map_err(Error::Db)?;
		let pending_number: u64 = match last_pruned {
			Some(buffer) => u64::decode(&mut buffer.as_slice())? + 1,
			None => 0,
		};
		let mut block = pending_number;
		let death_rows_queue =
			DeathRowQueue::new(if count_insertions { None } else { Some(db.clone()) });
		let mut pruning = RefWindow {
			death_rows_queue,
			pending_number,
			pending_canonicalizations: 0,
			pending_prunings: 0,
		};
		// read the journal
		trace!(target: "state-db", "Reading pruning journal. Pending #{}", pending_number);
		loop {
			let journal_key = to_journal_key(block);
			match db.get_meta(&journal_key).map_err(Error::Db)? {
				Some(record) => {
					let record: JournalRecord<BlockHash, Key> =
						Decode::decode(&mut record.as_slice())?;
					trace!(target: "state-db", "Pruning journal entry {} ({} inserted, {} deleted)", block, record.inserted.len(), record.deleted.len());
					pruning.death_rows_queue.import(
						pending_number,
						record.hash,
						record.inserted,
						record.deleted,
					);
				},
				None => break,
			}
			block += 1;
		}
		Ok(pruning)
	}

	pub fn window_size(&self) -> u64 {
		(self.death_rows_queue.len() - self.pending_prunings) as u64
	}

	pub fn next_hash(&self) -> Option<BlockHash> {
		self.death_rows_queue.get_hash(self.pending_prunings)
	}

	pub fn mem_used(&self) -> usize {
		0
	}

	pub fn pending(&self) -> u64 {
		self.pending_number + self.pending_prunings as u64
	}

	pub fn have_block(&self, hash: &BlockHash) -> bool {
		self.death_rows_queue.has_block(hash, self.pending_prunings)
	}

	/// Prune next block. Expects at least one block in the window. Adds changes to `commit`.
	pub fn prune_one(&mut self, commit: &mut CommitSet<Key>) -> Result<(), Error<D::Error>> {
		if let Some(pruned) =
			self.death_rows_queue.get(self.pending_number, self.pending_prunings)?
		{
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
		let inserted = if matches!(self.death_rows_queue, DeathRowQueue::MemQueue { .. }) {
			commit.data.inserted.iter().map(|(k, _)| k.clone()).collect()
		} else {
			Default::default()
		};
		let deleted = ::std::mem::take(&mut commit.data.deleted);
		let journal_record = JournalRecord { hash: hash.clone(), inserted, deleted };
		let block = self.pending_number + self.death_rows_queue.len() as u64;
		let journal_key = to_journal_key(block);
		commit.meta.inserted.push((journal_key.clone(), journal_record.encode()));
		self.death_rows_queue.import(
			self.pending_number,
			journal_record.hash,
			journal_record.inserted,
			journal_record.deleted,
		);
		self.pending_canonicalizations += 1;
	}

	/// Apply all pending changes
	pub fn apply_pending(&mut self) {
		self.pending_canonicalizations = 0;
		for _ in 0..self.pending_prunings {
			let pruned = self
				.death_rows_queue
				.pop_front(self.pending_number)
				// NOTE: `pop_front` should not return `MetaDb::Error` because blocks are visited
				// by `RefWindow::prune_one` first then `RefWindow::apply_pending` and
				// `DeathRowQueue::get` should load the blocks into cache already
				.expect("block must loaded in cache thus no MetaDb::Error")
				.expect("pending_prunings is always < death_rows_queue.len()");
			trace!(target: "state-db", "Applying pruning {:?} ({} deleted)", pruned.hash, pruned.deleted.len());
			self.pending_number += 1;
		}
		self.pending_prunings = 0;
	}

	/// Revert all pending changes
	pub fn revert_pending(&mut self) {
		self.death_rows_queue
			.revert_recent_add(self.pending_number, self.pending_canonicalizations);
		self.pending_canonicalizations = 0;
		self.pending_prunings = 0;
	}
}

#[cfg(test)]
mod tests {
	use super::RefWindow;
	use crate::{
		pruning::DeathRowQueue,
		test::{make_commit, make_db, TestDb},
		CommitSet,
	};
	use sp_core::H256;

	fn check_journal(pruning: &RefWindow<H256, H256, TestDb>, db: &TestDb) {
		let count_insertions = matches!(pruning.death_rows_queue, DeathRowQueue::MemQueue { .. });
		let restored: RefWindow<H256, H256, TestDb> = RefWindow::new(db, count_insertions).unwrap();
		assert_eq!(pruning.pending_number, restored.pending_number);
		assert_eq!(
			pruning.death_rows_queue.get_mem_queue_state(),
			restored.death_rows_queue.get_mem_queue_state()
		);
	}

	#[test]
	fn created_from_empty_db() {
		let db = make_db(&[]);
		let pruning: RefWindow<H256, H256, TestDb> = RefWindow::new(&db, true).unwrap();
		assert_eq!(pruning.pending_number, 0);
		let (death_rows, death_index) = pruning.death_rows_queue.get_mem_queue_state().unwrap();
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
		let (death_rows, death_index) = pruning.death_rows_queue.get_mem_queue_state().unwrap();
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
		let h = H256::random();
		pruning.note_canonical(&h, &mut commit);
		db.commit(&commit);
		assert!(pruning.have_block(&h));
		pruning.apply_pending();
		assert!(pruning.have_block(&h));
		assert!(commit.data.deleted.is_empty());
		let (death_rows, death_index) = pruning.death_rows_queue.get_mem_queue_state().unwrap();
		assert_eq!(death_rows.len(), 1);
		assert_eq!(death_index.len(), 2);
		assert!(db.data_eq(&make_db(&[1, 2, 3, 4, 5])));
		check_journal(&pruning, &db);

		let mut commit = CommitSet::default();
		pruning.prune_one(&mut commit).unwrap();
		assert!(!pruning.have_block(&h));
		db.commit(&commit);
		pruning.apply_pending();
		assert!(!pruning.have_block(&h));
		assert!(db.data_eq(&make_db(&[2, 4, 5])));
		let (death_rows, death_index) = pruning.death_rows_queue.get_mem_queue_state().unwrap();
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
}
