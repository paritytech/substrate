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

use crate::{
	noncanonical::LAST_CANONICAL, to_meta_key, CommitSet, Error, Hash, MetaDb, StateDbError,
	DEFAULT_MAX_BLOCK_CONSTRAINT,
};
use codec::{Decode, Encode};
use log::trace;
use std::collections::{HashMap, HashSet, VecDeque};

pub(crate) const LAST_PRUNED: &[u8] = b"last_pruned";
const PRUNING_JOURNAL: &[u8] = b"pruning_journal";

/// See module documentation.
#[derive(parity_util_mem_derive::MallocSizeOf)]
pub struct RefWindow<BlockHash: Hash, Key: Hash, D: MetaDb> {
	/// A queue of blocks keep tracking keys that should be deleted for each block in the
	/// pruning window.
	queue: DeathRowQueue<BlockHash, Key, D>,
	/// Block number that is next to be pruned.
	base: u64,
}

/// `DeathRowQueue` used to keep track of blocks in the pruning window, there are two flavors:
/// - `Mem`, used when the backend database do not supports reference counting, keep all
/// 	blocks in memory, and keep track of re-inserted keys to not delete them when pruning
/// - `DbBacked`, used when the backend database supports reference counting, only keep
/// 	a few number of blocks in memory and load more blocks on demand
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
		#[ignore_malloc_size_of = "Shared data"]
		db: D,
		/// A queue of keys that should be deleted for each block in the pruning window.
		/// Only caching the first few blocks of the pruning window, blocks inside are
		/// successive and ordered by block number
		cache: VecDeque<DeathRow<BlockHash, Key>>,
		/// A soft limit of the cache's size
		cache_capacity: usize,
		/// Last block number added to the window
		last: Option<u64>,
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
					queue.import(base, block, record);
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
		last: Option<u64>,
		window_size: u32,
	) -> Result<DeathRowQueue<BlockHash, Key, D>, Error<D::Error>> {
		// limit the cache capacity from 1 to `DEFAULT_MAX_BLOCK_CONSTRAINT`
		let cache_capacity = window_size.clamp(1, DEFAULT_MAX_BLOCK_CONSTRAINT) as usize;
		let mut cache = VecDeque::with_capacity(cache_capacity);
		trace!(target: "state-db", "Reading pruning journal for the database-backed queue. Pending #{}", base);
		DeathRowQueue::load_batch_from_db(&db, &mut cache, base, cache_capacity)?;
		Ok(DeathRowQueue::DbBacked { db, cache, cache_capacity, last })
	}

	/// import a new block to the back of the queue
	fn import(&mut self, base: u64, num: u64, journal_record: JournalRecord<BlockHash, Key>) {
		let JournalRecord { hash, inserted, deleted } = journal_record;
		trace!(target: "state-db", "Importing {}, base={}", num, base);
		match self {
			DeathRowQueue::DbBacked { cache, cache_capacity, last, .. } => {
				// If the new block continues cached range and there is space, load it directly into
				// cache.
				if num == base + cache.len() as u64 && cache.len() < *cache_capacity {
					trace!(target: "state-db", "Adding to DB backed cache {:?} (#{})", hash, num);
					cache.push_back(DeathRow { hash, deleted: deleted.into_iter().collect() });
				}
				*last = Some(num);
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
			DeathRowQueue::DbBacked { db, cache, cache_capacity, .. } => {
				if cache.is_empty() {
					DeathRowQueue::load_batch_from_db(db, cache, base, *cache_capacity)?;
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

	/// Load a batch of blocks from the backend database into `cache`, starting from `base` and up
	/// to `base + cache_capacity`
	fn load_batch_from_db(
		db: &D,
		cache: &mut VecDeque<DeathRow<BlockHash, Key>>,
		base: u64,
		cache_capacity: usize,
	) -> Result<(), Error<D::Error>> {
		let start = base + cache.len() as u64;
		let batch_size = cache_capacity;
		for i in 0..batch_size as u64 {
			match load_death_row_from_db::<BlockHash, Key, D>(db, start + i)? {
				Some(row) => {
					cache.push_back(row);
				},
				None => break,
			}
		}
		Ok(())
	}

	/// Check if the block at the given `index` of the queue exist
	/// it is the caller's responsibility to ensure `index` won't be out of bounds
	fn have_block(&self, hash: &BlockHash, index: usize) -> HaveBlock {
		match self {
			DeathRowQueue::DbBacked { cache, .. } => {
				if cache.len() > index {
					(cache[index].hash == *hash).into()
				} else {
					// The block is not in the cache but it still may exist on disk.
					HaveBlock::Maybe
				}
			},
			DeathRowQueue::Mem { death_rows, .. } => (death_rows[index].hash == *hash).into(),
		}
	}

	/// Return the number of block in the pruning window
	fn len(&self, base: u64) -> u64 {
		match self {
			DeathRowQueue::DbBacked { last, .. } => last.map_or(0, |l| l + 1 - base),
			DeathRowQueue::Mem { death_rows, .. } => death_rows.len() as u64,
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
	fn get_db_backed_queue_state(
		&self,
	) -> Option<(&VecDeque<DeathRow<BlockHash, Key>>, Option<u64>)> {
		match self {
			DeathRowQueue::DbBacked { cache, last, .. } => Some((cache, *last)),
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

#[derive(Encode, Decode, Default)]
struct JournalRecord<BlockHash: Hash, Key: Hash> {
	hash: BlockHash,
	inserted: Vec<Key>,
	deleted: Vec<Key>,
}

fn to_journal_key(block: u64) -> Vec<u8> {
	to_meta_key(PRUNING_JOURNAL, &block)
}

/// The result return by `RefWindow::have_block`
#[derive(Debug, PartialEq, Eq)]
pub enum HaveBlock {
	/// Definitely don't have this block.
	No,
	/// May or may not have this block, need further checking
	Maybe,
	/// Definitely has this block
	Yes,
}

impl From<bool> for HaveBlock {
	fn from(have: bool) -> Self {
		if have {
			HaveBlock::Yes
		} else {
			HaveBlock::No
		}
	}
}

impl<BlockHash: Hash, Key: Hash, D: MetaDb> RefWindow<BlockHash, Key, D> {
	pub fn new(
		db: D,
		window_size: u32,
		count_insertions: bool,
	) -> Result<RefWindow<BlockHash, Key, D>, Error<D::Error>> {
		// the block number of the first block in the queue or the next block number if the queue is
		// empty
		let base = match db.get_meta(&to_meta_key(LAST_PRUNED, &())).map_err(Error::Db)? {
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
			DeathRowQueue::new_mem(&db, base)?
		} else {
			let last = match last_canonicalized_number {
				Some(last_canonicalized_number) => {
					debug_assert!(last_canonicalized_number + 1 >= base);
					Some(last_canonicalized_number)
				},
				// None means `LAST_CANONICAL` is never been wrote, since the pruning journals are
				// in the same `CommitSet` as `LAST_CANONICAL`, it means no pruning journal have
				// ever been committed to the db, thus set `unload` to zero
				None => None,
			};
			DeathRowQueue::new_db_backed(db, base, last, window_size)?
		};

		Ok(RefWindow { queue, base })
	}

	pub fn window_size(&self) -> u64 {
		self.queue.len(self.base) as u64
	}

	/// Get the hash of the next pruning block
	pub fn next_hash(&mut self) -> Result<Option<BlockHash>, Error<D::Error>> {
		let res = match &mut self.queue {
			DeathRowQueue::DbBacked { db, cache, cache_capacity, .. } => {
				if cache.is_empty() {
					DeathRowQueue::load_batch_from_db(db, cache, self.base, *cache_capacity)?;
				}
				cache.front().map(|r| r.hash.clone())
			},
			DeathRowQueue::Mem { death_rows, .. } => death_rows.front().map(|r| r.hash.clone()),
		};
		Ok(res)
	}

	pub fn mem_used(&self) -> usize {
		0
	}

	fn is_empty(&self) -> bool {
		self.window_size() == 0
	}

	// Check if a block is in the pruning window and not be pruned yet
	pub fn have_block(&self, hash: &BlockHash, number: u64) -> HaveBlock {
		// if the queue is empty or the block number exceed the pruning window, we definitely
		// do not have this block
		if self.is_empty() || number < self.base || number >= self.base + self.window_size() {
			return HaveBlock::No
		}
		self.queue.have_block(hash, (number - self.base) as usize)
	}

	/// Prune next block. Expects at least one block in the window. Adds changes to `commit`.
	pub fn prune_one(&mut self, commit: &mut CommitSet<Key>) -> Result<(), Error<D::Error>> {
		if let Some(pruned) = self.queue.pop_front(self.base)? {
			trace!(target: "state-db", "Pruning {:?} ({} deleted)", pruned.hash, pruned.deleted.len());
			let index = self.base;
			commit.data.deleted.extend(pruned.deleted.into_iter());
			commit.meta.inserted.push((to_meta_key(LAST_PRUNED, &()), index.encode()));
			commit.meta.deleted.push(to_journal_key(self.base));
			self.base += 1;
			Ok(())
		} else {
			trace!(target: "state-db", "Trying to prune when there's nothing to prune");
			Err(Error::StateDb(StateDbError::BlockUnavailable))
		}
	}

	/// Add a change set to the window. Creates a journal record and pushes it to `commit`
	pub fn note_canonical(
		&mut self,
		hash: &BlockHash,
		number: u64,
		commit: &mut CommitSet<Key>,
	) -> Result<(), Error<D::Error>> {
		if self.base == 0 && self.is_empty() && number > 0 {
			// assume that parent was canonicalized
			self.base = number;
		} else if (self.base + self.window_size()) != number {
			return Err(Error::StateDb(StateDbError::InvalidBlockNumber))
		}
		trace!(target: "state-db", "Adding to pruning window: {:?} ({} inserted, {} deleted)", hash, commit.data.inserted.len(), commit.data.deleted.len());
		let inserted = if matches!(self.queue, DeathRowQueue::Mem { .. }) {
			commit.data.inserted.iter().map(|(k, _)| k.clone()).collect()
		} else {
			Default::default()
		};
		let deleted = std::mem::take(&mut commit.data.deleted);
		let journal_record = JournalRecord { hash: hash.clone(), inserted, deleted };
		commit.meta.inserted.push((to_journal_key(number), journal_record.encode()));
		self.queue.import(self.base, number, journal_record);
		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use super::{to_journal_key, DeathRowQueue, HaveBlock, JournalRecord, RefWindow, LAST_PRUNED};
	use crate::{
		noncanonical::LAST_CANONICAL,
		test::{make_commit, make_db, TestDb},
		to_meta_key, CommitSet, Error, Hash, StateDbError, DEFAULT_MAX_BLOCK_CONSTRAINT,
	};
	use codec::Encode;
	use sp_core::H256;

	fn check_journal(pruning: &RefWindow<H256, H256, TestDb>, db: &TestDb) {
		let count_insertions = matches!(pruning.queue, DeathRowQueue::Mem { .. });
		let restored: RefWindow<H256, H256, TestDb> =
			RefWindow::new(db.clone(), DEFAULT_MAX_BLOCK_CONSTRAINT, count_insertions).unwrap();
		assert_eq!(pruning.base, restored.base);
		assert_eq!(pruning.queue.get_mem_queue_state(), restored.queue.get_mem_queue_state());
	}

	#[test]
	fn created_from_empty_db() {
		let db = make_db(&[]);
		let pruning: RefWindow<H256, H256, TestDb> =
			RefWindow::new(db, DEFAULT_MAX_BLOCK_CONSTRAINT, true).unwrap();
		assert_eq!(pruning.base, 0);
		let (death_rows, death_index) = pruning.queue.get_mem_queue_state().unwrap();
		assert!(death_rows.is_empty());
		assert!(death_index.is_empty());
	}

	#[test]
	fn prune_empty() {
		let db = make_db(&[]);
		let mut pruning: RefWindow<H256, H256, TestDb> =
			RefWindow::new(db, DEFAULT_MAX_BLOCK_CONSTRAINT, true).unwrap();
		let mut commit = CommitSet::default();
		assert_eq!(
			Err(Error::StateDb(StateDbError::BlockUnavailable)),
			pruning.prune_one(&mut commit)
		);
		assert_eq!(pruning.base, 0);
		let (death_rows, death_index) = pruning.queue.get_mem_queue_state().unwrap();
		assert!(death_rows.is_empty());
		assert!(death_index.is_empty());
	}

	#[test]
	fn prune_one() {
		let mut db = make_db(&[1, 2, 3]);
		let mut pruning: RefWindow<H256, H256, TestDb> =
			RefWindow::new(db.clone(), DEFAULT_MAX_BLOCK_CONSTRAINT, true).unwrap();
		let mut commit = make_commit(&[4, 5], &[1, 3]);
		let hash = H256::random();
		pruning.note_canonical(&hash, 0, &mut commit).unwrap();
		db.commit(&commit);
		assert_eq!(pruning.have_block(&hash, 0), HaveBlock::Yes);
		assert_eq!(pruning.have_block(&hash, 0), HaveBlock::Yes);
		assert!(commit.data.deleted.is_empty());
		let (death_rows, death_index) = pruning.queue.get_mem_queue_state().unwrap();
		assert_eq!(death_rows.len(), 1);
		assert_eq!(death_index.len(), 2);
		assert!(db.data_eq(&make_db(&[1, 2, 3, 4, 5])));
		check_journal(&pruning, &db);

		let mut commit = CommitSet::default();
		pruning.prune_one(&mut commit).unwrap();
		assert_eq!(pruning.have_block(&hash, 0), HaveBlock::No);
		db.commit(&commit);
		assert_eq!(pruning.have_block(&hash, 0), HaveBlock::No);
		assert!(db.data_eq(&make_db(&[2, 4, 5])));
		let (death_rows, death_index) = pruning.queue.get_mem_queue_state().unwrap();
		assert!(death_rows.is_empty());
		assert!(death_index.is_empty());
		assert_eq!(pruning.base, 1);
	}

	#[test]
	fn prune_two() {
		let mut db = make_db(&[1, 2, 3]);
		let mut pruning: RefWindow<H256, H256, TestDb> =
			RefWindow::new(db.clone(), DEFAULT_MAX_BLOCK_CONSTRAINT, true).unwrap();
		let mut commit = make_commit(&[4], &[1]);
		pruning.note_canonical(&H256::random(), 0, &mut commit).unwrap();
		db.commit(&commit);
		let mut commit = make_commit(&[5], &[2]);
		pruning.note_canonical(&H256::random(), 1, &mut commit).unwrap();
		db.commit(&commit);
		assert!(db.data_eq(&make_db(&[1, 2, 3, 4, 5])));

		check_journal(&pruning, &db);

		let mut commit = CommitSet::default();
		pruning.prune_one(&mut commit).unwrap();
		db.commit(&commit);
		assert!(db.data_eq(&make_db(&[2, 3, 4, 5])));
		let mut commit = CommitSet::default();
		pruning.prune_one(&mut commit).unwrap();
		db.commit(&commit);
		assert!(db.data_eq(&make_db(&[3, 4, 5])));
		assert_eq!(pruning.base, 2);
	}

	#[test]
	fn prune_two_pending() {
		let mut db = make_db(&[1, 2, 3]);
		let mut pruning: RefWindow<H256, H256, TestDb> =
			RefWindow::new(db.clone(), DEFAULT_MAX_BLOCK_CONSTRAINT, true).unwrap();
		let mut commit = make_commit(&[4], &[1]);
		pruning.note_canonical(&H256::random(), 0, &mut commit).unwrap();
		db.commit(&commit);
		let mut commit = make_commit(&[5], &[2]);
		pruning.note_canonical(&H256::random(), 1, &mut commit).unwrap();
		db.commit(&commit);
		assert!(db.data_eq(&make_db(&[1, 2, 3, 4, 5])));
		let mut commit = CommitSet::default();
		pruning.prune_one(&mut commit).unwrap();
		db.commit(&commit);
		assert!(db.data_eq(&make_db(&[2, 3, 4, 5])));
		let mut commit = CommitSet::default();
		pruning.prune_one(&mut commit).unwrap();
		db.commit(&commit);
		assert!(db.data_eq(&make_db(&[3, 4, 5])));
		assert_eq!(pruning.base, 2);
	}

	#[test]
	fn reinserted_survives() {
		let mut db = make_db(&[1, 2, 3]);
		let mut pruning: RefWindow<H256, H256, TestDb> =
			RefWindow::new(db.clone(), DEFAULT_MAX_BLOCK_CONSTRAINT, true).unwrap();
		let mut commit = make_commit(&[], &[2]);
		pruning.note_canonical(&H256::random(), 0, &mut commit).unwrap();
		db.commit(&commit);
		let mut commit = make_commit(&[2], &[]);
		pruning.note_canonical(&H256::random(), 1, &mut commit).unwrap();
		db.commit(&commit);
		let mut commit = make_commit(&[], &[2]);
		pruning.note_canonical(&H256::random(), 2, &mut commit).unwrap();
		db.commit(&commit);
		assert!(db.data_eq(&make_db(&[1, 2, 3])));

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
		assert_eq!(pruning.base, 3);
	}

	#[test]
	fn reinserted_survive_pending() {
		let mut db = make_db(&[1, 2, 3]);
		let mut pruning: RefWindow<H256, H256, TestDb> =
			RefWindow::new(db.clone(), DEFAULT_MAX_BLOCK_CONSTRAINT, true).unwrap();
		let mut commit = make_commit(&[], &[2]);
		pruning.note_canonical(&H256::random(), 0, &mut commit).unwrap();
		db.commit(&commit);
		let mut commit = make_commit(&[2], &[]);
		pruning.note_canonical(&H256::random(), 1, &mut commit).unwrap();
		db.commit(&commit);
		let mut commit = make_commit(&[], &[2]);
		pruning.note_canonical(&H256::random(), 2, &mut commit).unwrap();
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
		assert_eq!(pruning.base, 3);
	}

	#[test]
	fn reinserted_ignores() {
		let mut db = make_db(&[1, 2, 3]);
		let mut pruning: RefWindow<H256, H256, TestDb> =
			RefWindow::new(db.clone(), DEFAULT_MAX_BLOCK_CONSTRAINT, false).unwrap();
		let mut commit = make_commit(&[], &[2]);
		pruning.note_canonical(&H256::random(), 0, &mut commit).unwrap();
		db.commit(&commit);
		let mut commit = make_commit(&[2], &[]);
		pruning.note_canonical(&H256::random(), 1, &mut commit).unwrap();
		db.commit(&commit);
		let mut commit = make_commit(&[], &[2]);
		pruning.note_canonical(&H256::random(), 2, &mut commit).unwrap();
		db.commit(&commit);
		assert!(db.data_eq(&make_db(&[1, 2, 3])));

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

	fn push_last_pruned<H: Hash>(block: u64, commit: &mut CommitSet<H>) {
		commit.meta.inserted.push((to_meta_key(LAST_PRUNED, &()), block.encode()));
	}

	#[test]
	fn init_db_backed_queue() {
		let mut db = make_db(&[]);
		let mut commit = CommitSet::default();

		fn load_pruning_from_db(db: TestDb) -> (usize, u64) {
			let pruning: RefWindow<u64, H256, TestDb> =
				RefWindow::new(db, DEFAULT_MAX_BLOCK_CONSTRAINT, false).unwrap();
			let (cache, _) = pruning.queue.get_db_backed_queue_state().unwrap();
			(cache.len(), pruning.base)
		}

		fn push_record(block: u64, commit: &mut CommitSet<H256>) {
			commit
				.meta
				.inserted
				.push((to_journal_key(block), JournalRecord::<u64, H256>::default().encode()));
		}

		// empty database
		let (loaded_blocks, base) = load_pruning_from_db(db.clone());
		assert_eq!(loaded_blocks, 0);
		assert_eq!(base, 0);

		// canonicalized the genesis block but no pruning
		push_last_canonicalized(0, &mut commit);
		push_record(0, &mut commit);
		db.commit(&commit);
		let (loaded_blocks, base) = load_pruning_from_db(db.clone());
		assert_eq!(loaded_blocks, 1);
		assert_eq!(base, 0);

		// pruned the genesis block
		push_last_pruned(0, &mut commit);
		db.commit(&commit);
		let (loaded_blocks, base) = load_pruning_from_db(db.clone());
		assert_eq!(loaded_blocks, 0);
		assert_eq!(base, 1);

		// canonicalize more blocks
		push_last_canonicalized(10, &mut commit);
		for i in 1..=10 {
			push_record(i, &mut commit);
		}
		db.commit(&commit);
		let (loaded_blocks, base) = load_pruning_from_db(db.clone());
		assert_eq!(loaded_blocks, 10);
		assert_eq!(base, 1);

		// pruned all blocks
		push_last_pruned(10, &mut commit);
		db.commit(&commit);
		let (loaded_blocks, base) = load_pruning_from_db(db.clone());
		assert_eq!(loaded_blocks, 0);
		assert_eq!(base, 11);
	}

	#[test]
	fn db_backed_queue() {
		let mut db = make_db(&[]);
		let mut pruning: RefWindow<u64, H256, TestDb> =
			RefWindow::new(db.clone(), DEFAULT_MAX_BLOCK_CONSTRAINT, false).unwrap();
		let cache_capacity = DEFAULT_MAX_BLOCK_CONSTRAINT as usize;

		// start as an empty queue
		let (cache, last) = pruning.queue.get_db_backed_queue_state().unwrap();
		assert_eq!(cache.len(), 0);
		assert_eq!(last, None);

		// import blocks
		// queue size and content should match
		for i in 0..(cache_capacity + 10) {
			let mut commit = make_commit(&[], &[]);
			pruning.note_canonical(&(i as u64), i as u64, &mut commit).unwrap();
			push_last_canonicalized(i as u64, &mut commit);
			db.commit(&commit);
			// blocks will fill the cache first
			let (cache, last) = pruning.queue.get_db_backed_queue_state().unwrap();
			if i < cache_capacity {
				assert_eq!(cache.len(), i + 1);
			} else {
				assert_eq!(cache.len(), cache_capacity);
			}
			assert_eq!(last, Some(i as u64));
		}
		assert_eq!(pruning.window_size(), cache_capacity as u64 + 10);
		let (cache, last) = pruning.queue.get_db_backed_queue_state().unwrap();
		assert_eq!(cache.len(), cache_capacity);
		assert_eq!(last, Some(cache_capacity as u64 + 10 - 1));
		for i in 0..cache_capacity {
			assert_eq!(cache[i].hash, i as u64);
		}

		// import a new block to the end of the queue
		// won't keep the new block in memory
		let mut commit = CommitSet::default();
		pruning
			.note_canonical(&(cache_capacity as u64 + 10), cache_capacity as u64 + 10, &mut commit)
			.unwrap();
		assert_eq!(pruning.window_size(), cache_capacity as u64 + 11);
		let (cache, _) = pruning.queue.get_db_backed_queue_state().unwrap();
		assert_eq!(cache.len(), cache_capacity);

		// revert the last add that no apply yet
		// NOTE: do not commit the previous `CommitSet` to db
		pruning = RefWindow::new(db.clone(), DEFAULT_MAX_BLOCK_CONSTRAINT, false).unwrap();
		let cache_capacity = DEFAULT_MAX_BLOCK_CONSTRAINT as usize;
		assert_eq!(pruning.window_size(), cache_capacity as u64 + 10);
		let (cache, _) = pruning.queue.get_db_backed_queue_state().unwrap();
		assert_eq!(cache.len(), cache_capacity);

		// remove one block from the start of the queue
		// block is removed from the head of cache
		let mut commit = CommitSet::default();
		pruning.prune_one(&mut commit).unwrap();
		db.commit(&commit);
		assert_eq!(pruning.window_size(), cache_capacity as u64 + 9);
		let (cache, _) = pruning.queue.get_db_backed_queue_state().unwrap();
		assert_eq!(cache.len(), cache_capacity - 1);
		for i in 0..(cache_capacity - 1) {
			assert_eq!(cache[i].hash, (i + 1) as u64);
		}

		// load a new queue from db
		// `cache` is full again but the content of the queue should be the same
		let pruning: RefWindow<u64, H256, TestDb> =
			RefWindow::new(db, DEFAULT_MAX_BLOCK_CONSTRAINT, false).unwrap();
		assert_eq!(pruning.window_size(), cache_capacity as u64 + 9);
		let (cache, _) = pruning.queue.get_db_backed_queue_state().unwrap();
		assert_eq!(cache.len(), cache_capacity);
		for i in 0..cache_capacity {
			assert_eq!(cache[i].hash, (i + 1) as u64);
		}
	}

	#[test]
	fn load_block_from_db() {
		let mut db = make_db(&[]);
		let mut pruning: RefWindow<u64, H256, TestDb> =
			RefWindow::new(db.clone(), DEFAULT_MAX_BLOCK_CONSTRAINT, false).unwrap();
		let cache_capacity = DEFAULT_MAX_BLOCK_CONSTRAINT as usize;

		// import blocks
		for i in 0..(cache_capacity as u64 * 2 + 10) {
			let mut commit = make_commit(&[], &[]);
			pruning.note_canonical(&i, i, &mut commit).unwrap();
			push_last_canonicalized(i as u64, &mut commit);
			db.commit(&commit);
		}

		// the following operations won't trigger loading block from db:
		// - getting block in cache
		// - getting block not in the queue
		assert_eq!(pruning.next_hash().unwrap().unwrap(), 0);
		let (cache, last) = pruning.queue.get_db_backed_queue_state().unwrap();
		assert_eq!(cache.len(), cache_capacity);
		assert_eq!(last, Some(cache_capacity as u64 * 2 + 10 - 1));

		// clear all block loaded in cache
		for _ in 0..cache_capacity * 2 {
			let mut commit = CommitSet::default();
			pruning.prune_one(&mut commit).unwrap();
			db.commit(&commit);
		}
		let (cache, _) = pruning.queue.get_db_backed_queue_state().unwrap();
		assert!(cache.is_empty());

		// getting the hash of block that not in cache will also trigger loading
		// the remaining blocks from db
		assert_eq!(pruning.next_hash().unwrap().unwrap(), (cache_capacity * 2) as u64);
		let (cache, _) = pruning.queue.get_db_backed_queue_state().unwrap();
		assert_eq!(cache.len(), 10);

		// load a new queue from db
		// `cache` should be the same
		let pruning: RefWindow<u64, H256, TestDb> =
			RefWindow::new(db, DEFAULT_MAX_BLOCK_CONSTRAINT, false).unwrap();
		assert_eq!(pruning.window_size(), 10);
		let (cache, _) = pruning.queue.get_db_backed_queue_state().unwrap();
		assert_eq!(cache.len(), 10);
		for i in 0..10 {
			assert_eq!(cache[i].hash, (cache_capacity * 2 + i) as u64);
		}
	}

	#[test]
	fn get_block_from_queue() {
		let mut db = make_db(&[]);
		let mut pruning: RefWindow<u64, H256, TestDb> =
			RefWindow::new(db.clone(), DEFAULT_MAX_BLOCK_CONSTRAINT, false).unwrap();
		let cache_capacity = DEFAULT_MAX_BLOCK_CONSTRAINT as u64;

		// import blocks and commit to db
		let mut commit = make_commit(&[], &[]);
		for i in 0..(cache_capacity + 10) {
			pruning.note_canonical(&i, i, &mut commit).unwrap();
		}
		db.commit(&commit);

		// import a block but not commit to db yet
		let mut pending_commit = make_commit(&[], &[]);
		let index = cache_capacity + 10;
		pruning.note_canonical(&index, index, &mut pending_commit).unwrap();

		let mut commit = make_commit(&[], &[]);
		// prune blocks that had committed to db
		for i in 0..(cache_capacity + 10) {
			assert_eq!(pruning.next_hash().unwrap(), Some(i));
			pruning.prune_one(&mut commit).unwrap();
		}
		// return `None` for block that did not commit to db
		assert_eq!(pruning.next_hash().unwrap(), None);
		assert_eq!(
			pruning.prune_one(&mut commit).unwrap_err(),
			Error::StateDb(StateDbError::BlockUnavailable)
		);
		// commit block to db and no error return
		db.commit(&pending_commit);
		assert_eq!(pruning.next_hash().unwrap(), Some(index));
		pruning.prune_one(&mut commit).unwrap();
		db.commit(&commit);
	}
}
