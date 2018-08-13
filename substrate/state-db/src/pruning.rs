// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! Pruning window.
//!
//! For each block we maintain a list of nodes pending deletion.
//! There is also a global index of node key to block number.
//! If a node is re-inserted into the window it gets removed from
//! the death list.
//! The changes are journaled in the DB.

use std::collections::{HashMap, HashSet, VecDeque};
use codec::{Encode, Decode};
use {CommitSet, Error, MetaDb, to_meta_key, Hash};

const LAST_PRUNED: &[u8] = b"last_pruned";
const PRUNING_JOURNAL: &[u8] = b"pruning_journal";

/// See module documentation.
pub struct RefWindow<BlockHash: Hash, Key: Hash> {
	death_rows: VecDeque<DeathRow<BlockHash, Key>>,
	death_index: HashMap<Key, u64>,
	pending_number: u64,
}

#[derive(Debug, PartialEq, Eq)]
struct DeathRow<BlockHash: Hash, Key: Hash> {
	hash: BlockHash,
	journal_key: Vec<u8>,
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

impl<BlockHash: Hash, Key: Hash> RefWindow<BlockHash, Key> {
	pub fn new<D: MetaDb>(db: &D) -> Result<RefWindow<BlockHash, Key>, Error<D::Error>> {
		let last_pruned = db.get_meta(&to_meta_key(LAST_PRUNED, &()))
			.map_err(|e| Error::Db(e))?;
		let pending_number: u64 = match last_pruned {
			Some(buffer) => u64::decode(&mut buffer.as_slice()).ok_or(Error::Decoding)? + 1,
			None => 1,
		};
		let mut block = pending_number;
		let mut pruning = RefWindow {
			death_rows: Default::default(),
			death_index: Default::default(),
			pending_number: pending_number,
		};
		// read the journal
		trace!(target: "state-db", "Reading pruning journal. Last pruned #{}", pending_number - 1);
		loop {
			let journal_key = to_journal_key(block);
			match db.get_meta(&journal_key).map_err(|e| Error::Db(e))? {
				Some(record) => {
					let record: JournalRecord<BlockHash, Key> = Decode::decode(&mut record.as_slice()).ok_or(Error::Decoding)?;
					trace!(target: "state-db", "Pruning journal entry {} ({} inserted, {} deleted)", block, record.inserted.len(), record.deleted.len());
					pruning.import(&record.hash, journal_key, record.inserted.into_iter(), record.deleted);
				},
				None => break,
			}
			block += 1;
		}
		Ok(pruning)
	}

	fn import<I: IntoIterator<Item=Key>>(&mut self, hash: &BlockHash, journal_key: Vec<u8>, inserted: I, deleted: Vec<Key>) {
		// remove all re-inserted keys from death rows
		for k in inserted {
			if let Some(block) = self.death_index.remove(&k) {
				self.death_rows[(block - self.pending_number) as usize].deleted.remove(&k);
			}
		}

		// add new keys
		let imported_block = self.pending_number + self.death_rows.len() as u64;
		for k in deleted.iter() {
			self.death_index.insert(k.clone(), imported_block);
		}
		self.death_rows.push_back(
			DeathRow {
				hash: hash.clone(),
				deleted: deleted.into_iter().collect(),
				journal_key: journal_key,
			}
		);
	}

	pub fn window_size(&self) -> u64 {
		self.death_rows.len() as u64
	}

	pub fn next_hash(&self) -> Option<BlockHash> {
		self.death_rows.front().map(|r| r.hash.clone())
	}

	pub fn mem_used(&self) -> usize {
		0
	}

	/// Prune next block. Expects at least one block in the window. Adds changes to `commit`.
	pub fn prune_one(&mut self, commit: &mut CommitSet<Key>) {
		let pruned = self.death_rows.pop_front().expect("prune_one is only called with a non-empty window");
		trace!(target: "state-db", "Pruning {:?} ({} deleted)", pruned.hash, pruned.deleted.len());
		for k in pruned.deleted.iter() {
			self.death_index.remove(&k);
		}
		commit.data.deleted.extend(pruned.deleted.into_iter());
		commit.meta.inserted.push((to_meta_key(LAST_PRUNED, &()), self.pending_number.encode()));
		commit.meta.deleted.push(pruned.journal_key);
		self.pending_number += 1;
	}

	/// Add a change set to the window. Creates a journal record and pushes it to `commit`
	pub fn note_finalized(&mut self, hash: &BlockHash, commit: &mut CommitSet<Key>) {
		trace!(target: "state-db", "Adding to pruning window: {:?} ({} inserted, {} deleted)", hash, commit.data.inserted.len(), commit.data.deleted.len());
		let inserted = commit.data.inserted.iter().map(|(k, _)| k.clone()).collect();
		let deleted = ::std::mem::replace(&mut commit.data.deleted, Vec::new());
		let journal_record = JournalRecord {
			hash: hash.clone(),
			inserted,
			deleted,
		};
		let block = self.pending_number + self.window_size();
		let journal_key = to_journal_key(block);
		commit.meta.inserted.push((journal_key.clone(), journal_record.encode()));

		self.import(hash, journal_key, journal_record.inserted.into_iter(), journal_record.deleted);
	}
}

#[cfg(test)]
mod tests {
	use super::RefWindow;
	use primitives::H256;
	use {CommitSet};
	use test::{make_db, make_commit, TestDb};

	fn check_journal(pruning: &RefWindow<H256, H256>, db: &TestDb) {
		let restored: RefWindow<H256, H256> = RefWindow::new(db).unwrap();
		assert_eq!(pruning.pending_number, restored.pending_number);
		assert_eq!(pruning.death_rows, restored.death_rows);
		assert_eq!(pruning.death_index, restored.death_index);
	}

	#[test]
	fn created_from_empty_db() {
		let db = make_db(&[]);
		let pruning: RefWindow<H256, H256> = RefWindow::new(&db).unwrap();
		assert_eq!(pruning.pending_number, 1);
		assert!(pruning.death_rows.is_empty());
		assert!(pruning.death_index.is_empty());
	}

	#[test]
	#[should_panic]
	fn prune_empty_panics() {
		let db = make_db(&[]);
		let mut pruning: RefWindow<H256, H256> = RefWindow::new(&db).unwrap();
		let mut commit = CommitSet::default();
		pruning.prune_one(&mut commit);
	}

	#[test]
	fn prune_one() {
		let mut db = make_db(&[1, 2, 3]);
		let mut pruning: RefWindow<H256, H256> = RefWindow::new(&db).unwrap();
		let mut commit = make_commit(&[4, 5], &[1, 3]);
		let h = H256::random();
		pruning.note_finalized(&h, &mut commit);
		db.commit(&commit);
		assert!(commit.data.deleted.is_empty());
		assert_eq!(pruning.death_rows.len(), 1);
		assert_eq!(pruning.death_index.len(), 2);
		assert!(db.data_eq(&make_db(&[1, 2, 3, 4, 5])));
		check_journal(&pruning, &db);

		let mut commit = CommitSet::default();
		pruning.prune_one(&mut commit);
		db.commit(&commit);
		assert!(db.data_eq(&make_db(&[2, 4, 5])));
		assert!(pruning.death_rows.is_empty());
		assert!(pruning.death_index.is_empty());
		assert_eq!(pruning.pending_number, 2);
	}

	#[test]
	fn prune_two() {
		let mut db = make_db(&[1, 2, 3]);
		let mut pruning: RefWindow<H256, H256> = RefWindow::new(&db).unwrap();
		let mut commit = make_commit(&[4], &[1]);
		pruning.note_finalized(&H256::random(), &mut commit);
		db.commit(&commit);
		let mut commit = make_commit(&[5], &[2]);
		pruning.note_finalized(&H256::random(), &mut commit);
		db.commit(&commit);
		assert!(db.data_eq(&make_db(&[1, 2, 3, 4, 5])));

		check_journal(&pruning, &db);

		let mut commit = CommitSet::default();
		pruning.prune_one(&mut commit);
		db.commit(&commit);
		assert!(db.data_eq(&make_db(&[2, 3, 4, 5])));
		let mut commit = CommitSet::default();
		pruning.prune_one(&mut commit);
		db.commit(&commit);
		assert!(db.data_eq(&make_db(&[3, 4, 5])));
		assert_eq!(pruning.pending_number, 3);
	}

	#[test]
	fn reinserted_survives() {
		let mut db = make_db(&[1, 2, 3]);
		let mut pruning: RefWindow<H256, H256> = RefWindow::new(&db).unwrap();
		let mut commit = make_commit(&[], &[2]);
		pruning.note_finalized(&H256::random(), &mut commit);
		db.commit(&commit);
		let mut commit = make_commit(&[2], &[]);
		pruning.note_finalized(&H256::random(), &mut commit);
		db.commit(&commit);
		let mut commit = make_commit(&[], &[2]);
		pruning.note_finalized(&H256::random(), &mut commit);
		db.commit(&commit);
		assert!(db.data_eq(&make_db(&[1, 2, 3])));

		check_journal(&pruning, &db);

		let mut commit = CommitSet::default();
		pruning.prune_one(&mut commit);
		db.commit(&commit);
		assert!(db.data_eq(&make_db(&[1, 2, 3])));
		let mut commit = CommitSet::default();
		pruning.prune_one(&mut commit);
		db.commit(&commit);
		assert!(db.data_eq(&make_db(&[1, 2, 3])));
		pruning.prune_one(&mut commit);
		db.commit(&commit);
		assert!(db.data_eq(&make_db(&[1, 3])));
		assert_eq!(pruning.pending_number, 4);
	}
}
