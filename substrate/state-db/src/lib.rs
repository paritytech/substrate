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

extern crate substrate_codec as codec;
extern crate substrate_primitives as primitives;

mod unfinalized;
mod pruning;
#[cfg(test)] mod test;

use primitives::{H256, blake2_256};
use codec::Slicable;
use std::collections::HashSet;
use unfinalized::UnfinalizedOverlay;
use pruning::RefWindow;

pub type DBValue = Vec<u8>;

pub trait KeyValueDb {
	type Error;

	fn get(&self, key: &H256) -> Result<Option<DBValue>, Self::Error>;
	fn get_meta(&self, key: &H256) -> Result<Option<DBValue>, Self::Error>;
}

#[derive(Debug)]
pub enum Error<D: KeyValueDb> {
	Db(D::Error),
	Decoding,
}

#[derive(Default, Debug, Clone)]
pub struct ChangeSet {
	inserted: Vec<(H256, DBValue)>,
	deleted: Vec<H256>,
}


#[derive(Default, Debug, Clone)]
pub struct CommitSet {
	data: ChangeSet,
	meta: ChangeSet,
}

/// Pruning contraints. If none are specified pruning is
#[derive(Default, Debug)]
pub struct Constraints {
	max_blocks: Option<u32>,
	max_mem: Option<usize>,
}

pub enum Pruning {
	Constrained(Constraints),
	ArchiveAll,
	ArchiveCanonical,
}

fn to_key<S: Slicable>(prefix: &[u8], data: &S) -> H256 {
	let mut buffer = data.encode();
	buffer.extend(prefix);
	blake2_256(&buffer).into()
}

pub struct StateDb {
	mode: Pruning,
	unfinalized: UnfinalizedOverlay,
	pruning: Option<RefWindow>,
	pinned: HashSet<H256>,
}

impl StateDb {
	pub fn new<D: KeyValueDb>(mode: Pruning, db: &D) -> Result<StateDb, Error<D>> {
		let unfinalized = UnfinalizedOverlay::new(db)?;
		let pruning = match mode {
			Pruning::Constrained(_) => Some(RefWindow::new(db)?),
			Pruning::ArchiveAll | Pruning::ArchiveCanonical => None,
		};
		Ok(StateDb {
			mode,
			unfinalized,
			pruning: pruning,
			pinned: Default::default(),
		})
	}

	pub fn insert_block(&mut self, hash: &H256, number: u64, parent_hash: &H256, mut changeset: ChangeSet) -> CommitSet {
		match self.mode {
			Pruning::ArchiveAll => {
				changeset.deleted.clear();
				// write changes immediatelly
				CommitSet {
					data: changeset,
					meta: Default::default(),
				}
			},
			Pruning::Constrained(_) | Pruning::ArchiveCanonical => {
				self.unfinalized.insert(hash, number, parent_hash, changeset)
			}
		}
	}

	pub fn finalize_block(&mut self, hash: &H256) -> CommitSet {
		let mut commit = match self.mode {
			Pruning::ArchiveAll => {
				CommitSet::default()
			},
			Pruning::ArchiveCanonical => {
				let mut commit = self.unfinalized.finalize(hash);
				commit.data.deleted.clear();
				commit
			},
			Pruning::Constrained(_) => {
				self.unfinalized.finalize(hash)
			},
		};
		if let Some(ref mut pruning) = self.pruning {
			pruning.note_finalized(hash, &mut commit);
		}
		self.prune(&mut commit);
		commit
	}

	fn prune(&mut self, commit: &mut CommitSet) {
		if let (&mut Some(ref mut pruning), &Pruning::Constrained(ref constraints)) = (&mut self.pruning, &self.mode) {
			loop {
				if pruning.window_size() <= constraints.max_blocks.unwrap_or(0) as u64 {
					break;
				}

				if constraints.max_mem.map_or(false, |m| pruning.mem_used() > m) {
					break;
				}

				let pinned = &self.pinned;
				if pruning.next_hash().map_or(false, |h| pinned.contains(&h)) {
					break;
				}

				pruning.prune_one(commit);
			}
		}
	}

	pub fn pin(&mut self, hash: &H256) {
		self.pinned.insert(*hash);
	}

	pub fn unpin(&mut self, hash: &H256) {
		self.pinned.remove(hash);
	}

	pub fn get<D: KeyValueDb>(&self, key: &H256, db: &D) -> Result<Option<DBValue>, Error<D>> {
		if let Some(value) = self.unfinalized.get(key) {
			return Ok(Some(value));
		}
		db.get(key).map_err(|e| Error::Db(e))
	}
}

#[cfg(test)]
mod tests {
	use primitives::H256;
	use {StateDb, Pruning, Constraints};
	use test::{make_db, make_changeset, TestDb};

	fn make_test_db(settings: Pruning) -> (TestDb, StateDb) {
		let mut db = make_db(&[91, 921, 922, 93]);
		let mut state_db = StateDb::new(settings, &db).unwrap();

		db.commit(&state_db.insert_block(&H256::from(1), 1, &H256::from(0), make_changeset(&[1], &[91])));
		db.commit(&state_db.insert_block(&H256::from(21), 2, &H256::from(1), make_changeset(&[21], &[921, 1])));
		db.commit(&state_db.insert_block(&H256::from(22), 2, &H256::from(1), make_changeset(&[22], &[922])));
		db.commit(&state_db.insert_block(&H256::from(3), 3, &H256::from(21), make_changeset(&[3], &[922])));
		db.commit(&state_db.finalize_block(&H256::from(1)));
		db.commit(&state_db.insert_block(&H256::from(4), 4, &H256::from(3), make_changeset(&[4], &[93])));
		db.commit(&state_db.finalize_block(&H256::from(21)));
		db.commit(&state_db.finalize_block(&H256::from(3)));

		(db, state_db)
	}

	#[test]
	fn full_archive_keeps_everything() {
		let (db, _) = make_test_db(Pruning::ArchiveAll);
		assert!(db.data_eq(&make_db(&[1, 21, 22, 3, 4, 91, 921, 922, 93])));
	}

	#[test]
	fn canonical_archive_keeps_canonical() {
		let (db, _) = make_test_db(Pruning::ArchiveCanonical);
		assert!(db.data_eq(&make_db(&[1, 21, 3, 91, 921, 922, 93])));
	}

	#[test]
	fn prune_window_1() {
		let (db, _) = make_test_db(Pruning::Constrained(Constraints {
			max_blocks: Some(1),
			max_mem: None,
		}));
		assert!(db.data_eq(&make_db(&[21, 3, 922, 93])));
	}

	#[test]
	fn prune_window_2() {
		let (db, _) = make_test_db(Pruning::Constrained(Constraints {
			max_blocks: Some(2),
			max_mem: None,
		}));
		assert!(db.data_eq(&make_db(&[1, 21, 3, 921, 922, 93])));
	}
}
