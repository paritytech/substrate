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

extern crate parking_lot;
extern crate substrate_codec as codec;
extern crate substrate_primitives as primitives;

mod unfinalized;
mod pruning;
#[cfg(test)] mod test;

use parking_lot::RwLock;
use codec::Slicable;
use std::collections::HashSet;
use unfinalized::UnfinalizedOverlay;
use pruning::RefWindow;

pub type DBValue = Vec<u8>;

pub trait Hash: Send + Sync + Sized + Eq + PartialEq + Clone + Default + Slicable + std::hash::Hash + 'static {}
impl<T: Send + Sync + Sized + Eq + PartialEq + Clone + Default + Slicable + std::hash::Hash + 'static> Hash for T {}

pub trait KeyValueDb {
	type Hash: Hash;
	type Error;

	fn get(&self, key: &Self::Hash) -> Result<Option<DBValue>, Self::Error>;
	fn get_meta(&self, key: &[u8]) -> Result<Option<DBValue>, Self::Error>;
}

#[derive(Debug)]
pub enum Error<D: KeyValueDb> {
	Db(D::Error),
	Decoding,
}

#[derive(Default, Debug, Clone)]
pub struct ChangeSet<H: Hash> {
	inserted: Vec<(H, DBValue)>,
	deleted: Vec<H>,
}


#[derive(Default, Debug, Clone)]
pub struct CommitSet<H: Hash> {
	data: ChangeSet<H>,
	meta: ChangeSet<Vec<u8>>,
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

fn to_meta_key<S: Slicable>(suffix: &[u8], data: &S) -> Vec<u8> {
	let mut buffer = data.encode();
	buffer.extend(suffix);
	buffer
}

pub struct StateDbSync<BlockHash: Hash, Key: Hash> {
	mode: Pruning,
	unfinalized: UnfinalizedOverlay<BlockHash, Key>,
	pruning: Option<RefWindow<BlockHash, Key>>,
	pinned: HashSet<BlockHash>,
}

impl<BlockHash: Hash, Key: Hash> StateDbSync<BlockHash, Key> {
	pub fn new<D: KeyValueDb<Hash=Key>>(mode: Pruning, db: &D) -> Result<StateDbSync<BlockHash, Key>, Error<D>> {
		let unfinalized: UnfinalizedOverlay<BlockHash, Key> = UnfinalizedOverlay::new(db)?;
		let pruning: Option<RefWindow<BlockHash, Key>> = match mode {
			Pruning::Constrained(_) => Some(RefWindow::new(db)?),
			Pruning::ArchiveAll | Pruning::ArchiveCanonical => None,
		};
		Ok(StateDbSync {
			mode,
			unfinalized,
			pruning: pruning,
			pinned: Default::default(),
		})
	}

	pub fn insert_block(&mut self, hash: &BlockHash, number: u64, parent_hash: &BlockHash, mut changeset: ChangeSet<Key>) -> CommitSet<Key> {
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

	pub fn finalize_block(&mut self, hash: &BlockHash) -> CommitSet<Key> {
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

	fn prune(&mut self, commit: &mut CommitSet<Key>) {
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

	pub fn pin(&mut self, hash: &BlockHash) {
		self.pinned.insert(hash.clone());
	}

	pub fn unpin(&mut self, hash: &BlockHash) {
		self.pinned.remove(hash);
	}

	pub fn get<D: KeyValueDb<Hash=Key>>(&self, key: &Key, db: &D) -> Result<Option<DBValue>, Error<D>> {
		if let Some(value) = self.unfinalized.get(key) {
			return Ok(Some(value));
		}
		db.get(key).map_err(|e| Error::Db(e))
	}
}

pub struct StateDb<BlockHash: Hash, Key: Hash> {
	db: RwLock<StateDbSync<BlockHash, Key>>,
}

impl<BlockHash: Hash, Key: Hash> StateDb<BlockHash, Key> {
	pub fn new<D: KeyValueDb<Hash=Key>>(mode: Pruning, db: &D) -> Result<StateDb<BlockHash, Key>, Error<D>> {
		Ok(StateDb {
			db: RwLock::new(StateDbSync::new(mode, db)?)
		})
	}

	pub fn insert_block(&self, hash: &BlockHash, number: u64, parent_hash: &BlockHash, changeset: ChangeSet<Key>) -> CommitSet<Key> {
		self.db.write().insert_block(hash, number, parent_hash, changeset)
	}

	pub fn finalize_block(&self, hash: &BlockHash) -> CommitSet<Key> {
		self.db.write().finalize_block(hash)
	}

	pub fn pin(&self, hash: &BlockHash) {
		self.db.write().pin(hash)
	}

	pub fn unpin(&self, hash: &BlockHash) {
		self.db.write().unpin(hash)
	}

	pub fn get<D: KeyValueDb<Hash=Key>>(&self, key: &Key, db: &D) -> Result<Option<DBValue>, Error<D>> {
		self.db.read().get(key, db)
	}
}

#[cfg(test)]
mod tests {
	use primitives::H256;
	use {StateDb, Pruning, Constraints};
	use test::{make_db, make_changeset, TestDb};

	fn make_test_db(settings: Pruning) -> (TestDb, StateDb<H256, H256>) {
		let mut db = make_db(&[91, 921, 922, 93]);
		let state_db = StateDb::new(settings, &db).unwrap();

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
