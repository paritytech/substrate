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

//! State database maintenance. Handles finalization and pruning in the database. The input to
//! this module is a `ChangeSet` which is basicall a list of key-value pairs (trie nodes) that
//! were added or deleted during block execution.
//!
//! # Finalization.
//! Finalization window tracks a tree of blocks identified by header hash. The in-memory
//! overlay allows to get any node that was was inserted in any any of the blocks within the window.
//! The tree is journaled to the backing database and rebuilt on startup.
//! Finalization function select one root from the top of the tree and discards all other roots and
//! their subtrees.
//!
//! # Pruning.
//! See `RefWindow` for pruning algorithm details. `StateDb` prunes on each finalization until pruning
//! constraints are satisfied.
//!

#[macro_use] extern crate log;
extern crate parking_lot;
extern crate substrate_codec as codec;
extern crate substrate_primitives as primitives;

mod unfinalized;
mod pruning;
#[cfg(test)] mod test;

use std::fmt;
use parking_lot::RwLock;
use codec::Codec;
use std::collections::HashSet;
use unfinalized::UnfinalizedOverlay;
use pruning::RefWindow;

/// Database value type.
pub type DBValue = Vec<u8>;

/// Basic set of requirements for the Block hash and node key types.
pub trait Hash: Send + Sync + Sized + Eq + PartialEq + Clone + Default + fmt::Debug + Codec + std::hash::Hash + 'static {}
impl<T: Send + Sync + Sized + Eq + PartialEq + Clone + Default + fmt::Debug + Codec + std::hash::Hash + 'static> Hash for T {}

/// Backend database trait. Read-only.
pub trait MetaDb {
	type Error: fmt::Debug;

	/// Get meta value, such as the journal.
	fn get_meta(&self, key: &[u8]) -> Result<Option<DBValue>, Self::Error>;
}


/// Backend database trait. Read-only.
pub trait HashDb {
	type Hash: Hash;
	type Error: fmt::Debug;

	/// Get state trie node.
	fn get(&self, key: &Self::Hash) -> Result<Option<DBValue>, Self::Error>;
}

/// Error type.
/// Error type.
pub enum Error<E: fmt::Debug> {
	/// Database backend error.
	Db(E),
	/// `Codec` decoding error.
	Decoding,
}

impl<E: fmt::Debug> fmt::Debug for Error<E> {
	fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
		match self {
			Error::Db(e) => e.fmt(f),
			Error::Decoding => write!(f, "Error decoding slicable value"),
		}
	}
}

/// A set of state node changes.
#[derive(Default, Debug, Clone)]
pub struct ChangeSet<H: Hash> {
	/// Inserted nodes.
	pub inserted: Vec<(H, DBValue)>,
	/// Delted nodes.
	pub deleted: Vec<H>,
}


/// A set of changes to the backing database.
#[derive(Default, Debug, Clone)]
pub struct CommitSet<H: Hash> {
	/// State node changes.
	pub data: ChangeSet<H>,
	/// Metadata changes.
	pub meta: ChangeSet<Vec<u8>>,
}

/// Pruning contraints. If none are specified pruning is
#[derive(Default, Debug, Clone)]
pub struct Constraints {
	/// Maximum blocks. Defaults to 0 when unspecified, effectively keeping only unfinalized states.
	pub max_blocks: Option<u32>,
	/// Maximum memory in the pruning overlay.
	pub max_mem: Option<usize>,
}

/// Pruning mode.
#[derive(Debug, Clone)]
pub enum PruningMode {
	/// Maintain a pruning window.
	Constrained(Constraints),
	/// No pruning. Finalization is a no-op.
	ArchiveAll,
	/// Finalization discards unfinalized nodes. All the finalized nodes are kept in the DB.
	ArchiveCanonical,
}

impl PruningMode {
	/// Create a mode that keeps given number of blocks.
	pub fn keep_blocks(n: u32) -> PruningMode {
		PruningMode::Constrained(Constraints {
			max_blocks: Some(n),
			max_mem: None,
		})
	}
}

fn to_meta_key<S: Codec>(suffix: &[u8], data: &S) -> Vec<u8> {
	let mut buffer = data.encode();
	buffer.extend(suffix);
	buffer
}

struct StateDbSync<BlockHash: Hash, Key: Hash> {
	mode: PruningMode,
	unfinalized: UnfinalizedOverlay<BlockHash, Key>,
	pruning: Option<RefWindow<BlockHash, Key>>,
	pinned: HashSet<BlockHash>,
}

impl<BlockHash: Hash, Key: Hash> StateDbSync<BlockHash, Key> {
	pub fn new<D: MetaDb>(mode: PruningMode, db: &D) -> Result<StateDbSync<BlockHash, Key>, Error<D::Error>> {
		trace!("StateDb settings: {:?}", mode);
		let unfinalized: UnfinalizedOverlay<BlockHash, Key> = UnfinalizedOverlay::new(db)?;
		let pruning: Option<RefWindow<BlockHash, Key>> = match mode {
			PruningMode::Constrained(Constraints {
				max_mem: Some(_),
				..
			}) => unimplemented!(),
			PruningMode::Constrained(_) => Some(RefWindow::new(db)?),
			PruningMode::ArchiveAll | PruningMode::ArchiveCanonical => None,
		};
		Ok(StateDbSync {
			mode,
			unfinalized,
			pruning: pruning,
			pinned: Default::default(),
		})
	}

	pub fn insert_block(&mut self, hash: &BlockHash, number: u64, parent_hash: &BlockHash, mut changeset: ChangeSet<Key>) -> CommitSet<Key> {
		if number == 0 {
			return CommitSet {
				data: changeset,
				meta: Default::default(),
			}
		}
		match self.mode {
			PruningMode::ArchiveAll => {
				changeset.deleted.clear();
				// write changes immediatelly
				CommitSet {
					data: changeset,
					meta: Default::default(),
				}
			},
			PruningMode::Constrained(_) | PruningMode::ArchiveCanonical => {
				self.unfinalized.insert(hash, number, parent_hash, changeset)
			}
		}
	}

	pub fn finalize_block(&mut self, hash: &BlockHash) -> CommitSet<Key> {
		let mut commit = match self.mode {
			PruningMode::ArchiveAll => {
				CommitSet::default()
			},
			PruningMode::ArchiveCanonical => {
				let mut commit = self.unfinalized.finalize(hash);
				commit.data.deleted.clear();
				commit
			},
			PruningMode::Constrained(_) => {
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
		if let (&mut Some(ref mut pruning), &PruningMode::Constrained(ref constraints)) = (&mut self.pruning, &self.mode) {
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

	pub fn get<D: HashDb<Hash=Key>>(&self, key: &Key, db: &D) -> Result<Option<DBValue>, Error<D::Error>> {
		if let Some(value) = self.unfinalized.get(key) {
			return Ok(Some(value));
		}
		db.get(key).map_err(|e| Error::Db(e))
	}
}

/// State DB maintenance. See module description.
/// Can be shared across threads.
pub struct StateDb<BlockHash: Hash, Key: Hash> {
	db: RwLock<StateDbSync<BlockHash, Key>>,
}

impl<BlockHash: Hash, Key: Hash> StateDb<BlockHash, Key> {
	/// Creates a new instance. Does not expect any metadata in the database.
	pub fn new<D: MetaDb>(mode: PruningMode, db: &D) -> Result<StateDb<BlockHash, Key>, Error<D::Error>> {
		Ok(StateDb {
			db: RwLock::new(StateDbSync::new(mode, db)?)
		})
	}

	/// Add a new unfinalized block.
	pub fn insert_block(&self, hash: &BlockHash, number: u64, parent_hash: &BlockHash, changeset: ChangeSet<Key>) -> CommitSet<Key> {
		self.db.write().insert_block(hash, number, parent_hash, changeset)
	}

	/// Finalize a previously inserted block.
	pub fn finalize_block(&self, hash: &BlockHash) -> CommitSet<Key> {
		self.db.write().finalize_block(hash)
	}

	/// Prevents pruning of specified block and its descendants.
	pub fn pin(&self, hash: &BlockHash) {
		self.db.write().pin(hash)
	}

	/// Allows pruning of specified block.
	pub fn unpin(&self, hash: &BlockHash) {
		self.db.write().unpin(hash)
	}

	/// Get a value from unfinalized/pruning overlay or the backing DB.
	pub fn get<D: HashDb<Hash=Key>>(&self, key: &Key, db: &D) -> Result<Option<DBValue>, Error<D::Error>> {
		self.db.read().get(key, db)
	}
}

#[cfg(test)]
mod tests {
	use primitives::H256;
	use {StateDb, PruningMode, Constraints};
	use test::{make_db, make_changeset, TestDb};

	fn make_test_db(settings: PruningMode) -> (TestDb, StateDb<H256, H256>) {
		let mut db = make_db(&[91, 921, 922, 93, 94]);
		let state_db = StateDb::new(settings, &db).unwrap();

		db.commit(&state_db.insert_block(&H256::from(1), 1, &H256::from(0), make_changeset(&[1], &[91])));
		db.commit(&state_db.insert_block(&H256::from(21), 2, &H256::from(1), make_changeset(&[21], &[921, 1])));
		db.commit(&state_db.insert_block(&H256::from(22), 2, &H256::from(1), make_changeset(&[22], &[922])));
		db.commit(&state_db.insert_block(&H256::from(3), 3, &H256::from(21), make_changeset(&[3], &[93])));
		db.commit(&state_db.finalize_block(&H256::from(1)));
		db.commit(&state_db.insert_block(&H256::from(4), 4, &H256::from(3), make_changeset(&[4], &[94])));
		db.commit(&state_db.finalize_block(&H256::from(21)));
		db.commit(&state_db.finalize_block(&H256::from(3)));

		(db, state_db)
	}

	#[test]
	fn full_archive_keeps_everything() {
		let (db, _) = make_test_db(PruningMode::ArchiveAll);
		assert!(db.data_eq(&make_db(&[1, 21, 22, 3, 4, 91, 921, 922, 93, 94])));
	}

	#[test]
	fn canonical_archive_keeps_canonical() {
		let (db, _) = make_test_db(PruningMode::ArchiveCanonical);
		assert!(db.data_eq(&make_db(&[1, 21, 3, 91, 921, 922, 93, 94])));
	}

	#[test]
	fn prune_window_0() {
		let (db, _) = make_test_db(PruningMode::Constrained(Constraints {
			max_blocks: Some(0),
			max_mem: None,
		}));
		assert!(db.data_eq(&make_db(&[21, 3, 922, 94])));
	}

	#[test]
	fn prune_window_1() {
		let (db, _) = make_test_db(PruningMode::Constrained(Constraints {
			max_blocks: Some(1),
			max_mem: None,
		}));
		assert!(db.data_eq(&make_db(&[21, 3, 922, 93, 94])));
	}

	#[test]
	fn prune_window_2() {
		let (db, _) = make_test_db(PruningMode::Constrained(Constraints {
			max_blocks: Some(2),
			max_mem: None,
		}));
		assert!(db.data_eq(&make_db(&[1, 21, 3, 921, 922, 93, 94])));
	}
}
