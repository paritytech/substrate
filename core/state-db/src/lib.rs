// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

//! State database maintenance. Handles canonicalization and pruning in the database. The input to
//! this module is a `ChangeSet` which is basically a list of key-value pairs (trie nodes) that
//! were added or deleted during block execution.
//!
//! # Canonicalization.
//! Canonicalization window tracks a tree of blocks identified by header hash. The in-memory
//! overlay allows to get any node that was inserted in any of the blocks within the window.
//! The tree is journaled to the backing database and rebuilt on startup.
//! Canonicalization function selects one root from the top of the tree and discards all other roots and
//! their subtrees.
//!
//! # Pruning.
//! See `RefWindow` for pruning algorithm details. `StateDb` prunes on each canonicalization until pruning
//! constraints are satisfied.

mod noncanonical;
mod pruning;
#[cfg(test)] mod test;

use std::fmt;
use parking_lot::RwLock;
use parity_codec as codec;
use codec::Codec;
use std::collections::HashSet;
use noncanonical::NonCanonicalOverlay;
use pruning::RefWindow;
use log::trace;

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
pub trait NodeDb {
	type Key: ?Sized;
	type Error: fmt::Debug;

	/// Get state trie node.
	fn get(&self, key: &Self::Key) -> Result<Option<DBValue>, Self::Error>;
}

/// Error type.
pub enum Error<E: fmt::Debug> {
	/// Database backend error.
	Db(E),
	/// `Codec` decoding error.
	Decoding,
	/// Trying to canonicalize invalid block.
	InvalidBlock,
	/// Trying to insert block with invalid number.
	InvalidBlockNumber,
	/// Trying to insert block with unknown parent.
	InvalidParent,
}

impl<E: fmt::Debug> fmt::Debug for Error<E> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match self {
			Error::Db(e) => e.fmt(f),
			Error::Decoding => write!(f, "Error decoding slicable value"),
			Error::InvalidBlock => write!(f, "Trying to canonicalize invalid block"),
			Error::InvalidBlockNumber => write!(f, "Trying to insert block with invalid number"),
			Error::InvalidParent => write!(f, "Trying to insert block with unknown parent"),
		}
	}
}

/// A set of state node changes.
#[derive(Default, Debug, Clone)]
pub struct ChangeSet<H: Hash> {
	/// Inserted nodes.
	pub inserted: Vec<(H, DBValue)>,
	/// Deleted nodes.
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

/// Pruning constraints. If none are specified pruning is
#[derive(Default, Debug, Clone)]
pub struct Constraints {
	/// Maximum blocks. Defaults to 0 when unspecified, effectively keeping only non-canonical states.
	pub max_blocks: Option<u32>,
	/// Maximum memory in the pruning overlay.
	pub max_mem: Option<usize>,
}

/// Pruning mode.
#[derive(Debug, Clone)]
pub enum PruningMode {
	/// Maintain a pruning window.
	Constrained(Constraints),
	/// No pruning. Canonicalization is a no-op.
	ArchiveAll,
	/// Canonicalization discards non-canonical nodes. All the canonical nodes are kept in the DB.
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

	/// Is this an archive (either ArchiveAll or ArchiveCanonical) pruning mode?
	pub fn is_archive(&self) -> bool {
		match *self {
			PruningMode::ArchiveAll | PruningMode::ArchiveCanonical => true,
			PruningMode::Constrained(_) => false
		}
	}

}

impl Default for PruningMode {
	fn default() -> Self {
		PruningMode::keep_blocks(256)
	}
}

fn to_meta_key<S: Codec>(suffix: &[u8], data: &S) -> Vec<u8> {
	let mut buffer = data.encode();
	buffer.extend(suffix);
	buffer
}

struct StateDbSync<BlockHash: Hash, Key: Hash> {
	mode: PruningMode,
	non_canonical: NonCanonicalOverlay<BlockHash, Key>,
	pruning: Option<RefWindow<BlockHash, Key>>,
	pinned: HashSet<BlockHash>,
}

impl<BlockHash: Hash, Key: Hash> StateDbSync<BlockHash, Key> {
	pub fn new<D: MetaDb>(mode: PruningMode, db: &D) -> Result<StateDbSync<BlockHash, Key>, Error<D::Error>> {
		trace!("StateDb settings: {:?}", mode);
		let non_canonical: NonCanonicalOverlay<BlockHash, Key> = NonCanonicalOverlay::new(db)?;
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
			non_canonical,
			pruning,
			pinned: Default::default(),
		})
	}

	pub fn insert_block<E: fmt::Debug>(&mut self, hash: &BlockHash, number: u64, parent_hash: &BlockHash, mut changeset: ChangeSet<Key>) -> Result<CommitSet<Key>, Error<E>> {
		match self.mode {
			PruningMode::ArchiveAll => {
				changeset.deleted.clear();
				// write changes immediately
				Ok(CommitSet {
					data: changeset,
					meta: Default::default(),
				})
			},
			PruningMode::Constrained(_) | PruningMode::ArchiveCanonical => {
				self.non_canonical.insert(hash, number, parent_hash, changeset)
			}
		}
	}

	pub fn canonicalize_block<E: fmt::Debug>(&mut self, hash: &BlockHash) -> Result<CommitSet<Key>, Error<E>> {
		let mut commit = match self.mode {
			PruningMode::ArchiveAll => {
				CommitSet::default()
			},
			PruningMode::ArchiveCanonical => {
				let mut commit = self.non_canonical.canonicalize(hash)?;
				commit.data.deleted.clear();
				commit
			},
			PruningMode::Constrained(_) => {
				self.non_canonical.canonicalize(hash)?
			},
		};
		if let Some(ref mut pruning) = self.pruning {
			pruning.note_canonical(hash, &mut commit);
		}
		self.prune(&mut commit);
		Ok(commit)
	}

	pub fn best_canonical(&self) -> Option<u64> {
		return self.non_canonical.last_canonicalized_block_number()
	}

	pub fn is_pruned(&self, hash: &BlockHash, number: u64) -> bool {
		match self.mode {
			PruningMode::ArchiveAll => false,
			PruningMode::ArchiveCanonical | PruningMode::Constrained(_) => {
				if self.best_canonical().map(|c| number > c).unwrap_or(true) {
					!self.non_canonical.have_block(hash)
				} else {
					self.pruning.as_ref().map_or(false, |pruning| number < pruning.pending() || !pruning.have_block(hash))
				}
			}
		}
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

	/// Revert all non-canonical blocks with the best block number.
	/// Returns a database commit or `None` if not possible.
	/// For archive an empty commit set is returned.
	pub fn revert_one(&mut self) -> Option<CommitSet<Key>> {
		match self.mode {
			PruningMode::ArchiveAll => {
				Some(CommitSet::default())
			},
			PruningMode::ArchiveCanonical | PruningMode::Constrained(_) => {
				self.non_canonical.revert_one()
			},
		}
	}

	pub fn pin(&mut self, hash: &BlockHash) {
		self.pinned.insert(hash.clone());
	}

	pub fn unpin(&mut self, hash: &BlockHash) {
		self.pinned.remove(hash);
	}

	pub fn get<D: NodeDb>(&self, key: &Key, db: &D) -> Result<Option<DBValue>, Error<D::Error>>
		where Key: AsRef<D::Key>
	{
		if let Some(value) = self.non_canonical.get(key) {
			return Ok(Some(value));
		}
		db.get(key.as_ref()).map_err(|e| Error::Db(e))
	}

	pub fn apply_pending(&mut self) {
		self.non_canonical.apply_pending();
		if let Some(pruning) = &mut self.pruning {
			pruning.apply_pending();
		}
		trace!(target: "forks", "First available: {:?} ({}), Last canon: {:?} ({}), Best forks: {:?}",
			self.pruning.as_ref().and_then(|p| p.next_hash()),
			self.pruning.as_ref().map(|p| p.pending()).unwrap_or(0),
			self.non_canonical.last_canonicalized_hash(),
			self.non_canonical.last_canonicalized_block_number().unwrap_or(0),
			self.non_canonical.top_level(),
		);
	}

	pub fn revert_pending(&mut self) {
		if let Some(pruning) = &mut self.pruning {
			pruning.revert_pending();
		}
		self.non_canonical.revert_pending();
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

	/// Add a new non-canonical block.
	pub fn insert_block<E: fmt::Debug>(&self, hash: &BlockHash, number: u64, parent_hash: &BlockHash, changeset: ChangeSet<Key>) -> Result<CommitSet<Key>, Error<E>> {
		self.db.write().insert_block(hash, number, parent_hash, changeset)
	}

	/// Finalize a previously inserted block.
	pub fn canonicalize_block<E: fmt::Debug>(&self, hash: &BlockHash) -> Result<CommitSet<Key>, Error<E>> {
		self.db.write().canonicalize_block(hash)
	}

	/// Prevents pruning of specified block and its descendants.
	pub fn pin(&self, hash: &BlockHash) {
		self.db.write().pin(hash)
	}

	/// Allows pruning of specified block.
	pub fn unpin(&self, hash: &BlockHash) {
		self.db.write().unpin(hash)
	}

	/// Get a value from non-canonical/pruning overlay or the backing DB.
	pub fn get<D: NodeDb>(&self, key: &Key, db: &D) -> Result<Option<DBValue>, Error<D::Error>>
		where Key: AsRef<D::Key>
	{
		self.db.read().get(key, db)
	}

	/// Revert all non-canonical blocks with the best block number.
	/// Returns a database commit or `None` if not possible.
	/// For archive an empty commit set is returned.
	pub fn revert_one(&self) -> Option<CommitSet<Key>> {
		self.db.write().revert_one()
	}

	/// Returns last finalized block number.
	pub fn best_canonical(&self) -> Option<u64> {
		return self.db.read().best_canonical()
	}

	/// Check if block is pruned away.
	pub fn is_pruned(&self, hash: &BlockHash, number: u64) -> bool {
		return self.db.read().is_pruned(hash, number)
	}

	/// Apply all pending changes
	pub fn apply_pending(&self) {
		self.db.write().apply_pending();
	}

	/// Revert all pending changes
	pub fn revert_pending(&self) {
		self.db.write().revert_pending();
	}
}

#[cfg(test)]
mod tests {
	use std::io;
	use primitives::H256;
	use crate::{StateDb, PruningMode, Constraints};
	use crate::test::{make_db, make_changeset, TestDb};

	fn make_test_db(settings: PruningMode) -> (TestDb, StateDb<H256, H256>) {
		let mut db = make_db(&[91, 921, 922, 93, 94]);
		let state_db = StateDb::new(settings, &db).unwrap();

		db.commit(
			&state_db
				.insert_block::<io::Error>(
					&H256::from_low_u64_be(1),
					1,
					&H256::from_low_u64_be(0),
					make_changeset(&[1], &[91]),
				)
				.unwrap(),
		);
		db.commit(
			&state_db
				.insert_block::<io::Error>(
					&H256::from_low_u64_be(21),
					2,
					&H256::from_low_u64_be(1),
					make_changeset(&[21], &[921, 1]),
				)
				.unwrap(),
		);
		db.commit(
			&state_db
				.insert_block::<io::Error>(
					&H256::from_low_u64_be(22),
					2,
					&H256::from_low_u64_be(1),
					make_changeset(&[22], &[922]),
				)
				.unwrap(),
		);
		db.commit(
			&state_db
				.insert_block::<io::Error>(
					&H256::from_low_u64_be(3),
					3,
					&H256::from_low_u64_be(21),
					make_changeset(&[3], &[93]),
				)
				.unwrap(),
		);
		state_db.apply_pending();
		db.commit(&state_db.canonicalize_block::<io::Error>(&H256::from_low_u64_be(1)).unwrap());
		state_db.apply_pending();
		db.commit(
			&state_db
				.insert_block::<io::Error>(
					&H256::from_low_u64_be(4),
					4,
					&H256::from_low_u64_be(3),
					make_changeset(&[4], &[94]),
				)
				.unwrap(),
		);
		state_db.apply_pending();
		db.commit(&state_db.canonicalize_block::<io::Error>(&H256::from_low_u64_be(21)).unwrap());
		state_db.apply_pending();
		db.commit(&state_db.canonicalize_block::<io::Error>(&H256::from_low_u64_be(3)).unwrap());
		state_db.apply_pending();

		(db, state_db)
	}

	#[test]
	fn full_archive_keeps_everything() {
		let (db, sdb) = make_test_db(PruningMode::ArchiveAll);
		assert!(db.data_eq(&make_db(&[1, 21, 22, 3, 4, 91, 921, 922, 93, 94])));
		assert!(!sdb.is_pruned(&H256::from_low_u64_be(0), 0));
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
		let (db, sdb) = make_test_db(PruningMode::Constrained(Constraints {
			max_blocks: Some(1),
			max_mem: None,
		}));
		assert!(sdb.is_pruned(&H256::from_low_u64_be(0), 0));
		assert!(sdb.is_pruned(&H256::from_low_u64_be(1), 1));
		assert!(sdb.is_pruned(&H256::from_low_u64_be(21), 2));
		assert!(sdb.is_pruned(&H256::from_low_u64_be(22), 2));
		assert!(db.data_eq(&make_db(&[21, 3, 922, 93, 94])));
	}

	#[test]
	fn prune_window_2() {
		let (db, sdb) = make_test_db(PruningMode::Constrained(Constraints {
			max_blocks: Some(2),
			max_mem: None,
		}));
		assert!(sdb.is_pruned(&H256::from_low_u64_be(0), 0));
		assert!(sdb.is_pruned(&H256::from_low_u64_be(1), 1));
		assert!(!sdb.is_pruned(&H256::from_low_u64_be(21), 2));
		assert!(sdb.is_pruned(&H256::from_low_u64_be(22), 2));
		assert!(db.data_eq(&make_db(&[1, 21, 3, 921, 922, 93, 94])));
	}
}
