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

//! Canonicalization window.
//! Maintains trees of block overlays and allows discarding trees/roots
//! The overlays are added in `insert` and removed in `canonicalize`.
//! All pending changes are kept in memory until next call to `apply_pending` or
//! `revert_pending`

use std::fmt;
use std::collections::{HashMap, VecDeque, hash_map::Entry};
use super::{Error, DBValue, ChangeSet, CommitSet, MetaDb, Hash, to_meta_key};
use crate::codec::{Encode, Decode};
use log::trace;

const NON_CANONICAL_JOURNAL: &[u8] = b"noncanonical_journal";
const LAST_CANONICAL: &[u8] = b"last_canonical";

/// See module documentation.
pub struct NonCanonicalOverlay<BlockHash: Hash, Key: Hash> {
	last_canonicalized: Option<(BlockHash, u64)>,
	levels: VecDeque<Vec<BlockOverlay<BlockHash, Key>>>,
	parents: HashMap<BlockHash, BlockHash>,
	pending_canonicalizations: Vec<BlockHash>,
	pending_insertions: Vec<BlockHash>,
	values: HashMap<Key, (u32, DBValue)>, //ref counted
}

#[derive(Encode, Decode)]
struct JournalRecord<BlockHash: Hash, Key: Hash> {
	hash: BlockHash,
	parent_hash: BlockHash,
	inserted: Vec<(Key, DBValue)>,
	deleted: Vec<Key>,
}

fn to_journal_key(block: u64, index: u64) -> Vec<u8> {
	to_meta_key(NON_CANONICAL_JOURNAL, &(block, index))
}

#[cfg_attr(test, derive(PartialEq, Debug))]
struct BlockOverlay<BlockHash: Hash, Key: Hash> {
	hash: BlockHash,
	journal_key: Vec<u8>,
	inserted: Vec<Key>,
	deleted: Vec<Key>,
}

fn insert_values<Key: Hash>(values: &mut HashMap<Key, (u32, DBValue)>, inserted: Vec<(Key, DBValue)>) {
	for (k, v) in inserted {
		debug_assert!(values.get(&k).map_or(true, |(_, value)| *value == v));
		let (ref mut counter, _) = values.entry(k).or_insert_with(|| (0, v));
		*counter += 1;
	}
}

fn discard_values<Key: Hash>(values: &mut HashMap<Key, (u32, DBValue)>, inserted: Vec<Key>) {
	for k in inserted {
		match values.entry(k) {
			Entry::Occupied(mut e) => {
				let (ref mut counter, _) = e.get_mut();
				*counter -= 1;
				if *counter == 0 {
					e.remove();
				}
			},
			Entry::Vacant(_) => {
				debug_assert!(false, "Trying to discard missing value");
			}
		}
	}
}

fn discard_descendants<BlockHash: Hash, Key: Hash>(
	levels: &mut VecDeque<Vec<BlockOverlay<BlockHash, Key>>>,
	mut values: &mut HashMap<Key, (u32, DBValue)>,
	index: usize,
	parents: &mut HashMap<BlockHash, BlockHash>,
	hash: &BlockHash,
	) {
	let mut discarded = Vec::new();
	if let Some(level) = levels.get_mut(index) {
		*level = level.drain(..).filter_map(|overlay| {
			let parent = parents.get(&overlay.hash).expect("there is a parent entry for each entry in levels; qed").clone();
			if parent == *hash {
				parents.remove(&overlay.hash);
				discarded.push(overlay.hash);
				discard_values(&mut values, overlay.inserted);
				None
			} else {
				Some(overlay)
			}
		}).collect();
	}
	for hash in discarded {
		discard_descendants(levels, values, index + 1, parents, &hash);
	}
}

impl<BlockHash: Hash, Key: Hash> NonCanonicalOverlay<BlockHash, Key> {
	/// Creates a new instance. Does not expect any metadata to be present in the DB.
	pub fn new<D: MetaDb>(db: &D) -> Result<NonCanonicalOverlay<BlockHash, Key>, Error<D::Error>> {
		let last_canonicalized = db.get_meta(&to_meta_key(LAST_CANONICAL, &()))
			.map_err(|e| Error::Db(e))?;
		let last_canonicalized = match last_canonicalized {
			Some(buffer) => Some(<(BlockHash, u64)>::decode(&mut buffer.as_slice()).ok_or(Error::Decoding)?),
			None => None,
		};
		let mut levels = VecDeque::new();
		let mut parents = HashMap::new();
		let mut values = HashMap::new();
		if let Some((ref hash, mut block)) = last_canonicalized {
			// read the journal
			trace!(target: "state-db", "Reading uncanonicalized journal. Last canonicalized #{} ({:?})", block, hash);
			let mut total: u64 = 0;
			block += 1;
			loop {
				let mut index: u64 = 0;
				let mut level = Vec::new();
				loop {
					let journal_key = to_journal_key(block, index);
					match db.get_meta(&journal_key).map_err(|e| Error::Db(e))? {
						Some(record) => {
							let record: JournalRecord<BlockHash, Key> = Decode::decode(&mut record.as_slice()).ok_or(Error::Decoding)?;
							let inserted = record.inserted.iter().map(|(k, _)| k.clone()).collect();
							let overlay = BlockOverlay {
								hash: record.hash.clone(),
								journal_key,
								inserted: inserted,
								deleted: record.deleted,
							};
							insert_values(&mut values, record.inserted);
							trace!(target: "state-db", "Uncanonicalized journal entry {}.{} ({} inserted, {} deleted)", block, index, overlay.inserted.len(), overlay.deleted.len());
							level.push(overlay);
							parents.insert(record.hash, record.parent_hash);
							index += 1;
							total += 1;
						},
						None => break,
					}
				}
				if level.is_empty() {
					break;
				}
				levels.push_back(level);
				block += 1;
			}
			trace!(target: "state-db", "Finished reading uncanonicalized journal, {} entries", total);
		}
		Ok(NonCanonicalOverlay {
			last_canonicalized,
			levels,
			parents,
			pending_canonicalizations: Default::default(),
			pending_insertions: Default::default(),
			values: values,
		})
	}

	/// Insert a new block into the overlay. If inserted on the second level or lover expects parent to be present in the window.
	pub fn insert<E: fmt::Debug>(&mut self, hash: &BlockHash, number: u64, parent_hash: &BlockHash, changeset: ChangeSet<Key>) -> Result<CommitSet<Key>, Error<E>> {
		let mut commit = CommitSet::default();
		let front_block_number = self.front_block_number();
		if self.levels.is_empty() && self.last_canonicalized.is_none() && number > 0 {
			// assume that parent was canonicalized
			let last_canonicalized = (parent_hash.clone(), number - 1);
			commit.meta.inserted.push((to_meta_key(LAST_CANONICAL, &()), last_canonicalized.encode()));
			self.last_canonicalized = Some(last_canonicalized);
		} else if self.last_canonicalized.is_some() {
			if number < front_block_number || number >= front_block_number + self.levels.len() as u64 + 1 {
				trace!(target: "state-db", "Failed to insert block {}, current is {} .. {})",
					number,
					front_block_number,
					front_block_number + self.levels.len() as u64,
				);
				return Err(Error::InvalidBlockNumber);
			}
			// check for valid parent if inserting on second level or higher
			if number == front_block_number {
				if !self.last_canonicalized.as_ref().map_or(false, |&(ref h, n)| h == parent_hash && n == number - 1) {
					return Err(Error::InvalidParent);
				}
			} else if !self.parents.contains_key(&parent_hash) {
				return Err(Error::InvalidParent);
			}
		}
		let level = if self.levels.is_empty() || number == front_block_number + self.levels.len() as u64 {
			self.levels.push_back(Vec::new());
			self.levels.back_mut().expect("can't be empty after insertion; qed")
		} else {
			self.levels.get_mut((number - front_block_number) as usize)
				.expect("number is [front_block_number .. front_block_number + levels.len()) is asserted in precondition; qed")
		};

		let index = level.len() as u64;
		let journal_key = to_journal_key(number, index);

		let inserted = changeset.inserted.iter().map(|(k, _)| k.clone()).collect();
		let overlay = BlockOverlay {
			hash: hash.clone(),
			journal_key: journal_key.clone(),
			inserted: inserted,
			deleted: changeset.deleted.clone(),
		};
		level.push(overlay);
		self.parents.insert(hash.clone(), parent_hash.clone());
		let journal_record = JournalRecord {
			hash: hash.clone(),
			parent_hash: parent_hash.clone(),
			inserted: changeset.inserted,
			deleted: changeset.deleted,
		};
		commit.meta.inserted.push((journal_key, journal_record.encode()));
		trace!(target: "state-db", "Inserted uncanonicalized changeset {}.{} ({} inserted, {} deleted)", number, index, journal_record.inserted.len(), journal_record.deleted.len());
		insert_values(&mut self.values, journal_record.inserted);
		self.pending_insertions.push(hash.clone());
		Ok(commit)
	}

	fn discard_journals(&self, level_index: usize, discarded_journals: &mut Vec<Vec<u8>>, hash: &BlockHash) {
		if let Some(level) = self.levels.get(level_index) {
			level.iter().for_each(|overlay| {
				let parent = self.parents.get(&overlay.hash).expect("there is a parent entry for each entry in levels; qed").clone();
				if parent == *hash {
					discarded_journals.push(overlay.journal_key.clone());
					self.discard_journals(level_index + 1, discarded_journals, &overlay.hash);
				}
			});
		}
	}

	fn front_block_number(&self) -> u64 {
		self.last_canonicalized.as_ref().map(|&(_, n)| n + 1).unwrap_or(0)
	}

	pub fn last_canonicalized_block_number(&self) -> Option<u64> {
		match self.last_canonicalized.as_ref().map(|&(_, n)| n) {
			Some(n) => Some(n + self.pending_canonicalizations.len() as u64),
			None if !self.pending_canonicalizations.is_empty() => Some(self.pending_canonicalizations.len() as u64),
			_ => None,
		}
	}

	pub fn last_canonicalized_hash(&self) -> Option<BlockHash> {
		self.last_canonicalized.as_ref().map(|&(ref h, _)| h.clone())
	}

	pub fn top_level(&self) -> Vec<(BlockHash, u64)> {
		let start = self.last_canonicalized_block_number().unwrap_or(0);
		self.levels
			.get(self.pending_canonicalizations.len())
			.map(|level| level.iter().map(|r| (r.hash.clone(), start)).collect())
			.unwrap_or_default()
	}

	/// Select a top-level root and canonicalized it. Discards all sibling subtrees and the root.
	/// Returns a set of changes that need to be added to the DB.
	pub fn canonicalize<E: fmt::Debug>(&mut self, hash: &BlockHash) -> Result<CommitSet<Key>, Error<E>> {
		trace!(target: "state-db", "Canonicalizing {:?}", hash);
		let level = self.levels.get(self.pending_canonicalizations.len()).ok_or_else(|| Error::InvalidBlock)?;
		let index = level
			.iter()
			.position(|overlay| overlay.hash == *hash)
			.ok_or_else(|| Error::InvalidBlock)?;

		let mut commit = CommitSet::default();
		let mut discarded_journals = Vec::new();
		for (i, overlay) in level.into_iter().enumerate() {
			if i == index {
				// that's the one we need to canonicalize
				commit.data.inserted = overlay.inserted.iter()
					.map(|k| (k.clone(), self.values.get(k).expect("For each key in verlays there's a value in values").1.clone()))
					.collect();
				commit.data.deleted = overlay.deleted.clone();
			} else {
				self.discard_journals(self.pending_canonicalizations.len() + 1, &mut discarded_journals, &overlay.hash);
			}
			discarded_journals.push(overlay.journal_key.clone());
		}
		commit.meta.deleted.append(&mut discarded_journals);
		let canonicalized = (hash.clone(), self.front_block_number() + self.pending_canonicalizations.len() as u64);
		commit.meta.inserted.push((to_meta_key(LAST_CANONICAL, &()), canonicalized.encode()));
		trace!(target: "state-db", "Discarding {} records", commit.meta.deleted.len());
		self.pending_canonicalizations.push(hash.clone());
		Ok(commit)
	}

	fn apply_canonicalizations(&mut self) {
		let last = self.pending_canonicalizations.last().cloned();
		let count = self.pending_canonicalizations.len() as u64;
		for hash in self.pending_canonicalizations.drain(..) {
			trace!(target: "state-db", "Post canonicalizing {:?}", hash);
			let level = self.levels.pop_front().expect("Hash validity is checked in `canonicalize`");
			let index = level
				.iter()
				.position(|overlay| overlay.hash == hash)
				.expect("Hash validity is checked in `canonicalize`");

			// discard unfinalized overlays and values
			for (i, overlay) in level.into_iter().enumerate() {
				self.parents.remove(&overlay.hash);
				if i != index {
					discard_descendants(&mut self.levels, &mut self.values, 0, &mut self.parents, &overlay.hash);
				}
				discard_values(&mut self.values, overlay.inserted);
			}
		}
		if let Some(hash) = last {
			let last_canonicalized = (hash, self.last_canonicalized.as_ref().map(|(_, n)| n + count).unwrap_or(count - 1));
			self.last_canonicalized = Some(last_canonicalized);
		}
	}

	/// Get a value from the node overlay. This searches in every existing changeset.
	pub fn get(&self, key: &Key) -> Option<DBValue> {
		if let Some((_, value)) = self.values.get(&key) {
			return Some(value.clone());
		}
		None
	}

	/// Check if the block is in the canonicalization queue. 
	pub fn have_block(&self, hash: &BlockHash) -> bool {
		(self.parents.contains_key(hash) || self.pending_insertions.contains(hash))
			&& !self.pending_canonicalizations.contains(hash)
	}

	/// Revert a single level. Returns commit set that deletes the journal or `None` if not possible.
	pub fn revert_one(&mut self) -> Option<CommitSet<Key>> {
		self.levels.pop_back().map(|level| {
			let mut commit = CommitSet::default();
			for overlay in level.into_iter() {
				commit.meta.deleted.push(overlay.journal_key);
				self.parents.remove(&overlay.hash);
				discard_values(&mut self.values, overlay.inserted);
			}
			commit
		})
	}

	fn revert_insertions(&mut self) {
		self.pending_insertions.reverse();
		for hash in self.pending_insertions.drain(..) {
			self.parents.remove(&hash);
			// find a level. When iterating insertions backwards the hash is always last in the level.
			let level_index =
				self.levels.iter().position(|level|
					level.last().expect("Hash is added in `insert` in reverse order").hash == hash)
				.expect("Hash is added in insert");

			let	overlay = self.levels[level_index].pop().expect("Empty levels are not allowed in self.levels");
			discard_values(&mut self.values, overlay.inserted);
			if self.levels[level_index].is_empty() {
				debug_assert_eq!(level_index, self.levels.len() - 1);
				self.levels.pop_back();
			}
		}
	}

	/// Apply all pending changes
	pub fn apply_pending(&mut self) {
		self.apply_canonicalizations();
		self.pending_insertions.clear();
	}

	/// Revert all pending changes
	pub fn revert_pending(&mut self) {
		self.pending_canonicalizations.clear();
		self.revert_insertions();
	}
}

#[cfg(test)]
mod tests {
	use std::io;
	use primitives::H256;
	use super::{NonCanonicalOverlay, to_journal_key};
	use crate::ChangeSet;
	use crate::test::{make_db, make_changeset};

	fn contains(overlay: &NonCanonicalOverlay<H256, H256>, key: u64) -> bool {
		overlay.get(&H256::from_low_u64_be(key)) == Some(H256::from_low_u64_be(key).as_bytes().to_vec())
	}

	#[test]
	fn created_from_empty_db() {
		let db = make_db(&[]);
		let overlay: NonCanonicalOverlay<H256, H256> = NonCanonicalOverlay::new(&db).unwrap();
		assert_eq!(overlay.last_canonicalized, None);
		assert!(overlay.levels.is_empty());
		assert!(overlay.parents.is_empty());
	}

	#[test]
	#[should_panic]
	fn canonicalize_empty_panics() {
		let db = make_db(&[]);
		let mut overlay = NonCanonicalOverlay::<H256, H256>::new(&db).unwrap();
		overlay.canonicalize::<io::Error>(&H256::default()).unwrap();
	}

	#[test]
	#[should_panic]
	fn insert_ahead_panics() {
		let db = make_db(&[]);
		let h1 = H256::random();
		let h2 = H256::random();
		let mut overlay = NonCanonicalOverlay::<H256, H256>::new(&db).unwrap();
		overlay.insert::<io::Error>(&h1, 2, &H256::default(), ChangeSet::default()).unwrap();
		overlay.insert::<io::Error>(&h2, 1, &h1, ChangeSet::default()).unwrap();
	}

	#[test]
	#[should_panic]
	fn insert_behind_panics() {
		let h1 = H256::random();
		let h2 = H256::random();
		let db = make_db(&[]);
		let mut overlay = NonCanonicalOverlay::<H256, H256>::new(&db).unwrap();
		overlay.insert::<io::Error>(&h1, 1, &H256::default(), ChangeSet::default()).unwrap();
		overlay.insert::<io::Error>(&h2, 3, &h1, ChangeSet::default()).unwrap();
	}

	#[test]
	#[should_panic]
	fn insert_unknown_parent_panics() {
		let db = make_db(&[]);
		let h1 = H256::random();
		let h2 = H256::random();
		let mut overlay = NonCanonicalOverlay::<H256, H256>::new(&db).unwrap();
		overlay.insert::<io::Error>(&h1, 1, &H256::default(), ChangeSet::default()).unwrap();
		overlay.insert::<io::Error>(&h2, 2, &H256::default(), ChangeSet::default()).unwrap();
	}

	#[test]
	#[should_panic]
	fn canonicalize_unknown_panics() {
		let h1 = H256::random();
		let h2 = H256::random();
		let db = make_db(&[]);
		let mut overlay = NonCanonicalOverlay::<H256, H256>::new(&db).unwrap();
		overlay.insert::<io::Error>(&h1, 1, &H256::default(), ChangeSet::default()).unwrap();
		overlay.canonicalize::<io::Error>(&h2).unwrap();
	}

	#[test]
	fn insert_canonicalize_one() {
		let h1 = H256::random();
		let mut db = make_db(&[1, 2]);
		let mut overlay = NonCanonicalOverlay::<H256, H256>::new(&db).unwrap();
		let changeset = make_changeset(&[3, 4], &[2]);
		let insertion = overlay.insert::<io::Error>(&h1, 1, &H256::default(), changeset.clone()).unwrap();
		assert_eq!(insertion.data.inserted.len(), 0);
		assert_eq!(insertion.data.deleted.len(), 0);
		assert_eq!(insertion.meta.inserted.len(), 2);
		assert_eq!(insertion.meta.deleted.len(), 0);
		db.commit(&insertion);
		let finalization = overlay.canonicalize::<io::Error>(&h1).unwrap();
		assert_eq!(finalization.data.inserted.len(), changeset.inserted.len());
		assert_eq!(finalization.data.deleted.len(), changeset.deleted.len());
		assert_eq!(finalization.meta.inserted.len(), 1);
		assert_eq!(finalization.meta.deleted.len(), 1);
		db.commit(&finalization);
		assert!(db.data_eq(&make_db(&[1, 3, 4])));
	}

	#[test]
	fn restore_from_journal() {
		let h1 = H256::random();
		let h2 = H256::random();
		let mut db = make_db(&[1, 2]);
		let mut overlay = NonCanonicalOverlay::<H256, H256>::new(&db).unwrap();
		db.commit(&overlay.insert::<io::Error>(&h1, 10, &H256::default(), make_changeset(&[3, 4], &[2])).unwrap());
		db.commit(&overlay.insert::<io::Error>(&h2, 11, &h1, make_changeset(&[5], &[3])).unwrap());
		assert_eq!(db.meta.len(), 3);

		let overlay2 = NonCanonicalOverlay::<H256, H256>::new(&db).unwrap();
		assert_eq!(overlay.levels, overlay2.levels);
		assert_eq!(overlay.parents, overlay2.parents);
		assert_eq!(overlay.last_canonicalized, overlay2.last_canonicalized);
	}

	#[test]
	fn restore_from_journal_after_canonicalize() {
		let h1 = H256::random();
		let h2 = H256::random();
		let mut db = make_db(&[1, 2]);
		let mut overlay = NonCanonicalOverlay::<H256, H256>::new(&db).unwrap();
		db.commit(&overlay.insert::<io::Error>(&h1, 10, &H256::default(), make_changeset(&[3, 4], &[2])).unwrap());
		db.commit(&overlay.insert::<io::Error>(&h2, 11, &h1, make_changeset(&[5], &[3])).unwrap());
		db.commit(&overlay.canonicalize::<io::Error>(&h1).unwrap());
		overlay.apply_pending();
		assert_eq!(overlay.levels.len(), 1);

		let overlay2 = NonCanonicalOverlay::<H256, H256>::new(&db).unwrap();
		assert_eq!(overlay.levels, overlay2.levels);
		assert_eq!(overlay.parents, overlay2.parents);
		assert_eq!(overlay.last_canonicalized, overlay2.last_canonicalized);
	}

	#[test]
	fn insert_canonicalize_two() {
		let h1 = H256::random();
		let h2 = H256::random();
		let mut db = make_db(&[1, 2, 3, 4]);
		let mut overlay = NonCanonicalOverlay::<H256, H256>::new(&db).unwrap();
		let changeset1 = make_changeset(&[5, 6], &[2]);
		let changeset2 = make_changeset(&[7, 8], &[5, 3]);
		db.commit(&overlay.insert::<io::Error>(&h1, 1, &H256::default(), changeset1).unwrap());
		assert!(contains(&overlay, 5));
		db.commit(&overlay.insert::<io::Error>(&h2, 2, &h1, changeset2).unwrap());
		assert!(contains(&overlay, 7));
		assert!(contains(&overlay, 5));
		assert_eq!(overlay.levels.len(), 2);
		assert_eq!(overlay.parents.len(), 2);
		db.commit(&overlay.canonicalize::<io::Error>(&h1).unwrap());
		assert!(contains(&overlay, 5));
		assert_eq!(overlay.levels.len(), 2);
		assert_eq!(overlay.parents.len(), 2);
		overlay.apply_pending();
		assert_eq!(overlay.levels.len(), 1);
		assert_eq!(overlay.parents.len(), 1);
		assert!(!contains(&overlay, 5));
		assert!(contains(&overlay, 7));
		db.commit(&overlay.canonicalize::<io::Error>(&h2).unwrap());
		overlay.apply_pending();
		assert_eq!(overlay.levels.len(), 0);
		assert_eq!(overlay.parents.len(), 0);
		assert!(db.data_eq(&make_db(&[1, 4, 6, 7, 8])));
	}

	#[test]
	fn insert_same_key() {
		let mut db = make_db(&[]);
		let (h_1, c_1) = (H256::random(), make_changeset(&[1], &[]));
		let (h_2, c_2) = (H256::random(), make_changeset(&[1], &[]));

		let mut overlay = NonCanonicalOverlay::<H256, H256>::new(&db).unwrap();
		db.commit(&overlay.insert::<io::Error>(&h_1, 1, &H256::default(), c_1).unwrap());
		db.commit(&overlay.insert::<io::Error>(&h_2, 1, &H256::default(), c_2).unwrap());
		assert!(contains(&overlay, 1));
		db.commit(&overlay.canonicalize::<io::Error>(&h_1).unwrap());
		assert!(contains(&overlay, 1));
		overlay.apply_pending();
		assert!(!contains(&overlay, 1));
	}

	#[test]
	fn insert_with_pending_canonicalization() {
		let h1 = H256::random();
		let h2 = H256::random();
		let h3 = H256::random();
		let mut db = make_db(&[]);
		let mut overlay = NonCanonicalOverlay::<H256, H256>::new(&db).unwrap();
		let changeset = make_changeset(&[], &[]);
		db.commit(&overlay.insert::<io::Error>(&h1, 1, &H256::default(), changeset.clone()).unwrap());
		db.commit(&overlay.insert::<io::Error>(&h2, 2, &h1, changeset.clone()).unwrap());
		overlay.apply_pending();
		db.commit(&overlay.canonicalize::<io::Error>(&h1).unwrap());
		db.commit(&overlay.canonicalize::<io::Error>(&h2).unwrap());
		db.commit(&overlay.insert::<io::Error>(&h3, 3, &h2, changeset.clone()).unwrap());
		overlay.apply_pending();
		assert_eq!(overlay.levels.len(), 1);
	}

	#[test]
	fn complex_tree() {
		use crate::MetaDb;
		let mut db = make_db(&[]);

		// - 1 - 1_1 - 1_1_1
		//     \ 1_2 - 1_2_1
		//           \ 1_2_2
		//           \ 1_2_3
		//
		// - 2 - 2_1 - 2_1_1
		//     \ 2_2
		//
		// 1_2_2 is the winner

		let (h_1, c_1) = (H256::random(), make_changeset(&[1], &[]));
		let (h_2, c_2) = (H256::random(), make_changeset(&[2], &[]));

		let (h_1_1, c_1_1) = (H256::random(), make_changeset(&[11], &[]));
		let (h_1_2, c_1_2) = (H256::random(), make_changeset(&[12], &[]));
		let (h_2_1, c_2_1) = (H256::random(), make_changeset(&[21], &[]));
		let (h_2_2, c_2_2) = (H256::random(), make_changeset(&[22], &[]));

		let (h_1_1_1, c_1_1_1) = (H256::random(), make_changeset(&[111], &[]));
		let (h_1_2_1, c_1_2_1) = (H256::random(), make_changeset(&[121], &[]));
		let (h_1_2_2, c_1_2_2) = (H256::random(), make_changeset(&[122], &[]));
		let (h_1_2_3, c_1_2_3) = (H256::random(), make_changeset(&[123], &[]));
		let (h_2_1_1, c_2_1_1) = (H256::random(), make_changeset(&[211], &[]));

		let mut overlay = NonCanonicalOverlay::<H256, H256>::new(&db).unwrap();
		db.commit(&overlay.insert::<io::Error>(&h_1, 1, &H256::default(), c_1).unwrap());

		db.commit(&overlay.insert::<io::Error>(&h_1_1, 2, &h_1, c_1_1).unwrap());
		db.commit(&overlay.insert::<io::Error>(&h_1_2, 2, &h_1, c_1_2).unwrap());

		db.commit(&overlay.insert::<io::Error>(&h_2, 1, &H256::default(), c_2).unwrap());

		db.commit(&overlay.insert::<io::Error>(&h_2_1, 2, &h_2, c_2_1).unwrap());
		db.commit(&overlay.insert::<io::Error>(&h_2_2, 2, &h_2, c_2_2).unwrap());

		db.commit(&overlay.insert::<io::Error>(&h_1_1_1, 3, &h_1_1, c_1_1_1).unwrap());
		db.commit(&overlay.insert::<io::Error>(&h_1_2_1, 3, &h_1_2, c_1_2_1).unwrap());
		db.commit(&overlay.insert::<io::Error>(&h_1_2_2, 3, &h_1_2, c_1_2_2).unwrap());
		db.commit(&overlay.insert::<io::Error>(&h_1_2_3, 3, &h_1_2, c_1_2_3).unwrap());
		db.commit(&overlay.insert::<io::Error>(&h_2_1_1, 3, &h_2_1, c_2_1_1).unwrap());

		assert!(contains(&overlay, 2));
		assert!(contains(&overlay, 11));
		assert!(contains(&overlay, 21));
		assert!(contains(&overlay, 111));
		assert!(contains(&overlay, 122));
		assert!(contains(&overlay, 211));
		assert_eq!(overlay.levels.len(), 3);
		assert_eq!(overlay.parents.len(), 11);
		assert_eq!(overlay.last_canonicalized, Some((H256::default(), 0)));

		// check if restoration from journal results in the same tree
		let overlay2 = NonCanonicalOverlay::<H256, H256>::new(&db).unwrap();
		assert_eq!(overlay.levels, overlay2.levels);
		assert_eq!(overlay.parents, overlay2.parents);
		assert_eq!(overlay.last_canonicalized, overlay2.last_canonicalized);

		// canonicalize 1. 2 and all its children should be discarded
		db.commit(&overlay.canonicalize::<io::Error>(&h_1).unwrap());
		overlay.apply_pending();
		assert_eq!(overlay.levels.len(), 2);
		assert_eq!(overlay.parents.len(), 6);
		assert!(!contains(&overlay, 1));
		assert!(!contains(&overlay, 2));
		assert!(!contains(&overlay, 21));
		assert!(!contains(&overlay, 22));
		assert!(!contains(&overlay, 211));
		assert!(contains(&overlay, 111));
		assert!(!contains(&overlay, 211));
		// check that journals are deleted
		assert!(db.get_meta(&to_journal_key(1, 0)).unwrap().is_none());
		assert!(db.get_meta(&to_journal_key(1, 1)).unwrap().is_none());
		assert!(db.get_meta(&to_journal_key(2, 1)).unwrap().is_some());
		assert!(db.get_meta(&to_journal_key(2, 2)).unwrap().is_none());
		assert!(db.get_meta(&to_journal_key(2, 3)).unwrap().is_none());

		// canonicalize 1_2. 1_1 and all its children should be discarded
		db.commit(&overlay.canonicalize::<io::Error>(&h_1_2).unwrap());
		overlay.apply_pending();
		assert_eq!(overlay.levels.len(), 1);
		assert_eq!(overlay.parents.len(), 3);
		assert!(!contains(&overlay, 11));
		assert!(!contains(&overlay, 111));
		assert!(contains(&overlay, 121));
		assert!(contains(&overlay, 122));
		assert!(contains(&overlay, 123));
		assert!(overlay.have_block(&h_1_2_1));
		assert!(!overlay.have_block(&h_1_2));
		assert!(!overlay.have_block(&h_1_1));
		assert!(!overlay.have_block(&h_1_1_1));

		// canonicalize 1_2_2
		db.commit(&overlay.canonicalize::<io::Error>(&h_1_2_2).unwrap());
		overlay.apply_pending();
		assert_eq!(overlay.levels.len(), 0);
		assert_eq!(overlay.parents.len(), 0);
		assert!(db.data_eq(&make_db(&[1, 12, 122])));
		assert_eq!(overlay.last_canonicalized, Some((h_1_2_2, 3)));
	}

	#[test]
	fn insert_revert() {
		let h1 = H256::random();
		let h2 = H256::random();
		let mut db = make_db(&[1, 2, 3, 4]);
		let mut overlay = NonCanonicalOverlay::<H256, H256>::new(&db).unwrap();
		assert!(overlay.revert_one().is_none());
		let changeset1 = make_changeset(&[5, 6], &[2]);
		let changeset2 = make_changeset(&[7, 8], &[5, 3]);
		db.commit(&overlay.insert::<io::Error>(&h1, 1, &H256::default(), changeset1).unwrap());
		db.commit(&overlay.insert::<io::Error>(&h2, 2, &h1, changeset2).unwrap());
		assert!(contains(&overlay, 7));
		db.commit(&overlay.revert_one().unwrap());
		assert_eq!(overlay.parents.len(), 1);
		assert!(contains(&overlay, 5));
		assert!(!contains(&overlay, 7));
		db.commit(&overlay.revert_one().unwrap());
		assert_eq!(overlay.levels.len(), 0);
		assert_eq!(overlay.parents.len(), 0);
		assert!(overlay.revert_one().is_none());
	}

	#[test]
	fn revert_pending_insertion() {
		let h1 = H256::random();
		let h2_1 = H256::random();
		let h2_2 = H256::random();
		let db = make_db(&[]);
		let mut overlay = NonCanonicalOverlay::<H256, H256>::new(&db).unwrap();
		let changeset1 = make_changeset(&[5, 6], &[2]);
		let changeset2 = make_changeset(&[7, 8], &[5, 3]);
		let changeset3 = make_changeset(&[9], &[]);
		overlay.insert::<io::Error>(&h1, 1, &H256::default(), changeset1).unwrap();
		assert!(contains(&overlay, 5));
		overlay.insert::<io::Error>(&h2_1, 2, &h1, changeset2).unwrap();
		overlay.insert::<io::Error>(&h2_2, 2, &h1, changeset3).unwrap();
		assert!(contains(&overlay, 7));
		assert!(contains(&overlay, 5));
		assert!(contains(&overlay, 9));
		assert_eq!(overlay.levels.len(), 2);
		assert_eq!(overlay.parents.len(), 3);
		overlay.revert_pending();
		assert!(!contains(&overlay, 5));
		assert_eq!(overlay.levels.len(), 0);
		assert_eq!(overlay.parents.len(), 0);
	}
}

