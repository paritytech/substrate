// Copyright 2017 Parity Technologies (UK) Ltd.
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
//! Last canonicalized overlay is kept in memory until next call to `canonicalize` or
//! `clear_overlay`

use std::collections::{HashMap, VecDeque};
use super::{Error, DBValue, ChangeSet, CommitSet, MetaDb, Hash, to_meta_key};
use codec::{Decode, Encode};

const NON_CANONICAL_JOURNAL: &[u8] = b"noncanonical_journal";
const LAST_CANONICAL: &[u8] = b"last_canonical";

/// See module documentation.
pub struct NonCanonicalOverlay<BlockHash: Hash, Key: Hash> {
	last_canonicalized: Option<(BlockHash, u64)>,
	levels: VecDeque<Vec<BlockOverlay<BlockHash, Key>>>,
	parents: HashMap<BlockHash, BlockHash>,
	last_canonicalized_overlay: HashMap<Key, DBValue>,
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
	values: HashMap<Key, DBValue>,
	deleted: Vec<Key>,
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
							let overlay = BlockOverlay {
								hash: record.hash.clone(),
								journal_key,
								values: record.inserted.into_iter().collect(),
								deleted: record.deleted,
							};
							trace!(target: "state-db", "Uncanonicalized journal entry {}.{} ({} inserted, {} deleted)", block, index, overlay.values.len(), overlay.deleted.len());
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
			last_canonicalized_overlay: Default::default(),
		})
	}

	/// Insert a new block into the overlay. If inserted on the second level or lover expects parent to be present in the window.
	pub fn insert(&mut self, hash: &BlockHash, number: u64, parent_hash: &BlockHash, changeset: ChangeSet<Key>) -> CommitSet<Key> {
		let mut commit = CommitSet::default();
		if self.levels.is_empty() && self.last_canonicalized.is_none() {
			// assume that parent was canonicalized
			let last_canonicalized = (parent_hash.clone(), number - 1);
			commit.meta.inserted.push((to_meta_key(LAST_CANONICAL, &()), last_canonicalized.encode()));
			self.last_canonicalized = Some(last_canonicalized);
		} else if self.last_canonicalized.is_some() {
			assert!(number >= self.front_block_number() && number < (self.front_block_number() + self.levels.len() as u64 + 1));
			// check for valid parent if inserting on second level or higher
			if number == self.front_block_number() {
				assert!(self.last_canonicalized.as_ref().map_or(false, |&(ref h, n)| h == parent_hash && n == number - 1));
			} else {
				assert!(self.parents.contains_key(&parent_hash));
			}
		}
		let level = if self.levels.is_empty() || number == self.front_block_number() + self.levels.len() as u64 {
			self.levels.push_back(Vec::new());
			self.levels.back_mut().expect("can't be empty after insertion; qed")
		} else {
			let front_block_number = self.front_block_number();
			self.levels.get_mut((number - front_block_number) as usize)
				.expect("number is [front_block_number .. front_block_number + levels.len()) is asserted in precondition; qed")
		};

		let index = level.len() as u64;
		let journal_key = to_journal_key(number, index);

		let overlay = BlockOverlay {
			hash: hash.clone(),
			journal_key: journal_key.clone(),
			values: changeset.inserted.iter().cloned().collect(),
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
		trace!(target: "state-db", "Inserted uncanonicalized changeset {}.{} ({} inserted, {} deleted)", number, index, journal_record.inserted.len(), journal_record.deleted.len());
		let journal_record = journal_record.encode();
		commit.meta.inserted.push((journal_key, journal_record));
		commit
	}

	fn discard(
		levels: &mut [Vec<BlockOverlay<BlockHash, Key>>],
		parents: &mut HashMap<BlockHash, BlockHash>,
		discarded_journals: &mut Vec<Vec<u8>>,
		number: u64,
		hash: &BlockHash,
	) {
		if let Some((level, sublevels)) = levels.split_first_mut() {
			level.retain(|ref overlay| {
				let parent = parents.get(&overlay.hash).expect("there is a parent entry for each entry in levels; qed").clone();
				if parent == *hash {
					parents.remove(&overlay.hash);
					discarded_journals.push(overlay.journal_key.clone());
					Self::discard(sublevels, parents, discarded_journals, number + 1, &overlay.hash);
					false
				} else {
					true
				}
			});
		}
	}

	fn front_block_number(&self) -> u64 {
		self.last_canonicalized.as_ref().map(|&(_, n)| n + 1).unwrap_or(0)
	}

	pub fn last_canonicalized_block_number(&self) -> u64 {
		self.last_canonicalized.as_ref().map(|&(_, n)| n).unwrap_or(0)
	}

	/// This may be called when the last finalization commit was applied to the database.
	pub fn clear_overlay(&mut self) {
		self.last_canonicalized_overlay.clear();
	}

	/// Select a top-level root and canonicalized it. Discards all sibling subtrees and the root.
	/// Returns a set of changes that need to be added to the DB.
	pub fn canonicalize(&mut self, hash: &BlockHash) -> CommitSet<Key> {
		trace!(target: "state-db", "Canonicalizing {:?}", hash);
		let level = self.levels.pop_front().expect("no blocks to canonicalize");
		let index = level.iter().position(|overlay| overlay.hash == *hash)
			.expect("attempting to canonicalize unknown block");

		let mut commit = CommitSet::default();
		let mut discarded_journals = Vec::new();
		for (i, overlay) in level.into_iter().enumerate() {
			self.parents.remove(&overlay.hash);
			if i == index {
				self.last_canonicalized_overlay = overlay.values;
				// that's the one we need to canonicalize
				commit.data.inserted = self.last_canonicalized_overlay.iter().map(|(k, v)| (k.clone(), v.clone())).collect();
				commit.data.deleted = overlay.deleted;
			} else {
				// TODO: borrow checker won't allow us to split out mutable references
				// required for recursive processing. A more efficient implementation
				// that does not require converting to vector is possible
				let mut vec: Vec<_> = self.levels.drain(..).collect();
				Self::discard(&mut vec, &mut self.parents, &mut discarded_journals, 0, &overlay.hash);
				self.levels.extend(vec.into_iter());
			}
			// cleanup journal entry
			discarded_journals.push(overlay.journal_key);
		}
		commit.meta.deleted.append(&mut discarded_journals);
		let last_canonicalized = (hash.clone(), self.front_block_number());
		commit.meta.inserted.push((to_meta_key(LAST_CANONICAL, &()), last_canonicalized.encode()));
		self.last_canonicalized = Some(last_canonicalized);
		trace!(target: "state-db", "Discarded {} records", commit.meta.deleted.len());
		commit
	}

	/// Get a value from the node overlay. This searches in every existing changeset.
	pub fn get(&self, key: &Key) -> Option<DBValue> {
		if let Some(value) = self.last_canonicalized_overlay.get(&key) {
			return Some(value.clone());
		}
		for level in self.levels.iter() {
			for overlay in level.iter() {
				if let Some(value) = overlay.values.get(&key) {
					return Some(value.clone());
				}
			}
		}
		None
	}

	/// Revert a single level. Returns commit set that deletes the journal or `None` if not possible.
	pub fn revert_one(&mut self) -> Option<CommitSet<Key>> {
		self.levels.pop_back().map(|level| {
			let mut commit = CommitSet::default();
			for overlay in level.into_iter() {
				commit.meta.deleted.push(overlay.journal_key);
				self.parents.remove(&overlay.hash);
			}
			commit
		})
	}
}

#[cfg(test)]
mod tests {
	use super::NonCanonicalOverlay;
	use {ChangeSet};
	use primitives::H256;
	use test::{make_db, make_changeset};

	fn contains(overlay: &NonCanonicalOverlay<H256, H256>, key: u64) -> bool {
		overlay.get(&H256::from(key)) == Some(H256::from(key).to_vec())
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
		overlay.canonicalize(&H256::default());
	}

	#[test]
	#[should_panic]
	fn insert_ahead_panics() {
		let db = make_db(&[]);
		let h1 = H256::random();
		let h2 = H256::random();
		let mut overlay = NonCanonicalOverlay::<H256, H256>::new(&db).unwrap();
		overlay.insert(&h1, 2, &H256::default(), ChangeSet::default());
		overlay.insert(&h2, 1, &h1, ChangeSet::default());
	}

	#[test]
	#[should_panic]
	fn insert_behind_panics() {
		let h1 = H256::random();
		let h2 = H256::random();
		let db = make_db(&[]);
		let mut overlay = NonCanonicalOverlay::<H256, H256>::new(&db).unwrap();
		overlay.insert(&h1, 1, &H256::default(), ChangeSet::default());
		overlay.insert(&h2, 3, &h1, ChangeSet::default());
	}

	#[test]
	#[should_panic]
	fn insert_unknown_parent_panics() {
		let db = make_db(&[]);
		let h1 = H256::random();
		let h2 = H256::random();
		let mut overlay = NonCanonicalOverlay::<H256, H256>::new(&db).unwrap();
		overlay.insert(&h1, 1, &H256::default(), ChangeSet::default());
		overlay.insert(&h2, 2, &H256::default(), ChangeSet::default());
	}

	#[test]
	#[should_panic]
	fn canonicalize_unknown_panics() {
		let h1 = H256::random();
		let h2 = H256::random();
		let db = make_db(&[]);
		let mut overlay = NonCanonicalOverlay::<H256, H256>::new(&db).unwrap();
		overlay.insert(&h1, 1, &H256::default(), ChangeSet::default());
		overlay.canonicalize(&h2);
	}

	#[test]
	fn insert_canonicalize_one() {
		let h1 = H256::random();
		let mut db = make_db(&[1, 2]);
		let mut overlay = NonCanonicalOverlay::<H256, H256>::new(&db).unwrap();
		let changeset = make_changeset(&[3, 4], &[2]);
		let insertion = overlay.insert(&h1, 1, &H256::default(), changeset.clone());
		assert_eq!(insertion.data.inserted.len(), 0);
		assert_eq!(insertion.data.deleted.len(), 0);
		assert_eq!(insertion.meta.inserted.len(), 2);
		assert_eq!(insertion.meta.deleted.len(), 0);
		db.commit(&insertion);
		let finalization = overlay.canonicalize(&h1);
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
		db.commit(&overlay.insert(&h1, 10, &H256::default(), make_changeset(&[3, 4], &[2])));
		db.commit(&overlay.insert(&h2, 11, &h1, make_changeset(&[5], &[3])));
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
		db.commit(&overlay.insert(&h1, 10, &H256::default(), make_changeset(&[3, 4], &[2])));
		db.commit(&overlay.insert(&h2, 11, &h1, make_changeset(&[5], &[3])));
		db.commit(&overlay.canonicalize(&h1));
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
		db.commit(&overlay.insert(&h1, 1, &H256::default(), changeset1));
		assert!(contains(&overlay, 5));
		db.commit(&overlay.insert(&h2, 2, &h1, changeset2));
		assert!(contains(&overlay, 7));
		assert!(contains(&overlay, 5));
		assert_eq!(overlay.levels.len(), 2);
		assert_eq!(overlay.parents.len(), 2);
		db.commit(&overlay.canonicalize(&h1));
		assert_eq!(overlay.levels.len(), 1);
		assert_eq!(overlay.parents.len(), 1);
		assert!(contains(&overlay, 5));
		overlay.clear_overlay();
		assert!(!contains(&overlay, 5));
		assert!(contains(&overlay, 7));
		db.commit(&overlay.canonicalize(&h2));
		overlay.clear_overlay();
		assert_eq!(overlay.levels.len(), 0);
		assert_eq!(overlay.parents.len(), 0);
		assert!(db.data_eq(&make_db(&[1, 4, 6, 7, 8])));
	}


	#[test]
	fn complex_tree() {
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
		db.commit(&overlay.insert(&h_1, 1, &H256::default(), c_1));

		db.commit(&overlay.insert(&h_1_1, 2, &h_1, c_1_1));
		db.commit(&overlay.insert(&h_1_2, 2, &h_1, c_1_2));

		db.commit(&overlay.insert(&h_2, 1, &H256::default(), c_2));

		db.commit(&overlay.insert(&h_2_1, 2, &h_2, c_2_1));
		db.commit(&overlay.insert(&h_2_2, 2, &h_2, c_2_2));

		db.commit(&overlay.insert(&h_1_1_1, 3, &h_1_1, c_1_1_1));
		db.commit(&overlay.insert(&h_1_2_1, 3, &h_1_2, c_1_2_1));
		db.commit(&overlay.insert(&h_1_2_2, 3, &h_1_2, c_1_2_2));
		db.commit(&overlay.insert(&h_1_2_3, 3, &h_1_2, c_1_2_3));
		db.commit(&overlay.insert(&h_2_1_1, 3, &h_2_1, c_2_1_1));

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
		db.commit(&overlay.canonicalize(&h_1));
		overlay.clear_overlay();
		assert_eq!(overlay.levels.len(), 2);
		assert_eq!(overlay.parents.len(), 6);
		assert!(!contains(&overlay, 1));
		assert!(!contains(&overlay, 2));
		assert!(!contains(&overlay, 21));
		assert!(!contains(&overlay, 22));
		assert!(!contains(&overlay, 211));
		assert!(contains(&overlay, 111));

		// canonicalize 1_2. 1_1 and all its children should be discarded
		db.commit(&overlay.canonicalize(&h_1_2));
		overlay.clear_overlay();
		assert_eq!(overlay.levels.len(), 1);
		assert_eq!(overlay.parents.len(), 3);
		assert!(!contains(&overlay, 11));
		assert!(!contains(&overlay, 111));
		assert!(contains(&overlay, 121));
		assert!(contains(&overlay, 122));
		assert!(contains(&overlay, 123));

		// canonicalize 1_2_2
		db.commit(&overlay.canonicalize(&h_1_2_2));
		overlay.clear_overlay();
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
		db.commit(&overlay.insert(&h1, 1, &H256::default(), changeset1));
		db.commit(&overlay.insert(&h2, 2, &h1, changeset2));
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

}

