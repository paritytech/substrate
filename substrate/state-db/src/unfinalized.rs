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

use std::collections::{HashMap, VecDeque};
use super::{Error, DBValue, Changeset, KeyValueDb, to_key};
use codec::{self, Slicable};
use primitives::H256;

const UNFINALIZED_JOURNAL: &[u8] = b"unfinalized_journal";
const LAST_UNFINALIZED: &[u8] = b"last_unfinalized";

pub struct UnfinalizedOverlay {
	front_block_number: u64,
	levels: VecDeque<Vec<BlockOverlay>>,
	parents: HashMap<H256, H256>,
}

struct JournalRecord {
	hash: H256,
	parent_hash: H256,
	inserted: Vec<(H256, DBValue)>,
	deleted: Vec<H256>,
}

impl Slicable for JournalRecord {
	fn encode(&self) -> Vec<u8> {
		let mut v = Vec::with_capacity(4096);
		self.hash.using_encoded(|s| v.extend(s));
		self.parent_hash.using_encoded(|s| v.extend(s));
		self.inserted.using_encoded(|s| v.extend(s));
		self.deleted.using_encoded(|s| v.extend(s));
		v
	}

	fn decode<I: codec::Input>(input: &mut I) -> Option<Self> {
		Some(JournalRecord {
			hash: Slicable::decode(input)?,
			parent_hash: Slicable::decode(input)?,
			inserted: Slicable::decode(input)?,
			deleted: Slicable::decode(input)?,
		})
	}
}

fn to_journal_key(block: u64, index: u64) -> H256 {
	to_key(UNFINALIZED_JOURNAL, &(block, index))
}

struct BlockOverlay {
	hash: H256,
	journal_key: H256,
	values: HashMap<H256, DBValue>,
	deleted: Vec<H256>,
}

impl UnfinalizedOverlay {
	pub fn new<D: KeyValueDb>(db: &D) -> Result<UnfinalizedOverlay, Error<D>> {
		let first_unfinalized = db.get(&to_key(LAST_UNFINALIZED, &()))
			.map_err(|e| Error::Db(e))?;
		let first_unfinalized: u64 = match first_unfinalized {
			Some(buffer) => Slicable::decode(&mut buffer.as_slice()).ok_or(Error::Decoding)?,
			None => 0,
		};
		let mut levels = VecDeque::new();
		let mut parents = HashMap::new();
		let mut block = first_unfinalized;
		// read the journal
		loop {
			let mut index: u64 = 0;
			let mut level = Vec::new();
			loop {
				let journal_key = to_journal_key(block, index);
				match db.get(&journal_key).map_err(|e| Error::Db(e))? {
					Some(record) => {
						let record: JournalRecord = Slicable::decode(&mut record.as_slice()).ok_or(Error::Decoding)?;
						let overlay = BlockOverlay {
							hash: record.hash,
							journal_key,
							values: record.inserted.into_iter().collect(),
							deleted: record.deleted,
						};
						level.push(overlay);
						parents.insert(record.hash, record.parent_hash);
						index += 1;
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
		Ok(UnfinalizedOverlay {
			front_block_number: first_unfinalized,
			levels,
			parents,
		})
	}

	pub fn insert(&mut self, hash: &H256, number: u64, parent_hash: &H256, changeset: Changeset) -> Changeset {
		if self.levels.is_empty() {
			self.front_block_number = number;
		} else {
			assert!(number >= self.front_block_number && number < (self.front_block_number + self.levels.len() as u64 + 1));
			// check for valid parent if inserting on second level or higher
			assert!(number == self.front_block_number || self.parents.contains_key(&parent_hash));
		}
		let level = if self.levels.is_empty() || number == self.front_block_number + self.levels.len() as u64 {
			self.levels.push_back(Vec::new());
			self.levels.back_mut().expect("can't be empty after insertion; qed")
		} else {
			self.levels.get_mut((number - self.front_block_number) as usize)
				.expect("number is [self.front_block_number .. self.front_block_number + levels.len()) is asserted in precondition; qed")
		};

		let index = level.len() as u64;
		let journal_key = to_journal_key(number, index);

		let overlay = BlockOverlay {
			hash: *hash,
			journal_key,
			values: changeset.inserted.iter().cloned().collect(),
			deleted: changeset.deleted.clone(),
		};
		level.push(overlay);
		self.parents.insert(*hash, *parent_hash);
		let journal_record = JournalRecord {
			hash: *hash,
			parent_hash: *parent_hash,
			inserted: changeset.inserted,
			deleted: changeset.deleted,
		};
		let journal_record = journal_record.encode();
		let journal_changeset = Changeset {
			inserted: vec![(journal_key, journal_record)],
			deleted: Default::default(),
		};
		journal_changeset
	}

	fn discard(
		levels: &mut [Vec<BlockOverlay>],
		parents: &mut HashMap<H256, H256>,
		discarded_journals: &mut Vec<H256>,
		number: u64,
		hash: &H256,
	) {
		if let Some((level, sublevels)) = levels.split_first_mut() {
			level.retain(|ref overlay| {
				let parent = *parents.get(&overlay.hash).expect("there is a parent entry for each entry in levels; qed");
				if parent == *hash {
					println!("delete");
					parents.remove(&overlay.hash);
					discarded_journals.push(overlay.journal_key);
					Self::discard(sublevels, parents, discarded_journals, number + 1, &overlay.hash);
					false
				} else {
					println!("keep");
					true
				}
			});
		}
	}

	pub fn finalize(&mut self, hash: &H256) -> Changeset {
		let level = self.levels.pop_front().expect("no blocks to finalize");
		let index = level.iter().position(|overlay| overlay.hash == *hash)
			.expect("attempting to finalize unknown block");

		let mut changeset = Changeset::default();
		let mut discarded_journals = Vec::new();
		for (i, overlay) in level.into_iter().enumerate() {
			self.parents.remove(&overlay.hash);
			if i == index {
				// that's the one we need to finalize
				changeset.inserted = overlay.values.into_iter().collect();
				changeset.deleted = overlay.deleted;
			} else {
				// TODO: borrow checker won't allow us to split out mutable refernces
				// required for recursive processing. A more efficient implementaion
				// that does not require converting to vector is possible
				let mut vec: Vec<_> = self.levels.drain(..).collect();
				Self::discard(&mut vec, &mut self.parents, &mut discarded_journals, 0, &overlay.hash);
				self.levels.extend(vec.into_iter());
			}
			// cleanup journal entry
			discarded_journals.push(overlay.journal_key);
		}
		changeset.deleted.append(&mut discarded_journals);
		self.front_block_number += 1;
		changeset
	}

	pub fn get(&self, key: &H256) -> Option<DBValue> {
		for level in self.levels.iter() {
			for overlay in level.iter() {
				if let Some(value) = overlay.values.get(&key) {
					return Some(value.clone());
				}
			}
		}
		None
	}
}

#[cfg(test)]
mod tests {
	use std::collections::HashMap;
	use super::UnfinalizedOverlay;
	use {DBValue, Changeset, to_key};
	use primitives::H256;

	fn make_changeset(inserted: &[u64], deleted: &[u64]) -> Changeset {
		Changeset {
			inserted: inserted.iter().map(|v| (to_key(b"test", v), to_key(b"value", v).to_vec())).collect(),
			deleted: deleted.iter().map(|v| to_key(b"test", v)).collect(),
		}
	}

	fn make_db(inserted: &[u64]) -> HashMap<H256, DBValue> {
		inserted.iter().map(|v| (to_key(b"test", v), to_key(b"value", v).to_vec())).collect()
	}

	fn apply_changeset(db: &mut HashMap<H256, DBValue>, changeset: &Changeset) {
		db.extend(changeset.inserted.iter().cloned());
		for k in changeset.deleted.iter() {
			db.remove(k);
		}
	}

	fn contains(overlay: &UnfinalizedOverlay, key: u64) -> bool {
		overlay.get(&to_key(b"test", &key)) == Some(to_key(b"value", &key).to_vec())
	}

	#[test]
	fn created_from_empty_db() {
		let db = HashMap::new();
		let overlay = UnfinalizedOverlay::new(&db).unwrap();
		assert_eq!(overlay.front_block_number, 0);
		assert!(overlay.levels.is_empty());
		assert!(overlay.parents.is_empty());
	}

	#[test]
	#[should_panic]
	fn finalize_empty_panics() {
		let db = HashMap::new();
		let mut overlay = UnfinalizedOverlay::new(&db).unwrap();
		overlay.finalize(&H256::default());
	}

	#[test]
	#[should_panic]
	fn insert_ahead_panics() {
		let db = HashMap::new();
		let h1 = H256::random();
		let h2 = H256::random();
		let mut overlay = UnfinalizedOverlay::new(&db).unwrap();
		overlay.insert(&h1, 2, &H256::default(), Changeset::default());
		overlay.insert(&h2, 1, &h1, Changeset::default());
	}

	#[test]
	#[should_panic]
	fn insert_behind_panics() {
		let h1 = H256::random();
		let h2 = H256::random();
		let db = HashMap::new();
		let mut overlay = UnfinalizedOverlay::new(&db).unwrap();
		overlay.insert(&h1, 1, &H256::default(), Changeset::default());
		overlay.insert(&h2, 3, &h1, Changeset::default());
	}

	#[test]
	#[should_panic]
	fn insert_unknown_parent_panics() {
		let db = HashMap::new();
		let h1 = H256::random();
		let h2 = H256::random();
		let mut overlay = UnfinalizedOverlay::new(&db).unwrap();
		overlay.insert(&h1, 1, &H256::default(), Changeset::default());
		overlay.insert(&h2, 2, &H256::default(), Changeset::default());
	}

	#[test]
	#[should_panic]
	fn finalize_unknown_panics() {
		let h1 = H256::random();
		let h2 = H256::random();
		let db = HashMap::new();
		let mut overlay = UnfinalizedOverlay::new(&db).unwrap();
		overlay.insert(&h1, 1, &H256::default(), Changeset::default());
		overlay.finalize(&h2);
	}

	#[test]
	fn insert_finalize_one() {
		let h1 = H256::random();
		let mut db = make_db(&[1, 2]);
		let mut overlay = UnfinalizedOverlay::new(&db).unwrap();
		let changeset = make_changeset(&[3, 4], &[2]);
		let insertion = overlay.insert(&h1, 1, &H256::default(), changeset.clone());
		assert_eq!(insertion.inserted.len(), 1);
		assert_eq!(insertion.deleted.len(), 0);
		apply_changeset(&mut db, &insertion);
		let finalization = overlay.finalize(&h1);
		assert_eq!(finalization.inserted.len(), changeset.inserted.len());
		assert_eq!(finalization.deleted.len(), changeset.deleted.len() + 1);
		apply_changeset(&mut db, &finalization);
		assert_eq!(db, make_db(&[1, 3, 4]));
	}

	#[test]
	fn insert_finalize_two() {
		let h1 = H256::random();
		let h2 = H256::random();
		let mut db = make_db(&[1, 2, 3, 4]);
		let mut overlay = UnfinalizedOverlay::new(&db).unwrap();
		let changeset1 = make_changeset(&[5, 6], &[2]);
		let changeset2 = make_changeset(&[7, 8], &[5, 3]);
		apply_changeset(&mut db, &overlay.insert(&h1, 1, &H256::default(), changeset1));
		assert!(contains(&overlay, 5));
		apply_changeset(&mut db, &overlay.insert(&h2, 2, &h1, changeset2));
		assert!(contains(&overlay, 7));
		assert!(contains(&overlay, 5));
		assert_eq!(overlay.levels.len(), 2);
		assert_eq!(overlay.parents.len(), 2);
		apply_changeset(&mut db, &overlay.finalize(&h1));
		assert_eq!(overlay.levels.len(), 1);
		assert_eq!(overlay.parents.len(), 1);
		assert!(!contains(&overlay, 5));
		assert!(contains(&overlay, 7));
		apply_changeset(&mut db, &overlay.finalize(&h2));
		assert_eq!(overlay.levels.len(), 0);
		assert_eq!(overlay.parents.len(), 0);
		assert_eq!(db, make_db(&[1, 4, 6, 7, 8]));
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

		let mut overlay = UnfinalizedOverlay::new(&db).unwrap();
		apply_changeset(&mut db, &overlay.insert(&h_1, 1, &H256::default(), c_1));

		apply_changeset(&mut db, &overlay.insert(&h_1_1, 2, &h_1, c_1_1));
		apply_changeset(&mut db, &overlay.insert(&h_1_2, 2, &h_1, c_1_2));

		apply_changeset(&mut db, &overlay.insert(&h_2, 1, &H256::default(), c_2));

		apply_changeset(&mut db, &overlay.insert(&h_2_1, 2, &h_2, c_2_1));
		apply_changeset(&mut db, &overlay.insert(&h_2_2, 2, &h_2, c_2_2));

		apply_changeset(&mut db, &overlay.insert(&h_1_1_1, 3, &h_1_1, c_1_1_1));
		apply_changeset(&mut db, &overlay.insert(&h_1_2_1, 3, &h_1_2, c_1_2_1));
		apply_changeset(&mut db, &overlay.insert(&h_1_2_2, 3, &h_1_2, c_1_2_2));
		apply_changeset(&mut db, &overlay.insert(&h_1_2_3, 3, &h_1_2, c_1_2_3));
		apply_changeset(&mut db, &overlay.insert(&h_2_1_1, 3, &h_2_1, c_2_1_1));

		assert!(contains(&overlay, 2));
		assert!(contains(&overlay, 11));
		assert!(contains(&overlay, 21));
		assert!(contains(&overlay, 111));
		assert!(contains(&overlay, 122));
		assert!(contains(&overlay, 211));
		assert_eq!(overlay.levels.len(), 3);
		assert_eq!(overlay.parents.len(), 11);

		// finalize 1. 2 and all its children should be discarded
		apply_changeset(&mut db, &overlay.finalize(&h_1));
		assert_eq!(overlay.levels.len(), 2);
		assert_eq!(overlay.parents.len(), 6);
		assert!(!contains(&overlay, 1));
		assert!(!contains(&overlay, 2));
		assert!(!contains(&overlay, 21));
		assert!(!contains(&overlay, 22));
		assert!(!contains(&overlay, 211));
		assert!(contains(&overlay, 111));

		// finalize 1_2. 1_1 and all its children should be discarded
		apply_changeset(&mut db, &overlay.finalize(&h_1_2));
		assert_eq!(overlay.levels.len(), 1);
		assert_eq!(overlay.parents.len(), 3);
		assert!(!contains(&overlay, 11));
		assert!(!contains(&overlay, 111));
		assert!(contains(&overlay, 121));
		assert!(contains(&overlay, 122));
		assert!(contains(&overlay, 123));

		// finalize 1_2_2
		apply_changeset(&mut db, &overlay.finalize(&h_1_2_2));
		assert_eq!(overlay.levels.len(), 0);
		assert_eq!(overlay.parents.len(), 0);
		assert_eq!(db, make_db(&[1, 12, 122]));
	}
}
