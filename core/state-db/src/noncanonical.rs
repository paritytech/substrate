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
use std::collections::{HashMap, VecDeque, hash_map::Entry, HashSet};
use super::{
	Error, DBValue, ChangeSet, OffstateChangeSet, CommitSet, MetaDb, Hash,
	to_meta_key, OffstateKey,
};
use codec::{Encode, Decode};
use log::trace;
use crate::branch::{RangeSet, BranchRanges};
use historied_data::tree::History;

const NON_CANONICAL_JOURNAL: &[u8] = b"noncanonical_journal";
const NON_CANONICAL_OFFSTATE_JOURNAL: &[u8] = b"offstate_noncanonical_journal";
const LAST_CANONICAL: &[u8] = b"last_canonical";

type BranchIndex = u64;

type BlockNumber = u64;

type GcIndex = u64;

/// See module documentation.
pub struct NonCanonicalOverlay<BlockHash: Hash, Key: Hash> {
	last_canonicalized: Option<(BlockHash, BlockNumber)>,
	levels: VecDeque<Vec<BlockOverlay<BlockHash, Key>>>,
	parents: HashMap<BlockHash, (BlockHash, BranchIndex)>,
	pending_canonicalizations: Vec<BlockHash>,
	pending_insertions: Vec<BlockHash>,
	values: HashMap<Key, (u32, DBValue)>, //ref counted
	branches: RangeSet,
	offstate_values: HashMap<OffstateKey, History<Option<DBValue>>>,
	/// second value is offstate pinned index: used in order to determine if the pinned 
	/// thread should block garbage collection.
	pinned: HashMap<BlockHash, (HashMap<Key, DBValue>, GcIndex)>,
	offstate_gc: OffstatePendingGC,
}

#[derive(Default)]
/// offstate gc only happen when all pinned threads that where
/// running at the time of cannonicalisation are finished.
struct OffstatePendingGC {
	/// Each gc call uses a new index.
	gc_last_index: GcIndex,
	/// Keep trace of last cannonicalization branch index height.
	/// All data in state are added after this value (branch is
	/// set as non modifiable on canonicalisation).
  pending_canonicalisation_query: Option<u64>,
	/// keys to gc that got their journal removed.
	keys_pending_gc: HashSet<OffstateKey>,
	/// store keys while waiting for a gc.
	next_keys_pending_gc: HashSet<OffstateKey>,
}

impl OffstatePendingGC {
	fn set_pending_gc(&mut self, branch_index: u64) {
		self.gc_last_index += 1;
		if self.pending_canonicalisation_query.is_some() {
			// TODO EMCH some better merge
			self.keys_pending_gc.extend(self.next_keys_pending_gc.drain());
		}
		self.pending_canonicalisation_query = Some(branch_index);
	}

	fn try_gc<K, V>(
		&mut self,
		offstate_values: &mut HashMap<OffstateKey, History<Option<DBValue>>>,
		branches: &RangeSet,
		pinned: &HashMap<K, (V, u64)>,
	) {
		if let Some(pending) = self.pending_canonicalisation_query {
			if pending < self.min_pinned_index(pinned) {

				// TODO EMCH double get is rather inefficient, see if it is possible
				// to reuse the hash of the hashset into the hashmap
				for key in self.keys_pending_gc.drain() {
					match offstate_values.get_mut(&key).map(|historied_value| {
						historied_value.gc(branches.reverse_iter_ranges())
					}) {
						Some(historied_data::PruneResult::Cleared) => {
							let _ = offstate_values.remove(&key);
						},
						_ => (),
					}
				}

				self.pending_canonicalisation_query = None;
			}
		}
	}

	fn min_pinned_index<K, V>(
		&self,
		pinned: &HashMap<K, (V, u64)>,
	) -> u64 {
		let mut min = u64::max_value();
		// global min
		for (_, (_, index)) in pinned.iter() {
			if *index < min {
				min = *index;
			}
		}
		min
	}

}

#[derive(Encode, Decode)]
struct JournalRecord<BlockHash: Hash, Key: Hash> {
	hash: BlockHash,
	parent_hash: BlockHash,
	inserted: Vec<(Key, DBValue)>,
	deleted: Vec<Key>,
}

#[derive(Encode, Decode)]
struct OffstateJournalRecord {
	inserted: Vec<(OffstateKey, DBValue)>,
	deleted: Vec<OffstateKey>,
}

fn to_journal_key(block: BlockNumber, index: u64) -> Vec<u8> {
	to_meta_key(NON_CANONICAL_JOURNAL, &(block, index))
}

fn to_offstate_journal_key(block: BlockNumber, index: u64) -> Vec<u8> {
	to_meta_key(NON_CANONICAL_OFFSTATE_JOURNAL, &(block, index))
}

#[cfg_attr(test, derive(PartialEq, Debug))]
struct BlockOverlay<BlockHash: Hash, Key: Hash> {
	hash: BlockHash,
	journal_key: Vec<u8>,
	offstate_journal_key: Vec<u8>,
	inserted: Vec<Key>,
	deleted: Vec<Key>,
	offstate_inserted: Vec<OffstateKey>,
	offstate_deleted: Vec<OffstateKey>,
}

fn insert_values<Key: Hash>(values: &mut HashMap<Key, (u32, DBValue)>, inserted: Vec<(Key, DBValue)>) {
	for (k, v) in inserted {
		debug_assert!(values.get(&k).map_or(true, |(_, value)| *value == v));
		let (ref mut counter, _) = values.entry(k).or_insert_with(|| (0, v));
		*counter += 1;
	}
}

fn insert_offstate_values<Key: Hash>(
	state: &BranchRanges,
	values: &mut HashMap<Key, History<Option<DBValue>>>,
	inserted: Vec<(Key, DBValue)>,
	deleted: Vec<Key>,
) {
	for (k, v) in inserted {
		let entry = values.entry(k).or_insert_with(|| Default::default());
		entry.set(state, Some(v));
	}
	for k in deleted {
		let entry = values.entry(k).or_insert_with(|| Default::default());
		entry.set(state, None);
	}
}

fn discard_values<Key: Hash>(
	values: &mut HashMap<Key, (u32, DBValue)>,
	inserted: Vec<Key>,
	mut into: Option<&mut HashMap<Key, DBValue>>,
) {
	for k in inserted {
		match values.entry(k) {
			Entry::Occupied(mut e) => {
				let (ref mut counter, _) = e.get_mut();
				*counter -= 1;
				if *counter == 0 {
					let (key, (_, value)) = e.remove_entry();
					if let Some(ref mut into) = into {
						into.insert(key, value);
					}
				}
			},
			Entry::Vacant(_) => {
				debug_assert!(false, "Trying to discard missing value");
			}
		}
	}
}

fn discard_offstate_values(
	inserted: Vec<OffstateKey>,
	deleted: Vec<OffstateKey>,
	into: &mut OffstatePendingGC,
) {
	let into = if into.pending_canonicalisation_query.is_some() {
		&mut into.next_keys_pending_gc
	} else {
		&mut into.keys_pending_gc
	};
	into.extend(inserted);
	into.extend(deleted);
}


fn discard_descendants<BlockHash: Hash, Key: Hash>(
	levels: &mut VecDeque<Vec<BlockOverlay<BlockHash, Key>>>,
	mut values: &mut HashMap<Key, (u32, DBValue)>,
	index: usize,
	parents: &mut HashMap<BlockHash, (BlockHash, BranchIndex)>,
	pinned: &mut HashMap<BlockHash, (HashMap<Key, DBValue>, u64)>,
	offstate_gc: &mut OffstatePendingGC,
	hash: &BlockHash,
) {
	let mut discarded = Vec::new();
	if let Some(level) = levels.get_mut(index) {
		*level = level.drain(..).filter_map(|overlay| {
			let parent = parents.get(&overlay.hash).expect("there is a parent entry for each entry in levels; qed").0.clone();
			if parent == *hash {
				parents.remove(&overlay.hash);
				discarded.push(overlay.hash);
				let mut pinned = pinned.get_mut(hash);
				discard_values(&mut values, overlay.inserted, pinned.as_mut().map(|p| &mut p.0));
				discard_offstate_values(
					overlay.offstate_inserted,
					overlay.offstate_deleted,
					offstate_gc,
				);
				None
			} else {
				Some(overlay)
			}
		}).collect();
	}
	for hash in discarded {
		discard_descendants(levels, values, index + 1, parents, pinned, offstate_gc, &hash);
	}
}

impl<BlockHash: Hash, Key: Hash> NonCanonicalOverlay<BlockHash, Key> {
	/// Creates a new instance. Does not expect any metadata to be present in the DB.
	pub fn new<D: MetaDb>(db: &D) -> Result<NonCanonicalOverlay<BlockHash, Key>, Error<D::Error>> {
		let last_canonicalized = db.get_meta(&to_meta_key(LAST_CANONICAL, &()))
			.map_err(|e| Error::Db(e))?;
		let last_canonicalized = match last_canonicalized {
			Some(buffer) => Some(<(BlockHash, BlockNumber)>::decode(&mut buffer.as_slice())?),
			None => None,
		};
		let mut levels = VecDeque::new();
		let mut parents = HashMap::new();
		let mut values = HashMap::new();
		let mut offstate_values = HashMap::new();
		let mut branches = RangeSet::default();
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
					let offstate_journal_key = to_offstate_journal_key(block, index);
					match db.get_meta(&journal_key).map_err(|e| Error::Db(e))? {
						Some(record) => {
							let record: JournalRecord<BlockHash, Key> = Decode::decode(&mut record.as_slice())?;

							// TODO EMCh following two range fetch can be optimize when parent level
							// got a single element.
							// fetch parent info
							let parent_branch_index = parents.get(&record.parent_hash)
								.map(|(_, i)| *i).unwrap_or(0);
							let parent_branch_range = Some(
								branches.branch_ranges_from_cache(parent_branch_index, Some(block - 1))
							);
							let (branch_range, branch_index) = branches.import(
								block,
								parent_branch_index,
								parent_branch_range,
							);

							let (offstate_record_inserted, offstate_record_deleted) = if let Some(record) = db
								.get_meta(&offstate_journal_key).map_err(|e| Error::Db(e))? {
									let record = OffstateJournalRecord::decode(&mut record.as_slice())?;
									(Some(record.inserted), Some(record.deleted))
							} else { (None, None) };
							let inserted = record.inserted.iter().map(|(k, _)| k.clone()).collect();
							let offstate_inserted = offstate_record_inserted.as_ref()
								.map(|inserted| inserted.iter().map(|(k, _)| k.clone()).collect())
								.unwrap_or(Vec::new());
							let offstate_deleted = offstate_record_deleted.clone().unwrap_or(Vec::new());
							let overlay = BlockOverlay {
								hash: record.hash.clone(),
								journal_key,
								offstate_journal_key,
								inserted: inserted,
								deleted: record.deleted,
								offstate_inserted,
								offstate_deleted,
							};
							insert_values(&mut values, record.inserted);
							if offstate_record_inserted.is_some() || offstate_record_deleted.is_some() {
								insert_offstate_values(
									&branch_range,
									&mut offstate_values,
									offstate_record_inserted.unwrap_or(Vec::new()),
									offstate_record_deleted.unwrap_or(Vec::new()),
								);
							}
							trace!(
								target: "state-db",
								"Uncanonicalized journal entry {}.{} ({} {} inserted, {} {} deleted)",
								block,
								index,
								overlay.inserted.len(),
								overlay.offstate_inserted.len(),
								overlay.deleted.len(),
								overlay.offstate_deleted.len(),
							);
							level.push(overlay);
							parents.insert(record.hash, (record.parent_hash, branch_index));
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
			pinned: Default::default(),
			values,
			offstate_values,
			offstate_gc: Default::default(),
			branches,
		})
	}

	/// Insert a new block into the overlay. If inserted on the second level or lower
	/// expects parent to be present in the window.
	pub fn insert<E: fmt::Debug>(
		&mut self,
		hash: &BlockHash,
		number: BlockNumber,
		parent_hash: &BlockHash,
		changeset: ChangeSet<Key>,
		offstate_changeset: OffstateChangeSet<OffstateKey>,
	) -> Result<CommitSet<Key>, Error<E>> {
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
		let offstate_journal_key = to_offstate_journal_key(number, index);

		let inserted = changeset.inserted.iter().map(|(k, _)| k.clone()).collect();
		let mut offstate_inserted = Vec::new();
		let mut offstate_inserted_value = Vec::new();
		let mut offstate_deleted = Vec::new();
		for (k, v) in offstate_changeset.into_iter() {
			if let Some(v) = v {
				offstate_inserted.push(k.clone());
				offstate_inserted_value.push((k, v));
			} else {
				offstate_deleted.push(k);
			}
		}
		let overlay = BlockOverlay {
			hash: hash.clone(),
			journal_key: journal_key.clone(),
			offstate_journal_key: offstate_journal_key.clone(),
			inserted: inserted,
			deleted: changeset.deleted.clone(),
			offstate_inserted,
			offstate_deleted: offstate_deleted.clone(),
		};
		level.push(overlay);
		let	parent_branch_index = self.parents.get(&parent_hash).map(|(_, i)| *i).unwrap_or(0);
		let	parent_branch_range = if number == 0 {
			None
		} else {
			Some(self.branches.branch_ranges_from_cache(parent_branch_index, Some(number - 1)))
		};
		let (branch_range, branch_index) = self.branches.import(
			number,
			parent_branch_index,
			parent_branch_range,
		);

		self.parents.insert(hash.clone(), (parent_hash.clone(), branch_index));
		let journal_record = JournalRecord {
			hash: hash.clone(),
			parent_hash: parent_hash.clone(),
			inserted: changeset.inserted,
			deleted: changeset.deleted,
		};
		commit.meta.inserted.push((journal_key, journal_record.encode()));
		let offstate_journal_record = OffstateJournalRecord {
			inserted: offstate_inserted_value,
			deleted: offstate_deleted,
		};
		commit.meta.inserted.push((offstate_journal_key, offstate_journal_record.encode()));
	
		trace!(
			target: "state-db",
			"Inserted uncanonicalized changeset {}.{} ({} {} inserted, {} deleted)",
			number,
			index,
			journal_record.inserted.len(),
			offstate_journal_record.inserted.len(),
			journal_record.deleted.len(),
		);
		insert_values(&mut self.values, journal_record.inserted);
		insert_offstate_values(
			&branch_range,
			&mut self.offstate_values,
			offstate_journal_record.inserted,
			offstate_journal_record.deleted,
		);
		self.pending_insertions.push(hash.clone());
		Ok(commit)
	}

	fn discard_journals(
		&self,
		level_index: usize,
		discarded_journals: &mut Vec<Vec<u8>>,
		discarded_blocks: &mut Vec<BlockHash>,
		hash: &BlockHash
	) {
		if let Some(level) = self.levels.get(level_index) {
			level.iter().for_each(|overlay| {
				let (parent, _branch_index) = self.parents.get(&overlay.hash)
					.expect("there is a parent entry for each entry in levels; qed");
				if parent == hash {
					discarded_journals.push(overlay.journal_key.clone());
					discarded_journals.push(overlay.offstate_journal_key.clone());
					discarded_blocks.push(overlay.hash.clone());
					self.discard_journals(level_index + 1, discarded_journals, discarded_blocks, &overlay.hash);
				}
			});
		}
	}

	fn front_block_number(&self) -> BlockNumber {
		self.last_canonicalized.as_ref().map(|&(_, n)| n + 1).unwrap_or(0)
	}

	pub fn last_canonicalized_block_number(&self) -> Option<BlockNumber> {
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
	pub fn canonicalize<E: fmt::Debug>(
		&mut self,
		hash: &BlockHash,
		commit: &mut CommitSet<Key>,
	) -> Result<(), Error<E>> {
		trace!(target: "state-db", "Canonicalizing {:?}", hash);
		let level = self.levels.get(self.pending_canonicalizations.len()).ok_or_else(|| Error::InvalidBlock)?;
		let index = level
			.iter()
			.position(|overlay| overlay.hash == *hash)
			.ok_or_else(|| Error::InvalidBlock)?;

		let mut discarded_journals = Vec::new();
		let mut discarded_blocks = Vec::new();
		for (i, overlay) in level.iter().enumerate() {
			if i != index {
				self.discard_journals(
					self.pending_canonicalizations.len() + 1,
					&mut discarded_journals,
					&mut discarded_blocks,
					&overlay.hash
				);
			}
			discarded_journals.push(overlay.journal_key.clone());
			discarded_journals.push(overlay.offstate_journal_key.clone());
			discarded_blocks.push(overlay.hash.clone());
		}

		// get the one we need to canonicalize
		let overlay = &level[index];
		commit.data.inserted.extend(overlay.inserted.iter()
			.map(|k| (k.clone(), self.values.get(k).expect("For each key in overlays there's a value in values").1.clone())));
		commit.data.deleted.extend(overlay.deleted.clone());
		let block_number = self.front_block_number() + self.pending_canonicalizations.len() as u64;
		if !overlay.offstate_inserted.is_empty() || !overlay.offstate_deleted.is_empty() {
			// canonicalization is not frequent enough that we pass range
			// in parameter for now
			if let Some(range) = self.get_branch_range(hash, block_number) {
				commit.offstate.extend(
					overlay.offstate_inserted.iter()
					.map(|k| (k.clone(), self.offstate_values.get(k)
						.expect("For each key in overlays there's a value in values")
						.get(&range)
						.expect("For each key in overlays there's a historied entry in values")
						.clone())));
				// some deletion can be pruned if in first block so handle is
				// a bit less restrictive
				commit.offstate.extend(
					overlay.offstate_deleted.iter()
					.filter_map(|k| self.offstate_values.get(k)
						.map(|v| (k.clone(), v.get(&range)
							.expect("For each key in overlays there's a historied entry \
								in values, and pruned empty value are cleared")
							.clone())
						)
					)
				);
			}
		}

		commit.meta.deleted.append(&mut discarded_journals);
		let canonicalized = (hash.clone(), block_number);
		commit.meta.inserted.push((to_meta_key(LAST_CANONICAL, &()), canonicalized.encode()));
		trace!(target: "state-db", "Discarding {} records", commit.meta.deleted.len());
		self.pending_canonicalizations.push(hash.clone());
		Ok(())
	}

	fn apply_canonicalizations(&mut self) {
		let last = self.pending_canonicalizations.last().cloned();
		let last_index = last.as_ref().and_then(|last| self.parents.get(last))
			.map(|(_, index)| *index);
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
					discard_descendants(
						&mut self.levels,
						&mut self.values,
						0,
						&mut self.parents,
						&mut self.pinned,
						&mut self.offstate_gc,
						&overlay.hash,
					);
				}

				let mut pinned = self.pinned.get_mut(&overlay.hash);
				discard_values(&mut self.values, overlay.inserted, pinned.as_mut().map(|p| &mut p.0));
				discard_offstate_values(
					overlay.offstate_inserted,
					overlay.offstate_deleted,
					&mut self.offstate_gc,
				);
			}
		}
		if let Some(hash) = last {
			let block_number = self.last_canonicalized.as_ref()
				.map(|(_, n)| n + count).unwrap_or(count - 1);
			self.last_canonicalized = Some((hash, block_number));

			if let Some(branch_index_cannonicalize) = last_index {
				// this needs to be call after parents update
				// TODO EMCH may be needed in 'canonicalize', and restore or commit here
				self.branches.update_finalize_treshold(branch_index_cannonicalize, block_number, true);
				// gc is at the right place
				self.offstate_gc.set_pending_gc(branch_index_cannonicalize);
				// try to run the garbage collection (can run later if there is
				// pinned process).
				self.offstate_gc.try_gc(&mut self.offstate_values, &self.branches, &self.pinned);
			}
		}

	}

	/// Get a value from the node overlay. This searches in every existing changeset.
	pub fn get(&self, key: &Key) -> Option<DBValue> {
		if let Some((_, value)) = self.values.get(&key) {
			return Some(value.clone());
		}
		for pinned in self.pinned.values() {
			if let Some(value) = pinned.0.get(&key) {
				return Some(value.clone());
			}
		}
		None
	}

	/// Get a value from the node overlay. This searches in every existing changeset.
	pub fn get_offstate(&self, key: &[u8], state: &BranchRanges) -> Option<&Option<DBValue>> {
		if let Some(value) = self.offstate_values.get(key) {
			return value.get(state);
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
				commit.meta.deleted.push(overlay.offstate_journal_key);
				if let Some((_, branch_index)) = self.parents.remove(&overlay.hash) {
					self.branches.revert(branch_index);
				}
				discard_values(&mut self.values, overlay.inserted, None);
				discard_offstate_values(
					overlay.offstate_inserted,
					overlay.offstate_deleted,
					&mut self.offstate_gc,
				);
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
			discard_values(&mut self.values, overlay.inserted, None);
			// TODO EMCH we need discard state?? from  update finalize treshold here!! see discard value
			// usgage
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

	/// Pin state values in memory
	pub fn pin(&mut self, hash: &BlockHash) {
		self.pinned.insert(hash.clone(), (Default::default(), self.offstate_gc.gc_last_index));
	}

	/// TODO EMCH aka get state for hash to query offstate storage.
	pub fn get_branch_range(&self, hash: &BlockHash, number: BlockNumber) -> Option<BranchRanges> {
		self.parents.get(hash).map(|(_, branch_index)| *branch_index).map(|branch_index| {
		  self.branches.branch_ranges_from_cache(branch_index, Some(number))
		})
	}

	/// Discard pinned state
	pub fn unpin(&mut self, hash: &BlockHash) {
		self.pinned.remove(hash);
		self.offstate_gc.try_gc(&mut self.offstate_values, &self.branches, &self.pinned);
	}

	/// Iterator over values at a given state. Deletion are included in the result as a None value.
	pub fn offstate_iter<'a>(
		&'a self,
		state: &'a BranchRanges,
	) -> impl Iterator<Item = (&'a OffstateKey, &'a Option<DBValue>)> {
		let state = state.clone();
		self.offstate_values.iter().filter_map(move |(k, v)| {
			v.get(&state).map(|v| (k, v))
		})
	}
}

#[cfg(test)]
mod tests {
	use std::io;
	use std::collections::BTreeMap;
	use primitives::H256;
	use super::{NonCanonicalOverlay, to_journal_key};
	use crate::{ChangeSet, OffstateChangeSet, CommitSet, OffstateKey};
	use crate::test::{make_db, make_changeset, make_offstate_changeset};
	use crate::branch::BranchRanges;

	fn contains(overlay: &NonCanonicalOverlay<H256, H256>, key: u64) -> bool {
		overlay.get(&H256::from_low_u64_be(key)) == Some(H256::from_low_u64_be(key).as_bytes().to_vec())
	}

	fn contains_offstate(
		overlay: &NonCanonicalOverlay<H256, H256>,
		key: u64,
		state: &H256,
		block: u64,
	) -> bool {
		overlay.get_branch_range(state, block).and_then(|state| {
			overlay.get_offstate(&H256::from_low_u64_be(key).as_bytes().to_vec(), &state)
		}) == Some(&Some(H256::from_low_u64_be(key).as_bytes().to_vec()))
	}

	fn contains_offstate2(
		overlay: &NonCanonicalOverlay<H256, H256>,
		key: u64,
		state: &BranchRanges,
	) -> bool {
		overlay.get_offstate(&H256::from_low_u64_be(key).as_bytes().to_vec(), &state)
			== Some(&Some(H256::from_low_u64_be(key).as_bytes().to_vec()))
	}

	fn contains_both(
		overlay: &NonCanonicalOverlay<H256, H256>,
		key: u64,
		state: &H256,
		block: u64,
	) -> bool {
		contains(overlay, key) && contains_offstate(overlay, key, state, block)
	}

	fn contains_any(
		overlay: &NonCanonicalOverlay<H256, H256>,
		key: u64,
		state: &H256,
		block: u64,
	) -> bool {
		contains(overlay, key) || contains_offstate(overlay, key, state, block)
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
		let mut commit = CommitSet::default();
		overlay.canonicalize::<io::Error>(&H256::default(), &mut commit).unwrap();
	}

	#[test]
	#[should_panic]
	fn insert_ahead_panics() {
		let db = make_db(&[]);
		let h1 = H256::random();
		let h2 = H256::random();
		let mut overlay = NonCanonicalOverlay::<H256, H256>::new(&db).unwrap();
		overlay.insert::<io::Error>(
			&h1, 2, &H256::default(),
			ChangeSet::default(), OffstateChangeSet::default(),
		).unwrap();
		overlay.insert::<io::Error>(
			&h2, 1, &h1,
			ChangeSet::default(), OffstateChangeSet::default(),
		).unwrap();
	}

	#[test]
	#[should_panic]
	fn insert_behind_panics() {
		let h1 = H256::random();
		let h2 = H256::random();
		let db = make_db(&[]);
		let mut overlay = NonCanonicalOverlay::<H256, H256>::new(&db).unwrap();
		overlay.insert::<io::Error>(
			&h1, 1, &H256::default(),
			ChangeSet::default(), OffstateChangeSet::default(),
		).unwrap();
		overlay.insert::<io::Error>(
			&h2, 3, &h1,
			ChangeSet::default(), OffstateChangeSet::default(),
		).unwrap();
	}

	#[test]
	#[should_panic]
	fn insert_unknown_parent_panics() {
		let db = make_db(&[]);
		let h1 = H256::random();
		let h2 = H256::random();
		let mut overlay = NonCanonicalOverlay::<H256, H256>::new(&db).unwrap();
		overlay.insert::<io::Error>(
			&h1, 1, &H256::default(),
			ChangeSet::default(), OffstateChangeSet::default(),
		).unwrap();
		overlay.insert::<io::Error>(
			&h2, 2, &H256::default(),
			ChangeSet::default(), OffstateChangeSet::default(),
		).unwrap();
	}

	#[test]
	#[should_panic]
	fn canonicalize_unknown_panics() {
		let h1 = H256::random();
		let h2 = H256::random();
		let db = make_db(&[]);
		let mut overlay = NonCanonicalOverlay::<H256, H256>::new(&db).unwrap();
		overlay.insert::<io::Error>(
			&h1, 1, &H256::default(),
			ChangeSet::default(), OffstateChangeSet::default(),
		).unwrap();
		let mut commit = CommitSet::default();
		overlay.canonicalize::<io::Error>(&h2, &mut commit).unwrap();
	}

	#[test]
	fn insert_canonicalize_one() {
		let h1 = H256::random();
		let mut db = make_db(&[1, 2]);
		db.initialize_offstate(&[1, 2]);
		let mut overlay = NonCanonicalOverlay::<H256, H256>::new(&db).unwrap();
		let changeset = make_changeset(&[3, 4], &[2]);
		let offstate_changeset = make_offstate_changeset(&[3, 4], &[2]);
		let insertion = overlay.insert::<io::Error>(
			&h1, 1, &H256::default(),
			changeset.clone(), offstate_changeset.clone(),
		).unwrap();
		assert_eq!(insertion.data.inserted.len(), 0);
		assert_eq!(insertion.data.deleted.len(), 0);
		assert_eq!(insertion.offstate.len(), 0);
		// last cannonical, journal_record and offstate_journal_record
		assert_eq!(insertion.meta.inserted.len(), 3);
		assert_eq!(insertion.meta.deleted.len(), 0);
		db.commit(&insertion);
		let mut finalization = CommitSet::default();
		overlay.canonicalize::<io::Error>(&h1, &mut finalization).unwrap();
		assert_eq!(finalization.data.inserted.len(), changeset.inserted.len());
		assert_eq!(finalization.data.deleted.len(), changeset.deleted.len());
		assert_eq!(finalization.offstate.len(), offstate_changeset.len());
		assert_eq!(finalization.meta.inserted.len(), 1);
		// normal and offstate discarded journall
		assert_eq!(finalization.meta.deleted.len(), 2);
		db.commit(&finalization);
		assert!(db.data_eq(&make_db(&[1, 3, 4])));
		assert!(db.offstate_eq(&[1, 3, 4]));
	}

	#[test]
	fn restore_from_journal() {
		let h1 = H256::random();
		let h2 = H256::random();
		let mut db = make_db(&[1, 2]);
		db.initialize_offstate(&[1, 2]);
		let mut overlay = NonCanonicalOverlay::<H256, H256>::new(&db).unwrap();
		db.commit(&overlay.insert::<io::Error>(
			&h1, 10, &H256::default(),
			make_changeset(&[3, 4], &[2]),
			make_offstate_changeset(&[3, 4], &[2]),
		).unwrap());
		db.commit(&overlay.insert::<io::Error>(
			&h2, 11, &h1,
			make_changeset(&[5], &[3]),
			make_offstate_changeset(&[5], &[3]),
		).unwrap());
		assert_eq!(db.meta.len(), 5);

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
		db.initialize_offstate(&[1, 2]);
		let mut overlay = NonCanonicalOverlay::<H256, H256>::new(&db).unwrap();
		db.commit(&overlay.insert::<io::Error>(
			&h1, 10, &H256::default(),
			make_changeset(&[3, 4], &[2]),
			make_offstate_changeset(&[3, 4], &[2]),
		).unwrap());
		db.commit(&overlay.insert::<io::Error>(
			&h2,11, &h1,
			make_changeset(&[5], &[3]),
			make_offstate_changeset(&[5], &[3]),
		).unwrap());
		let mut commit = CommitSet::default();
		overlay.canonicalize::<io::Error>(&h1, &mut commit).unwrap();
		db.commit(&commit);
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
		db.initialize_offstate(&[1, 2, 3, 4]);
		let mut overlay = NonCanonicalOverlay::<H256, H256>::new(&db).unwrap();
		let changeset1 = make_changeset(&[5, 6], &[2]);
		let changeset2 = make_changeset(&[7, 8], &[5, 3]);
		let offstate_changeset1 = make_offstate_changeset(&[5, 6], &[2]);
		let offstate_changeset2 = make_offstate_changeset(&[7, 8], &[5, 3]);
		db.commit(&overlay.insert::<io::Error>(
			&h1, 1, &H256::default(),
			changeset1, offstate_changeset1,
		).unwrap());
		assert!(contains_both(&overlay, 5, &h1, 1));
		db.commit(&overlay.insert::<io::Error>(
			&h2, 2, &h1,
			changeset2, offstate_changeset2,
		).unwrap());
		assert!(contains_both(&overlay, 7, &h2, 2));
		assert!(!contains_offstate(&overlay, 5, &h2, 2));
		assert!(contains_offstate(&overlay, 5, &h1, 1));
		assert!(contains_both(&overlay, 5, &h1, 1));
		assert_eq!(overlay.levels.len(), 2);
		assert_eq!(overlay.parents.len(), 2);
		let mut commit = CommitSet::default();
		overlay.canonicalize::<io::Error>(&h1, &mut commit).unwrap();
		db.commit(&commit);
		assert!(contains(&overlay, 5));
		assert_eq!(overlay.levels.len(), 2);
		assert_eq!(overlay.parents.len(), 2);
		overlay.apply_pending();
		assert_eq!(overlay.levels.len(), 1);
		assert_eq!(overlay.parents.len(), 1);
		assert!(!contains_any(&overlay, 5, &h1, 1));
		assert!(contains_both(&overlay, 7, &h2, 2));
		let mut commit = CommitSet::default();
		overlay.canonicalize::<io::Error>(&h2, &mut commit).unwrap();
		db.commit(&commit);
		overlay.apply_pending();
		assert_eq!(overlay.levels.len(), 0);
		assert_eq!(overlay.parents.len(), 0);
		assert!(db.data_eq(&make_db(&[1, 4, 6, 7, 8])));
		assert!(db.offstate_eq(&[1, 4, 6, 7, 8]));
	}

	#[test]
	fn insert_same_key() {
		let mut db = make_db(&[]);
		let (h_1, c_1) = (H256::random(), make_changeset(&[1], &[]));
		let (h_2, c_2) = (H256::random(), make_changeset(&[1], &[]));
		let o_c_1 = make_offstate_changeset(&[1], &[]);
		let o_c_2 = make_offstate_changeset(&[1], &[]);

		let mut overlay = NonCanonicalOverlay::<H256, H256>::new(&db).unwrap();
		db.commit(&overlay.insert::<io::Error>(&h_1, 1, &H256::default(), c_1, o_c_1).unwrap());
		db.commit(&overlay.insert::<io::Error>(&h_2, 1, &H256::default(), c_2, o_c_2).unwrap());
		assert!(contains_both(&overlay, 1, &h_2, 1));
		let mut commit = CommitSet::default();
		overlay.canonicalize::<io::Error>(&h_1, &mut commit).unwrap();
		db.commit(&commit);
		assert!(contains_both(&overlay, 1, &h_2, 1));
		overlay.apply_pending();
		assert!(!contains_any(&overlay, 1, &h_2, 1));
	}

	#[test]
	fn insert_with_pending_canonicalization() {
		let h1 = H256::random();
		let h2 = H256::random();
		let h3 = H256::random();
		let mut db = make_db(&[]);
		let mut overlay = NonCanonicalOverlay::<H256, H256>::new(&db).unwrap();
		let changeset = make_changeset(&[], &[]);
		let ochangeset = make_offstate_changeset(&[], &[]);
		db.commit(&overlay.insert::<io::Error>(
			&h1, 1, &H256::default(),
			changeset.clone(), ochangeset.clone(),
		).unwrap());
		db.commit(&overlay.insert::<io::Error>(
			&h2, 2, &h1,
			changeset.clone(), ochangeset.clone(),
		).unwrap());
		overlay.apply_pending();
		let mut commit = CommitSet::default();
		overlay.canonicalize::<io::Error>(&h1, &mut commit).unwrap();
		overlay.canonicalize::<io::Error>(&h2, &mut commit).unwrap();
		db.commit(&commit);
		db.commit(&overlay.insert::<io::Error>(
			&h3, 3, &h2,
			changeset.clone(), ochangeset.clone(),
		).unwrap());
		overlay.apply_pending();
		assert_eq!(overlay.levels.len(), 1);
	}

	fn make_both_changeset(inserted: &[u64], deleted: &[u64]) -> (
		H256,
		ChangeSet<H256>,
		OffstateChangeSet<OffstateKey>,
	) {
		(
			H256::random(),
			make_changeset(inserted, deleted),
			make_offstate_changeset(inserted, deleted),
		)
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

		let (h_1, c_1, o_c_1) = make_both_changeset(&[1], &[]);
		let (h_2, c_2, o_c_2) = make_both_changeset(&[2], &[]);

		let (h_1_1, c_1_1, o_c_1_1) = make_both_changeset(&[11], &[]);
		let (h_1_2, c_1_2, o_c_1_2) = make_both_changeset(&[12], &[]);
		let (h_2_1, c_2_1, o_c_2_1) = make_both_changeset(&[21], &[]);
		let (h_2_2, c_2_2, o_c_2_2) = make_both_changeset(&[22], &[]);

		let (h_1_1_1, c_1_1_1, o_c_1_1_1) = make_both_changeset(&[111], &[]);
		let (h_1_2_1, c_1_2_1, o_c_1_2_1) = make_both_changeset(&[121], &[]);
		let (h_1_2_2, c_1_2_2, o_c_1_2_2) = make_both_changeset(&[122], &[]);
		let (h_1_2_3, c_1_2_3, o_c_1_2_3) = make_both_changeset(&[123], &[]);
		let (h_2_1_1, c_2_1_1, o_c_2_1_1) = make_both_changeset(&[211], &[]);

		let mut overlay = NonCanonicalOverlay::<H256, H256>::new(&db).unwrap();
		db.commit(&overlay.insert::<io::Error>(&h_1, 1, &H256::default(), c_1, o_c_1).unwrap());

		db.commit(&overlay.insert::<io::Error>(&h_1_1, 2, &h_1, c_1_1, o_c_1_1).unwrap());
		db.commit(&overlay.insert::<io::Error>(&h_1_2, 2, &h_1, c_1_2, o_c_1_2).unwrap());

		db.commit(&overlay.insert::<io::Error>(&h_2, 1, &H256::default(), c_2, o_c_2).unwrap());

		db.commit(&overlay.insert::<io::Error>(&h_2_1, 2, &h_2, c_2_1, o_c_2_1).unwrap());
		db.commit(&overlay.insert::<io::Error>(&h_2_2, 2, &h_2, c_2_2, o_c_2_2).unwrap());

		db.commit(&overlay.insert::<io::Error>(&h_1_1_1, 3, &h_1_1, c_1_1_1, o_c_1_1_1).unwrap());
		db.commit(&overlay.insert::<io::Error>(&h_1_2_1, 3, &h_1_2, c_1_2_1, o_c_1_2_1).unwrap());
		db.commit(&overlay.insert::<io::Error>(&h_1_2_2, 3, &h_1_2, c_1_2_2, o_c_1_2_2).unwrap());
		db.commit(&overlay.insert::<io::Error>(&h_1_2_3, 3, &h_1_2, c_1_2_3, o_c_1_2_3).unwrap());
		db.commit(&overlay.insert::<io::Error>(&h_2_1_1, 3, &h_2_1, c_2_1_1, o_c_2_1_1).unwrap());

		assert!(contains_both(&overlay, 2, &h_2_1_1, 3));
		assert!(contains_both(&overlay, 11, &h_1_1_1, 3));
		assert!(contains_both(&overlay, 21, &h_2_1_1, 3));
		assert!(contains_both(&overlay, 111, &h_1_1_1, 3));
		assert!(contains_both(&overlay, 122, &h_1_2_2, 3));
		assert!(contains_both(&overlay, 211, &h_2_1_1, 3));
		assert_eq!(overlay.levels.len(), 3);
		assert_eq!(overlay.parents.len(), 11);
		assert_eq!(overlay.last_canonicalized, Some((H256::default(), 0)));

		// check if restoration from journal results in the same tree
		let overlay2 = NonCanonicalOverlay::<H256, H256>::new(&db).unwrap();
		assert_eq!(overlay.levels, overlay2.levels);
		let parents_no_iter: BTreeMap<_, _> = overlay.parents.iter()
			.map(|(k, (v, _))| (k.clone(), v.clone())).collect();
		let parents_no_iter2: BTreeMap<_, _> = overlay2.parents.iter()
			.map(|(k, (v, _))| (k.clone(), v.clone())).collect();
		assert_eq!(parents_no_iter, parents_no_iter2);
		assert_eq!(overlay.last_canonicalized, overlay2.last_canonicalized);

		// canonicalize 1. 2 and all its children should be discarded
		let mut commit = CommitSet::default();
		overlay.canonicalize::<io::Error>(&h_1, &mut commit).unwrap();
		db.commit(&commit);
		overlay.apply_pending();
		assert_eq!(overlay.levels.len(), 2);
		assert_eq!(overlay.parents.len(), 6);
		assert!(!contains_any(&overlay, 1, &h_1, 1));
		assert!(!contains_any(&overlay, 2, &h_2, 1));
		assert!(!contains_any(&overlay, 21, &h_2_1, 2));
		assert!(!contains_any(&overlay, 22, &h_2_2, 2));
		assert!(!contains_any(&overlay, 211, &h_2_1_1, 3));
		assert!(contains_both(&overlay, 111, &h_1_1_1, 3));
		assert!(contains_both(&overlay, 12, &h_1_2, 2));
		// check that journals are deleted
		assert!(db.get_meta(&to_journal_key(1, 0)).unwrap().is_none());
		assert!(db.get_meta(&to_journal_key(1, 1)).unwrap().is_none());
		assert!(db.get_meta(&to_journal_key(2, 1)).unwrap().is_some());
		assert!(db.get_meta(&to_journal_key(2, 2)).unwrap().is_none());
		assert!(db.get_meta(&to_journal_key(2, 3)).unwrap().is_none());

		// canonicalize 1_2. 1_1 and all its children should be discarded
		let mut commit = CommitSet::default();
		overlay.canonicalize::<io::Error>(&h_1_2, &mut commit).unwrap();
		db.commit(&commit);
		overlay.apply_pending();
		assert_eq!(overlay.levels.len(), 1);
		assert_eq!(overlay.parents.len(), 3);
		assert!(!contains_any(&overlay, 11, &h_1_1, 2));
		assert!(!contains_any(&overlay, 111, &h_1_1_1, 3));
		assert!(contains_both(&overlay, 121, &h_1_2_1, 3));
		assert!(contains_both(&overlay, 122, &h_1_2_2, 3));
		assert!(contains_both(&overlay, 123, &h_1_2_3, 3));
		assert!(overlay.have_block(&h_1_2_1));
		assert!(!overlay.have_block(&h_1_2));
		assert!(!overlay.have_block(&h_1_1));
		assert!(!overlay.have_block(&h_1_1_1));

		// canonicalize 1_2_2
		let mut commit = CommitSet::default();
		overlay.canonicalize::<io::Error>(&h_1_2_2, &mut commit).unwrap();
		db.commit(&commit);
		overlay.apply_pending();
		assert_eq!(overlay.levels.len(), 0);
		assert_eq!(overlay.parents.len(), 0);
		assert!(db.data_eq(&make_db(&[1, 12, 122])));
		assert!(db.offstate_eq(&[1, 12, 122]));
		assert_eq!(overlay.last_canonicalized, Some((h_1_2_2, 3)));
	}

	#[test]
	fn insert_revert() {
		let h1 = H256::random();
		let h2 = H256::random();
		let mut db = make_db(&[1, 2, 3, 4]);
		db.initialize_offstate(&[1, 2, 3, 4]);
		let mut overlay = NonCanonicalOverlay::<H256, H256>::new(&db).unwrap();
		assert!(overlay.revert_one().is_none());
		let changeset1 = make_changeset(&[5, 6], &[2]);
		let ochangeset1 = make_offstate_changeset(&[5, 6], &[2]);
		let changeset2 = make_changeset(&[7, 8], &[5, 3]);
		let ochangeset2 = make_offstate_changeset(&[7, 8], &[5, 3]);
		db.commit(&overlay.insert::<io::Error>(
			&h1, 1, &H256::default(),
			changeset1, ochangeset1,
		).unwrap());
		db.commit(&overlay.insert::<io::Error>(
			&h2, 2, &h1,
			changeset2, ochangeset2,
		).unwrap());
		assert!(contains_both(&overlay, 7, &h2, 2));
		db.commit(&overlay.revert_one().unwrap());
		assert_eq!(overlay.parents.len(), 1);
		assert!(contains_both(&overlay, 5, &h1, 1));
		assert!(!contains(&overlay, 7));
		assert!(!contains_any(&overlay, 7, &h1, 1));
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
		let ochangeset1 = make_offstate_changeset(&[5, 6], &[2]);
		let changeset2 = make_changeset(&[7, 8], &[5, 3]);
		let ochangeset2 = make_offstate_changeset(&[7, 8], &[5, 3]);
		let changeset3 = make_changeset(&[9], &[]);
		let ochangeset3 = make_offstate_changeset(&[9], &[]);
		overlay.insert::<io::Error>(
			&h1, 1, &H256::default(),
			changeset1, ochangeset1,
		).unwrap();
		assert!(contains(&overlay, 5));
		overlay.insert::<io::Error>(
			&h2_1, 2, &h1,
			changeset2, ochangeset2,
		).unwrap();
		overlay.insert::<io::Error>(
			&h2_2, 2, &h1,
			changeset3, ochangeset3,
		).unwrap();
		assert!(contains_offstate(&overlay, 5, &h1, 1));
		assert!(contains_both(&overlay, 7, &h2_1, 2));
		assert!(!contains_offstate(&overlay, 5, &h2_1, 2));
		assert!(contains(&overlay, 5));
		assert!(contains_both(&overlay, 9, &h2_2, 2));
		assert_eq!(overlay.levels.len(), 2);
		assert_eq!(overlay.parents.len(), 3);
		overlay.revert_pending();
		assert!(!contains_any(&overlay, 5, &h1, 1));
		assert_eq!(overlay.levels.len(), 0);
		assert_eq!(overlay.parents.len(), 0);
	}

	#[test]
	fn keeps_pinned() {
		let mut db = make_db(&[]);

		// - 1 - 1_1
		//     \ 1_2

		let (h_1, c_1, o_c_1) = make_both_changeset(&[1], &[]);
		let (h_2, c_2, o_c_2) = make_both_changeset(&[2], &[]);

		let mut overlay = NonCanonicalOverlay::<H256, H256>::new(&db).unwrap();
		db.commit(&overlay.insert::<io::Error>(&h_1, 1, &H256::default(), c_1, o_c_1).unwrap());
		db.commit(&overlay.insert::<io::Error>(&h_2, 1, &H256::default(), c_2, o_c_2).unwrap());

		overlay.pin(&h_1);
		let h1_context = overlay.get_branch_range(&h_1, 1).unwrap();
		let h2_context = overlay.get_branch_range(&h_2, 1).unwrap();
	
		let mut commit = CommitSet::default();
		overlay.canonicalize::<io::Error>(&h_2, &mut commit).unwrap();
		db.commit(&commit);
		overlay.apply_pending();
		assert!(contains(&overlay, 1));
		// we cannot use contains_offstate because offstate pining is relying on
		// asumption that pinned context memoïzed its branch state.
		assert!(contains_offstate2(&overlay, 1, &h1_context));
		assert!(!contains_offstate(&overlay, 1, &h_1, 1));
		overlay.unpin(&h_1);
		assert!(!contains(&overlay, 1));
		assert!(!contains_offstate2(&overlay, 1, &h1_context));
	}
}
