// Copyright 2018-2019 Parity Technologies (UK) Ltd.
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

//! Helper for managing the set of available leaves in the chain for DB implementations.

use std::collections::BTreeMap;
use std::cmp::Reverse;
use kvdb::{KeyValueDB, DBTransaction};
use runtime_primitives::traits::SimpleArithmetic;
use parity_codec::{Encode, Decode};
use crate::error;

#[derive(Debug, Clone, PartialEq, Eq)]
struct LeafSetItem<H, N> {
	hash: H,
	number: Reverse<N>,
}

/// A displaced leaf after import.
#[must_use = "Displaced items from the leaf set must be handled."]
pub struct ImportDisplaced<H, N> {
	new_hash: H,
	displaced: LeafSetItem<H, N>,
}

/// Displaced leaves after finalization.
#[must_use = "Displaced items from the leaf set must be handled."]
pub struct FinalizationDisplaced<H, N> {
	leaves: BTreeMap<Reverse<N>, Vec<H>>,
}

impl<H, N: Ord> FinalizationDisplaced<H, N> {
	/// Merge with another. This should only be used for displaced items that
	/// are produced within one transaction of each other.
	pub fn merge(&mut self, mut other: Self) {
		// this will ignore keys that are in duplicate, however
		// if these are actually produced correctly via the leaf-set within
		// one transaction, then there will be no overlap in the keys.
		self.leaves.append(&mut other.leaves);
	}
}

/// list of leaf hashes ordered by number (descending).
/// stored in memory for fast access.
/// this allows very fast checking and modification of active leaves.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LeafSet<H, N> {
	storage: BTreeMap<Reverse<N>, Vec<H>>,
	pending_added: Vec<LeafSetItem<H, N>>,
	pending_removed: Vec<H>,
}

impl<H, N> LeafSet<H, N> where
	H: Clone + PartialEq + Decode + Encode,
	N: std::fmt::Debug + Clone + SimpleArithmetic + Decode + Encode,
{
	/// Construct a new, blank leaf set.
	pub fn new() -> Self {
		Self {
			storage: BTreeMap::new(),
			pending_added: Vec::new(),
			pending_removed: Vec::new(),
		}
	}

	/// Read the leaf list from the DB, using given prefix for keys.
	pub fn read_from_db(db: &KeyValueDB, column: Option<u32>, prefix: &[u8]) -> error::Result<Self> {
		let mut storage = BTreeMap::new();

		for (key, value) in db.iter_from_prefix(column, prefix) {
			if !key.starts_with(prefix) { break }
			let raw_hash = &mut &key[prefix.len()..];
			let hash = match Decode::decode(raw_hash) {
				Some(hash) => hash,
				None => return Err(error::Error::Backend("Error decoding hash".into())),
			};
			let number = match Decode::decode(&mut &value[..]) {
				Some(number) => number,
				None => return Err(error::Error::Backend("Error decoding number".into())),
			};
			storage.entry(Reverse(number)).or_insert_with(Vec::new).push(hash);
		}
		Ok(Self {
			storage,
			pending_added: Vec::new(),
			pending_removed: Vec::new(),
		})
	}

	/// update the leaf list on import. returns a displaced leaf if there was one.
	pub fn import(&mut self, hash: H, number: N, parent_hash: H) -> Option<ImportDisplaced<H, N>> {
		// avoid underflow for genesis.
		let displaced = if number != N::zero() {
			let new_number = Reverse(number.clone() - N::one());
			let was_displaced = self.remove_leaf(&new_number, &parent_hash);

			if was_displaced {
				self.pending_removed.push(parent_hash.clone());
				Some(ImportDisplaced {
					new_hash: hash.clone(),
					displaced: LeafSetItem {
						hash: parent_hash,
						number: new_number,
					},
				})
			} else {
				None
			}
		} else {
			None
		};

		self.insert_leaf(Reverse(number.clone()), hash.clone());
		self.pending_added.push(LeafSetItem { hash, number: Reverse(number) });
		displaced
	}

	/// Note a block height finalized, displacing all leaves with number less than the finalized block's.
	///
	/// Although it would be more technically correct to also prune out leaves at the
	/// same number as the finalized block, but with different hashes, the current behavior
	/// is simpler and our assumptions about how finalization works means that those leaves
	/// will be pruned soon afterwards anyway.
	pub fn finalize_height(&mut self, number: N) -> FinalizationDisplaced<H, N> {
		let boundary = if number == N::zero() {
			return FinalizationDisplaced { leaves: BTreeMap::new() };
		} else {
			number - N::one()
		};

		let below_boundary = self.storage.split_off(&Reverse(boundary));
		self.pending_removed.extend(below_boundary.values().flat_map(|h| h.iter()).cloned());
		FinalizationDisplaced {
			leaves: below_boundary,
		}
	}

	/// Undo all pending operations.
	///
	/// This returns an `Undo` struct, where any
	/// `Displaced` objects that have returned by previous method calls
	/// should be passed to via the appropriate methods. Otherwise,
	/// the on-disk state may get out of sync with in-memory state.
	pub fn undo(&mut self) -> Undo<H, N> {
		Undo { inner: self }
	}

	/// currently since revert only affects the canonical chain
	/// we assume that parent has no further children
	/// and we add it as leaf again
	pub fn revert(&mut self, hash: H, number: N, parent_hash: H) {
		self.insert_leaf(Reverse(number.clone() - N::one()), parent_hash);
		self.remove_leaf(&Reverse(number), &hash);
	}

	/// returns an iterator over all hashes in the leaf set
	/// ordered by their block number descending.
	pub fn hashes(&self) -> Vec<H> {
		self.storage.iter().flat_map(|(_, hashes)| hashes.iter()).cloned().collect()
	}

	/// Write the leaf list to the database transaction.
	pub fn prepare_transaction(&mut self, tx: &mut DBTransaction, column: Option<u32>, prefix: &[u8]) {
		let mut buf = prefix.to_vec();
		for LeafSetItem { hash, number } in self.pending_added.drain(..) {
			hash.using_encoded(|s| buf.extend(s));
			tx.put_vec(column, &buf[..], number.0.encode());
			buf.truncate(prefix.len()); // reuse allocation.
		}
		for hash in self.pending_removed.drain(..) {
			hash.using_encoded(|s| buf.extend(s));
			tx.delete(column, &buf[..]);
			buf.truncate(prefix.len()); // reuse allocation.
		}
	}

	#[cfg(test)]
	fn contains(&self, number: N, hash: H) -> bool {
		self.storage.get(&Reverse(number)).map_or(false, |hashes| hashes.contains(&hash))
	}

	fn insert_leaf(&mut self, number: Reverse<N>, hash: H) {
		self.storage.entry(number).or_insert_with(Vec::new).push(hash);
	}

	// returns true if this leaf was contained, false otherwise.
	fn remove_leaf(&mut self, number: &Reverse<N>, hash: &H) -> bool {
		let mut empty = false;
		let removed = self.storage.get_mut(number).map_or(false, |leaves| {
			let mut found = false;
			leaves.retain(|h| if h == hash {
				found = true;
				false
			} else {
				true
			});

			if leaves.is_empty() { empty = true }

			found
		});

		if removed && empty {
			self.storage.remove(number);
		}

		removed
	}
}

/// Helper for undoing operations.
pub struct Undo<'a, H: 'a, N: 'a> {
	inner: &'a mut LeafSet<H, N>,
}

impl<'a, H: 'a, N: 'a> Undo<'a, H, N> where
	H: Clone + PartialEq + Decode + Encode,
	N: std::fmt::Debug + Clone + SimpleArithmetic + Decode + Encode,
{
	/// Undo an imported block by providing the displaced leaf.
	pub fn undo_import(&mut self, displaced: ImportDisplaced<H, N>) {
		let new_number = Reverse(displaced.displaced.number.0.clone() + N::one());
		self.inner.remove_leaf(&new_number, &displaced.new_hash);
		self.inner.insert_leaf(new_number, displaced.displaced.hash);
	}

	/// Undo a finalization operation by providing the displaced leaves.
	pub fn undo_finalization(&mut self, mut displaced: FinalizationDisplaced<H, N>) {
		self.inner.storage.append(&mut displaced.leaves);
	}
}

impl<'a, H: 'a, N: 'a> Drop for Undo<'a, H, N> {
	fn drop(&mut self) {
		self.inner.pending_added.clear();
		self.inner.pending_removed.clear();
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn it_works() {
		let mut set = LeafSet::new();
		set.import(0u32, 0u32, 0u32);

		set.import(1_1, 1, 0);
		set.import(2_1, 2, 1_1);
		set.import(3_1, 3, 2_1);

		assert!(set.contains(3, 3_1));
		assert!(!set.contains(2, 2_1));
		assert!(!set.contains(1, 1_1));
		assert!(!set.contains(0, 0));

		set.import(2_2, 2, 1_1);

		assert!(set.contains(3, 3_1));
		assert!(set.contains(2, 2_2));
	}

	#[test]
	fn flush_to_disk() {
		const PREFIX: &[u8] = b"abcdefg";
		let db = ::kvdb_memorydb::create(0);

		let mut set = LeafSet::new();
		set.import(0u32, 0u32, 0u32);

		set.import(1_1, 1, 0);
		set.import(2_1, 2, 1_1);
		set.import(3_1, 3, 2_1);

		let mut tx = DBTransaction::new();

		set.prepare_transaction(&mut tx, None, PREFIX);
		db.write(tx).unwrap();

		let set2 = LeafSet::read_from_db(&db, None, PREFIX).unwrap();
		assert_eq!(set, set2);
	}

	#[test]
	fn two_leaves_same_height_can_be_included() {
		let mut set = LeafSet::new();

		set.import(1_1u32, 10u32,0u32);
		set.import(1_2, 10, 0);

		assert!(set.storage.contains_key(&Reverse(10)));
		assert!(set.contains(10, 1_1));
		assert!(set.contains(10, 1_2));
		assert!(!set.contains(10, 1_3));
	}

	#[test]
	fn finalization_consistent_with_disk() {
		const PREFIX: &[u8] = b"prefix";
		let db = ::kvdb_memorydb::create(0);

		let mut set = LeafSet::new();
		set.import(10_1u32, 10u32, 0u32);
		set.import(11_1, 11, 10_2);
		set.import(11_2, 11, 10_2);
		set.import(12_1, 12, 11_123);

		assert!(set.contains(10, 10_1));

		let mut tx = DBTransaction::new();
		set.prepare_transaction(&mut tx, None, PREFIX);
		db.write(tx).unwrap();

		let _ = set.finalize_height(11);
		let mut tx = DBTransaction::new();
		set.prepare_transaction(&mut tx, None, PREFIX);
		db.write(tx).unwrap();

		assert!(set.contains(11, 11_1));
		assert!(set.contains(11, 11_2));
		assert!(set.contains(12, 12_1));
		assert!(!set.contains(10, 10_1));

		let set2 = LeafSet::read_from_db(&db, None, PREFIX).unwrap();
		assert_eq!(set, set2);
	}

	#[test]
	fn undo_finalization() {
		let mut set = LeafSet::new();
		set.import(10_1u32, 10u32, 0u32);
		set.import(11_1, 11, 10_2);
		set.import(11_2, 11, 10_2);
		set.import(12_1, 12, 11_123);

		let displaced = set.finalize_height(11);
		assert!(!set.contains(10, 10_1));

		set.undo().undo_finalization(displaced);
		assert!(set.contains(10, 10_1));
	}
}
