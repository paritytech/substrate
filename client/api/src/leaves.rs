// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! Helper for managing the set of available leaves in the chain for DB implementations.

use codec::{Decode, Encode};
use sp_blockchain::{Error, Result};
use sp_database::{Database, Transaction};
use sp_runtime::traits::AtLeast32Bit;
use std::{cmp::Reverse, collections::BTreeMap};

type DbHash = sp_core::H256;

#[derive(Debug, Clone, PartialEq, Eq)]
struct LeafSetItem<H, N> {
	hash: H,
	number: Reverse<N>,
}

/// Inserted and removed leaves after an import action.
pub struct ImportOutcome<H, N> {
	inserted: LeafSetItem<H, N>,
	removed: Option<H>,
}

/// Inserted and removed leaves after a remove action.
pub struct RemoveOutcome<H, N> {
	inserted: Option<H>,
	removed: LeafSetItem<H, N>,
}

/// Removed leaves after a finalization action.
pub struct FinalizationOutcome<H, N> {
	removed: BTreeMap<Reverse<N>, Vec<H>>,
}

impl<H, N: Ord> FinalizationOutcome<H, N> {
	/// Merge with another. This should only be used for displaced items that
	/// are produced within one transaction of each other.
	pub fn merge(&mut self, mut other: Self) {
		// this will ignore keys that are in duplicate, however
		// if these are actually produced correctly via the leaf-set within
		// one transaction, then there will be no overlap in the keys.
		self.removed.append(&mut other.removed);
	}

	/// Iterate over all displaced leaves.
	pub fn leaves(&self) -> impl Iterator<Item = &H> {
		self.removed.values().flatten()
	}
}

/// list of leaf hashes ordered by number (descending).
/// stored in memory for fast access.
/// this allows very fast checking and modification of active leaves.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LeafSet<H, N> {
	storage: BTreeMap<Reverse<N>, Vec<H>>,
}

impl<H, N> LeafSet<H, N>
where
	H: Clone + PartialEq + Decode + Encode,
	N: std::fmt::Debug + Clone + AtLeast32Bit + Decode + Encode,
{
	/// Construct a new, blank leaf set.
	pub fn new() -> Self {
		Self { storage: BTreeMap::new() }
	}

	/// Read the leaf list from the DB, using given prefix for keys.
	pub fn read_from_db(db: &dyn Database<DbHash>, column: u32, prefix: &[u8]) -> Result<Self> {
		let mut storage = BTreeMap::new();

		match db.get(column, prefix) {
			Some(leaves) => {
				let vals: Vec<_> = match Decode::decode(&mut leaves.as_ref()) {
					Ok(vals) => vals,
					Err(_) => return Err(Error::Backend("Error decoding leaves".into())),
				};
				for (number, hashes) in vals.into_iter() {
					storage.insert(Reverse(number), hashes);
				}
			},
			None => {},
		}
		Ok(Self { storage })
	}

	/// Update the leaf list on import.
	pub fn import(&mut self, hash: H, number: N, parent_hash: H) -> ImportOutcome<H, N> {
		let number = Reverse(number);

		let removed = if number.0 != N::zero() {
			let parent_number = Reverse(number.0.clone() - N::one());
			self.remove_leaf(&parent_number, &parent_hash).then(|| parent_hash)
		} else {
			None
		};

		self.insert_leaf(number.clone(), hash.clone());

		ImportOutcome { inserted: LeafSetItem { hash, number }, removed }
	}

	/// Update the leaf list on removal.
	///
	/// Note that the leaves set structure doesn't have the information to decide if the
	/// leaf we're removing is the last children of the parent. Follows that this method requires
	/// the caller to check this condition and optionally pass the `parent_hash` if `hash` is
	/// its last child.
	///
	/// Returns `None` if no modifications are applied.
	pub fn remove(
		&mut self,
		hash: H,
		number: N,
		parent_hash: Option<H>,
	) -> Option<RemoveOutcome<H, N>> {
		let number = Reverse(number);

		if !self.remove_leaf(&number, &hash) {
			return None
		}

		let inserted = parent_hash.and_then(|parent_hash| {
			if number.0 != N::zero() {
				let parent_number = Reverse(number.0.clone() - N::one());
				self.insert_leaf(parent_number, parent_hash.clone());
				Some(parent_hash)
			} else {
				None
			}
		});

		Some(RemoveOutcome { inserted, removed: LeafSetItem { hash, number } })
	}

	/// Note a block height finalized, displacing all leaves with number less than the finalized
	/// block's.
	///
	/// Although it would be more technically correct to also prune out leaves at the
	/// same number as the finalized block, but with different hashes, the current behavior
	/// is simpler and our assumptions about how finalization works means that those leaves
	/// will be pruned soon afterwards anyway.
	pub fn finalize_height(&mut self, number: N) -> FinalizationOutcome<H, N> {
		let boundary = if number == N::zero() {
			return FinalizationOutcome { removed: BTreeMap::new() }
		} else {
			number - N::one()
		};

		let below_boundary = self.storage.split_off(&Reverse(boundary));
		FinalizationOutcome { removed: below_boundary }
	}

	/// The same as [`Self::finalize_height`], but it only simulates the operation.
	///
	/// This means that no changes are done.
	///
	/// Returns the leaves that would be displaced by finalizing the given block.
	pub fn displaced_by_finalize_height(&self, number: N) -> FinalizationOutcome<H, N> {
		let boundary = if number == N::zero() {
			return FinalizationOutcome { removed: BTreeMap::new() }
		} else {
			number - N::one()
		};

		let below_boundary = self.storage.range(&Reverse(boundary)..);
		FinalizationOutcome {
			removed: below_boundary.map(|(k, v)| (k.clone(), v.clone())).collect(),
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

	/// Revert to the given block height by dropping all leaves in the leaf set
	/// with a block number higher than the target.
	pub fn revert(&mut self, best_hash: H, best_number: N) {
		let items = self
			.storage
			.iter()
			.flat_map(|(number, hashes)| hashes.iter().map(move |h| (h.clone(), number.clone())))
			.collect::<Vec<_>>();

		for (hash, number) in &items {
			if number.0 > best_number {
				assert!(
					self.remove_leaf(number, hash),
					"item comes from an iterator over storage; qed",
				);
			}
		}

		let best_number = Reverse(best_number);
		let leaves_contains_best = self
			.storage
			.get(&best_number)
			.map_or(false, |hashes| hashes.contains(&best_hash));

		// we need to make sure that the best block exists in the leaf set as
		// this is an invariant of regular block import.
		if !leaves_contains_best {
			self.insert_leaf(best_number.clone(), best_hash.clone());
		}
	}

	/// returns an iterator over all hashes in the leaf set
	/// ordered by their block number descending.
	pub fn hashes(&self) -> Vec<H> {
		self.storage.iter().flat_map(|(_, hashes)| hashes.iter()).cloned().collect()
	}

	/// Number of known leaves.
	pub fn count(&self) -> usize {
		self.storage.values().map(|level| level.len()).sum()
	}

	/// Write the leaf list to the database transaction.
	pub fn prepare_transaction(
		&mut self,
		tx: &mut Transaction<DbHash>,
		column: u32,
		prefix: &[u8],
	) {
		let leaves: Vec<_> = self.storage.iter().map(|(n, h)| (n.0.clone(), h.clone())).collect();
		tx.set_from_vec(column, prefix, leaves.encode());
	}

	/// Check if given block is a leaf.
	pub fn contains(&self, number: N, hash: H) -> bool {
		self.storage
			.get(&Reverse(number))
			.map_or(false, |hashes| hashes.contains(&hash))
	}

	fn insert_leaf(&mut self, number: Reverse<N>, hash: H) {
		self.storage.entry(number).or_insert_with(Vec::new).push(hash);
	}

	// Returns true if this leaf was contained, false otherwise.
	fn remove_leaf(&mut self, number: &Reverse<N>, hash: &H) -> bool {
		let mut empty = false;
		let removed = self.storage.get_mut(number).map_or(false, |leaves| {
			let mut found = false;
			leaves.retain(|h| {
				if h == hash {
					found = true;
					false
				} else {
					true
				}
			});

			if leaves.is_empty() {
				empty = true
			}

			found
		});

		if removed && empty {
			self.storage.remove(number);
		}

		removed
	}

	/// Returns the highest leaf and all hashes associated to it.
	pub fn highest_leaf(&self) -> Option<(N, &[H])> {
		self.storage.iter().next().map(|(k, v)| (k.0.clone(), &v[..]))
	}
}

/// Helper for undoing operations.
pub struct Undo<'a, H: 'a, N: 'a> {
	inner: &'a mut LeafSet<H, N>,
}

impl<'a, H: 'a, N: 'a> Undo<'a, H, N>
where
	H: Clone + PartialEq + Decode + Encode,
	N: std::fmt::Debug + Clone + AtLeast32Bit + Decode + Encode,
{
	/// Undo an imported block by providing the import operation outcome.
	/// No additional operations should be performed between import and undo.
	pub fn undo_import(&mut self, outcome: ImportOutcome<H, N>) {
		if let Some(removed_hash) = outcome.removed {
			let removed_number = Reverse(outcome.inserted.number.0.clone() - N::one());
			self.inner.insert_leaf(removed_number, removed_hash);
		}
		self.inner.remove_leaf(&outcome.inserted.number, &outcome.inserted.hash);
	}

	/// Undo a removed block by providing the displaced leaf.
	/// No additional operations should be performed between remove and undo.
	pub fn undo_remove(&mut self, outcome: RemoveOutcome<H, N>) {
		if let Some(inserted_hash) = outcome.inserted {
			let inserted_number = Reverse(outcome.removed.number.0.clone() - N::one());
			self.inner.remove_leaf(&inserted_number, &inserted_hash);
		}
		self.inner.insert_leaf(outcome.removed.number, outcome.removed.hash);
	}

	/// Undo a finalization operation by providing the displaced leaves.
	/// No additional operations should be performed between finalization and undo.
	pub fn undo_finalization(&mut self, mut outcome: FinalizationOutcome<H, N>) {
		self.inner.storage.append(&mut outcome.removed);
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use std::sync::Arc;

	#[test]
	fn import_works() {
		let mut set = LeafSet::new();
		set.import(0u32, 0u32, 0u32);

		set.import(1_1, 1, 0);
		set.import(2_1, 2, 1_1);
		set.import(3_1, 3, 2_1);

		assert_eq!(set.count(), 1);
		assert!(set.contains(3, 3_1));
		assert!(!set.contains(2, 2_1));
		assert!(!set.contains(1, 1_1));
		assert!(!set.contains(0, 0));

		set.import(2_2, 2, 1_1);
		set.import(1_2, 1, 0);
		set.import(2_3, 2, 1_2);

		assert_eq!(set.count(), 3);
		assert!(set.contains(3, 3_1));
		assert!(set.contains(2, 2_2));
		assert!(set.contains(2, 2_3));

		// Finally test the undo feature

		let outcome = set.import(2_4, 2, 1_1);
		assert_eq!(outcome.inserted.hash, 2_4);
		assert_eq!(outcome.removed, None);
		assert_eq!(set.count(), 4);
		assert!(set.contains(2, 2_4));

		set.undo().undo_import(outcome);
		assert_eq!(set.count(), 3);
		assert!(set.contains(3, 3_1));
		assert!(set.contains(2, 2_2));
		assert!(set.contains(2, 2_3));

		let outcome = set.import(3_2, 3, 2_3);
		assert_eq!(outcome.inserted.hash, 3_2);
		assert_eq!(outcome.removed, Some(2_3));
		assert_eq!(set.count(), 3);
		assert!(set.contains(3, 3_2));

		set.undo().undo_import(outcome);
		assert_eq!(set.count(), 3);
		assert!(set.contains(3, 3_1));
		assert!(set.contains(2, 2_2));
		assert!(set.contains(2, 2_3));
	}

	#[test]
	fn removal_works() {
		let mut set = LeafSet::new();
		set.import(10_1u32, 10u32, 0u32);
		set.import(11_1, 11, 10_1);
		set.import(11_2, 11, 10_1);
		set.import(12_1, 12, 11_1);

		let outcome = set.remove(12_1, 12, Some(11_1)).unwrap();
		assert_eq!(outcome.removed.hash, 12_1);
		assert_eq!(outcome.inserted, Some(11_1));
		assert_eq!(set.count(), 2);
		assert!(set.contains(11, 11_1));
		assert!(set.contains(11, 11_2));

		let outcome = set.remove(11_1, 11, None).unwrap();
		assert_eq!(outcome.removed.hash, 11_1);
		assert_eq!(outcome.inserted, None);
		assert_eq!(set.count(), 1);
		assert!(set.contains(11, 11_2));

		let outcome = set.remove(11_2, 11, Some(10_1)).unwrap();
		assert_eq!(outcome.removed.hash, 11_2);
		assert_eq!(outcome.inserted, Some(10_1));
		assert_eq!(set.count(), 1);
		assert!(set.contains(10, 10_1));

		set.undo().undo_remove(outcome);
		assert_eq!(set.count(), 1);
		assert!(set.contains(11, 11_2));
	}

	#[test]
	fn finalization_works() {
		let mut set = LeafSet::new();
		set.import(9_1u32, 9u32, 0u32);
		set.import(10_1, 10, 9_1);
		set.import(10_2, 10, 9_1);
		set.import(11_1, 11, 10_1);
		set.import(11_2, 11, 10_1);
		set.import(12_1, 12, 11_2);

		let outcome = set.finalize_height(11);
		assert_eq!(set.count(), 2);
		assert!(set.contains(11, 11_1));
		assert!(set.contains(12, 12_1));
		assert_eq!(
			outcome.removed,
			[(Reverse(10), vec![10_2])].into_iter().collect::<BTreeMap<_, _>>(),
		);

		set.undo().undo_finalization(outcome);
		assert_eq!(set.count(), 3);
		assert!(set.contains(11, 11_1));
		assert!(set.contains(12, 12_1));
		assert!(set.contains(10, 10_2));
	}

	#[test]
	fn flush_to_disk() {
		const PREFIX: &[u8] = b"abcdefg";
		let db = Arc::new(sp_database::MemDb::default());

		let mut set = LeafSet::new();
		set.import(0u32, 0u32, 0u32);

		set.import(1_1, 1, 0);
		set.import(2_1, 2, 1_1);
		set.import(3_1, 3, 2_1);

		let mut tx = Transaction::new();

		set.prepare_transaction(&mut tx, 0, PREFIX);
		db.commit(tx).unwrap();

		let set2 = LeafSet::read_from_db(&*db, 0, PREFIX).unwrap();
		assert_eq!(set, set2);
	}

	#[test]
	fn two_leaves_same_height_can_be_included() {
		let mut set = LeafSet::new();

		set.import(1_1u32, 10u32, 0u32);
		set.import(1_2, 10, 0);

		assert!(set.storage.contains_key(&Reverse(10)));
		assert!(set.contains(10, 1_1));
		assert!(set.contains(10, 1_2));
		assert!(!set.contains(10, 1_3));
	}

	#[test]
	fn finalization_consistent_with_disk() {
		const PREFIX: &[u8] = b"prefix";
		let db = Arc::new(sp_database::MemDb::default());

		let mut set = LeafSet::new();
		set.import(10_1u32, 10u32, 0u32);
		set.import(11_1, 11, 10_2);
		set.import(11_2, 11, 10_2);
		set.import(12_1, 12, 11_123);

		assert!(set.contains(10, 10_1));

		let mut tx = Transaction::new();
		set.prepare_transaction(&mut tx, 0, PREFIX);
		db.commit(tx).unwrap();

		let _ = set.finalize_height(11);
		let mut tx = Transaction::new();
		set.prepare_transaction(&mut tx, 0, PREFIX);
		db.commit(tx).unwrap();

		assert!(set.contains(11, 11_1));
		assert!(set.contains(11, 11_2));
		assert!(set.contains(12, 12_1));
		assert!(!set.contains(10, 10_1));

		let set2 = LeafSet::read_from_db(&*db, 0, PREFIX).unwrap();
		assert_eq!(set, set2);
	}
}
