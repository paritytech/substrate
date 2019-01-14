// Copyright 2018 Parity Technologies (UK) Ltd.
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

use std::collections::BTreeSet;
use std::cmp::{Ord, Ordering};
use kvdb::{KeyValueDB, DBTransaction};
use runtime_primitives::traits::SimpleArithmetic;
use codec::{Encode, Decode};
use error;

/// helper wrapper type to keep a list of block hashes ordered
/// by `number` descending in a `BTreeSet` which allows faster and simpler
/// insertion and removal than keeping them in a list.
#[derive(Debug, Clone)]
struct LeafSetItem<H, N> {
	hash: H,
	number: N,
}

impl<H, N> Ord for LeafSetItem<H, N> where N: Ord {
	fn cmp(&self, other: &Self) -> Ordering {
		// reverse (descending) order
		other.number.cmp(&self.number)
	}
}

impl<H, N> PartialOrd for LeafSetItem<H, N> where N: PartialOrd {
	fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
		// reverse (descending) order
		other.number.partial_cmp(&self.number)
	}
}

impl<H, N> PartialEq for LeafSetItem<H, N> where N: PartialEq {
	fn eq(&self, other: &LeafSetItem<H, N>) -> bool {
		self.number == other.number
	}
}

impl<H, N> Eq for LeafSetItem<H, N> where N: PartialEq {}

/// A displaced leaf after import.
pub struct DisplacedLeaf<H, N> {
	new_hash: H,
	displaced: LeafSetItem<H, N>,
}

/// list of leaf hashes ordered by number (descending).
/// stored in memory for fast access.
/// this allows very fast checking and modification of active leaves.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LeafSet<H, N> {
	storage: BTreeSet<LeafSetItem<H, N>>,
	pending_added: Vec<LeafSetItem<H, N>>,
	pending_removed: Vec<H>,
}

impl<H, N> LeafSet<H, N> where
	H: Clone + Decode + Encode,
	N: Clone + SimpleArithmetic + Decode + Encode,
{
	/// Construct a new, blank leaf set.
	pub fn new() -> Self {
		Self {
			storage: BTreeSet::new(),
			pending_added: Vec::new(),
			pending_removed: Vec::new(),
		}
	}

	/// Read the leaf list from the DB, using given prefix for keys.
	pub fn read_from_db(db: &KeyValueDB, column: Option<u32>, prefix: &[u8]) -> error::Result<Self> {
		let mut storage = BTreeSet::new();

		for (key, value) in db.iter_from_prefix(column, prefix) {
			if !key.starts_with(prefix) { break }
			let raw_hash = &mut &key[prefix.len()..];
			let hash = match Decode::decode(raw_hash) {
				Some(hash) => hash,
				None => return Err(error::ErrorKind::Backend("Error decoding hash".into()).into()),
			};
			let number = match Decode::decode(&mut &value[..]) {
				Some(number) => number,
				None => return Err(error::ErrorKind::Backend("Error decoding number".into()).into()),
			};
			storage.insert(LeafSetItem { hash, number });
		}
		Ok(Self {
			storage,
			pending_added: Vec::new(),
			pending_removed: Vec::new(),
		})
	}

	/// update the leaf list on import. returns a displaced leaf if there was one.
	pub fn import(&mut self, hash: H, number: N, parent_hash: H) -> Option<DisplacedLeaf<H, N>> {
		// avoid underflow for genesis.
		let displaced = if number != N::zero() {
			let displaced = LeafSetItem {
				hash: parent_hash.clone(),
				number: number.clone() - N::one(),
			};
			let was_displaced = self.storage.remove(&displaced);

			if was_displaced {
				self.pending_removed.push(parent_hash);
				Some(DisplacedLeaf {
					new_hash: hash.clone(),
					displaced,
				})
			} else {
				None
			}
		} else {
			None
		};

		let item = LeafSetItem { hash, number };
		self.storage.insert(item.clone());
		self.pending_added.push(item);
		displaced
	}

	/// Undo an import operation, with a displaced leaf.
	pub fn undo(&mut self, displaced: DisplacedLeaf<H, N>) {
		let new_number = displaced.displaced.number.clone() + N::one();
		self.storage.remove(&LeafSetItem { hash: displaced.new_hash, number: new_number });
		self.storage.insert(displaced.displaced);
		self.pending_added.clear();
		self.pending_removed.clear();
	}

	/// currently since revert only affects the canonical chain
	/// we assume that parent has no further children
	/// and we add it as leaf again
	pub fn revert(&mut self, hash: H, number: N, parent_hash: H) {
		self.storage.insert(LeafSetItem {
			hash: parent_hash,
			number: number.clone() - N::one(),
		});
		self.storage.remove(&LeafSetItem { hash, number });
	}

	/// returns an iterator over all hashes in the leaf set
	/// ordered by their block number descending.
	pub fn hashes(&self) -> Vec<H> {
		self.storage.iter().map(|item| item.hash.clone()).collect()
	}

	/// Write the leaf list to the database transaction.
	pub fn prepare_transaction(&mut self, tx: &mut DBTransaction, column: Option<u32>, prefix: &[u8]) {
		let mut buf = prefix.to_vec();
		for LeafSetItem { hash, number } in self.pending_added.drain(..) {
			hash.using_encoded(|s| buf.extend(s));
			tx.put_vec(column, &buf[..], number.encode());
			buf.truncate(prefix.len()); // reuse allocation.
		}
		for hash in self.pending_removed.drain(..) {
			hash.using_encoded(|s| buf.extend(s));
			tx.delete(column, &buf[..]);
			buf.truncate(prefix.len()); // reuse allocation.
		}
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

		assert!(set.storage.contains(&LeafSetItem { hash: 3_1, number: 3 }));
		assert!(!set.storage.contains(&LeafSetItem { hash: 2_1, number: 2 }));
		assert!(!set.storage.contains(&LeafSetItem { hash: 1_1, number: 1 }));
		assert!(!set.storage.contains(&LeafSetItem { hash: 0, number: 0 }));

		set.import(2_2, 2, 1_1);

		assert!(set.storage.contains(&LeafSetItem { hash: 3_1, number: 3 }));
		assert!(set.storage.contains(&LeafSetItem { hash: 2_2, number: 2 }));
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
}
