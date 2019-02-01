// Copyright 2019 Parity Technologies (UK) Ltd.
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


use std::collections::BTreeMap;
use std::cmp::Ord;
use kvdb::{KeyValueDB, DBTransaction};
use codec::{Encode, Decode};
use crate::error;
use std::hash::Hash;
use std::fmt::Debug;

/// Map of children blocks stored in memory for fast access.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ChildrenMap<K, V> where 
	K: Ord + Eq + Hash + Clone + Encode + Decode + Debug,
	V: Ord + Eq + Hash + Clone + Encode + Decode + Debug,
{
	storage: BTreeMap<K, Vec<V>>,
	pending_added: Vec<(K, V)>,
	pending_removed: Vec<(K, V)>,
}

impl<K, V> ChildrenMap<K, V> where
	K: Ord + Eq + Hash + Clone + Encode + Decode + Debug,
	V: Ord + Eq + Hash + Clone + Encode + Decode + Debug,
{
	/// Creates an empty children map.
	pub fn new() -> Self {
		Self {
			storage: BTreeMap::new(),
			pending_added: Vec::new(),
			pending_removed: Vec::new(),
		}
	}

	/// Reads a children map from DB.
	pub fn read_from_db(db: &KeyValueDB, column: Option<u32>, prefix: &[u8]) -> error::Result<Self> {
		let mut storage: BTreeMap<K, Vec<V>> = BTreeMap::new();
		for (key, value) in db.iter_from_prefix(column, prefix) {
			if !key.starts_with(prefix) { break }
			let raw_hash = &mut &key[prefix.len()..];
			let parent_hash = match Decode::decode(raw_hash) {
				Some(hash) => hash,
				None => return Err(error::ErrorKind::Backend("Error decoding hash".into()).into()),
			};
			let raw_value = &mut &value[..];
			let child = match Decode::decode(raw_value) {
				Some(child) => child,
				None => return Err(error::ErrorKind::Backend("Error decoding child".into()).into()),
			};

			match storage.get_mut(&parent_hash) {
				Some(children) => {
					children.push(child);
				},
				None => {
					storage.insert(parent_hash, vec![child]);
				}
			};
		}
		Ok(Self {
			storage,
			pending_added: Vec::new(),
			pending_removed: Vec::new(),
		})
	}

	/// Update the children list on import.
	pub fn import(&mut self, parent_hash: K, hash: V) {
		match self.storage.get_mut(&parent_hash) {
			Some(children) => {
				children.push(hash.clone());
			}
			None => { 
				self.storage.insert(parent_hash.clone(), vec![hash.clone()]);
			}
		};
		self.pending_added.push((parent_hash, hash));
	}

	/// Write the children list to the database transaction.
	pub fn prepare_transaction(&mut self, tx: &mut DBTransaction, column: Option<u32>, prefix: &[u8]) {
		let mut buf = prefix.to_vec();
		for (parent, child) in self.pending_added.drain(..) {
			parent.using_encoded(|s| buf.extend(s));
			tx.put_vec(column, &buf[..], child.encode());
			buf.truncate(prefix.len()); // reuse allocation.
		}
	}

	/// Gets the hashes of the children blocks of `parent_hash`.
	pub fn hashes(&self, parent_hash: K) -> Vec<V> {
		match self.storage.get(&parent_hash) {
			Some(children) => children.clone(),
			None => vec![],
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn children_works() {
		let mut children = ChildrenMap::new();

		children.import(0u32, 0u32);
		children.import(1_1, 1_3);
		children.import(1_2, 1_4);

		assert!(children.storage.contains_key(&1_1));
		assert!(children.storage.contains_key(&1_2));
		assert!(!children.storage.contains_key(&1_3));
		assert!(!children.storage.contains_key(&1_4));
	}

	#[test]
	fn children_hashes() {
		let mut children = ChildrenMap::new();

		children.import(0u32, 0u32);
		children.import(1_1, 1_3);
		children.import(1_2, 1_4);
		children.import(1_2, 1_5);

		assert_eq!(children.hashes(1_1), vec![1_3]);
		assert_eq!(children.hashes(1_2), vec![1_4, 1_5]);
	}

	#[test]
	fn children_flush() {
		const PREFIX: &[u8] = b"a";
		let db = ::kvdb_memorydb::create(0);

		let mut children = ChildrenMap::new();
		children.import(0u32, 0u32);
		children.import(1_1, 1_3);
		children.import(1_2, 1_4);

		let mut tx = DBTransaction::new();

		children.prepare_transaction(&mut tx, None, PREFIX);
		db.write(tx).unwrap();

		let children2 = ChildrenMap::read_from_db(&db, None, PREFIX).unwrap();
		assert_eq!(children, children2);
	}
}