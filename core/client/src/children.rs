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
}

impl<K, V> ChildrenMap<K, V> where
	K: Ord + Eq + Hash + Clone + Encode + Decode + Debug,
	V: Ord + Eq + Hash + Clone + Encode + Decode + Debug,
{
	/// Creates an empty children map.
	pub fn new() -> Self {
		Self {
			storage: BTreeMap::new(),
		}
	}

	/// Returns the hashes of the children blocks of the block with `parent_hash`.
	pub fn hashes(&self, db: &KeyValueDB, column: Option<u32>, prefix: &[u8],
		parent_hash: K) -> error::Result<Vec<V>> {
		
		let mut buf = prefix.to_vec();
		parent_hash.using_encoded(|s| buf.extend(s));
		let raw_val = match db.get(column, &buf[..]).unwrap() {
			Some(val) => val,
			None => return Ok(vec![]),
		};
		let children: Vec<V> = match Decode::decode(&mut &raw_val[..]) {
			Some(children) => children,
			None => return Err(error::ErrorKind::Backend("Error decoding children".into()).into()),
		};
		Ok(children)
	}

	/// Returns the hashes of the children blocks of the block with `parent_hash`.
	/// It doesn't read the database.
	pub fn hashes_from_mem(&self, parent_hash: K) -> Vec<V> {
		match self.storage.get(&parent_hash) {
			Some(children) => children.clone(),
			None => vec![],
		}
	}

	/// Import the hash `child_hash` as child of `parent_hash`.
	/// It doesn't save changes to database.
	pub fn import(&mut self, parent_hash: K, child_hash: V) {
		match self.storage.get_mut(&parent_hash) {
			Some(children) => children.push(child_hash),
			None => { 
				self.storage.insert(parent_hash, vec![child_hash]);
			}
		}
	}

	/// Prepare the transaction `tx` that saves the content of the ChildrenMap to database.
	/// It clears the content of ChildrenMap.
	pub fn prepare_transaction(&mut self, db: &KeyValueDB, tx: &mut DBTransaction, column: Option<u32>, prefix: &[u8])
		-> error::Result<()> {
		for (parent_hash, children) in self.storage.iter() {
			let mut children_db = self.hashes(db, column, prefix, parent_hash.clone())?;
			children_db.extend(children.iter().cloned());
			let mut buf = prefix.to_vec();
			parent_hash.using_encoded(|s| buf.extend(s));
			tx.put_vec(column, &buf[..], children_db.encode());
		}
		self.storage.clear();
		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn children_write_read() {
		const PREFIX: &[u8] = b"children";
		let db = ::kvdb_memorydb::create(0);

		let mut children = ChildrenMap::new();
		let mut tx = DBTransaction::new();

		children.import(0u32, 0u32);
		children.import(1_1, 1_3);
		children.import(1_2, 1_4);
		children.import(1_1, 1_5);
		children.import(1_2, 1_6);
		
		children.prepare_transaction(&db, &mut tx, None, PREFIX);
		db.write(tx).unwrap();
		
		let r1: Vec<u32> = children.hashes(&db, None, PREFIX, 1_1).unwrap();
		let r2: Vec<u32> = children.hashes(&db, None, PREFIX, 1_2).unwrap();
		
		assert_eq!(r1, vec![1_3, 1_5]);
		assert_eq!(r2, vec![1_4, 1_6]);
	}
}