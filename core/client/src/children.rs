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


use std::collections::HashMap;
use kvdb::{KeyValueDB, DBTransaction};
use parity_codec::{Encode, Decode};
use crate::error;
use std::hash::Hash;


/// Map of children blocks stored in memory for fast access.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ChildrenMap<K, V> where 
	K: Eq + Hash + Clone + Encode + Decode,
	V: Eq + Hash + Clone + Encode + Decode,
{
	storage: HashMap<K, Vec<V>>,
}

impl<K, V> ChildrenMap<K, V> where
	K: Eq + Hash + Clone + Encode + Decode,
	V: Eq + Hash + Clone + Encode + Decode,
{
	/// Creates an empty children map.
	pub fn new() -> Self {
		Self {
			storage: HashMap::new(),
		}
	}

	/// Returns the hashes of the children blocks of the block with `parent_hash`.
	pub fn hashes(&self, db: &KeyValueDB, column: Option<u32>, prefix: &[u8], parent_hash: K) -> error::Result<Vec<V>> {
		let mut buf = prefix.to_vec();
		parent_hash.using_encoded(|s| buf.extend(s));

		let raw_val_opt = match db.get(column, &buf[..]) {
			Ok(raw_val_opt) => raw_val_opt,
			Err(_) => return Err(error::ErrorKind::Backend("Error reading value from database".into()).into()),
		};

		let raw_val = match raw_val_opt {
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
		self.storage.get(&parent_hash).cloned().unwrap_or_default()
	}

	/// Import the hash `child_hash` as child of `parent_hash`.
	/// It doesn't save changes to database.
	pub fn import(&mut self, parent_hash: K, child_hash: V) {
		self.storage.entry(parent_hash).or_insert_with(Vec::new).push(child_hash);
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
		
		let _ = children.prepare_transaction(&db, &mut tx, None, PREFIX);
		db.write(tx).unwrap();
		
		let r1: Vec<u32> = children.hashes(&db, None, PREFIX, 1_1).unwrap();
		let r2: Vec<u32> = children.hashes(&db, None, PREFIX, 1_2).unwrap();
		
		assert_eq!(r1, vec![1_3, 1_5]);
		assert_eq!(r2, vec![1_4, 1_6]);
	}
}