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

use kvdb::{KeyValueDB, DBTransaction};
use parity_codec::{Encode, Decode};
use crate::error;
use std::hash::Hash;


/// Map of father to children blocks.
pub struct ChildrenMap;

impl ChildrenMap {
	/// Returns the hashes of the children blocks of the block with `parent_hash`.
	pub fn children_hashes<
		K: Eq + Hash + Clone + Encode + Decode,
		V: Eq + Hash + Clone + Encode + Decode,
	>(db: &KeyValueDB, column: Option<u32>, prefix: &[u8], parent_hash: K) -> error::Result<Vec<V>> {
		let mut buf = prefix.to_vec();
		parent_hash.using_encoded(|s| buf.extend(s));

		let raw_val_opt = match db.get(column, &buf[..]) {
			Ok(raw_val_opt) => raw_val_opt,
			Err(_) => return Err(error::ErrorKind::Backend("Error reading value from database".into()).into()),
		};

		let raw_val = match raw_val_opt {
			Some(val) => val,
			None => return Ok(Vec::new()),
		};

		let children: Vec<V> = match Decode::decode(&mut &raw_val[..]) {
			Some(children) => children,
			None => return Err(error::ErrorKind::Backend("Error decoding children".into()).into()),
		};

		Ok(children)
	}

	/// Prepare the database transaction `tx` that adds `child_hash` to the children of `parent_hash`.
	pub fn prepare_transaction<
		K: Eq + Hash + Clone + Encode + Decode,
		V: Eq + Hash + Clone + Encode + Decode,
	>(
		db: &KeyValueDB,
		tx: &mut DBTransaction,
		column: Option<u32>,
		prefix: &[u8],
		parent_hash: K,
		child_hash: V,
	) -> error::Result<()> {
		let mut children_db = Self::children_hashes(db, column, prefix, parent_hash.clone())?;
		children_db.push(child_hash);
		let mut buf = prefix.to_vec();
		parent_hash.using_encoded(|s| buf.extend(s));
		tx.put_vec(column, &buf[..], children_db.encode());
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