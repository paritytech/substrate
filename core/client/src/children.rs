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

//! Functionality for reading and storing children hashes from db.

use kvdb::{KeyValueDB, DBTransaction};
use parity_codec::{Encode, Decode};
use crate::error;
use std::hash::Hash;


/// Returns the hashes of the children blocks of the block with `parent_hash`.
pub fn read_children<
	K: Eq + Hash + Clone + Encode + Decode,
	V: Eq + Hash + Clone + Encode + Decode,
>(db: &KeyValueDB, column: Option<u32>, prefix: &[u8], parent_hash: K) -> error::Result<Vec<V>> {
	let mut buf = prefix.to_vec();
	parent_hash.using_encoded(|s| buf.extend(s));

	let raw_val_opt = match db.get(column, &buf[..]) {
		Ok(raw_val_opt) => raw_val_opt,
		Err(_) => return Err(error::Error::Backend("Error reading value from database".into())),
	};

	let raw_val = match raw_val_opt {
		Some(val) => val,
		None => return Ok(Vec::new()),
	};

	let children: Vec<V> = match Decode::decode(&mut &raw_val[..]) {
		Some(children) => children,
		None => return Err(error::Error::Backend("Error decoding children".into())),
	};

	Ok(children)
}

/// Insert the key-value pair (`parent_hash`, `children_hashes`) in the transaction.
/// Any existing value is overwritten upon write.
pub fn write_children<
	K: Eq + Hash + Clone + Encode + Decode,
	V: Eq + Hash + Clone + Encode + Decode,
>(
	tx: &mut DBTransaction,
	column: Option<u32>,
	prefix: &[u8],
	parent_hash: K,
	children_hashes: V,
) {
	let mut key = prefix.to_vec();
	parent_hash.using_encoded(|s| key.extend(s));
	tx.put_vec(column, &key[..], children_hashes.encode());
}

/// Prepare transaction to remove the children of `parent_hash`.
pub fn remove_children<
	K: Eq + Hash + Clone + Encode + Decode,
>(
	tx: &mut DBTransaction,
	column: Option<u32>,
	prefix: &[u8],
	parent_hash: K,
) {
	let mut key = prefix.to_vec();
	parent_hash.using_encoded(|s| key.extend(s));
	tx.delete(column, &key[..]);
}


#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn children_write_read_remove() {
		const PREFIX: &[u8] = b"children";
		let db = ::kvdb_memorydb::create(0);

		let mut tx = DBTransaction::new();

		let mut children1 = Vec::new();
		children1.push(1_3);
		children1.push(1_5);
		write_children(&mut tx, None, PREFIX, 1_1, children1);

		let mut children2 = Vec::new();
		children2.push(1_4);
		children2.push(1_6);
		write_children(&mut tx, None, PREFIX, 1_2, children2);

		db.write(tx.clone()).unwrap();

		let r1: Vec<u32> = read_children(&db, None, PREFIX, 1_1).unwrap();
		let r2: Vec<u32> = read_children(&db, None, PREFIX, 1_2).unwrap();

		assert_eq!(r1, vec![1_3, 1_5]);
		assert_eq!(r2, vec![1_4, 1_6]);

		remove_children(&mut tx, None, PREFIX, 1_2);
		db.write(tx).unwrap();

		let r1: Vec<u32> = read_children(&db, None, PREFIX, 1_1).unwrap();
		let r2: Vec<u32> = read_children(&db, None, PREFIX, 1_2).unwrap();

		assert_eq!(r1, vec![1_3, 1_5]);
		assert_eq!(r2.len(), 0);		
	}
}
