// Copyright 2017-2019 Parity Technologies (UK) Ltd
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

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
