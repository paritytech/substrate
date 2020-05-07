// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
use std::{collections::HashMap, sync::Arc};

use kvdb::KeyValueDB;
use node_primitives::Hash;
use sp_trie::{trie_types::TrieDBMut, TrieMut};

use crate::simple_trie::SimpleTrie;

/// Generate trie from given `key_values`.
///
/// Will fill your database `db` with trie data from `key_values` and
/// return root.
pub fn generate_trie(
	db: Arc<dyn KeyValueDB>,
	key_values: impl IntoIterator<Item=(Vec<u8>, Vec<u8>)>,
) -> Hash {
	let mut root = Hash::default();

	let (db, overlay) = {
		let mut overlay = HashMap::new();
		overlay.insert(
			hex::decode("03170a2e7597b7b7e3d84c05391d139a62b157e78786d8c082f29dcf4c111314").expect("null key is valid"),
			Some(vec![0]),
		);
		let mut trie = SimpleTrie { db, overlay: &mut overlay };
		{
			let mut trie_db = TrieDBMut::new(&mut trie, &mut root);

			for (key, value) in key_values {
				trie_db.insert(&key, &value).expect("trie insertion failed");
			}

			trie_db.commit();
		}
		( trie.db, overlay )
	};

	let mut transaction = db.transaction();
	for (key, value) in overlay.into_iter() {
		match value {
			Some(value) => transaction.put(0, &key[..], &value[..]),
			None => transaction.delete(0, &key[..]),
		}
	}
	db.write(transaction).expect("Failed to write transaction");

	root
}
