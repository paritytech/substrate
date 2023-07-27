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


use node_primitives::{Block, Hash};
use sp_runtime::traits::BlakeTwo256;
use sp_trie::trie_types::TrieDBMutBuilderV1;

/// Generate trie from given `key_values`.
///
/// Will fill your database `db` with trie data from `key_values` and
/// return root.
pub fn generate_trie(
	db: sc_client_db::StorageDb<Block>,
	key_values: impl IntoIterator<Item = (Vec<u8>, Vec<u8>)>,
) -> Hash {
	/*
	overlay.emplace(
		array_bytes::hex2bytes(
			"03170a2e7597b7b7e3d84c05391d139a62b157e78786d8c082f29dcf4c111314",
		)
		.expect("null key is valid"),
		Default::default(),
		vec![0],
	);
	*/
	let mut trie_db =
		TrieDBMutBuilderV1::<BlakeTwo256>::new(&db).build();
	for (key, value) in key_values {
		trie_db.insert(&key, &value).expect("trie insertion failed");
	}

	let commit = trie_db.commit();
	let root = commit.root_hash();

	let mut transaction = sc_client_db::Transaction::default();
	let trie_commit = sp_state_machine::TrieCommit {
		main: commit,
		child: Default::default(),
	};
	sc_client_db::apply_tree_commit::<BlakeTwo256>(trie_commit, db.state_db.is_none(),  &mut transaction);
	
	db.db.commit(transaction).expect("Failed to write transaction");

	root
}
