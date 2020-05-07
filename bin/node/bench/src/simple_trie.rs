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
use sp_trie::DBValue;
use hash_db::{HashDB, AsHashDB, Prefix, Hasher as _};

pub type Hasher = sp_core::Blake2Hasher;

/// Immutable generated trie database with root.
pub struct SimpleTrie<'a> {
	pub db: Arc<dyn KeyValueDB>,
	pub overlay: &'a mut HashMap<Vec<u8>, Option<Vec<u8>>>,
}

impl<'a> AsHashDB<Hasher, DBValue> for SimpleTrie<'a> {
	fn as_hash_db(&self) -> &dyn hash_db::HashDB<Hasher, DBValue> { &*self }

	fn as_hash_db_mut<'b>(&'b mut self) -> &'b mut (dyn HashDB<Hasher, DBValue> + 'b) {
		&mut *self
	}
}

impl<'a> HashDB<Hasher, DBValue> for SimpleTrie<'a> {
	fn get(&self, key: &Hash, prefix: Prefix) -> Option<DBValue> {
		let key = sp_trie::prefixed_key::<Hasher>(key, prefix);
		if let Some(value) = self.overlay.get(&key) {
			return value.clone();
		}
		self.db.get(0, &key).expect("Database backend error")
	}

	fn contains(&self, hash: &Hash, prefix: Prefix) -> bool {
		self.get(hash, prefix).is_some()
	}

	fn insert(&mut self, prefix: Prefix, value: &[u8]) -> Hash {
		let key = Hasher::hash(value);
		self.emplace(key, prefix, value.to_vec());
		key
	}

	fn emplace(&mut self, key: Hash, prefix: Prefix, value: DBValue) {
		let key = sp_trie::prefixed_key::<Hasher>(&key, prefix);
		self.overlay.insert(key, Some(value));
	}

	fn remove(&mut self, key: &Hash, prefix: Prefix) {
		let key = sp_trie::prefixed_key::<Hasher>(key, prefix);
		self.overlay.insert(key, None);
	}
}
