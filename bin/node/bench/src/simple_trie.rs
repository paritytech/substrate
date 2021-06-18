// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
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

use std::{collections::HashMap, sync::Arc};

use kvdb::KeyValueDB;
use node_primitives::Hash;
use sp_trie::{DBValue, Meta, StateHasher, MetaHasher};
use hash_db::{HashDB, AsHashDB, Prefix, Hasher as _};

pub type Hasher = sp_core::Blake2Hasher;

/// Immutable generated trie database with root.
pub struct SimpleTrie<'a> {
	pub db: Arc<dyn KeyValueDB>,
	pub overlay: &'a mut HashMap<Vec<u8>, Option<Vec<u8>>>,
}

impl<'a> AsHashDB<Hasher, DBValue, Meta, Option<u32>> for SimpleTrie<'a> {
	fn as_hash_db(&self) -> &dyn hash_db::HashDB<Hasher, DBValue, Meta, Option<u32>> { &*self }

	fn as_hash_db_mut<'b>(&'b mut self) -> &'b mut (dyn HashDB<Hasher, DBValue, Meta, Option<u32>> + 'b) {
		&mut *self
	}
}

impl<'a> HashDB<Hasher, DBValue, Meta, Option<u32>> for SimpleTrie<'a> {
	fn get(&self, key: &Hash, prefix: Prefix) -> Option<DBValue> {
		let key = sp_trie::prefixed_key::<Hasher>(key, prefix);
		if let Some(value) = self.overlay.get(&key) {
			return value.clone();
		}
		self.db.get(0, &key).expect("Database backend error")
	}

	fn get_with_meta(&self, key: &Hash, prefix: Prefix, global: Option<u32>) -> Option<(DBValue, Meta)> {
		let result = self.get(key, prefix);
		result.map(|value| <StateHasher as MetaHasher<Hasher, _>>::extract_value_owned(value, global))
	}

	fn contains(&self, hash: &Hash, prefix: Prefix) -> bool {
		self.get(hash, prefix).is_some()
	}

	fn insert_with_meta(&mut self, prefix: Prefix, value: &[u8], meta: Meta) -> Hash {
		let key = <StateHasher as MetaHasher<Hasher, DBValue>>::hash(value, &meta);
		let stored_value = <StateHasher as MetaHasher<Hasher, _>>::stored_value(value, meta);
		self.emplace(key, prefix, stored_value);
		key
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
