// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

/// Test utils

use std::collections::HashMap;
use primitives::H256;
use {DBValue, ChangeSet, CommitSet, to_key, KeyValueDb};

#[derive(Default, Debug, Clone, PartialEq, Eq)]
pub struct TestDb {
	pub data: HashMap<H256, DBValue>,
	pub meta: HashMap<H256, DBValue>,
}

impl KeyValueDb for TestDb {
	type Error = ();
	fn get(&self, key: &H256) -> Result<Option<DBValue>, ()> {
		Ok(self.data.get(key).cloned())
	}

	fn get_meta(&self, key: &H256) -> Result<Option<DBValue>, ()> {
		Ok(self.meta.get(key).cloned())
	}
}

impl TestDb {
	pub fn commit(&mut self, commit: &CommitSet) {
		self.data.extend(commit.data.inserted.iter().cloned());
		for k in commit.data.deleted.iter() {
			self.data.remove(k);
		}
		self.meta.extend(commit.meta.inserted.iter().cloned());
		for k in commit.meta.deleted.iter() {
			self.meta.remove(k);
		}
	}

	pub fn data_eq(&self, other: &TestDb) -> bool {
		self.data == other.data
	}
}

pub fn make_changeset(inserted: &[u64], deleted: &[u64]) -> ChangeSet {
	ChangeSet {
		inserted: inserted.iter().map(|v| (to_key(b"test", v), to_key(b"value", v).to_vec())).collect(),
		deleted: deleted.iter().map(|v| to_key(b"test", v)).collect(),
	}
}

pub fn make_commit(inserted: &[u64], deleted: &[u64]) -> CommitSet {
	CommitSet {
		data: make_changeset(inserted, deleted),
		meta: ChangeSet::default(),
	}
}

pub fn make_db(inserted: &[u64]) -> TestDb {
	TestDb {
		data: inserted.iter().map(|v| (to_key(b"test", v), to_key(b"value", v).to_vec())).collect(),
		meta: Default::default(),
	}
}

