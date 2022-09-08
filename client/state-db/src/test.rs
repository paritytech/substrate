// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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

//! Test utils

use crate::{ChangeSet, CommitSet, DBValue, MetaDb, NodeDb};
use sp_core::H256;
use std::{
	collections::HashMap,
	sync::{Arc, RwLock},
};

#[derive(Default, Debug, Clone)]
pub struct TestDb(Arc<RwLock<TestDbInner>>);

#[derive(Default, Debug, Clone, PartialEq, Eq)]
struct TestDbInner {
	pub data: HashMap<H256, DBValue>,
	pub meta: HashMap<Vec<u8>, DBValue>,
}

impl MetaDb for TestDb {
	type Error = ();

	fn get_meta(&self, key: &[u8]) -> Result<Option<DBValue>, ()> {
		Ok(self.0.read().unwrap().meta.get(key).cloned())
	}
}

impl NodeDb for TestDb {
	type Error = ();
	type Key = H256;

	fn get(&self, key: &H256) -> Result<Option<DBValue>, ()> {
		Ok(self.0.read().unwrap().data.get(key).cloned())
	}
}

impl TestDb {
	pub fn commit(&mut self, commit: &CommitSet<H256>) {
		self.0.write().unwrap().data.extend(commit.data.inserted.iter().cloned());
		self.0.write().unwrap().meta.extend(commit.meta.inserted.iter().cloned());
		for k in commit.data.deleted.iter() {
			self.0.write().unwrap().data.remove(k);
		}
		self.0.write().unwrap().meta.extend(commit.meta.inserted.iter().cloned());
		for k in commit.meta.deleted.iter() {
			self.0.write().unwrap().meta.remove(k);
		}
	}

	pub fn data_eq(&self, other: &TestDb) -> bool {
		self.0.read().unwrap().data == other.0.read().unwrap().data
	}

	pub fn meta_len(&self) -> usize {
		self.0.read().unwrap().meta.len()
	}
}

pub fn make_changeset(inserted: &[u64], deleted: &[u64]) -> ChangeSet<H256> {
	ChangeSet {
		inserted: inserted
			.iter()
			.map(|v| (H256::from_low_u64_be(*v), H256::from_low_u64_be(*v).as_bytes().to_vec()))
			.collect(),
		deleted: deleted.iter().map(|v| H256::from_low_u64_be(*v)).collect(),
	}
}

pub fn make_commit(inserted: &[u64], deleted: &[u64]) -> CommitSet<H256> {
	CommitSet { data: make_changeset(inserted, deleted), meta: ChangeSet::default() }
}

pub fn make_db(inserted: &[u64]) -> TestDb {
	TestDb(Arc::new(RwLock::new(TestDbInner {
		data: inserted
			.iter()
			.map(|v| (H256::from_low_u64_be(*v), H256::from_low_u64_be(*v).as_bytes().to_vec()))
			.collect(),
		meta: Default::default(),
	})))
}
