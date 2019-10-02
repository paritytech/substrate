// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

//! Test utils

use std::collections::HashMap;
use primitives::H256;
use crate::{
	DBValue, ChangeSet, OffstateChangeSet, CommitSet, MetaDb, NodeDb, OffstateDb,
	OffstateKey,
};
use historied_data::tree::Serialized;
use historied_data::linear::DefaultVersion;

type Ser<'a> = Serialized<'a, DefaultVersion>;

#[derive(Default, Debug, Clone, PartialEq, Eq)]
pub struct TestDb {
	pub data: HashMap<H256, DBValue>,
	pub meta: HashMap<Vec<u8>, DBValue>,
	pub offstate: HashMap<OffstateKey, DBValue>,
	pub last_block: u64,
}

impl MetaDb for TestDb {
	type Error = ();

	fn get_meta(&self, key: &[u8]) -> Result<Option<DBValue>, ()> {
		Ok(self.meta.get(key).cloned())
	}
}

impl OffstateDb<Option<u64>> for TestDb {
	type Error = ();

	fn get_offstate(&self, key: &[u8], state: &Option<u64>) -> Result<Option<DBValue>, ()> {
		let state = state.unwrap_or(self.last_block);
		Ok(self.offstate.get(key)
			.map(|s| Ser::from(s.as_slice().into()))
			.and_then(|s| s.get(state)
				.map(Into::into)
		))
		
	}

	fn get_offstate_pairs(&self, state: &Option<u64>) -> Vec<(OffstateKey, DBValue)> {
		let state = state.unwrap_or(self.last_block);
		self.offstate.iter().filter_map(|(a, s)| (
			Ser::from(s.as_slice().into())
				.get(state)
				.map(|v| (a.clone(), v.to_vec()))
		)).collect()
	}
}

impl NodeDb for TestDb {
	type Error = ();
	type Key = H256;

	fn get(&self, key: &H256) -> Result<Option<DBValue>, ()> {
		Ok(self.data.get(key).cloned())
	}
}

impl TestDb {
	pub fn commit(&mut self, commit: &CommitSet<H256>) {
		self.data.extend(commit.data.inserted.iter().cloned());
		for k in commit.data.deleted.iter() {
			self.data.remove(k);
		}
		for (k, o) in commit.offstate.iter() {
			if let Some(v) = o {
				self.offstate.insert(k.to_vec(), v.to_vec());
			} else {
				self.offstate.remove(k);
			}
		}
		self.meta.extend(commit.meta.inserted.iter().cloned());
		for k in commit.meta.deleted.iter() {
			self.meta.remove(k);
		}
	}

	pub fn data_eq(&self, other: &TestDb) -> bool {
		self.data == other.data
	}

	pub fn offstate_eq(&self, values: &[u64]) -> bool {
		let data = make_offstate_changeset(values, &[]);
		self.offstate == data.into_iter().filter_map(|(k, v)| v.map(|v| (k,v))).collect()
	}

	pub fn initialize_offstate(&mut self, inserted: &[u64]) {
		let data = make_offstate_changeset(inserted, &[]);
		self.offstate = data.into_iter().filter_map(|(k, v)| v.map(|v| (k,v))).collect();
	}
}

pub fn make_changeset(inserted: &[u64], deleted: &[u64]) -> ChangeSet<H256> {
	ChangeSet {
		inserted: inserted
			.iter()
			.map(|v| {
				(H256::from_low_u64_be(*v), H256::from_low_u64_be(*v).as_bytes().to_vec())
			})
			.collect(),
		deleted: deleted.iter().map(|v| H256::from_low_u64_be(*v)).collect(),
	}
}

pub fn make_offstate_changeset(inserted: &[u64], deleted: &[u64]) -> OffstateChangeSet<OffstateKey> {
	inserted.iter()
		.map(|v| (
			H256::from_low_u64_be(*v).as_bytes().to_vec(),
			Some(H256::from_low_u64_be(*v).as_bytes().to_vec()),
		))
		.chain(
			deleted
				.iter()
				.map(|v| (H256::from_low_u64_be(*v).as_bytes().to_vec(), None))
		)
		.collect()
}

pub fn make_commit(inserted: &[u64], deleted: &[u64]) -> CommitSet<H256> {
	CommitSet {
		data: make_changeset(inserted, deleted),
		meta: ChangeSet::default(),
		offstate: OffstateChangeSet::default(),
	}
}

pub fn make_commit_both(inserted: &[u64], deleted: &[u64]) -> CommitSet<H256> {
	CommitSet {
		data: make_changeset(inserted, deleted),
		meta: ChangeSet::default(),
		offstate: make_offstate_changeset(inserted, deleted),
	}
}

impl CommitSet<H256> {
	pub fn initialize_offstate(&mut self, inserted: &[u64], deleted: &[u64]) {
		let data = make_offstate_changeset(inserted, deleted);
		self.offstate = data;
	}
}

pub fn make_db(inserted: &[u64]) -> TestDb {
	TestDb {
		data: inserted
			.iter()
			.map(|v| {
				(H256::from_low_u64_be(*v), H256::from_low_u64_be(*v).as_bytes().to_vec())
			})
			.collect(),
		meta: Default::default(),
		offstate: Default::default(),
		last_block: Default::default(),
	}
}

