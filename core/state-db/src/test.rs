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

use std::collections::{HashMap, BTreeMap};
use primitives::H256;
use crate::{
	DBValue, ChangeSet, KvChangeSet, KvKey, MetaDb, NodeDb, KvDb,
	CommitSet, CommitSetCanonical,
};
use historied_data::tree::Serialized;
use historied_data::PruneResult;
use historied_data::linear::DefaultVersion;

type Ser<'a> = Serialized<'a, DefaultVersion>;

#[derive(Default, Debug, Clone, PartialEq, Eq)]
pub struct TestDb {
	pub data: HashMap<H256, DBValue>,
	pub meta: HashMap<Vec<u8>, DBValue>,
	pub kv: HashMap<KvKey, DBValue>,
	// Heuristic : increase on commit_canonical.
	pub kv_last_block: u64,
}

impl MetaDb for TestDb {
	type Error = ();

	fn get_meta(&self, key: &[u8]) -> Result<Option<DBValue>, ()> {
		Ok(self.meta.get(key).cloned())
	}
}

impl KvDb<u64> for TestDb {
	type Error = ();

	fn get_kv(&self, key: &[u8], state: &u64) -> Result<Option<DBValue>, ()> {
		Ok(self.kv.get(key)
			.map(|s| Ser::from_slice(s.as_slice()))
			.and_then(|s| s.get(*state)
				.unwrap_or(None) // flatten
				.map(Into::into)
		))
	}

	fn get_kv_pairs(&self, state: &u64) -> Vec<(KvKey, DBValue)> {
		self.kv.iter().filter_map(|(a, s)| (
			Ser::from_slice(s.as_slice())
				.get(*state)
				.unwrap_or(None) // flatten
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
		for (k, o) in commit.kv.iter() {
			let encoded = self.kv.entry(k.clone())
				.or_insert_with(|| Ser::default().into_vec());
			let mut ser = Ser::from_mut(&mut (*encoded));
			ser.push(self.kv_last_block, o.as_ref().map(|v| v.as_slice()));
		}
		self.meta.extend(commit.meta.inserted.iter().cloned());
		for k in commit.meta.deleted.iter() {
			self.meta.remove(k);
		}
	}

	pub fn commit_canonical(&mut self, commit: &CommitSetCanonical<H256>) {

		self.kv_last_block += 1;
		self.commit(&commit.0);

		if let Some((block_prune, kv_prune_key)) = commit.1.as_ref() {
			for k in kv_prune_key.iter() {
				match self.kv.get_mut(k).map(|v| {
					let mut ser = Ser::from_mut(v);
					ser.prune(*block_prune)
				}) {
					Some(PruneResult::Cleared) => { let _ = self.kv.remove(k); },
					Some(PruneResult::Changed) // changed applyied on mutable buffer without copy.
					| Some(PruneResult::Unchanged)
					| None => (),
				}
			}
		}
	}

	pub fn data_eq(&self, other: &TestDb) -> bool {
		self.data == other.data
	}

	pub fn kv_eq_at(&self, values: &[u64], block: Option<u64>) -> bool {
		let block = block.unwrap_or(self.kv_last_block);
		let data = make_kv_changeset(values, &[]);
		let self_kv: BTreeMap<_, _> = self.get_kv_pairs(&block).into_iter().collect();
		self_kv == data.into_iter().filter_map(|(k, v)| v.map(|v| (k,v))).collect()
	}

	pub fn kv_eq(&self, values: &[u64]) -> bool {
		self.kv_eq_at(values, None)
	}

	pub fn initialize_kv(&mut self, inserted: &[u64]) {
		let data = make_kv_changeset(inserted, &[]);
		self.kv = data.into_iter()
			.filter_map(|(k, v)| v.map(|v| (k,v)))
			.map(|(k, v)| {
				let mut ser = Ser::default();
				ser.push(self.kv_last_block, Some(v.as_slice()));
				(k, ser.into_vec())
			})
			.collect();
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

pub fn make_kv_changeset(
	inserted: &[u64],
	deleted: &[u64],
) -> KvChangeSet<KvKey> {
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
		kv: KvChangeSet::default(),
	}
}

pub fn make_commit_both(inserted: &[u64], deleted: &[u64]) -> CommitSetCanonical<H256> {
	(CommitSet {
		data: make_changeset(inserted, deleted),
		meta: ChangeSet::default(),
		kv: make_kv_changeset(inserted, deleted),
	}, None)
}

impl CommitSet<H256> {
	pub fn initialize_kv(&mut self, inserted: &[u64], deleted: &[u64]) {
		let data = make_kv_changeset(inserted, deleted);
		self.kv = data;
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
		kv: Default::default(),
		kv_last_block: Default::default(),
	}
}
