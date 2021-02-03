// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

//! In-memory implementation of offchain workers database.

use std::collections::hash_map::{HashMap, Entry};
use crate::offchain::OffchainStorage;
use std::iter::Iterator;
use historied_db::management::tree::{TreeManagement, ForkPlan};
use historied_db::{Latest, management::{Management, ManagementMut}};
use historied_db::historied::tree::Tree;
use historied_db::historied::{DataRef, DataRefMut};
use parking_lot::RwLock;
use std::sync::Arc;
use codec::Codec;

/// In-memory storage for offchain workers.
#[derive(Debug, Clone, Default)]
pub struct InMemOffchainStorage {
	storage: HashMap<Vec<u8>, Vec<u8>>,
}

type InMemLinearBackend = historied_db::backend::in_memory::MemoryOnly<
	Option<Vec<u8>>,
	u64,
>;

type InMemTreeBackend = historied_db::backend::in_memory::MemoryOnly<
	historied_db::historied::linear::Linear<Option<Vec<u8>>, u64, InMemLinearBackend>,
	u32,
>;

/// Historied value with multiple paralell branches.
pub type InMemHValue = Tree<u32, u64, Option<Vec<u8>>, InMemTreeBackend, InMemLinearBackend>;


/// In-memory storage for offchain workers.
/// With block chain data history.
#[derive(Debug, Clone, Default)]
pub struct BlockChainInMemOffchainStorage<Hash: Ord> {
	// Note that we could parameterized over historied management here.
	// Also could remove inner mutability if changing historied db simple db trait.
	historied_management: Arc<RwLock<TreeManagement<Hash, u32, u64, ()>>>,
	storage: Arc<RwLock<HashMap<Vec<u8>, InMemHValue>>>,
}

/// In-memory storage for offchain workers.
#[derive(Debug, Clone, Default)]
pub struct BlockChainInMemOffchainStorageAt {
	storage: Arc<RwLock<HashMap<Vec<u8>, InMemHValue>>>,
	at_read: ForkPlan<u32, u64>,
	at_write: Option<Latest<(u32, u64)>>,
}

impl InMemOffchainStorage {
	/// Consume the offchain storage and iterate over all key value pairs.
	pub fn into_iter(self) -> impl Iterator<Item = (Vec<u8>, Vec<u8>)> {
		self.storage.into_iter()
	}

	/// Iterate over all key value pairs by reference.
	pub fn iter<'a>(&'a self) -> impl Iterator<Item = (&'a Vec<u8>, &'a Vec<u8>)> {
		self.storage.iter()
	}

	/// Remove a key and its associated value from the offchain database.
	pub fn remove(&mut self, prefix: &[u8], key: &[u8]) {
		let key: Vec<u8> = prefix.iter().chain(key).cloned().collect();
		self.storage.remove(&key);
	}
}

impl OffchainStorage for InMemOffchainStorage {
	fn set(&mut self, prefix: &[u8], key: &[u8], value: &[u8]) {
		let key = prefix.iter().chain(key).cloned().collect();
		self.storage.insert(key, value.to_vec());
	}

	fn remove(&mut self, prefix: &[u8], key: &[u8]) {
		let key: Vec<u8> = prefix.iter().chain(key).cloned().collect();
		self.storage.remove(&key);
	}

	fn get(&self, prefix: &[u8], key: &[u8]) -> Option<Vec<u8>> {
		let key: Vec<u8> = prefix.iter().chain(key).cloned().collect();
		self.storage.get(&key).cloned()
	}

	fn compare_and_set(
		&mut self,
		prefix: &[u8],
		key: &[u8],
		old_value: Option<&[u8]>,
		new_value: &[u8],
	) -> bool {
		let key = prefix.iter().chain(key).cloned().collect();

		match self.storage.entry(key) {
			Entry::Vacant(entry) => if old_value.is_none() {
				entry.insert(new_value.to_vec());
				true
			} else { false },
			Entry::Occupied(ref mut entry) if Some(entry.get().as_slice()) == old_value => {
				entry.insert(new_value.to_vec());
				true
			},
			_ => false,
		}
	}
}

impl<H> crate::offchain::BlockChainOffchainStorage for BlockChainInMemOffchainStorage<H>
	where
		H: Ord + Clone + Send + Sync + Codec,
{
	type BlockId = H;
	type OffchainStorage = BlockChainInMemOffchainStorageAt;

	fn at(&self, id: Self::BlockId) -> Option<Self::OffchainStorage> {
		if let Some(at_read) = self.historied_management.write().get_db_state(&id) {
			let at_write = self.historied_management.write().get_db_state_mut(&id);
			Some(BlockChainInMemOffchainStorageAt {
				storage: self.storage.clone(),
				at_read,
				at_write,
			})
		} else {
			None
		}
	}

	fn latest(&self) -> Option<Self::BlockId> {
		self.historied_management.write().latest_external_state()
	}
}

impl OffchainStorage for BlockChainInMemOffchainStorageAt {
	fn set(&mut self, prefix: &[u8], key: &[u8], value: &[u8]) {
		let test: Option<fn(Option<&[u8]>) -> bool> = None;
		self.modify(
			prefix,
			key,
			test,
			Some(value),
			false,
		);
	}

	fn remove(&mut self, prefix: &[u8], key: &[u8]) {
		let test: Option<fn(Option<&[u8]>) -> bool> = None;
		self.modify(
			prefix,
			key,
			test,
			None,
			false,
		);
	}

	fn get(&self, prefix: &[u8], key: &[u8]) -> Option<Vec<u8>> {
		let key: Vec<u8> = prefix.iter().chain(key).cloned().collect();
		self.storage.read().get(&key)
			.and_then(|h| {
				h.get_ref(&self.at_read).cloned().flatten()
			})
	}

	fn compare_and_set(
		&mut self,
		prefix: &[u8],
		item_key: &[u8],
		old_value: Option<&[u8]>,
		new_value: &[u8],
	) -> bool {
		let test = |v: Option<&[u8]>| old_value == v;
		self.modify(
			prefix,
			item_key,
			Some(test),
			Some(new_value),
			false,
		)
	}
}

impl BlockChainInMemOffchainStorageAt {
	fn modify(
		&mut self,
		prefix: &[u8],
		item_key: &[u8],
		condition: Option<impl Fn(Option<&[u8]>) -> bool>,
		new_value: Option<&[u8]>,
		is_new: bool,
	) -> bool {
		if self.at_write.is_none() && is_new {
			panic!("Incoherent state for offchain writing");
		}
		let at_write_inner;
		let at_write = if is_new {
			self.at_write.as_ref().expect("checked above")
		} else {
			// Here we should not use at_write because at write do resolve
			// a tree leaf (so is_new true).
			use historied_db::StateIndex;
			at_write_inner = Latest::unchecked_latest(self.at_read.index());
			&at_write_inner
		};
		let key: Vec<u8> = prefix.iter().chain(item_key).cloned().collect();
		let is_set;
		let mut storage_write = self.storage.write();
		let histo = storage_write.get_mut(&key);
		let val = histo.as_ref().and_then(|h| {
			h.get_ref(&self.at_read).cloned().flatten()
		});

		is_set = condition.map(|c| c(val.as_ref().map(|v| v.as_slice()))).unwrap_or(true);

		if is_set {
			use historied_db::historied::DataMut;
			let is_insert = new_value.is_some();
			let new_value = new_value.map(|v| v.to_vec());
			if let Some(histo) = histo {
				if is_new {
					let _update_result = histo.set_mut(new_value, at_write);
				} else {
					use historied_db::historied::force::ForceDataMut;
					use historied_db::StateIndex;
					let mut index = Default::default();
					let _update_result = histo.force_set(
						new_value,
						at_write.index_ref().unwrap_or_else(|| {
							index = at_write.index();
							&index
						}),
					);
				}
			} else {
				if is_insert {
					let new_histo = InMemHValue::new(new_value, at_write, ((), ()));
					storage_write.insert(key, new_histo);
				} else {
					return is_set;
				}
			};
		}

		is_set
	}
}
