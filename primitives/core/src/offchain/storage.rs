// This file is part of Substrate.

// Copyright (C) 2019-2020 Parity Technologies (UK) Ltd.
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
use historied_db::{Latest, Management, ManagementRef};
use historied_db::historied::tree::Tree;
use historied_db::historied::{InMemoryValueRef, InMemoryValue};
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
	u32
>;

type InMemTreeBackend = historied_db::backend::in_memory::MemoryOnly<
	historied_db::historied::linear::Linear<Option<Vec<u8>>, u32, InMemLinearBackend>,
	u32,
>;

/// Historied value with multiple paralell branches.
pub type InMemHValue = Tree<u32, u32, Option<Vec<u8>>, InMemTreeBackend, InMemLinearBackend>;


/// In-memory storage for offchain workers.
/// With block chain data history.
#[derive(Debug, Clone, Default)]
pub struct BlockChainInMemOffchainStorage<Hash: Ord> {
	// Note that we could parameterized over historied management here.
	// Also could remove inner mutability if changing historied db simple db trait.
	historied_management: Arc<RwLock<TreeManagement<Hash, u32, u32, Option<Vec<u8>>, ()>>>,
	storage: Arc<RwLock<HashMap<Vec<u8>, InMemHValue>>>,
}

/// In-memory storage for offchain workers.
#[derive(Debug, Clone, Default)]
pub struct BlockChainInMemOffchainStorageAt {
	storage: Arc<RwLock<HashMap<Vec<u8>, InMemHValue>>>,
	at_read: ForkPlan<u32, u32>,
	at_write: Option<Latest<(u32, u32)>>,
}

/// In-memory storage for offchain workers,
/// and for new state (without concurrency handling).
#[derive(Debug, Clone, Default)]
pub struct BlockChainInMemOffchainStorageAtNew(BlockChainInMemOffchainStorageAt);

impl InMemOffchainStorage {
	/// Consume the offchain storage and iterate over all key value pairs.
	pub fn into_iter(self) -> impl Iterator<Item=(Vec<u8>,Vec<u8>)> {
		self.storage.into_iter()
	}

	/// Iterate over all key value pairs by reference.
	pub fn iter<'a>(&'a self) -> impl Iterator<Item=(&'a Vec<u8>,&'a Vec<u8>)> {
		self.storage.iter()
	}

	/// Remove a key and its associated value from the offchain database.
	pub fn remove(&mut self, prefix: &[u8], key: &[u8]) {
		let key: Vec<u8> = prefix.iter().chain(key).cloned().collect();
		let _ = self.storage.remove(&key);
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
	type OffchainStorageNew = BlockChainInMemOffchainStorageAtNew;

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

	fn at_new(&self, id: Self::BlockId) -> Option<Self::OffchainStorageNew> {
		self.at(id).map(|at| BlockChainInMemOffchainStorageAtNew(at))
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

impl OffchainStorage for BlockChainInMemOffchainStorageAtNew {
	fn set(&mut self, prefix: &[u8], key: &[u8], value: &[u8]) {
		let test: Option<fn(Option<&[u8]>) -> bool> = None;
		self.0.modify(
			prefix,
			key,
			test,
			Some(value),
			true,
		);
	}

	fn remove(&mut self, prefix: &[u8], key: &[u8]) {
		let test: Option<fn(Option<&[u8]>) -> bool> = None;
		self.0.modify(
			prefix,
			key,
			test,
			None,
			true,
		);
	}

	fn get(&self, prefix: &[u8], key: &[u8]) -> Option<Vec<u8>> {
		self.0.get(prefix, key)
	}

	fn compare_and_set(
		&mut self,
		prefix: &[u8],
		item_key: &[u8],
		old_value: Option<&[u8]>,
		new_value: &[u8],
	) -> bool {
		let test = |v: Option<&[u8]>| old_value == v;
		self.0.modify(
			prefix,
			item_key,
			Some(test),
			Some(new_value),
			true,
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
			at_write_inner = Latest::unchecked_latest(self.at_read.latest_index());
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
			use historied_db::historied::Value;
			let is_insert = new_value.is_some();
			let new_value = new_value.map(|v| v.to_vec());
			if let Some(histo) = histo {
				if is_new {
					let _update_result = histo.set_mut(new_value, at_write);
				} else {
					use historied_db::historied::ConditionalValueMut;
					use historied_db::historied::StateIndex;
					let _update_result = histo.set_if_possible_no_overwrite(
						new_value,
						at_write.index_ref(),
					).expect("Concurrency failure for sequential write of offchain storage");
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

/// Change to be applied to the offchain worker db in regards to a key.
#[derive(Debug,Clone,Hash,Eq,PartialEq)]
pub enum OffchainOverlayedChange {
	/// Remove the data associated with the key
	Remove,
	/// Remove the data associated with the key, with
	/// local blockchain storage.
	RemoveLocal,
	/// Overwrite the value of an associated key
	SetValue(Vec<u8>),
	/// Overwrite the value of an associated key, with local
	/// blockchain storage.
	SetLocalValue(Vec<u8>),
}

/// In-memory storage for offchain workers recoding changes for the actual offchain storage implementation.
#[derive(Debug, Clone)]
pub enum OffchainOverlayedChanges {
	/// Writing overlay changes to the offchain worker database is disabled by configuration.
	Disabled,
	/// Overlay changes can be recorded using the inner collection of this variant,
	/// where the identifier is the tuple of `(prefix, key)`.
	Enabled(HashMap<(Vec<u8>, Vec<u8>), OffchainOverlayedChange>),
}

impl Default for OffchainOverlayedChanges {
	fn default() -> Self {
		Self::Disabled
	}
}

impl OffchainOverlayedChanges {
	/// Create the disabled variant.
	pub fn disabled() -> Self {
		Self::Disabled
	}

	/// Create the enabled variant.
	pub fn enabled() -> Self {
		Self::Enabled(HashMap::new())
	}

	/// Consume the offchain storage and iterate over all key value pairs.
	pub fn into_iter(self) -> OffchainOverlayedChangesIntoIter {
		OffchainOverlayedChangesIntoIter::new(self)
	}

	/// Iterate over all key value pairs by reference.
	pub fn iter<'a>(&'a self) -> OffchainOverlayedChangesIter {
		OffchainOverlayedChangesIter::new(&self)
	}

	/// Drain all elements of changeset.
	pub fn drain<'a, 'd>(&'a mut self) -> OffchainOverlayedChangesDrain<'d> where 'a: 'd {
		OffchainOverlayedChangesDrain::new(self)
	}

	/// Remove a key and its associated value from the offchain database.
	pub fn remove(&mut self, prefix: &[u8], key: &[u8], is_local: bool) {
		if let Self::Enabled(ref mut storage) = self {
			let _ = if is_local {
				storage.insert((prefix.to_vec(), key.to_vec()), OffchainOverlayedChange::RemoveLocal)
			} else {
				storage.insert((prefix.to_vec(), key.to_vec()), OffchainOverlayedChange::Remove)
			};
		}
	}

	/// Set the value associated with a key under a prefix to the value provided.
	pub fn set(&mut self, prefix: &[u8], key: &[u8], value: &[u8], is_local: bool) {
		if let Self::Enabled(ref mut storage) = self {
			let _ = if is_local {
				storage.insert((prefix.to_vec(), key.to_vec()), OffchainOverlayedChange::SetLocalValue(value.to_vec()))
			} else {
				storage.insert((prefix.to_vec(), key.to_vec()), OffchainOverlayedChange::SetValue(value.to_vec()))
			};
		}
	}

	/// Obtain a associated value to the given key in storage with prefix.
	pub fn get(&self, prefix: &[u8], key: &[u8]) -> Option<OffchainOverlayedChange> {
		if let Self::Enabled(ref storage) = self {
			let key = (prefix.to_vec(), key.to_vec());
			storage.get(&key).cloned()
		} else {
			None
		}
	}
}

use std::collections::hash_map;

/// Iterate by reference over the prepared offchain worker storage changes.
pub struct OffchainOverlayedChangesIter<'i> {
	inner: Option<hash_map::Iter<'i, (Vec<u8>, Vec<u8>), OffchainOverlayedChange>>,
}

impl<'i> Iterator for OffchainOverlayedChangesIter<'i> {
	type Item = (&'i (Vec<u8>, Vec<u8>), &'i OffchainOverlayedChange);
	fn next(&mut self) -> Option<Self::Item> {
		if let Some(ref mut iter) = self.inner {
			iter.next()
		} else {
			None
		}
	}
}

impl<'i> OffchainOverlayedChangesIter<'i> {
	/// Create a new iterator based on a refernce to the parent container.
	pub fn new(container: &'i OffchainOverlayedChanges) -> Self {
		match container {
			OffchainOverlayedChanges::Enabled(inner) => Self {
				inner: Some(inner.iter())
			},
			OffchainOverlayedChanges::Disabled => Self { inner: None, },
		}
	}
}


/// Iterate by value over the prepared offchain worker storage changes.
pub struct OffchainOverlayedChangesIntoIter {
	inner: Option<hash_map::IntoIter<(Vec<u8>,Vec<u8>),OffchainOverlayedChange>>,
}

impl Iterator for OffchainOverlayedChangesIntoIter {
	type Item = ((Vec<u8>, Vec<u8>), OffchainOverlayedChange);
	fn next(&mut self) -> Option<Self::Item> {
		if let Some(ref mut iter) = self.inner {
			iter.next()
		} else {
			None
		}
	}
}

impl OffchainOverlayedChangesIntoIter {
	/// Create a new iterator by consuming the collection.
	pub fn new(container: OffchainOverlayedChanges) -> Self {
		match container {
			OffchainOverlayedChanges::Enabled(inner) => Self {
				inner: Some(inner.into_iter())
			},
			OffchainOverlayedChanges::Disabled => Self { inner: None, },
		}
	}
}

/// Iterate over all items while draining them from the collection.
pub struct OffchainOverlayedChangesDrain<'d> {
	inner: Option<hash_map::Drain<'d, (Vec<u8>, Vec<u8>), OffchainOverlayedChange>>,
}

impl<'d> Iterator for OffchainOverlayedChangesDrain<'d> {
	type Item = ((Vec<u8>, Vec<u8>), OffchainOverlayedChange);
	fn next(&mut self) -> Option<Self::Item> {
		if let Some(ref mut iter) = self.inner {
			iter.next()
		} else {
			None
		}
	}
}

impl<'d> OffchainOverlayedChangesDrain<'d> {
	/// Create a new iterator by taking a mut reference to the collection,
	/// for the lifetime of the created drain iterator.
	pub fn new(container: &'d mut OffchainOverlayedChanges) -> Self {
		match container {
			OffchainOverlayedChanges::Enabled(ref mut inner) => Self {
				inner: Some(inner.drain())
			},
			OffchainOverlayedChanges::Disabled => Self { inner: None, },
		}
	}
}


#[cfg(test)]
mod test {
	use super::*;
	use super::super::STORAGE_PREFIX;

	#[test]
	fn test_drain() {
		let mut ooc = OffchainOverlayedChanges::enabled();
		ooc.set(STORAGE_PREFIX,b"kkk", b"vvv", false);
		let drained = ooc.drain().count();
		assert_eq!(drained, 1);
		let leftover = ooc.iter().count();
		assert_eq!(leftover, 0);

		ooc.set(STORAGE_PREFIX, b"a", b"v", false);
		ooc.set(STORAGE_PREFIX, b"b", b"v", false);
		ooc.set(STORAGE_PREFIX, b"c", b"v", false);
		ooc.set(STORAGE_PREFIX, b"d", b"v", false);
		ooc.set(STORAGE_PREFIX, b"e", b"v", false);
		assert_eq!(ooc.iter().count(), 5);
	}

	#[test]
	fn test_accumulated_set_remove_set() {
		let mut ooc = OffchainOverlayedChanges::enabled();
		ooc.set(STORAGE_PREFIX, b"ppp", b"qqq", false);
		ooc.remove(STORAGE_PREFIX, b"ppp", false);
		// keys are equiv, so it will overwrite the value and the overlay will contain
		// one item
		assert_eq!(ooc.iter().count(), 1);

		ooc.set(STORAGE_PREFIX, b"ppp", b"rrr", false);
		let mut iter = ooc.into_iter();
		assert_eq!(
			iter.next(),
			Some(
				((STORAGE_PREFIX.to_vec(), b"ppp".to_vec()),
				OffchainOverlayedChange::SetValue(b"rrr".to_vec()))
			)
		);
		assert_eq!(iter.next(), None);
	}
}
