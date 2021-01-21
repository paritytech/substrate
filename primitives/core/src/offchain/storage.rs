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

/// In-memory storage for offchain workers.
#[derive(Debug, Clone, Default)]
pub struct InMemOffchainStorage {
	storage: HashMap<Vec<u8>, Vec<u8>>,
}

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

/// Change to be applied to the offchain worker db in regards to a key.
#[derive(Debug,Clone,Hash,Eq,PartialEq)]
pub enum OffchainOverlayedChange {
	/// Remove the data associated with the key
	Remove,
	/// Overwrite the value of an associated key
	SetValue(Vec<u8>),
}

/// In-memory storage for offchain workers recoding changes for the actual offchain storage implementation.
#[derive(Debug, Clone, Default)]
pub struct OffchainOverlayedChanges {
	changes: HashMap<(Vec<u8>, Vec<u8>), OffchainOverlayedChange>,
}

impl OffchainOverlayedChanges {
	/// Consume the offchain storage and iterate over all key value pairs.
	pub fn into_iter(self) -> impl Iterator<Item = ((Vec<u8>, Vec<u8>), OffchainOverlayedChange)> {
		self.changes.into_iter()
	}

	/// Iterate over all key value pairs by reference.
	pub fn iter(&self) -> impl Iterator<Item = (&(Vec<u8>, Vec<u8>), &OffchainOverlayedChange)> {
		self.changes.iter()
	}

	/// Drain all elements of changeset.
	pub fn drain(&mut self) -> impl Iterator<Item = ((Vec<u8>, Vec<u8>), OffchainOverlayedChange)> + '_ {
		self.changes.drain()
	}

	/// Remove a key and its associated value from the offchain database.
	pub fn remove(&mut self, prefix: &[u8], key: &[u8]) {
		self.changes.insert((prefix.to_vec(), key.to_vec()), OffchainOverlayedChange::Remove);
	}

	/// Set the value associated with a key under a prefix to the value provided.
	pub fn set(&mut self, prefix: &[u8], key: &[u8], value: &[u8]) {
		self.changes.insert(
			(prefix.to_vec(), key.to_vec()),
			OffchainOverlayedChange::SetValue(value.to_vec()),
		);
	}

	/// Obtain a associated value to the given key in storage with prefix.
	pub fn get(&self, prefix: &[u8], key: &[u8]) -> Option<OffchainOverlayedChange> {
		let key = (prefix.to_vec(), key.to_vec());
		self.changes.get(&key).cloned()
	}
}

#[cfg(test)]
mod test {
	use super::*;
	use super::super::STORAGE_PREFIX;

	#[test]
	fn test_drain() {
		let mut ooc = OffchainOverlayedChanges::default();
		ooc.set(STORAGE_PREFIX,b"kkk", b"vvv");
		let drained = ooc.drain().count();
		assert_eq!(drained, 1);
		let leftover = ooc.iter().count();
		assert_eq!(leftover, 0);

		ooc.set(STORAGE_PREFIX, b"a", b"v");
		ooc.set(STORAGE_PREFIX, b"b", b"v");
		ooc.set(STORAGE_PREFIX, b"c", b"v");
		ooc.set(STORAGE_PREFIX, b"d", b"v");
		ooc.set(STORAGE_PREFIX, b"e", b"v");
		assert_eq!(ooc.iter().count(), 5);
	}

	#[test]
	fn test_accumulated_set_remove_set() {
		let mut ooc = OffchainOverlayedChanges::default();
		ooc.set(STORAGE_PREFIX, b"ppp", b"qqq");
		ooc.remove(STORAGE_PREFIX, b"ppp");
		// keys are equiv, so it will overwrite the value and the overlay will contain
		// one item
		assert_eq!(ooc.iter().count(), 1);

		ooc.set(STORAGE_PREFIX, b"ppp", b"rrr");
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
