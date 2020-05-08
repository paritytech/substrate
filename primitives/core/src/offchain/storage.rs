// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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
		let _ = self.storage.remove(&key);
	}
}

impl OffchainStorage for InMemOffchainStorage {
	fn set(&mut self, prefix: &[u8], key: &[u8], value: &[u8]) {
		let key = prefix.iter().chain(key).cloned().collect();
		self.storage.insert(key, value.to_vec());
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
#[derive(Debug, Clone)]
pub enum OffchainOverlayedChanges {
	/// Writing overlay changes to the offchain worker database is disabled by configuration.
	Disabled,
	/// Overlay changes can be recorded using the inner collection of this variant.
	Enabled(HashMap<Vec<u8>, OffchainOverlayedChange>),
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
	pub fn remove(&mut self, prefix: &[u8], key: &[u8]) {
		if let Self::Enabled(ref mut storage) = self {
			let key: Vec<u8> = prefix.iter().chain(key).cloned().collect();
			let _ = storage.insert(key, OffchainOverlayedChange::Remove);
		}
	}

	/// Set the value associated with a key under a prefix to the value provided.
	pub fn set(&mut self, prefix: &[u8], key: &[u8], value: &[u8]) {
		if let Self::Enabled(ref mut storage) = self {
			let key = prefix.iter().chain(key).cloned().collect();
			let _ = storage.insert(key, OffchainOverlayedChange::SetValue(value.to_vec()));
		}
	}

	/// Obtain a associated value to the given key in storage with prefix.
	pub fn get(&self, prefix: &[u8], key: &[u8]) -> Option<OffchainOverlayedChange> {
		if let Self::Enabled(ref storage) = self {
			let key: Vec<u8> = prefix.iter().chain(key).cloned().collect();
			storage.get(&key).cloned()
		} else {
			None
		}
	}
}

use std::collections::hash_map;

/// Iterate by reference over the prepared offchain worker storage changes.
pub struct OffchainOverlayedChangesIter<'i> {
	inner: Option<hash_map::Iter<'i, Vec<u8>, OffchainOverlayedChange>>,
}

impl<'i> Iterator for OffchainOverlayedChangesIter<'i> {
	type Item = (&'i Vec<u8>, &'i OffchainOverlayedChange);
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
	inner: Option<hash_map::IntoIter<Vec<u8>,OffchainOverlayedChange>>,
}

impl Iterator for OffchainOverlayedChangesIntoIter {
	type Item = (Vec<u8>, OffchainOverlayedChange);
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
	inner: Option<hash_map::Drain<'d, Vec<u8>,OffchainOverlayedChange>>,
}

impl<'d> Iterator for OffchainOverlayedChangesDrain<'d> {
	type Item = (Vec<u8>, OffchainOverlayedChange);
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
		let mut ooc = OffchainOverlayedChanges::enabled();
		ooc.set(STORAGE_PREFIX, b"ppp", b"qqq");
		ooc.remove(STORAGE_PREFIX, b"ppp");
		// keys are equiv, so it will overwrite the value and the overlay will contain
		// one item
		assert_eq!(ooc.iter().count(), 1);

		ooc.set(STORAGE_PREFIX, b"ppp", b"rrr");
		let mut iter = ooc.into_iter();
		let mut k = STORAGE_PREFIX.to_vec();
		k.extend_from_slice(&b"ppp"[..]);
		assert_eq!(iter.next(), Some((k, OffchainOverlayedChange::SetValue(b"rrr".to_vec()))));
		assert_eq!(iter.next(), None);
	}
}
