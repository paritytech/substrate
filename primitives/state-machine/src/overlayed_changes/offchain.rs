// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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

//! Overlayed changes for offchain indexing.

use super::changeset::OverlayedMap;
use codec::{Decode, Encode};
use sp_core::offchain::OffchainOverlayedChange;
use sp_std::prelude::Vec;
#[cfg(not(feature = "std"))]
use sp_std::vec;

/// In-memory storage for offchain workers recoding changes for the actual offchain storage
/// implementation.
#[derive(Debug, Clone, Default)]
pub struct OffchainOverlayedChanges(OverlayedMap<(Vec<u8>, Vec<u8>), OffchainOverlayedChange>);

/// Item for iterating over offchain changes.
///
/// First element i a tuple of `(prefix, key)`, second element ist the actual change
/// (remove or set value).
type OffchainOverlayedChangesItem<'i> = (&'i (Vec<u8>, Vec<u8>), &'i OffchainOverlayedChange);

/// Iterator over offchain changes, owned memory version.
type OffchainOverlayedChangesItemOwned = ((Vec<u8>, Vec<u8>), OffchainOverlayedChange);

impl OffchainOverlayedChanges {
	/// Consume the offchain storage and iterate over all key value pairs.
	pub fn into_iter(self) -> impl Iterator<Item = OffchainOverlayedChangesItemOwned> {
		self.0.into_changes().map(|kv| (kv.0, kv.1.into_value()))
	}

	/// Iterate over all key value pairs by reference.
	pub fn iter<'a>(&'a self) -> impl Iterator<Item = OffchainOverlayedChangesItem<'a>> {
		self.0.changes().map(|kv| (kv.0, kv.1.value_ref()))
	}

	/// Drain all elements of changeset.
	pub fn drain(&mut self) -> impl Iterator<Item = OffchainOverlayedChangesItemOwned> {
		sp_std::mem::take(self).into_iter()
	}

	/// Remove a key and its associated value from the offchain database.
	pub fn remove(&mut self, prefix: &[u8], key: &[u8]) {
		let _ = self
			.0
			.set((prefix.to_vec(), key.to_vec()), OffchainOverlayedChange::Remove, None);
	}

	/// Set the value associated with a key under a prefix to the value provided.
	/// if a secodary key is provided (secondary_key, value) will be pushed into the to
	/// Vec<(secondary_key, value)> at the position of the key
	pub fn set(&mut self, prefix: &[u8], key: &[u8], secondary_key: Option<&[u8]>, value: &[u8]) {
		let key = (prefix.to_vec(), key.to_vec());
		let secondary_key = secondary_key.map(|k| k.to_vec());
		if secondary_key.is_none() {
			let _ = self.0.set(key, OffchainOverlayedChange::SetValue(value.to_vec()), None);
			return
		}
		let overlayed_change: Option<OffchainOverlayedChange> =
			self.0.get(&key).map(|entry| entry.value_ref()).cloned();
		let value_to_insert = match overlayed_change {
			Some(OffchainOverlayedChange::SetValue(val)) => {
				let mut container: Vec<(Vec<u8>, Vec<u8>)> =
					Vec::decode(&mut &val[..]).unwrap_or(vec![]);
				container.push((secondary_key.unwrap(), value.to_vec()));
				container
			},
			_ => {
				vec![(secondary_key.unwrap(), value.to_vec())]
			},
		};

		let _ = self
			.0
			.set(key, OffchainOverlayedChange::SetValue(value_to_insert.encode()), None);
	}

	/// Obtain a associated value to the given key in storage with prefix.
	pub fn get(&self, prefix: &[u8], key: &[u8]) -> Option<OffchainOverlayedChange> {
		let key = (prefix.to_vec(), key.to_vec());
		self.0.get(&key).map(|entry| entry.value_ref()).cloned()
	}

	/// Reference to inner change set.
	pub fn overlay(&self) -> &OverlayedMap<(Vec<u8>, Vec<u8>), OffchainOverlayedChange> {
		&self.0
	}

	/// Mutable reference to inner change set.
	pub fn overlay_mut(
		&mut self,
	) -> &mut OverlayedMap<(Vec<u8>, Vec<u8>), OffchainOverlayedChange> {
		&mut self.0
	}
}

#[cfg(test)]
mod test {
	use super::*;
	use sp_core::offchain::STORAGE_PREFIX;

	#[test]
	fn test_drain() {
		let mut ooc = OffchainOverlayedChanges::default();
		ooc.set(STORAGE_PREFIX, b"kkk", None, b"vvv");
		let drained = ooc.drain().count();
		assert_eq!(drained, 1);
		let leftover = ooc.iter().count();
		assert_eq!(leftover, 0);

		ooc.set(STORAGE_PREFIX, b"a", None, b"v");
		ooc.set(STORAGE_PREFIX, b"b", None, b"v");
		ooc.set(STORAGE_PREFIX, b"c", None, b"v");
		ooc.set(STORAGE_PREFIX, b"d", None, b"v");
		ooc.set(STORAGE_PREFIX, b"e", None, b"v");
		assert_eq!(ooc.iter().count(), 5);
	}

	#[test]
	fn test_accumulated_set_remove_set() {
		let mut ooc = OffchainOverlayedChanges::default();
		ooc.set(STORAGE_PREFIX, b"ppp", None, b"qqq");
		ooc.remove(STORAGE_PREFIX, b"ppp");
		// keys are equiv, so it will overwrite the value and the overlay will contain
		// one item
		assert_eq!(ooc.iter().count(), 1);

		ooc.set(STORAGE_PREFIX, b"ppp", None, b"rrr");
		let mut iter = ooc.into_iter();
		assert_eq!(
			iter.next(),
			Some((
				(STORAGE_PREFIX.to_vec(), b"ppp".to_vec()),
				OffchainOverlayedChange::SetValue(b"rrr".to_vec())
			))
		);
		assert_eq!(iter.next(), None);
	}

	#[test]
	fn test_set_with_different_secondary_keys() {
		let mut ooc = OffchainOverlayedChanges::default();
		ooc.set(STORAGE_PREFIX, b"ppp", Some(b"hello"), b"qqq");

		// only one primary key has been set, in the overlay
		// there should be only one value on the overlay
		assert_eq!(ooc.iter().count(), 1);

		ooc.set(STORAGE_PREFIX, b"ppp", Some(b"world"), b"aaa");

		// There should still be only one value on the overlay
		assert_eq!(ooc.iter().count(), 1);

		let mut iter = ooc.into_iter();
		assert_eq!(
			iter.next(),
			Some((
				(STORAGE_PREFIX.to_vec(), b"ppp".to_vec()),
				OffchainOverlayedChange::SetValue(
					vec![
						(b"hello".to_vec(), b"qqq".to_vec()),
						(b"world".to_vec(), b"aaa".to_vec())
					]
					.encode()
				)
			))
		);
		assert_eq!(iter.next(), None);
	}
}
