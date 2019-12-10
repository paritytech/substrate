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

//! The overlayed changes to state.

#[cfg(test)]
use std::iter::FromIterator;
use std::collections::{HashMap, BTreeMap, BTreeSet};
use codec::Decode;
use crate::changes_trie::{NO_EXTRINSIC_INDEX, Configuration as ChangesTrieConfig};
use primitives::storage::well_known_keys::EXTRINSIC_INDEX;
use std::{mem, ops};

/// The overlayed changes to state to be queried on top of the backend.
///
/// A transaction shares all prospective changes within an inner overlay
/// that can be cleared.
#[derive(Debug, Default, Clone)]
pub struct OverlayedChanges {
	/// Changes that are not yet committed.
	pub(crate) prospective: OverlayedChangeSet,
	/// Committed changes.
	pub(crate) committed: OverlayedChangeSet,
	/// Changes trie configuration. None by default, but could be installed by the
	/// runtime if it supports change tries.
	pub(crate) changes_trie_config: Option<ChangesTrieConfig>,
}

/// The storage value, used inside OverlayedChanges.
#[derive(Debug, Default, Clone)]
#[cfg_attr(test, derive(PartialEq))]
pub struct OverlayedValue {
	/// Current value. None if value has been deleted.
	pub value: Option<Vec<u8>>,
	/// The set of extinsic indices where the values has been changed.
	/// Is filled only if runtime has announced changes trie support.
	pub extrinsics: Option<BTreeSet<u32>>,
}

/// Prospective or committed overlayed change set.
#[derive(Debug, Default, Clone)]
#[cfg_attr(test, derive(PartialEq))]
pub struct OverlayedChangeSet {
	/// Top level storage changes.
	pub top: BTreeMap<Vec<u8>, OverlayedValue>,
	/// Child storage changes.
	pub children: HashMap<Vec<u8>, BTreeMap<Vec<u8>, OverlayedValue>>,
}

#[cfg(test)]
impl FromIterator<(Vec<u8>, OverlayedValue)> for OverlayedChangeSet {
	fn from_iter<T: IntoIterator<Item = (Vec<u8>, OverlayedValue)>>(iter: T) -> Self {
		Self {
			top: iter.into_iter().collect(),
			children: Default::default(),
		}
	}
}

impl OverlayedChangeSet {
	/// Whether the change set is empty.
	pub fn is_empty(&self) -> bool {
		self.top.is_empty() && self.children.is_empty()
	}

	/// Clear the change set.
	pub fn clear(&mut self) {
		self.top.clear();
		self.children.clear();
	}
}

impl OverlayedChanges {
	/// Whether the overlayed changes are empty.
	pub fn is_empty(&self) -> bool {
		self.prospective.is_empty() && self.committed.is_empty()
	}

	/// Sets the changes trie configuration.
	///
	/// Returns false if configuration has been set already and we now trying
	/// to install different configuration. This isn't supported now.
	pub(crate) fn set_changes_trie_config(&mut self, config: ChangesTrieConfig) -> bool {
		if let Some(ref old_config) = self.changes_trie_config {
			// we do not support changes trie configuration' change now
			if *old_config != config {
				return false;
			}
		}

		self.changes_trie_config = Some(config);
		true
	}

	/// Returns a double-Option: None if the key is unknown (i.e. and the query should be refered
	/// to the backend); Some(None) if the key has been deleted. Some(Some(...)) for a key whose
	/// value has been set.
	pub fn storage(&self, key: &[u8]) -> Option<Option<&[u8]>> {
		self.prospective.top.get(key)
			.or_else(|| self.committed.top.get(key))
			.map(|x| x.value.as_ref().map(AsRef::as_ref))
	}

	/// Returns a double-Option: None if the key is unknown (i.e. and the query should be refered
	/// to the backend); Some(None) if the key has been deleted. Some(Some(...)) for a key whose
	/// value has been set.
	pub fn child_storage(&self, storage_key: &[u8], key: &[u8]) -> Option<Option<&[u8]>> {
		if let Some(map) = self.prospective.children.get(storage_key) {
			if let Some(val) = map.get(key) {
				return Some(val.value.as_ref().map(AsRef::as_ref));
			}
		}

		if let Some(map) = self.committed.children.get(storage_key) {
			if let Some(val) = map.get(key) {
				return Some(val.value.as_ref().map(AsRef::as_ref));
			}
		}

		None
	}

	/// Inserts the given key-value pair into the prospective change set.
	///
	/// `None` can be used to delete a value specified by the given key.
	pub(crate) fn set_storage(&mut self, key: Vec<u8>, val: Option<Vec<u8>>) {
		let extrinsic_index = self.extrinsic_index();
		let entry = self.prospective.top.entry(key).or_default();
		entry.value = val;

		if let Some(extrinsic) = extrinsic_index {
			entry.extrinsics.get_or_insert_with(Default::default)
				.insert(extrinsic);
		}
	}

	/// Inserts the given key-value pair into the prospective child change set.
	///
	/// `None` can be used to delete a value specified by the given key.
	pub(crate) fn set_child_storage(&mut self, storage_key: Vec<u8>, key: Vec<u8>, val: Option<Vec<u8>>) {
		let extrinsic_index = self.extrinsic_index();
		let map_entry = self.prospective.children.entry(storage_key).or_default();
		let entry = map_entry.entry(key).or_default();
		entry.value = val;

		if let Some(extrinsic) = extrinsic_index {
			entry.extrinsics.get_or_insert_with(Default::default)
				.insert(extrinsic);
		}
	}

	/// Clear child storage of given storage key.
	///
	/// NOTE that this doesn't take place immediately but written into the prospective
	/// change set, and still can be reverted by [`discard_prospective`].
	///
	/// [`discard_prospective`]: #method.discard_prospective
	pub(crate) fn clear_child_storage(&mut self, storage_key: &[u8]) {
		let extrinsic_index = self.extrinsic_index();
		let map_entry = self.prospective.children.entry(storage_key.to_vec()).or_default();

		map_entry.values_mut().for_each(|e| {
			if let Some(extrinsic) = extrinsic_index {
				e.extrinsics.get_or_insert_with(Default::default)
					.insert(extrinsic);
			}

			e.value = None;
		});

		if let Some(committed_map) = self.committed.children.get(storage_key) {
			for (key, value) in committed_map.iter() {
				if !map_entry.contains_key(key) {
					map_entry.insert(key.clone(), OverlayedValue {
						value: None,
						extrinsics: extrinsic_index.map(|i| {
							let mut e = value.extrinsics.clone()
								.unwrap_or_else(|| BTreeSet::default());
							e.insert(i);
							e
						}),
					});
				}
			}
		}
	}

	/// Removes all key-value pairs which keys share the given prefix.
	///
	/// NOTE that this doesn't take place immediately but written into the prospective
	/// change set, and still can be reverted by [`discard_prospective`].
	///
	/// [`discard_prospective`]: #method.discard_prospective
	pub(crate) fn clear_prefix(&mut self, prefix: &[u8]) {
		let extrinsic_index = self.extrinsic_index();

		// Iterate over all prospective and mark all keys that share
		// the given prefix as removed (None).
		for (key, entry) in self.prospective.top.iter_mut() {
			if key.starts_with(prefix) {
				entry.value = None;

				if let Some(extrinsic) = extrinsic_index {
					entry.extrinsics.get_or_insert_with(Default::default)
						.insert(extrinsic);
				}
			}
		}

		// Then do the same with keys from commited changes.
		// NOTE that we are making changes in the prospective change set.
		for key in self.committed.top.keys() {
			if key.starts_with(prefix) {
				let entry = self.prospective.top.entry(key.clone()).or_default();
				entry.value = None;

				if let Some(extrinsic) = extrinsic_index {
					entry.extrinsics.get_or_insert_with(Default::default)
						.insert(extrinsic);
				}
			}
		}
	}

	pub(crate) fn clear_child_prefix(&mut self, storage_key: &[u8], prefix: &[u8]) {
		let extrinsic_index = self.extrinsic_index();
		let map_entry = self.prospective.children.entry(storage_key.to_vec()).or_default();

		for (key, entry) in map_entry.iter_mut() {
			if key.starts_with(prefix) {
				entry.value = None;

				if let Some(extrinsic) = extrinsic_index {
					entry.extrinsics.get_or_insert_with(Default::default)
						.insert(extrinsic);
				}
			}
		}

		if let Some(child_committed) = self.committed.children.get(storage_key) {
			// Then do the same with keys from commited changes.
			// NOTE that we are making changes in the prospective change set.
			for key in child_committed.keys() {
				if key.starts_with(prefix) {
					let entry = map_entry.entry(key.clone()).or_default();
					entry.value = None;

					if let Some(extrinsic) = extrinsic_index {
						entry.extrinsics.get_or_insert_with(Default::default)
							.insert(extrinsic);
					}
				}
			}
		}
	}

	/// Discard prospective changes to state.
	pub fn discard_prospective(&mut self) {
		self.prospective.clear();
	}

	/// Commit prospective changes to state.
	pub fn commit_prospective(&mut self) {
		if self.committed.is_empty() {
			mem::swap(&mut self.prospective, &mut self.committed);
		} else {
			let top_to_commit = mem::replace(&mut self.prospective.top, BTreeMap::new());
			for (key, val) in top_to_commit.into_iter() {
				let entry = self.committed.top.entry(key).or_default();
				entry.value = val.value;

				if let Some(prospective_extrinsics) = val.extrinsics {
					entry.extrinsics.get_or_insert_with(Default::default)
						.extend(prospective_extrinsics);
				}
			}
			for (storage_key, map) in self.prospective.children.drain() {
				let map_dest = self.committed.children.entry(storage_key).or_default();
				for (key, val) in map.into_iter() {
					let entry = map_dest.entry(key).or_default();
					entry.value = val.value;

					if let Some(prospective_extrinsics) = val.extrinsics {
						entry.extrinsics.get_or_insert_with(Default::default)
							.extend(prospective_extrinsics);
					}
				}
			}
		}
	}

	/// Consume `OverlayedChanges` and take committed set.
	///
	/// Panics:
	/// Will panic if there are any uncommitted prospective changes.
	pub fn into_committed(self) -> (
		impl Iterator<Item=(Vec<u8>, Option<Vec<u8>>)>,
		impl Iterator<Item=(Vec<u8>, impl Iterator<Item=(Vec<u8>, Option<Vec<u8>>)>)>,
	){
		assert!(self.prospective.is_empty());
		(self.committed.top.into_iter().map(|(k, v)| (k, v.value)),
			self.committed.children.into_iter()
				.map(|(sk, v)| (sk, v.into_iter().map(|(k, v)| (k, v.value)))))
	}

	/// Inserts storage entry responsible for current extrinsic index.
	#[cfg(test)]
	pub(crate) fn set_extrinsic_index(&mut self, extrinsic_index: u32) {
		use codec::Encode;
		self.prospective.top.insert(EXTRINSIC_INDEX.to_vec(), OverlayedValue {
			value: Some(extrinsic_index.encode()),
			extrinsics: None,
		});
	}

	/// Returns current extrinsic index to use in changes trie construction.
	/// None is returned if it is not set or changes trie config is not set.
	/// Persistent value (from the backend) can be ignored because runtime must
	/// set this index before first and unset after last extrinsic is executied.
	/// Changes that are made outside of extrinsics, are marked with
	/// `NO_EXTRINSIC_INDEX` index.
	fn extrinsic_index(&self) -> Option<u32> {
		match self.changes_trie_config.is_some() {
			true => Some(
				self.storage(EXTRINSIC_INDEX)
					.and_then(|idx| idx.and_then(|idx| Decode::decode(&mut &*idx).ok()))
					.unwrap_or(NO_EXTRINSIC_INDEX)),
			false => None,
		}
	}

	/// Returns the next (in lexicographic order) storage key in the overlayed alongside its value.
	/// If no value is next then `None` is returned.
	pub fn next_storage_key_change(&self, key: &[u8]) -> Option<(&[u8], &OverlayedValue)> {
		let range = (ops::Bound::Excluded(key), ops::Bound::Unbounded);

		let next_prospective_key = self.prospective.top
			.range::<[u8], _>(range)
			.next()
			.map(|(k, v)| (&k[..], v));

		let next_committed_key = self.committed.top
			.range::<[u8], _>(range)
			.next()
			.map(|(k, v)| (&k[..], v));

		match (next_committed_key, next_prospective_key) {
			// Committed is strictly less than prospective
			(Some(committed_key), Some(prospective_key)) if committed_key.0 < prospective_key.0 =>
				Some(committed_key),
			(committed_key, None) => committed_key,
			// Prospective key is less or equal to committed or committed doesn't exist
			(_, prospective_key) => prospective_key,
		}
	}

	/// Returns the next (in lexicographic order) child storage key in the overlayed alongside its
	/// value.  If no value is next then `None` is returned.
	pub fn next_child_storage_key_change(
		&self,
		storage_key: &[u8],
		key: &[u8]
	) -> Option<(&[u8], &OverlayedValue)> {
		let range = (ops::Bound::Excluded(key), ops::Bound::Unbounded);

		let next_prospective_key = self.prospective.children.get(storage_key)
			.and_then(|map| map.range::<[u8], _>(range).next().map(|(k, v)| (&k[..], v)));

		let next_committed_key = self.committed.children.get(storage_key)
			.and_then(|map| map.range::<[u8], _>(range).next().map(|(k, v)| (&k[..], v)));

		match (next_committed_key, next_prospective_key) {
			// Committed is strictly less than prospective
			(Some(committed_key), Some(prospective_key)) if committed_key.0 < prospective_key.0 =>
				Some(committed_key),
			(committed_key, None) => committed_key,
			// Prospective key is less or equal to committed or committed doesn't exist
			(_, prospective_key) => prospective_key,
		}
	}
}

#[cfg(test)]
impl From<Option<Vec<u8>>> for OverlayedValue {
	fn from(value: Option<Vec<u8>>) -> OverlayedValue {
		OverlayedValue { value, ..Default::default() }
	}
}

#[cfg(test)]
mod tests {
	use hex_literal::hex;
	use primitives::{
		Blake2Hasher, traits::Externalities, storage::well_known_keys::EXTRINSIC_INDEX,
	};
	use crate::backend::InMemory;
	use crate::changes_trie::InMemoryStorage as InMemoryChangesTrieStorage;
	use crate::ext::Ext;
	use super::*;

	fn strip_extrinsic_index(map: &BTreeMap<Vec<u8>, OverlayedValue>)
		-> BTreeMap<Vec<u8>, OverlayedValue>
	{
		let mut clone = map.clone();
		clone.remove(&EXTRINSIC_INDEX.to_vec());
		clone
	}

	#[test]
	fn overlayed_storage_works() {
		let mut overlayed = OverlayedChanges::default();

		let key = vec![42, 69, 169, 142];

		assert!(overlayed.storage(&key).is_none());

		overlayed.set_storage(key.clone(), Some(vec![1, 2, 3]));
		assert_eq!(overlayed.storage(&key).unwrap(), Some(&[1, 2, 3][..]));

		overlayed.commit_prospective();
		assert_eq!(overlayed.storage(&key).unwrap(), Some(&[1, 2, 3][..]));

		overlayed.set_storage(key.clone(), Some(vec![]));
		assert_eq!(overlayed.storage(&key).unwrap(), Some(&[][..]));

		overlayed.set_storage(key.clone(), None);
		assert!(overlayed.storage(&key).unwrap().is_none());

		overlayed.discard_prospective();
		assert_eq!(overlayed.storage(&key).unwrap(), Some(&[1, 2, 3][..]));

		overlayed.set_storage(key.clone(), None);
		overlayed.commit_prospective();
		assert!(overlayed.storage(&key).unwrap().is_none());
	}

	#[test]
	fn overlayed_storage_root_works() {
		let initial: BTreeMap<_, _> = vec![
			(b"doe".to_vec(), b"reindeer".to_vec()),
			(b"dog".to_vec(), b"puppyXXX".to_vec()),
			(b"dogglesworth".to_vec(), b"catXXX".to_vec()),
			(b"doug".to_vec(), b"notadog".to_vec()),
		].into_iter().collect();
		let backend = InMemory::<Blake2Hasher>::from(initial);
		let mut overlay = OverlayedChanges {
			committed: vec![
				(b"dog".to_vec(), Some(b"puppy".to_vec()).into()),
				(b"dogglesworth".to_vec(), Some(b"catYYY".to_vec()).into()),
				(b"doug".to_vec(), Some(vec![]).into()),
			].into_iter().collect(),
			prospective: vec![
				(b"dogglesworth".to_vec(), Some(b"cat".to_vec()).into()),
				(b"doug".to_vec(), None.into()),
			].into_iter().collect(),
			..Default::default()
		};

		let changes_trie_storage = InMemoryChangesTrieStorage::<Blake2Hasher, u64>::new();
		let mut ext = Ext::new(
			&mut overlay,
			&backend,
			Some(&changes_trie_storage),
			None,
		);
		const ROOT: [u8; 32] = hex!("39245109cef3758c2eed2ccba8d9b370a917850af3824bc8348d505df2c298fa");

		assert_eq!(&ext.storage_root()[..], &ROOT);
	}

	#[test]
	fn changes_trie_configuration_is_saved() {
		let mut overlay = OverlayedChanges::default();
		assert!(overlay.changes_trie_config.is_none());
		assert_eq!(
			overlay.set_changes_trie_config(
				ChangesTrieConfig { digest_interval: 4, digest_levels: 1, },
			),
			true,
		);
		assert!(overlay.changes_trie_config.is_some());
	}

	#[test]
	fn changes_trie_configuration_is_saved_twice() {
		let mut overlay = OverlayedChanges::default();
		assert!(overlay.changes_trie_config.is_none());
		assert_eq!(overlay.set_changes_trie_config(ChangesTrieConfig {
			digest_interval: 4, digest_levels: 1,
		}), true);
		overlay.set_extrinsic_index(0);
		overlay.set_storage(vec![1], Some(vec![2]));
		assert_eq!(overlay.set_changes_trie_config(ChangesTrieConfig {
			digest_interval: 4, digest_levels: 1,
		}), true);
		assert_eq!(
			strip_extrinsic_index(&overlay.prospective.top),
			vec![
				(vec![1], OverlayedValue { value: Some(vec![2]),
				 extrinsics: Some(vec![0].into_iter().collect()) }),
			].into_iter().collect(),
		);
	}

	#[test]
	fn panics_when_trying_to_save_different_changes_trie_configuration() {
		let mut overlay = OverlayedChanges::default();
		assert_eq!(overlay.set_changes_trie_config(ChangesTrieConfig {
			digest_interval: 4, digest_levels: 1,
		}), true);
		assert_eq!(overlay.set_changes_trie_config(ChangesTrieConfig {
			digest_interval: 2, digest_levels: 1,
		}), false);
	}

	#[test]
	fn extrinsic_changes_are_collected() {
		let mut overlay = OverlayedChanges::default();
		let _ = overlay.set_changes_trie_config(ChangesTrieConfig {
			digest_interval: 4, digest_levels: 1,
		});

		overlay.set_storage(vec![100], Some(vec![101]));

		overlay.set_extrinsic_index(0);
		overlay.set_storage(vec![1], Some(vec![2]));

		overlay.set_extrinsic_index(1);
		overlay.set_storage(vec![3], Some(vec![4]));

		overlay.set_extrinsic_index(2);
		overlay.set_storage(vec![1], Some(vec![6]));

		assert_eq!(strip_extrinsic_index(&overlay.prospective.top),
			vec![
				(vec![1], OverlayedValue { value: Some(vec![6]),
				 extrinsics: Some(vec![0, 2].into_iter().collect()) }),
				(vec![3], OverlayedValue { value: Some(vec![4]),
				 extrinsics: Some(vec![1].into_iter().collect()) }),
				(vec![100], OverlayedValue { value: Some(vec![101]),
				 extrinsics: Some(vec![NO_EXTRINSIC_INDEX].into_iter().collect()) }),
			].into_iter().collect());

		overlay.commit_prospective();

		overlay.set_extrinsic_index(3);
		overlay.set_storage(vec![3], Some(vec![7]));

		overlay.set_extrinsic_index(4);
		overlay.set_storage(vec![1], Some(vec![8]));

		assert_eq!(strip_extrinsic_index(&overlay.committed.top),
			vec![
				(vec![1], OverlayedValue { value: Some(vec![6]),
				 extrinsics: Some(vec![0, 2].into_iter().collect()) }),
				(vec![3], OverlayedValue { value: Some(vec![4]),
				 extrinsics: Some(vec![1].into_iter().collect()) }),
				(vec![100], OverlayedValue { value: Some(vec![101]),
				 extrinsics: Some(vec![NO_EXTRINSIC_INDEX].into_iter().collect()) }),
			].into_iter().collect());

		assert_eq!(strip_extrinsic_index(&overlay.prospective.top),
			vec![
				(vec![1], OverlayedValue { value: Some(vec![8]),
				 extrinsics: Some(vec![4].into_iter().collect()) }),
				(vec![3], OverlayedValue { value: Some(vec![7]),
				 extrinsics: Some(vec![3].into_iter().collect()) }),
			].into_iter().collect());

		overlay.commit_prospective();

		assert_eq!(strip_extrinsic_index(&overlay.committed.top),
			vec![
				(vec![1], OverlayedValue { value: Some(vec![8]),
				 extrinsics: Some(vec![0, 2, 4].into_iter().collect()) }),
				(vec![3], OverlayedValue { value: Some(vec![7]),
				 extrinsics: Some(vec![1, 3].into_iter().collect()) }),
				(vec![100], OverlayedValue { value: Some(vec![101]),
				 extrinsics: Some(vec![NO_EXTRINSIC_INDEX].into_iter().collect()) }),
			].into_iter().collect());

		assert_eq!(overlay.prospective,
			Default::default());
	}

	#[test]
	fn next_storage_key_change_works() {
		let mut overlay = OverlayedChanges::default();
		overlay.set_storage(vec![20], Some(vec![20]));
		overlay.set_storage(vec![30], Some(vec![30]));
		overlay.set_storage(vec![40], Some(vec![40]));
		overlay.commit_prospective();
		overlay.set_storage(vec![10], Some(vec![10]));
		overlay.set_storage(vec![30], None);

		// next_prospective < next_committed
		let next_to_5 = overlay.next_storage_key_change(&[5]).unwrap();
		assert_eq!(next_to_5.0.to_vec(), vec![10]);
		assert_eq!(next_to_5.1.value, Some(vec![10]));

		// next_committed < next_prospective
		let next_to_10 = overlay.next_storage_key_change(&[10]).unwrap();
		assert_eq!(next_to_10.0.to_vec(), vec![20]);
		assert_eq!(next_to_10.1.value, Some(vec![20]));

		// next_committed == next_prospective
		let next_to_20 = overlay.next_storage_key_change(&[20]).unwrap();
		assert_eq!(next_to_20.0.to_vec(), vec![30]);
		assert_eq!(next_to_20.1.value, None);

		// next_committed, no next_prospective
		let next_to_30 = overlay.next_storage_key_change(&[30]).unwrap();
		assert_eq!(next_to_30.0.to_vec(), vec![40]);
		assert_eq!(next_to_30.1.value, Some(vec![40]));

		overlay.set_storage(vec![50], Some(vec![50]));
		// next_prospective, no next_committed
		let next_to_40 = overlay.next_storage_key_change(&[40]).unwrap();
		assert_eq!(next_to_40.0.to_vec(), vec![50]);
		assert_eq!(next_to_40.1.value, Some(vec![50]));
	}

	#[test]
	fn next_child_storage_key_change_works() {
		let child = b"Child1".to_vec();
		let mut overlay = OverlayedChanges::default();
		overlay.set_child_storage(child.clone(), vec![20], Some(vec![20]));
		overlay.set_child_storage(child.clone(), vec![30], Some(vec![30]));
		overlay.set_child_storage(child.clone(), vec![40], Some(vec![40]));
		overlay.commit_prospective();
		overlay.set_child_storage(child.clone(), vec![10], Some(vec![10]));
		overlay.set_child_storage(child.clone(), vec![30], None);

		// next_prospective < next_committed
		let next_to_5 = overlay.next_child_storage_key_change(&child, &[5]).unwrap();
		assert_eq!(next_to_5.0.to_vec(), vec![10]);
		assert_eq!(next_to_5.1.value, Some(vec![10]));

		// next_committed < next_prospective
		let next_to_10 = overlay.next_child_storage_key_change(&child, &[10]).unwrap();
		assert_eq!(next_to_10.0.to_vec(), vec![20]);
		assert_eq!(next_to_10.1.value, Some(vec![20]));

		// next_committed == next_prospective
		let next_to_20 = overlay.next_child_storage_key_change(&child, &[20]).unwrap();
		assert_eq!(next_to_20.0.to_vec(), vec![30]);
		assert_eq!(next_to_20.1.value, None);

		// next_committed, no next_prospective
		let next_to_30 = overlay.next_child_storage_key_change(&child, &[30]).unwrap();
		assert_eq!(next_to_30.0.to_vec(), vec![40]);
		assert_eq!(next_to_30.1.value, Some(vec![40]));

		overlay.set_child_storage(child.clone(), vec![50], Some(vec![50]));
		// next_prospective, no next_committed
		let next_to_40 = overlay.next_child_storage_key_change(&child, &[40]).unwrap();
		assert_eq!(next_to_40.0.to_vec(), vec![50]);
		assert_eq!(next_to_40.1.value, Some(vec![50]));
	}
}
