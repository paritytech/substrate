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

#[cfg(test)] use std::iter::FromIterator;
use std::collections::{HashMap, BTreeSet};
use codec::Decode;
use crate::changes_trie::{NO_EXTRINSIC_INDEX, Configuration as ChangesTrieConfig};
use primitives::storage::well_known_keys::EXTRINSIC_INDEX;
use primitives::child_trie::{KeySpace, ChildTrie, ChildTrieReadRef};

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

/// All changes related to a child trie.
#[derive(Debug, Clone)]
#[cfg_attr(test, derive(PartialEq))]
pub struct ChildOverlayChangeSet {
	/// Mapping of key with optional value, if value is `None` that is a removal.
	pub values: HashMap<Vec<u8>, OverlayedValue>,
	/// Child trie value.
	pub child_trie: ChildTrie,
}

/// Prospective or committed overlayed change set.
#[derive(Debug, Default, Clone)]
#[cfg_attr(test, derive(PartialEq))]
pub struct OverlayedChangeSet {
	/// Top level storage changes.
	pub top: HashMap<Vec<u8>, OverlayedValue>,
	/// Child storage changes.
	pub children: HashMap<KeySpace, ChildOverlayChangeSet>,
	/// Association from parent storage location to keyspace.
	/// If value is none the child is moved or deleted.
	pub pending_child: HashMap<Vec<u8>, Option<KeySpace>>,
}

#[cfg(test)]
impl FromIterator<(Vec<u8>, OverlayedValue)> for OverlayedChangeSet {
	fn from_iter<T: IntoIterator<Item = (Vec<u8>, OverlayedValue)>>(iter: T) -> Self {
		Self {
			top: iter.into_iter().collect(),
			children: Default::default(),
			pending_child: Default::default(),
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
		self.pending_child.clear();
	}
}

#[derive(Debug, Clone)]
#[cfg_attr(test, derive(PartialEq))]
/// Possible result from value
/// query in the overlay.
pub enum OverlayedValueResult<'a> {
	/// The key is unknown (i.e. and the query should be refered
	/// to the backend)
	NotFound,
	/// The key has been deleted.
	Deleted,
	/// Current value set in the overlay.
	Modified(&'a[u8]),
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

	/// Get the `OverlayedValueResult` for a given key.
	pub fn storage(&self, key: &[u8]) -> OverlayedValueResult {
		match self.prospective.top.get(key).or_else(|| self.committed.top.get(key)) {
			Some(OverlayedValue { value: Some(val), .. }) => OverlayedValueResult::Modified(val.as_ref()),
			Some(OverlayedValue { value: None, .. }) => OverlayedValueResult::Deleted,
			None => OverlayedValueResult::NotFound,
		}
	}

	/// Get the `OverlayedValueResult` for a given child key.
	pub fn child_storage(&self, child_trie: ChildTrieReadRef, key: &[u8]) -> OverlayedValueResult {
		let keyspace = child_trie.keyspace();
		match self.prospective.children.get(keyspace)
			.and_then(|map| map.values.get(key).map(|v| &v.value)) {
			Some(Some(val)) =>
				return OverlayedValueResult::Modified(val.as_ref()),
			Some(None) =>
				return OverlayedValueResult::Deleted,
			None => (),
		}

		match self.committed.children.get(keyspace)
			.and_then(|map| map.values.get(key).map(|v| &v.value)) {
			Some(Some(val)) =>
				return OverlayedValueResult::Modified(val.as_ref()),
			Some(None) =>
				return OverlayedValueResult::Deleted,
			None => OverlayedValueResult::NotFound,
		}

	}

	/// returns a child trie if present
	pub fn child_trie(&self, storage_key: &[u8]) -> Option<Option<ChildTrie>> {

		match self.prospective.pending_child.get(storage_key) {
			Some(Some(keyspace)) => {
				let map = self.prospective.children.get(keyspace)
					.expect("pending entry always have a children association; qed");
				return Some(Some(map.child_trie.clone()));
			},
			Some(None) => return Some(None),
			None => (),
		}

		match self.committed.pending_child.get(storage_key) {
			Some(Some(keyspace)) => {
				let map = self.committed.children.get(keyspace)
					.expect("pending entry always have a children association; qed");
				return Some(Some(map.child_trie.clone()));
			},
			Some(None) => return Some(None),
			None => (),
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
	pub(crate) fn set_child_storage(&mut self, child_trie: &ChildTrie, key: Vec<u8>, val: Option<Vec<u8>>) {
		let extrinsic_index = self.extrinsic_index();
		let p = &mut self.prospective.children;
		let pc = &mut self.prospective.pending_child;
		let map_entry = p.entry(child_trie.keyspace().clone())
			.or_insert_with(|| {
				let parent = child_trie.parent_slice().to_vec();
				pc.insert(parent, Some(child_trie.keyspace().clone()));
				ChildOverlayChangeSet {
					values: Default::default(),
					child_trie: child_trie.clone(),
				}
			});
		let entry = map_entry.values.entry(key).or_default();
		entry.value = val;

		if let Some(extrinsic) = extrinsic_index {
			entry.extrinsics.get_or_insert_with(Default::default)
				.insert(extrinsic);
		}
	}

	/// Try to update child trie. Some changes are not allowed:
	/// - keyspace
	/// - root
	/// - parent path
  /// TODO EMCH merge removed the extrinsic local to a child trie
  /// it should update the storage_key value extrinsics (parent).
	pub(crate) fn set_child_trie(&mut self, child_trie: ChildTrie) -> bool {
		if let Some(Some(old_ct)) = self.prospective.pending_child
			.get(child_trie.parent_slice()) {
			let old_ct = self.prospective.children.get_mut(old_ct)
				.expect("pending entry always have a children association; qed");
			let old_ct = &mut old_ct.child_trie;
			if old_ct.is_updatable_with(&child_trie) {
				*old_ct = child_trie;
			} else {
				return false;
			}
		} else {
			if let Some(old_ct) = self.committed.pending_child
				.get(child_trie.parent_slice()).and_then(|k|
					k.as_ref().and_then(|k| self.committed.children.get(k))) {
				if old_ct.child_trie.root_initial_value() != child_trie.root_initial_value()
					|| old_ct.child_trie.keyspace() != child_trie.keyspace()
					|| old_ct.child_trie.parent_slice() != child_trie.parent_slice() {
					return false;
				}
			}
			self.prospective.pending_child
				.insert(child_trie.parent_slice().to_vec(), Some(child_trie.keyspace().clone()));
			self.prospective.children.insert(
				child_trie.keyspace().to_vec(),
				ChildOverlayChangeSet {
					values: Default::default(),
					child_trie: child_trie.clone(),
				}
			);
		}
		true
	}

	/// Clear child storage of given storage key.
	///
	/// NOTE that this doesn't take place immediately but written into the prospective
	/// change set, and still can be reverted by [`discard_prospective`].
	///
	/// [`discard_prospective`]: #method.discard_prospective
	pub(crate) fn clear_child_storage(&mut self, child_trie: &ChildTrie) {
		let extrinsic_index = self.extrinsic_index();
		let map_entry = self.prospective.children.entry(child_trie.keyspace().clone())
			.or_insert_with(|| ChildOverlayChangeSet {
				values: Default::default(),
				child_trie: child_trie.clone(),
			});

		map_entry.values.values_mut().for_each(|e| {
			if let Some(extrinsic) = extrinsic_index {
				e.extrinsics.get_or_insert_with(Default::default)
					.insert(extrinsic);
			}
			e.value = None;
		});

		if let Some(child_set) = self.committed.children.get(child_trie.keyspace()) {
			for (key, value) in child_set.values.iter() {
				if !map_entry.values.contains_key(key) {
					map_entry.values.insert(key.clone(), OverlayedValue {
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

	pub(crate) fn clear_child_prefix(&mut self, child_trie: &ChildTrie, prefix: &[u8]) {
		let extrinsic_index = self.extrinsic_index();
		let map_entry = self.prospective.children.entry(child_trie.keyspace().to_vec())
			.or_insert_with(|| ChildOverlayChangeSet {
				values: Default::default(),
				child_trie: child_trie.clone(),
			});


		for (key, entry) in map_entry.values.iter_mut() {
			if key.starts_with(prefix) {
				entry.value = None;

				if let Some(extrinsic) = extrinsic_index {
					entry.extrinsics.get_or_insert_with(Default::default)
						.insert(extrinsic);
				}
			}
		}

		if let Some(child_committed) = self.committed.children.get(child_trie.keyspace()) {
			// Then do the same with keys from commited changes.
			// NOTE that we are making changes in the prospective change set.
			for key in child_committed.values.keys() {
				if key.starts_with(prefix) {
					let entry = map_entry.values.entry(key.clone()).or_default();
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
			::std::mem::swap(&mut self.prospective, &mut self.committed);
		} else {
			for (key, val) in self.prospective.top.drain() {
				let entry = self.committed.top.entry(key).or_default();
				entry.value = val.value;

				if let Some(prospective_extrinsics) = val.extrinsics {
					entry.extrinsics.get_or_insert_with(Default::default)
						.extend(prospective_extrinsics);
				}
			}
			for (keyspace, ChildOverlayChangeSet {mut values, child_trie}) in self.prospective.children.drain() {
				let child_set = self.committed.children.entry(keyspace)
					.or_insert_with(|| ChildOverlayChangeSet {
						values: Default::default(),
						child_trie: child_trie.clone(),
					});
				for (key, val) in values.drain() {
					let entry = child_set.values.entry(key).or_default();
					entry.value = val.value;

					if let Some(prospective_extrinsics) = val.extrinsics {
						entry.extrinsics.get_or_insert_with(Default::default)
							.extend(prospective_extrinsics);
					}
				}
			}
			self.committed.pending_child.extend(self.prospective.pending_child.drain());
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
				.map(|(ks, v)| (ks, v.values.into_iter().map(|(k, v)| (k, v.value)))))
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
				match self.storage(EXTRINSIC_INDEX) {
					OverlayedValueResult::Modified(idx) => Decode::decode(&mut &*idx)
						.unwrap_or(NO_EXTRINSIC_INDEX),
					OverlayedValueResult::Deleted
					| OverlayedValueResult::NotFound => NO_EXTRINSIC_INDEX,
				}
			),
			false => None,
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
	use primitives::{Blake2Hasher, H256};
	use primitives::storage::well_known_keys::EXTRINSIC_INDEX;
	use crate::backend::InMemory;
	use crate::changes_trie::InMemoryStorage as InMemoryChangesTrieStorage;
	use crate::ext::Ext;
	use crate::Externalities;
	use super::*;

	fn strip_extrinsic_index(map: &HashMap<Vec<u8>, OverlayedValue>) -> HashMap<Vec<u8>, OverlayedValue> {
		let mut clone = map.clone();
		clone.remove(&EXTRINSIC_INDEX.to_vec());
		clone
	}

	#[test]
	fn overlayed_storage_works() {
		let mut overlayed = OverlayedChanges::default();

		let key = vec![42, 69, 169, 142];

		assert_eq!(overlayed.storage(&key), OverlayedValueResult::NotFound);

		overlayed.set_storage(key.clone(), Some(vec![1, 2, 3]));
		assert_eq!(overlayed.storage(&key), OverlayedValueResult::Modified(&[1, 2, 3][..]));

		overlayed.commit_prospective();
		assert_eq!(overlayed.storage(&key), OverlayedValueResult::Modified(&[1, 2, 3][..]));

		overlayed.set_storage(key.clone(), Some(vec![]));
		assert_eq!(overlayed.storage(&key), OverlayedValueResult::Modified(&[][..]));

		overlayed.set_storage(key.clone(), None);
		assert_eq!(overlayed.storage(&key), OverlayedValueResult::Deleted);

		overlayed.discard_prospective();
		assert_eq!(overlayed.storage(&key), OverlayedValueResult::Modified(&[1, 2, 3][..]));

		overlayed.set_storage(key.clone(), None);
		overlayed.commit_prospective();
		assert_eq!(overlayed.storage(&key), OverlayedValueResult::Deleted);
	}

	#[test]
	fn overlayed_storage_root_works() {
		let initial: HashMap<_, _> = vec![
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
			crate::NeverOffchainExt::new(),
			None,
		);
		const ROOT: [u8; 32] = hex!("39245109cef3758c2eed2ccba8d9b370a917850af3824bc8348d505df2c298fa");

		assert_eq!(ext.storage_root(), H256::from(ROOT));
	}

	#[test]
	fn changes_trie_configuration_is_saved() {
		let mut overlay = OverlayedChanges::default();
		assert!(overlay.changes_trie_config.is_none());
		assert_eq!(overlay.set_changes_trie_config(ChangesTrieConfig {
			digest_interval: 4, digest_levels: 1,
		}), true);
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
				(vec![1], OverlayedValue { value: Some(vec![2]), extrinsics: Some(vec![0].into_iter().collect()) }),
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
				(vec![1], OverlayedValue { value: Some(vec![6]), extrinsics: Some(vec![0, 2].into_iter().collect()) }),
				(vec![3], OverlayedValue { value: Some(vec![4]), extrinsics: Some(vec![1].into_iter().collect()) }),
				(vec![100], OverlayedValue { value: Some(vec![101]), extrinsics: Some(vec![NO_EXTRINSIC_INDEX].into_iter().collect()) }),
			].into_iter().collect());

		overlay.commit_prospective();

		overlay.set_extrinsic_index(3);
		overlay.set_storage(vec![3], Some(vec![7]));

		overlay.set_extrinsic_index(4);
		overlay.set_storage(vec![1], Some(vec![8]));

		assert_eq!(strip_extrinsic_index(&overlay.committed.top),
			vec![
				(vec![1], OverlayedValue { value: Some(vec![6]), extrinsics: Some(vec![0, 2].into_iter().collect()) }),
				(vec![3], OverlayedValue { value: Some(vec![4]), extrinsics: Some(vec![1].into_iter().collect()) }),
				(vec![100], OverlayedValue { value: Some(vec![101]), extrinsics: Some(vec![NO_EXTRINSIC_INDEX].into_iter().collect()) }),
			].into_iter().collect());

		assert_eq!(strip_extrinsic_index(&overlay.prospective.top),
			vec![
				(vec![1], OverlayedValue { value: Some(vec![8]), extrinsics: Some(vec![4].into_iter().collect()) }),
				(vec![3], OverlayedValue { value: Some(vec![7]), extrinsics: Some(vec![3].into_iter().collect()) }),
			].into_iter().collect());

		overlay.commit_prospective();

		assert_eq!(strip_extrinsic_index(&overlay.committed.top),
			vec![
				(vec![1], OverlayedValue { value: Some(vec![8]), extrinsics: Some(vec![0, 2, 4].into_iter().collect()) }),
				(vec![3], OverlayedValue { value: Some(vec![7]), extrinsics: Some(vec![1, 3].into_iter().collect()) }),
				(vec![100], OverlayedValue { value: Some(vec![101]), extrinsics: Some(vec![NO_EXTRINSIC_INDEX].into_iter().collect()) }),
			].into_iter().collect());

		assert_eq!(overlay.prospective,
			Default::default());
	}
}
