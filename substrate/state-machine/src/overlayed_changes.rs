// Copyright 2017 Parity Technologies (UK) Ltd.
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

use std::collections::{HashMap, HashSet};
use changes_trie::Configuration as ChangesTrieConfig;

/// The overlayed changes to state to be queried on top of the backend.
///
/// A transaction shares all prospective changes within an inner overlay
/// that can be cleared.
#[derive(Debug, Default, Clone)]
pub struct OverlayedChanges {
	pub(crate) prospective: HashMap<Vec<u8>, Option<Vec<u8>>>,
	pub(crate) committed: HashMap<Vec<u8>, Option<Vec<u8>>>,
	pub(crate) extrinsic_changes: Option<ExtrinsicChanges>,
}

/// Extrinsic-level map of storage changes at given block.
///
/// Used by runtimes that are maintaining change tries.
#[derive(Debug, Clone)]
pub(crate) struct ExtrinsicChanges {
	/// Configuration of changes trie.
	pub changes_trie_config: ChangesTrieConfig,
	/// Block number that is currently processing.
	pub block: u64,
	/// Extrinsic index that is currently processing.
	pub extrinsic_index: u32,
	/// Prospective mapping of storage keys to the indices of extrinsics
	/// where keys were changed in.
	pub prospective: HashMap<Vec<u8>, HashSet<u32>>,
	/// Committed mapping of storage keys to the indices of extrinsics
	/// where keys were changed in.
	pub committed: HashMap<Vec<u8>, HashSet<u32>>,
}

impl OverlayedChanges {
	/// Sets the changes trie configuration.
	pub(crate) fn set_changes_trie_config(&mut self, block: u64, config: ChangesTrieConfig) {
		assert!(match self.extrinsic_changes {
			None => true,
			Some(ref old_changes) => old_changes.block == block
				&& old_changes.changes_trie_config == config,
		});

		if self.extrinsic_changes.is_none() {
			self.extrinsic_changes = Some(ExtrinsicChanges {
				changes_trie_config: config,
				block,
				extrinsic_index: Default::default(),
				prospective: Default::default(),
				committed: Default::default(),
			})
		}
	}

	/// Sets the index extrinsic that is currently executing.
	pub(crate) fn set_extrinsic_index(&mut self, index: u32) {
		if let Some(extrinsic_changes) = self.extrinsic_changes.as_mut() {
			extrinsic_changes.extrinsic_index = index;
		}
	}

	/// Returns a double-Option: None if the key is unknown (i.e. and the query should be refered
	/// to the backend); Some(None) if the key has been deleted. Some(Some(...)) for a key whose
	/// value has been set.
	pub fn storage(&self, key: &[u8]) -> Option<Option<&[u8]>> {
		self.prospective.get(key)
			.or_else(|| self.committed.get(key))
			.map(|x| x.as_ref().map(AsRef::as_ref))
	}

	/// Inserts the given key-value pair into the prospective change set.
	///
	/// `None` can be used to delete a value specified by the given key.
	pub(crate) fn set_storage(&mut self, key: Vec<u8>, val: Option<Vec<u8>>) {
		self.extrinsic_changes.as_mut().map(|ec| ec.note_changed_key(key.clone()));
		self.prospective.insert(key, val);
	}

	/// Removes all key-value pairs which keys share the given prefix.
	///
	/// NOTE that this doesn't take place immediately but written into the prospective
	/// change set, and still can be reverted by [`discard_prospective`].
	///
	/// [`discard_prospective`]: #method.discard_prospective
	pub(crate) fn clear_prefix(&mut self, prefix: &[u8]) {
		// Iterate over all prospective and mark all keys that share
		// the given prefix as removed (None).
		for (key, value) in self.prospective.iter_mut() {
			if key.starts_with(prefix) {
				self.extrinsic_changes.as_mut().map(|ec| ec.note_changed_key(key.clone()));
				*value = None;
			}
		}

		// Then do the same with keys from commited changes.
		// NOTE that we are making changes in the prospective change set.
		for key in self.committed.keys() {
			if key.starts_with(prefix) {
				self.extrinsic_changes.as_mut().map(|ec| ec.note_changed_key(key.clone()));
				self.prospective.insert(key.to_owned(), None);
			}
		}
	}

	/// Discard prospective changes to state.
	pub fn discard_prospective(&mut self) {
		self.prospective.clear();
		self.extrinsic_changes.as_mut().map(|ec| ec.discard_prospective());
	}

	/// Commit prospective changes to state.
	pub fn commit_prospective(&mut self) {
		if self.committed.is_empty() {
			::std::mem::swap(&mut self.prospective, &mut self.committed);
		} else {
			self.committed.extend(self.prospective.drain());
		}

		self.extrinsic_changes.as_mut().map(|ec| ec.commit_prospective());
	}

	/// Drain committed changes to an iterator.
	///
	/// Panics:
	/// Will panic if there are any uncommitted prospective changes.
	pub fn drain<'a>(&'a mut self) -> impl Iterator<Item=(Vec<u8>, Option<Vec<u8>>)> + 'a {
		assert!(self.prospective.is_empty());
		self.committed.drain()
	}

	/// Consume `OverlayedChanges` and take committed set.
	///
	/// Panics:
	/// Will panic if there are any uncommitted prospective changes.
	pub fn into_committed(self) -> impl Iterator<Item=(Vec<u8>, Option<Vec<u8>>)> {
		assert!(self.prospective.is_empty());
		self.committed.into_iter()
	}
}

impl ExtrinsicChanges {
	/// Note key changed in the block.
	pub fn note_changed_key(&mut self, key: Vec<u8>) {
		self.prospective.entry(key).or_default()
			.insert(self.extrinsic_index);
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
			for (key, extrinsics) in self.prospective.drain() {
				self.committed.entry(key.clone()).or_default()
					.extend(extrinsics);
			}
		}
	}
}

#[cfg(test)]
mod tests {
	use primitives::{KeccakHasher, RlpCodec, H256};
	use backend::InMemory;
	use changes_trie::InMemoryStorage as InMemoryChangesTrieStorage;
	use ext::Ext;
	use {Externalities};
	use super::*;

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
		let initial: HashMap<_, _> = vec![
			(b"doe".to_vec(), b"reindeer".to_vec()),
			(b"dog".to_vec(), b"puppyXXX".to_vec()),
			(b"dogglesworth".to_vec(), b"catXXX".to_vec()),
			(b"doug".to_vec(), b"notadog".to_vec()),
		].into_iter().collect();
		let backend = InMemory::<KeccakHasher, RlpCodec>::from(initial);
		let mut overlay = OverlayedChanges {
			committed: vec![
				(b"dog".to_vec(), Some(b"puppy".to_vec())),
				(b"dogglesworth".to_vec(), Some(b"catYYY".to_vec())),
				(b"doug".to_vec(), Some(vec![])),
			].into_iter().collect(),
			prospective: vec![
				(b"dogglesworth".to_vec(), Some(b"cat".to_vec())),
				(b"doug".to_vec(), None),
			].into_iter().collect(),
			..Default::default()
		};

		let changes_trie_storage = InMemoryChangesTrieStorage::new();
		let mut ext = Ext::new(&mut overlay, &backend, Some(&changes_trie_storage));
		const ROOT: [u8; 32] = hex!("8aad789dff2f538bca5d8ea56e8abe10f4c7ba3a5dea95fea4cd6e7c3a1168d3");
		assert_eq!(ext.storage_root(), H256(ROOT));
	}

	#[test]
	fn changes_trie_configuration_is_saved() {
		let mut overlay = OverlayedChanges::default();
		assert!(overlay.extrinsic_changes.is_none());
		overlay.set_changes_trie_config(1, ChangesTrieConfig {
			digest_interval: 4, digest_levels: 1,
		});
		assert!(overlay.extrinsic_changes.is_some());
	}

	#[test]
	fn changes_trie_configuration_is_saved_twice() {
		let mut overlay = OverlayedChanges::default();
		assert!(overlay.extrinsic_changes.is_none());
		overlay.set_changes_trie_config(1, ChangesTrieConfig {
			digest_interval: 4, digest_levels: 1,
		});
		overlay.set_extrinsic_index(0);
		overlay.set_storage(vec![1], Some(vec![2]));
		overlay.set_changes_trie_config(1, ChangesTrieConfig {
			digest_interval: 4, digest_levels: 1,
		});
		assert_eq!(
			overlay.extrinsic_changes.as_ref().map(|c| c.prospective.clone()),
			Some(vec![
				(vec![1], vec![0].into_iter().collect()),
			].into_iter().collect())
		);
	}

	#[test]
	#[should_panic]
	fn panics_when_trying_to_save_different_changes_trie_configuration() {
		let mut overlay = OverlayedChanges::default();
		overlay.set_changes_trie_config(1, ChangesTrieConfig {
			digest_interval: 4, digest_levels: 1,
		});
		overlay.set_changes_trie_config(1, ChangesTrieConfig {
			digest_interval: 2, digest_levels: 1,
		});
	}

	#[test]
	#[should_panic]
	fn panics_when_trying_to_save_changes_trie_configuration_of_different_block() {
		let mut overlay = OverlayedChanges::default();
		overlay.set_changes_trie_config(1, ChangesTrieConfig {
			digest_interval: 4, digest_levels: 1,
		});
		overlay.set_changes_trie_config(2, ChangesTrieConfig {
			digest_interval: 4, digest_levels: 1,
		});
	}

	#[test]
	fn extrinsic_changes_are_collected() {
		let mut overlay = OverlayedChanges::default();
		assert!(overlay.extrinsic_changes.is_none());
		overlay.set_changes_trie_config(1, ChangesTrieConfig {
			digest_interval: 4, digest_levels: 1,
		});

		overlay.set_extrinsic_index(0);
		overlay.set_storage(vec![1], Some(vec![2]));

		overlay.set_extrinsic_index(1);
		overlay.set_storage(vec![3], Some(vec![4]));

		overlay.set_extrinsic_index(2);
		overlay.set_storage(vec![1], Some(vec![6]));

		assert_eq!(overlay.extrinsic_changes.as_ref().unwrap().prospective,
			vec![
				(vec![1], vec![0, 2].into_iter().collect()),
				(vec![3], vec![1].into_iter().collect()),
			].into_iter().collect());

		overlay.commit_prospective();

		overlay.set_extrinsic_index(3);
		overlay.set_storage(vec![3], Some(vec![7]));

		overlay.set_extrinsic_index(4);
		overlay.set_storage(vec![1], Some(vec![8]));

		assert_eq!(overlay.extrinsic_changes.as_ref().unwrap().committed,
			vec![
				(vec![1], vec![0, 2].into_iter().collect()),
				(vec![3], vec![1].into_iter().collect()),
			].into_iter().collect());

		assert_eq!(overlay.extrinsic_changes.as_ref().unwrap().prospective,
			vec![
				(vec![1], vec![4].into_iter().collect()),
				(vec![3], vec![3].into_iter().collect()),
			].into_iter().collect());

		overlay.commit_prospective();

		assert_eq!(overlay.extrinsic_changes.as_ref().unwrap().committed,
			vec![
				(vec![1], vec![0, 2, 4].into_iter().collect()),
				(vec![3], vec![1, 3].into_iter().collect()),
			].into_iter().collect());

		assert_eq!(overlay.extrinsic_changes.as_ref().unwrap().prospective,
			Default::default());
	}
}
