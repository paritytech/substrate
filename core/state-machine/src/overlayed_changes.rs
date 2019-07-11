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
use std::collections::{HashMap, HashSet};
use parity_codec::Decode;
use crate::changes_trie::{NO_EXTRINSIC_INDEX, Configuration as ChangesTrieConfig};
use primitives::storage::well_known_keys::EXTRINSIC_INDEX;

#[derive(Debug, Clone)]
#[cfg_attr(test, derive(PartialEq))]
/// State of a transaction, the state are stored
/// and updated in a linear indexed way.
pub(crate) enum TransactionState {
	/// Overlay is under change.
	/// Is not necessarilly the last change.
	/// Contains an index to commit position
	Pending,
	/// Information is committed, but can still be dropped.
	Prospective,
	/// Committed is information that cannot
	/// be dropped.
	Committed,
	/// Transaction or prospective has been dropped.
	Dropped,
}

/// The overlayed changes to state to be queried on top of the backend.
///
/// A transaction shares all prospective changes within an inner overlay
/// that can be cleared.
#[derive(Debug, Default, Clone)]
pub struct OverlayedChanges {
//	/// History current position.
//	pub(crate) current: usize, -> end of history vec
	/// Changes with their history.
	pub(crate) changes: OverlayedChangeSet,
	/// Changes trie configuration. None by default, but could be installed by the
	/// runtime if it supports change tries.
	pub(crate) changes_trie_config: Option<ChangesTrieConfig>,
}

/// The storage value, used inside OverlayedChanges.
#[derive(Debug, Default, Clone)]
#[cfg_attr(test, derive(PartialEq))]
pub struct OverlayedValue {
	/// Values change historic with history state index.
	pub value: Option<Vec<u8>>,
	/// The set of extinsic indices where the values has been changed.
	/// Same history system as value (but over .
	pub extrinsics: Option<HashSet<u32>>,
}

// TODO EMCH implement debug with latest vals only (at overlay changeset maybe).
// this is pub crate for direct building in test (same with fields) -> TODO
// make fields private and have a build method and make history private?.
#[derive(Debug, Default, Clone)]
#[cfg_attr(test, derive(PartialEq))]
pub(crate) struct History<V>(pub Vec<(V, usize)>);

/// Overlayed change set, keep history of value.
#[derive(Debug, Clone)]
#[cfg_attr(test, derive(PartialEq))]
pub struct OverlayedChangeSet {
	/// Indexed changes history.
	/// First index is initial state,
	/// operation such as `init_transaction`,
	/// `commit_transaction` or `drop_transaction`
	/// will change this state.
	pub(crate) history: Vec<TransactionState>,
  /// Current state in history.
	pub(crate) state: usize,
	/// Top level storage changes.
	pub(crate) top: HashMap<Vec<u8>, History<OverlayedValue>>,
	/// Child storage changes.
	pub(crate) children: HashMap<Vec<u8>, (HashMap<Vec<u8>, History<OverlayedValue>>)>,
}

impl Default for OverlayedChangeSet {
	fn default() -> Self {
		OverlayedChangeSet {
			history: vec![TransactionState::Pending],
			state: 0,
			top: Default::default(),
			children: Default::default(),
		}
	}
}

#[cfg(test)]
impl FromIterator<(Vec<u8>, OverlayedValue)> for OverlayedChangeSet {
	fn from_iter<T: IntoIterator<Item = (Vec<u8>, OverlayedValue)>>(iter: T) -> Self {

    let mut result = OverlayedChangeSet::default();
		result.top = iter.into_iter().map(|(k, v)| (k, History(vec![(v, 0)]))).collect();
    result
	}
}

impl<V> History<V> {
	// TODO could have gc on get here we got some iteration that
	// do not need to be repeated when tx dropped (history only
	// updated on set).
	fn get(&self, history: &[TransactionState]) -> Option<&V> {
		// ix is never 0, 
		let mut ix = self.0.len();
		if ix == 0 {
			return None;
		}
		// internal method: should be use properly
		// (history of the right overlay change set
		// is size aligned).
		debug_assert!(history.len() >= ix); 
		while ix > 0 {
			ix -= 1;
			let hix = self.0[ix].1;
			match history[hix] {
				TransactionState::Pending
				| TransactionState::Prospective
				| TransactionState::Committed =>
					return Some(&self.0[ix].0),
				TransactionState::Dropped => (), 
			}
		}
		None
	}

	#[cfg(test)]
	fn get_prospective(&self, history: &[TransactionState]) -> Option<&V> {
		// ix is never 0, 
		let mut ix = self.0.len();
		if ix == 0 {
			return None;
		}
		debug_assert!(history.len() >= ix); 
		while ix > 0 {
			ix -= 1;
			let hix = self.0[ix].1;
			match history[hix] {
				TransactionState::Pending
				| TransactionState::Prospective =>
					return Some(&self.0[ix].0),
				TransactionState::Committed
				| TransactionState::Dropped => (), 
			}
		}
		None
	}

	#[cfg(test)]
	fn get_committed(&self, history: &[TransactionState]) -> Option<&V> {
		// ix is never 0, 
		let mut ix = self.0.len();
		if ix == 0 {
			return None;
		}
		debug_assert!(history.len() >= ix); 
		while ix > 0 {
			ix -= 1;
			let hix = self.0[ix].1;
			match history[hix] {
				TransactionState::Committed =>
					return Some(&self.0[ix].0),
				TransactionState::Pending
				| TransactionState::Prospective
				| TransactionState::Dropped => (), 
			}
		}
		None
	}



	fn into_committed(mut self, history: &[TransactionState]) -> Option<V> {
		// ix is never 0, 
		let mut ix = self.0.len();
		if ix == 0 {
			return None;
		}
		// internal method: should be use properly
		// (history of the right overlay change set
		// is size aligned).
		debug_assert!(history.len() >= ix); 
		while ix > 0 {
			ix -= 1;
			let hix = self.0[ix].1;
			match history[hix] {
				TransactionState::Committed => {
					self.0.truncate(ix + 1);
					return self.0.pop().map(|v| v.0);
				},
				TransactionState::Pending
				| TransactionState::Prospective
				| TransactionState::Dropped => (), 
			}
		}
		None
	}

	fn get_mut(&mut self, history: &[TransactionState]) -> Option<(&mut V, usize)> {

		let mut ix = self.0.len();
		if ix == 0 {
			return None;
		}
		// internal method: should be use properly
		// (history of the right overlay change set
		// is size aligned).
		debug_assert!(history.len() >= ix); 
		while ix > 0 {
			ix -= 1;
			let hix = self.0[ix].1;
			match history[hix] {
				TransactionState::Pending
				| TransactionState::Prospective => {
					let tx = self.0[ix].1;
					return Some((&mut self.0[ix].0, tx))
				},
				| TransactionState::Committed => {
					// No need for previous state
					if ix > 0 {
						self.0.truncate(ix + 1);
						let tv = self.0.pop().expect("just checked");
						self.0[0] = tv;
						self.0.truncate(1);
					}
					let tx = self.0[0].1;
					return Some((&mut self.0[0].0, tx))
				},
				TransactionState::Dropped => { let _ = self.0.pop(); },
			}
		}
		None
	}

	// should only be call after a get_mut check
	fn push(&mut self, val:V, tx_ix: usize) {
		self.0.push((val, tx_ix))
	}

	fn set(&mut self, history: &[TransactionState], state: usize, val: V) {
    	// TODO EMCH : this is not optimal : can end get_mut as soon as ix < state
    	// needs a variant for get_mut.
		match self.get_mut(history) {
			Some((v, ix)) => {
				if ix == state {
					*v = val;
					return;
				}
			},
			None => (),
		}
		self.push(val, history.len() - 1);
	}

}

impl History<OverlayedValue> {
	fn set_ext(&mut self, history: &[TransactionState], state: usize, val: Option<Vec<u8>>, extrinsic_index: Option<u32>) {
		if let Some((mut current, c_ix)) = self.get_mut(history) {

				if c_ix == state {
					current.value = val;
					if let Some(extrinsic) = extrinsic_index {
						current.extrinsics.get_or_insert_with(Default::default)
							.insert(extrinsic);
					}

				} else {
					let mut extrinsics = current.extrinsics.clone();
					extrinsic_index.map(|extrinsic| extrinsics.get_or_insert_with(Default::default)
						.insert(extrinsic));
					self.push(OverlayedValue {
						value: val,
						extrinsics,
					}, state);
				}
			} else {
				let mut extrinsics: Option<HashSet<u32>> = None;
				 extrinsic_index.map(|extrinsic| extrinsics.get_or_insert_with(Default::default)
						.insert(extrinsic));

				self.push(OverlayedValue {
					 value: val,
					 extrinsics,
				 }, state);
 
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
		self.history = vec![TransactionState::Pending];
		self.state = 0;
		self.top.clear();
		self.children.clear();
	}

	/// Discard prospective changes to state.
	pub fn discard_prospective(&mut self) {
		let mut i = self.state + 1;
		while i > 0 {
			i -= 1;
			match self.history[i] {
				TransactionState::Pending
				| TransactionState::Prospective => self.history[i] = TransactionState::Dropped,
				// can have dropped from transaction -> TODO make Dropped perspective variant? = earliest
				// stop in some case
				TransactionState::Dropped => (),
				TransactionState::Committed => break,
			}
		}
		self.history.push(TransactionState::Pending);
		self.state = self.history.len() - 1;
  }

	/// Commit prospective changes to state.
	pub fn commit_prospective(&mut self) {
		debug_assert!(self.history.len() > 0);
		// TODO EMCH can use offset and a GC state
		self.history[self.state] = TransactionState::Committed;
		self.history.push(TransactionState::Pending);
		self.state = self.history.len() - 1;
	}

	/// Iterator over current state of the overlay.
	pub fn top_iter_ext(&self) -> impl Iterator<Item = (&Vec<u8>, &OverlayedValue)> {
		self.top.iter()
			.filter_map(move |(k, v)|
				v.get(self.history.as_slice()).map(|v| (k, v)))
	}


	/// Iterator over current state of the overlay.
	pub fn top_iter(&self) -> impl Iterator<Item = (&Vec<u8>, Option<&Vec<u8>>)> {
		self.top_iter_ext().map(|(k, v)| (k, v.value.as_ref()))
	}

	/// Iterator over current state of the overlay.
	pub fn child_iter_ext(
		&self,
		storage_key: &[u8],
	) -> impl Iterator<Item = (&Vec<u8>, &OverlayedValue)> {
		self.children.get(storage_key)
			.into_iter()
			.flat_map(move |child| child.iter()
				.filter_map(move |(k, v)|
					v.get(self.history.as_slice()).map(|v| (k, v)))
			)
	}

	/// Iterator over current state of the overlay.
	pub fn child_iter(&self, storage_key: &[u8]) -> impl Iterator<Item = (&Vec<u8>, Option<&Vec<u8>>)> {
		self.child_iter_ext(storage_key).map(|(k, v)| (k, v.value.as_ref()))
	}

	/// Test only method to access current prospective changes.
	/// It is here to keep old test compatibility and should be
	/// avoid for new tests.
	#[cfg(test)]
	pub(crate) fn top_prospective(&self) -> HashMap<Vec<u8>, OverlayedValue> {
		let mut result = HashMap::new();
		for (k, v) in self.top.iter() {
			if let Some(v) = v.get_prospective(self.history.as_slice()) {
				result.insert(k.clone(), v.clone());
			}
		}
		result
	}
	/// Test only method to access current commited changes.
	/// It is here to keep old test compatibility and should be
	/// avoid for new tests.
	#[cfg(test)]
	pub(crate) fn top_committed(&self) -> HashMap<Vec<u8>, OverlayedValue> {
		let mut result = HashMap::new();
		for (k, v) in self.top.iter() {
			if let Some(v) = v.get_committed(self.history.as_slice()) {
				result.insert(k.clone(), v.clone());
			}
		}
		result
	}

}

impl OverlayedChanges {
	/// Whether the overlayed changes are empty.
	pub fn is_empty(&self) -> bool {
		self.changes.is_empty()
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
	/// To make some non followed change
	#[cfg(test)]
	pub(crate) fn remove_changes_trie_config(&mut self) -> Option<ChangesTrieConfig> {
		self.changes_trie_config.take()
	}


	/// Returns a double-Option: None if the key is unknown (i.e. and the query should be refered
	/// to the backend); Some(None) if the key has been deleted. Some(Some(...)) for a key whose
	/// value has been set.
	pub fn storage(&self, key: &[u8]) -> Option<Option<&[u8]>> {
		if let Some(overlay_val) = self.changes.top.get(key) {
			if let Some(o_val) = overlay_val.get(self.changes.history.as_slice()) {
				return Some(o_val.value.as_ref().map(|v| v.as_slice()))
			}
		}
		None
	}

	/// Returns a double-Option: None if the key is unknown (i.e. and the query should be refered
	/// to the backend); Some(None) if the key has been deleted. Some(Some(...)) for a key whose
	/// value has been set.
	pub fn child_storage(&self, storage_key: &[u8], key: &[u8]) -> Option<Option<&[u8]>> {
		if let Some(map) = self.changes.children.get(storage_key) {
			if let Some(overlay_val) = map.get(key) {
				if let Some(o_val) = overlay_val.get(self.changes.history.as_slice()) {
					return Some(o_val.value.as_ref().map(|v| v.as_slice()))
				}
			}
		}
		None
	}

	/// Inserts the given key-value pair into the prospective change set.
	///
	/// `None` can be used to delete a value specified by the given key.
	pub(crate) fn set_storage(&mut self, key: Vec<u8>, val: Option<Vec<u8>>) {
		let extrinsic_index = self.extrinsic_index();
		let entry = self.changes.top.entry(key).or_default();
		entry.set_ext(self.changes.history.as_slice(), self.changes.state, val, extrinsic_index);
	}

	/// Inserts the given key-value pair into the prospective child change set.
	///
	/// `None` can be used to delete a value specified by the given key.
	pub(crate) fn set_child_storage(&mut self, storage_key: Vec<u8>, key: Vec<u8>, val: Option<Vec<u8>>) {
		let extrinsic_index = self.extrinsic_index();
		let map_entry = self.changes.children.entry(storage_key).or_default();
		let entry = map_entry.entry(key).or_default();
		entry.set_ext(self.changes.history.as_slice(), self.changes.state, val, extrinsic_index);
	}

	/// Clear child storage of given storage key.
	///
	/// NOTE that this doesn't take place immediately but written into the prospective
	/// change set, and still can be reverted by [`discard_prospective`].
	///
	/// [`discard_prospective`]: #method.discard_prospective
	pub(crate) fn clear_child_storage(&mut self, storage_key: &[u8]) {
		let extrinsic_index = self.extrinsic_index();
		let history = self.changes.history.as_slice();
		let state = self.changes.state;
		let map_entry = self.changes.children.entry(storage_key.to_vec()).or_default();

		map_entry.values_mut().for_each(|e| e.set_ext(history, state, None, extrinsic_index));
	}

	/// Removes all key-value pairs which keys share the given prefix.
	///
	/// NOTE that this doesn't take place immediately but written into the prospective
	/// change set, and still can be reverted by [`discard_prospective`].
	///
	/// [`discard_prospective`]: #method.discard_prospective
	pub(crate) fn clear_prefix(&mut self, prefix: &[u8]) {
		let extrinsic_index = self.extrinsic_index();

		for (key, entry) in self.changes.top.iter_mut() {
			if key.starts_with(prefix) {
				entry.set_ext(self.changes.history.as_slice(), self.changes.state, None, extrinsic_index);
			}
		}
	}

	/// Discard prospective changes to state.
	pub fn discard_prospective(&mut self) {
		self.changes.discard_prospective();
	}

	/// Commit prospective changes to state.
	pub fn commit_prospective(&mut self) {
		self.changes.commit_prospective();
	}

	/// Consume `OverlayedChanges` and take committed set.
	///
	/// Panics:
	/// Will panic if there are any uncommitted prospective changes.
	pub fn into_committed(self) -> (
		impl Iterator<Item=(Vec<u8>, Option<Vec<u8>>)>,
		impl Iterator<Item=(Vec<u8>, impl Iterator<Item=(Vec<u8>, Option<Vec<u8>>)>)>,
	){
		let top = self.changes.top;
		let children = self.changes.children;
		let history = self.changes.history.clone();
		let history2 = self.changes.history;
		(
			top.into_iter()
				.filter_map(move |(k, v)| v.into_committed(history.as_slice()).map(|v| (k, v.value))),
			children.into_iter().map(move |(sk, v)| {
				let historys = history2.clone();
				(sk, v.into_iter()
					.filter_map(move |(k, v)| v.into_committed(historys.as_slice()).map(|v| (k, v.value))))
			})
		)
	}

	/// Inserts storage entry responsible for current extrinsic index.
	#[cfg(test)]
	pub(crate) fn set_extrinsic_index(&mut self, extrinsic_index: u32) {
		use parity_codec::Encode;
	
		let value = extrinsic_index.encode();
		let entry = self.changes.top.entry(EXTRINSIC_INDEX.to_vec()).or_default();
		entry.set_ext(self.changes.history.as_slice(), self.changes.state, Some(value), None);
	}

	/// Test only method to build from committed info and prospective.
	/// Create an history of two states.
	#[cfg(test)]
	pub(crate) fn new_from_top(
		committed: Vec<(Vec<u8>, Option<Vec<u8>>)>,
		prospective: Vec<(Vec<u8>, Option<Vec<u8>>)>,
	) -> Self {
    let mut changes = OverlayedChangeSet::default();
		changes.top = committed.into_iter().map(|(k, v)|
			(k, History(vec![(OverlayedValue { value: v, extrinsics: None }, 0)]))).collect();
		changes.commit_prospective();
		let mut result = OverlayedChanges { changes, changes_trie_config: None };
		prospective.into_iter().for_each(|(k, v)| result.set_storage(k, v));
		result
	}
	/// Test only method to build from committed info and prospective.
	/// Create an history of two states.
	/// TODO EMCH replace prev fn with this one.
	#[cfg(test)]
	pub(crate) fn new_from_top_changes(
		committed: Vec<(Vec<u8>, Option<Vec<u8>>)>,
		prospective: Vec<(Vec<u8>, Option<Vec<u8>>)>,
		changes_trie_config: Option<ChangesTrieConfig>,
	) -> Self {
		let mut changes = OverlayedChangeSet::default();
		let mut result = OverlayedChanges { changes, changes_trie_config };
		committed.into_iter().for_each(|(k, v)| result.set_storage(k, v));
		result.changes.commit_prospective();
		prospective.into_iter().for_each(|(k, v)| result.set_storage(k, v));
		result
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
					.and_then(|idx| idx.and_then(|idx| Decode::decode(&mut &*idx)))
					.unwrap_or(NO_EXTRINSIC_INDEX)),
			false => None,
		}
	}
}

#[cfg(feature = "bench")]
/// Expose private function of overlay for benching.
pub struct BenchOverlay<'a>(pub &'a mut OverlayedChanges);


#[cfg(feature = "bench")]
impl<'a> BenchOverlay<'a> {
	pub fn bench_set_storage(&mut self, key: Vec<u8>, val: Option<Vec<u8>>) {
		self.0.set_storage(key, val)
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

	fn strip_extrinsic_index(mut map: HashMap<Vec<u8>, OverlayedValue>) -> HashMap<Vec<u8>, OverlayedValue> {
		map.remove(&EXTRINSIC_INDEX.to_vec());
		map
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
		let initial: HashMap<_, _> = vec![
			(b"doe".to_vec(), b"reindeer".to_vec()),
			(b"dog".to_vec(), b"puppyXXX".to_vec()),
			(b"dogglesworth".to_vec(), b"catXXX".to_vec()),
			(b"doug".to_vec(), b"notadog".to_vec()),
		].into_iter().collect();
		let backend = InMemory::<Blake2Hasher>::from(initial);
		let mut overlay = OverlayedChanges::new_from_top(
			vec![
				(b"dog".to_vec(), Some(b"puppy".to_vec()).into()),
				(b"dogglesworth".to_vec(), Some(b"catYYY".to_vec()).into()),
				(b"doug".to_vec(), Some(vec![]).into()),
			].into_iter().collect(),
			vec![
				(b"dogglesworth".to_vec(), Some(b"cat".to_vec()).into()),
				(b"doug".to_vec(), None.into()),
			].into_iter().collect());

		let changes_trie_storage = InMemoryChangesTrieStorage::<Blake2Hasher, u64>::new();
		let mut ext = Ext::new(
			&mut overlay,
			&backend,
			Some(&changes_trie_storage),
			crate::NeverOffchainExt::new(),
		);
		const ROOT: [u8; 32] = hex!("0b41e488cccbd67d1f1089592c2c235f5c5399b053f7fe9152dd4b5f279914cd");
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
			strip_extrinsic_index(overlay.changes.top_prospective()),
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

		assert_eq!(strip_extrinsic_index(overlay.changes.top_prospective()),
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

		assert_eq!(strip_extrinsic_index(overlay.changes.top_committed()),
			vec![
				(vec![1], OverlayedValue { value: Some(vec![6]), extrinsics: Some(vec![0, 2].into_iter().collect()) }),
				(vec![3], OverlayedValue { value: Some(vec![4]), extrinsics: Some(vec![1].into_iter().collect()) }),
				(vec![100], OverlayedValue { value: Some(vec![101]), extrinsics: Some(vec![NO_EXTRINSIC_INDEX].into_iter().collect()) }),
			].into_iter().collect());

		assert_eq!(strip_extrinsic_index(overlay.changes.top_prospective()),
			vec![
				(vec![1], OverlayedValue { value: Some(vec![8]), extrinsics: Some(vec![0, 2, 4].into_iter().collect()) }),
				(vec![3], OverlayedValue { value: Some(vec![7]), extrinsics: Some(vec![1, 3].into_iter().collect()) }),
			].into_iter().collect());

		overlay.commit_prospective();

		assert_eq!(strip_extrinsic_index(overlay.changes.top_committed()),
			vec![
				(vec![1], OverlayedValue { value: Some(vec![8]), extrinsics: Some(vec![0, 2, 4].into_iter().collect()) }),
				(vec![3], OverlayedValue { value: Some(vec![7]), extrinsics: Some(vec![1, 3].into_iter().collect()) }),
				(vec![100], OverlayedValue { value: Some(vec![101]), extrinsics: Some(vec![NO_EXTRINSIC_INDEX].into_iter().collect()) }),
			].into_iter().collect());

		assert_eq!(overlay.changes.top_prospective(),
			Default::default());
	}
}
