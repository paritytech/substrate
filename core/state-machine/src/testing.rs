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

//! Test implementation for Externalities.

use std::collections::{HashMap};
use std::iter::FromIterator;
use hash_db::Hasher;
use crate::backend::{InMemory, Backend, MapTransaction};
use primitives::storage::well_known_keys::is_child_storage_key;
use crate::changes_trie::{
	build_changes_trie, InMemoryStorage as ChangesTrieInMemoryStorage,
	BlockNumber as ChangesTrieBlockNumber,
};
use primitives::offchain;
use primitives::storage::well_known_keys::{CHANGES_TRIE_CONFIG, CODE, HEAP_PAGES};
use primitives::child_trie::{ChildTrie, ChildTrieReadRef};
use parity_codec::Encode;
use super::{Externalities, OverlayedChanges, OverlayedValueResult};

const EXT_NOT_ALLOWED_TO_FAIL: &str = "Externalities not allowed to fail within runtime";

type StorageTuple = MapTransaction;

/// Simple HashMap-based Externalities impl.
pub struct TestExternalities<H: Hasher, N: ChangesTrieBlockNumber> {
	overlay: OverlayedChanges,
	backend: InMemory<H>,
	changes_trie_storage: ChangesTrieInMemoryStorage<H, N>,
	offchain: Option<Box<dyn offchain::Externalities>>,
}

impl<H: Hasher, N: ChangesTrieBlockNumber> TestExternalities<H, N> {
	/// Create a new instance of `TestExternalities` with storage.
	pub fn new(storage: HashMap<Vec<u8>, Vec<u8>>) -> Self {
		Self::new_with_children(MapTransaction{ top: storage, children: Default::default() })
	}

	/// Create a new instance of `TestExternalities` with storage and children.
	pub fn new_with_children(storage: StorageTuple) -> Self {
		Self::new_with_code_with_children(&[], storage)
	}

	/// Create a new instance of `TestExternalities` with code and storage.
	pub fn new_with_code(code: &[u8], storage: HashMap<Vec<u8>, Vec<u8>>) -> Self {
		Self::new_with_code_with_children(
			code,
			MapTransaction{ top: storage, children: Default::default() },
		)
	}

	/// Create a new instance of `TestExternalities` with code, storage and children.
	pub fn new_with_code_with_children(code: &[u8], mut storage: StorageTuple) -> Self {
		let mut overlay = OverlayedChanges::default();

		assert!(storage.top.keys().all(|key| !is_child_storage_key(key)));
		assert!(storage.children.keys().all(|key| is_child_storage_key(key)));

		super::set_changes_trie_config(
			&mut overlay,
			storage.top.get(&CHANGES_TRIE_CONFIG.to_vec()).cloned(),
			false,
		).expect("changes trie configuration is correct in test env; qed");

		storage.top.insert(HEAP_PAGES.to_vec(), 8u64.encode());
		storage.top.insert(CODE.to_vec(), code.to_vec());

		TestExternalities {
			overlay,
			changes_trie_storage: ChangesTrieInMemoryStorage::new(),
			backend: storage.into(),
			offchain: None,
		}
	}

	/// Insert key/value into backend
	pub fn insert(&mut self, k: Vec<u8>, v: Vec<u8>) {
		self.backend = self.backend.update(vec![(None, k, Some(v))]);
	}

	/// Set offchain externaltiies.
	pub fn set_offchain_externalities(&mut self, offchain: impl offchain::Externalities + 'static) {
		self.offchain = Some(Box::new(offchain));
	}

	/// Get mutable reference to changes trie storage.
	pub fn changes_trie_storage(&mut self) -> &mut ChangesTrieInMemoryStorage<H, N> {
		&mut self.changes_trie_storage
	}

	/// Return a new backend with all pending value.
	pub fn commit_all(&self) -> InMemory<H> {
		let top = self.overlay.committed.top.clone().into_iter()
			.chain(self.overlay.prospective.top.clone().into_iter())
			.map(|(k, v)| (None, k, v.value));

		let children = self.overlay.committed.children.clone().into_iter()
			.chain(self.overlay.prospective.children.clone().into_iter())
			.flat_map(|(_keyspace, changeset)| {
				let child_trie = changeset.child_trie;
				changeset.values.into_iter()
					.map(move |(k, v)| (Some(child_trie.clone()), k, v))
					.collect::<Vec<_>>()
			});

		self.backend.update(top.chain(children).collect())
	}
}

impl<H: Hasher, N: ChangesTrieBlockNumber> std::fmt::Debug for TestExternalities<H, N> {
	fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
		write!(f, "overlay: {:?}\nbackend: {:?}", self.overlay, self.backend.pairs())
	}
}

impl<H: Hasher, N: ChangesTrieBlockNumber> PartialEq for TestExternalities<H, N> {
	/// This doesn't test if they are in the same state, only if they contains the
	/// same data at this state
	fn eq(&self, other: &TestExternalities<H, N>) -> bool {
		self.commit_all().eq(&other.commit_all())
	}
}

impl<H: Hasher, N: ChangesTrieBlockNumber> FromIterator<(Vec<u8>, Vec<u8>)> for TestExternalities<H, N> {
	fn from_iter<I: IntoIterator<Item=(Vec<u8>, Vec<u8>)>>(iter: I) -> Self {
		Self::new(iter.into_iter().collect())
	}
}

impl<H: Hasher, N: ChangesTrieBlockNumber> Default for TestExternalities<H, N> {
	fn default() -> Self { Self::new(Default::default()) }
}

impl<H: Hasher, N: ChangesTrieBlockNumber> From<HashMap<Vec<u8>, Vec<u8>>> for TestExternalities<H, N> {
	fn from(hashmap: HashMap<Vec<u8>, Vec<u8>>) -> Self {
		Self::from_iter(hashmap)
	}
}

impl<H: Hasher, N: ChangesTrieBlockNumber> From<StorageTuple> for TestExternalities<H, N> {
	fn from(storage: StorageTuple) -> Self {
		Self::new_with_children(storage)
	}
}

impl<H, N> Externalities<H> for TestExternalities<H, N>
	where
		H: Hasher,
		N: ChangesTrieBlockNumber,
		H::Out: Ord + 'static
{
	fn storage(&self, key: &[u8]) -> Option<Vec<u8>> {
		match self.overlay.storage(key) {
			OverlayedValueResult::NotFound =>
				self.backend.storage(key).expect(EXT_NOT_ALLOWED_TO_FAIL),
			OverlayedValueResult::Deleted => None,
			OverlayedValueResult::Modified(value) => Some(value.to_vec()),
		}
	}

	fn original_storage(&self, key: &[u8]) -> Option<Vec<u8>> {
		self.backend.storage(key).expect(EXT_NOT_ALLOWED_TO_FAIL)
	}

	fn child_storage(&self, child_trie: ChildTrieReadRef, key: &[u8]) -> Option<Vec<u8>> {
		match self.overlay.child_storage(child_trie.clone(), key) {
			OverlayedValueResult::NotFound =>
				self.backend.child_storage(child_trie, key).expect(EXT_NOT_ALLOWED_TO_FAIL),
			OverlayedValueResult::Deleted => None,
			OverlayedValueResult::Modified(value) => Some( value.to_vec()),
		}
	}

	fn child_trie(&self, storage_key: &[u8]) -> Option<ChildTrie> {
		self.overlay.child_trie(storage_key).unwrap_or_else(||
			self.backend.child_trie(storage_key).expect(EXT_NOT_ALLOWED_TO_FAIL))
	}

	fn set_child_trie(&mut self, ct: ChildTrie) -> bool {
		// do check for backend
 		let ct = match self.child_trie(ct.parent_slice()) {
			Some(ct_old) => if ct_old.is_updatable_with(&ct) {
				ct
			} else {
				return false;
			},
			None => if ct.is_new() {
				ct
			} else {
				return false;
			},
		};
		self.overlay.set_child_trie(ct)
	}

	fn place_storage(&mut self, key: Vec<u8>, maybe_value: Option<Vec<u8>>) {
		if is_child_storage_key(&key) {
			panic!("Refuse to directly set child storage key");
		}

		self.overlay.set_storage(key, maybe_value);
	}

	fn place_child_storage(
		&mut self,
		child_trie: &ChildTrie,
		key: Vec<u8>,
		value: Option<Vec<u8>>
	) {
		self.overlay.set_child_storage(child_trie, key, value);
	}

	fn kill_child_storage(&mut self, child_trie: &ChildTrie) {
		let backend = &self.backend;
		let overlay = &mut self.overlay;

		overlay.clear_child_storage(child_trie);
		backend.for_keys_in_child_storage(child_trie.node_ref(), |key| {
			overlay.set_child_storage(child_trie, key.to_vec(), None);
		});
	}

	fn clear_prefix(&mut self, prefix: &[u8]) {
		if is_child_storage_key(prefix) {
			panic!("Refuse to directly clear prefix that is part of child storage key");
		}

		self.overlay.clear_prefix(prefix);

		let backend = &self.backend;
		let overlay = &mut self.overlay;
		backend.for_keys_with_prefix(prefix, |key| {
			overlay.set_storage(key.to_vec(), None);
		});
	}

	fn chain_id(&self) -> u64 { 42 }

	fn storage_root(&mut self) -> H::Out {
		let child_storage_tries =
			self.overlay.prospective.children.values()
				.chain(self.overlay.committed.children.values())
				.map(|v|&v.child_trie);

		let child_delta_iter = child_storage_tries.map(|child_trie| {
			let keyspace = child_trie.keyspace();
			let committed_iter = self.overlay.committed.children
				.get(keyspace).into_iter()
				.flat_map(|map| map.values.iter().map(|(k, v)| (k.clone(), v.clone())));
			let prospective_iter = self.overlay.prospective.children
				.get(keyspace).into_iter()
				.flat_map(|map| map.values.iter().map(|(k, v)| (k.clone(), v.clone())));

			(child_trie, committed_iter.chain(prospective_iter))
		});

		// compute and memoize
		let delta = self.overlay.committed.top.iter().map(|(k, v)| (k.clone(), v.value.clone()))
			.chain(self.overlay.prospective.top.iter().map(|(k, v)| (k.clone(), v.value.clone())));

		self.backend.full_storage_root(delta, child_delta_iter).0
	}

	fn child_storage_root(&mut self, child_trie: &ChildTrie) -> Vec<u8> {
		let keyspace = child_trie.keyspace();
		let delta = self.overlay.committed.children.get(keyspace)
			.into_iter()
			.flat_map(|map| map.values.iter().map(|(k, v)| (k.clone(), v.clone())))
			.chain(self.overlay.prospective.children.get(keyspace)
				.into_iter()
				.flat_map(|map| map.values.clone().into_iter()));
		self.backend.child_storage_root(child_trie, delta).0
	}

	fn storage_changes_root(&mut self, parent: H::Out) -> Result<Option<H::Out>, ()> {
		Ok(build_changes_trie::<_, _, H, N>(
			&self.backend,
			Some(&self.changes_trie_storage),
			&self.overlay,
			parent,
		)?.map(|(_, root)| root))
	}

	fn offchain(&mut self) -> Option<&mut dyn offchain::Externalities> {
		self.offchain
			.as_mut()
			.map(|x| &mut **x as _)
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use primitives::{Blake2Hasher, H256};
	use hex_literal::hex;

	#[test]
	fn commit_should_work() {
		let mut ext = TestExternalities::<Blake2Hasher, u64>::default();
		ext.set_storage(b"doe".to_vec(), b"reindeer".to_vec());
		ext.set_storage(b"dog".to_vec(), b"puppy".to_vec());
		ext.set_storage(b"dogglesworth".to_vec(), b"cat".to_vec());
		const ROOT: [u8; 32] = hex!("2a340d3dfd52f5992c6b117e9e45f479e6da5afffafeb26ab619cf137a95aeb8");
		assert_eq!(ext.storage_root(), H256::from(ROOT));
	}

	#[test]
	fn set_and_retrieve_code() {
		let mut ext = TestExternalities::<Blake2Hasher, u64>::default();

		let code = vec![1, 2, 3];
		ext.set_storage(CODE.to_vec(), code.clone());

		assert_eq!(&ext.storage(CODE).unwrap(), &code);
	}
}
