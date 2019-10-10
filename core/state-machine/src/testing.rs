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

use std::{collections::HashMap, any::{Any, TypeId}};
use hash_db::Hasher;
use crate::{
	backend::{InMemory, Backend}, OverlayedChanges,
	changes_trie::{
		build_changes_trie, InMemoryStorage as ChangesTrieInMemoryStorage,
		BlockNumber as ChangesTrieBlockNumber,
	},
};
use primitives::{
	storage::{
		ChildStorageKey,
		well_known_keys::{CHANGES_TRIE_CONFIG, CODE, HEAP_PAGES, is_child_storage_key}
	},
	traits::Externalities, hash::H256, Blake2Hasher,
};
use codec::Encode;
use externalities::{Extensions, Extension};

const EXT_NOT_ALLOWED_TO_FAIL: &str = "Externalities not allowed to fail within runtime";

type StorageTuple = (HashMap<Vec<u8>, Vec<u8>>, HashMap<Vec<u8>, HashMap<Vec<u8>, Vec<u8>>>);

/// Simple HashMap-based Externalities impl.
pub struct TestExternalities<H: Hasher<Out=H256>=Blake2Hasher, N: ChangesTrieBlockNumber=u64> {
	overlay: OverlayedChanges,
	backend: InMemory<H>,
	changes_trie_storage: ChangesTrieInMemoryStorage<H, N>,
	extensions: Extensions,
}

impl<H: Hasher<Out=H256>, N: ChangesTrieBlockNumber> TestExternalities<H, N> {
	/// Create a new instance of `TestExternalities` with storage.
	pub fn new(storage: StorageTuple) -> Self {
		Self::new_with_code(&[], storage)
	}

	/// Create a new instance of `TestExternalities` with code and storage.
	pub fn new_with_code(code: &[u8], mut storage: StorageTuple) -> Self {
		let mut overlay = OverlayedChanges::default();

		assert!(storage.0.keys().all(|key| !is_child_storage_key(key)));
		assert!(storage.1.keys().all(|key| is_child_storage_key(key)));

		super::set_changes_trie_config(
			&mut overlay,
			storage.0.get(&CHANGES_TRIE_CONFIG.to_vec()).cloned(),
			false,
		).expect("changes trie configuration is correct in test env; qed");

		storage.0.insert(HEAP_PAGES.to_vec(), 8u64.encode());
		storage.0.insert(CODE.to_vec(), code.to_vec());

		let backend: HashMap<_, _> = storage.1.into_iter()
			.map(|(keyspace, map)| (Some(keyspace), map))
			.chain(Some((None, storage.0)).into_iter())
			.collect();

		TestExternalities {
			overlay,
			changes_trie_storage: ChangesTrieInMemoryStorage::new(),
			backend: backend.into(),
			extensions: Default::default(),
		}
	}

	/// Insert key/value into backend
	pub fn insert(&mut self, k: Vec<u8>, v: Vec<u8>) {
		self.backend = self.backend.update(vec![(None, k, Some(v))]);
	}

	/// Registers the given extension for this instance.
	pub fn register_extension<E: Any + Extension>(&mut self, ext: E) {
		self.extensions.register(ext);
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
			.flat_map(|(keyspace, map)| {
				map.into_iter()
					.map(|(k, v)| (Some(keyspace.clone()), k, v.value))
					.collect::<Vec<_>>()
			});

		self.backend.update(top.chain(children).collect())
	}

	/// Execute the given closure while `self` is set as externalities.
	///
	/// Returns the result of the given closure.
	pub fn execute_with<R>(&mut self, execute: impl FnOnce() -> R) -> R {
		externalities::set_and_run_with_externalities(self, execute)
	}
}

impl<H: Hasher<Out=H256>, N: ChangesTrieBlockNumber> std::fmt::Debug for TestExternalities<H, N> {
	fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
		write!(f, "overlay: {:?}\nbackend: {:?}", self.overlay, self.backend.pairs())
	}
}

impl<H: Hasher<Out=H256>, N: ChangesTrieBlockNumber> PartialEq for TestExternalities<H, N> {
	/// This doesn't test if they are in the same state, only if they contains the
	/// same data at this state
	fn eq(&self, other: &TestExternalities<H, N>) -> bool {
		self.commit_all().eq(&other.commit_all())
	}
}

impl<H: Hasher<Out=H256>, N: ChangesTrieBlockNumber> Default for TestExternalities<H, N> {
	fn default() -> Self { Self::new(Default::default()) }
}

impl<H: Hasher<Out=H256>, N: ChangesTrieBlockNumber> From<StorageTuple> for TestExternalities<H, N> {
	fn from(storage: StorageTuple) -> Self {
		Self::new(storage)
	}
}

impl<H, N> Externalities for TestExternalities<H, N> where
	H: Hasher<Out=H256>,
	N: ChangesTrieBlockNumber,
{
	fn storage(&self, key: &[u8]) -> Option<Vec<u8>> {
		self.overlay.storage(key).map(|x| x.map(|x| x.to_vec())).unwrap_or_else(||
			self.backend.storage(key).expect(EXT_NOT_ALLOWED_TO_FAIL))
	}

	fn storage_hash(&self, key: &[u8]) -> Option<H256> {
		self.storage(key).map(|v| H::hash(&v))
	}

	fn original_storage(&self, key: &[u8]) -> Option<Vec<u8>> {
		self.backend.storage(key).expect(EXT_NOT_ALLOWED_TO_FAIL)
	}

	fn original_storage_hash(&self, key: &[u8]) -> Option<H256> {
		self.storage_hash(key)
	}

	fn child_storage(&self, storage_key: ChildStorageKey, key: &[u8]) -> Option<Vec<u8>> {
		self.overlay
			.child_storage(storage_key.as_ref(), key)
			.map(|x| x.map(|x| x.to_vec()))
			.unwrap_or_else(|| self.backend
				.child_storage(storage_key.as_ref(), key)
				.expect(EXT_NOT_ALLOWED_TO_FAIL)
			)
	}

	fn child_storage_hash(&self, storage_key: ChildStorageKey, key: &[u8]) -> Option<H256> {
		self.child_storage(storage_key, key).map(|v| H::hash(&v))
	}

	fn original_child_storage(&self, storage_key: ChildStorageKey, key: &[u8]) -> Option<Vec<u8>> {
		self.backend
			.child_storage(storage_key.as_ref(), key)
			.map(|x| x.map(|x| x.to_vec()))
			.expect(EXT_NOT_ALLOWED_TO_FAIL)
	}

	fn original_child_storage_hash(&self, storage_key: ChildStorageKey, key: &[u8]) -> Option<H256> {
		self.child_storage_hash(storage_key, key)
	}

	fn place_storage(&mut self, key: Vec<u8>, maybe_value: Option<Vec<u8>>) {
		if is_child_storage_key(&key) {
			panic!("Refuse to directly set child storage key");
		}

		self.overlay.set_storage(key, maybe_value);
	}

	fn place_child_storage(
		&mut self,
		storage_key: ChildStorageKey,
		key: Vec<u8>,
		value: Option<Vec<u8>>,
	) {
		self.overlay.set_child_storage(storage_key.into_owned(), key, value);
	}

	fn kill_child_storage(&mut self, storage_key: ChildStorageKey) {
		let backend = &self.backend;
		let overlay = &mut self.overlay;

		overlay.clear_child_storage(storage_key.as_ref());
		backend.for_keys_in_child_storage(storage_key.as_ref(), |key| {
			overlay.set_child_storage(storage_key.as_ref().to_vec(), key.to_vec(), None);
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

	fn clear_child_prefix(&mut self, storage_key: ChildStorageKey, prefix: &[u8]) {
		self.overlay.clear_child_prefix(storage_key.as_ref(), prefix);

		let backend = &self.backend;
		let overlay = &mut self.overlay;
		backend.for_child_keys_with_prefix(storage_key.as_ref(), prefix, |key| {
			overlay.set_child_storage(storage_key.as_ref().to_vec(), key.to_vec(), None);
		});
	}

	fn chain_id(&self) -> u64 { 42 }

	fn storage_root(&mut self) -> H256 {
		let child_storage_keys =
			self.overlay.prospective.children.keys()
				.chain(self.overlay.committed.children.keys());

		let child_delta_iter = child_storage_keys.map(|storage_key|
			(storage_key.clone(), self.overlay.committed.children.get(storage_key)
				.into_iter()
				.flat_map(|map| map.iter().map(|(k, v)| (k.clone(), v.value.clone())))
				.chain(self.overlay.prospective.children.get(storage_key)
					.into_iter()
					.flat_map(|map| map.iter().map(|(k, v)| (k.clone(), v.value.clone()))))));


		// compute and memoize
		let delta = self.overlay.committed.top.iter().map(|(k, v)| (k.clone(), v.value.clone()))
			.chain(self.overlay.prospective.top.iter().map(|(k, v)| (k.clone(), v.value.clone())));
		self.backend.full_storage_root(delta, child_delta_iter).0
	}

	fn child_storage_root(&mut self, storage_key: ChildStorageKey) -> Vec<u8> {
		let storage_key = storage_key.as_ref();

		let (root, is_empty, _) = {
			let delta = self.overlay.committed.children.get(storage_key)
				.into_iter()
				.flat_map(|map| map.clone().into_iter().map(|(k, v)| (k, v.value)))
				.chain(self.overlay.prospective.children.get(storage_key)
						.into_iter()
						.flat_map(|map| map.clone().into_iter().map(|(k, v)| (k, v.value))));

			self.backend.child_storage_root(storage_key, delta)
		};
		if is_empty {
			self.overlay.set_storage(storage_key.into(), None);
		} else {
			self.overlay.set_storage(storage_key.into(), Some(root.clone()));
		}
		root
	}

	fn storage_changes_root(&mut self, parent: H256) -> Result<Option<H256>, ()> {
		Ok(build_changes_trie::<_, _, H, N>(
			&self.backend,
			Some(&self.changes_trie_storage),
			&self.overlay,
			parent,
		)?.map(|(_, root, _)| root))
	}
}

impl<H, N> externalities::ExtensionStore for TestExternalities<H, N> where
	H: Hasher<Out=H256>,
	N: ChangesTrieBlockNumber,
{
	fn extension_by_type_id(&mut self, type_id: TypeId) -> Option<&mut dyn Any> {
		self.extensions.get_mut(type_id)
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
