// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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

use std::any::{Any, TypeId};
use hash_db::Hasher;
use crate::{
	backend::{InMemory, Backend}, OverlayedChanges,
	changes_trie::{
		InMemoryStorage as ChangesTrieInMemoryStorage,
		BlockNumber as ChangesTrieBlockNumber,
	},
	ext::Ext,
};
use sp_core::{
	storage::{
		well_known_keys::{CHANGES_TRIE_CONFIG, CODE, HEAP_PAGES, is_child_storage_key},
		Storage,
	},
	hash::H256, Blake2Hasher,
};
use codec::Encode;
use sp_externalities::{Extensions, Extension};

/// Simple HashMap-based Externalities impl.
pub struct TestExternalities<H: Hasher<Out=H256>=Blake2Hasher, N: ChangesTrieBlockNumber=u64> {
	overlay: OverlayedChanges,
	backend: InMemory<H>,
	changes_trie_storage: ChangesTrieInMemoryStorage<H, N>,
	extensions: Extensions,
}

impl<H: Hasher<Out=H256>, N: ChangesTrieBlockNumber> TestExternalities<H, N> {
	/// Get externalities implementation.
	pub fn ext(&mut self) -> Ext<H, N, InMemory<H>, ChangesTrieInMemoryStorage<H, N>> {
		Ext::new(
			&mut self.overlay,
			&self.backend,
			Some(&self.changes_trie_storage),
			Some(&mut self.extensions),
		)
	}

	/// Create a new instance of `TestExternalities` with storage.
	pub fn new(storage: Storage) -> Self {
		Self::new_with_code(&[], storage)
	}

	/// Create a new instance of `TestExternalities` with code and storage.
	pub fn new_with_code(code: &[u8], mut storage: Storage) -> Self {
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
			extensions: Default::default(),
		}
	}

	/// Insert key/value into backend
	pub fn insert(&mut self, k: Vec<u8>, v: Vec<u8>) {
		self.backend = self.backend.update(vec![(None, vec![(k, Some(v))])]);
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
		let top: Vec<_> = self.overlay.committed.top.clone().into_iter()
			.chain(self.overlay.prospective.top.clone().into_iter())
			.map(|(k, v)| (k, v.value)).collect();
		let mut transaction = vec![(None, top)];

		self.overlay.committed.children.clone().into_iter()
			.chain(self.overlay.prospective.children.clone().into_iter())
			.for_each(|(keyspace, (map, child_info))| {
				transaction.push((
					Some((keyspace, child_info)),
					map.into_iter()
						.map(|(k, v)| (k, v.value))
						.collect::<Vec<_>>(),
				))
			});

		self.backend.update(transaction)
	}

	/// Execute the given closure while `self` is set as externalities.
	///
	/// Returns the result of the given closure.
	pub fn execute_with<R>(&mut self, execute: impl FnOnce() -> R) -> R {
		let mut ext = self.ext();
		sp_externalities::set_and_run_with_externalities(&mut ext, execute)
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

impl<H: Hasher<Out=H256>, N: ChangesTrieBlockNumber> From<Storage> for TestExternalities<H, N> {
	fn from(storage: Storage) -> Self {
		Self::new(storage)
	}
}

impl<H, N> sp_externalities::ExtensionStore for TestExternalities<H, N> where
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
	use sp_core::traits::Externalities;
	use hex_literal::hex;

	#[test]
	fn commit_should_work() {
		let mut ext = TestExternalities::<Blake2Hasher, u64>::default();
		let mut ext = ext.ext();
		ext.set_storage(b"doe".to_vec(), b"reindeer".to_vec());
		ext.set_storage(b"dog".to_vec(), b"puppy".to_vec());
		ext.set_storage(b"dogglesworth".to_vec(), b"cat".to_vec());
		const ROOT: [u8; 32] = hex!("2a340d3dfd52f5992c6b117e9e45f479e6da5afffafeb26ab619cf137a95aeb8");
		assert_eq!(&ext.storage_root()[..], &ROOT);
	}

	#[test]
	fn set_and_retrieve_code() {
		let mut ext = TestExternalities::<Blake2Hasher, u64>::default();
		let mut ext = ext.ext();

		let code = vec![1, 2, 3];
		ext.set_storage(CODE.to_vec(), code.clone());

		assert_eq!(&ext.storage(CODE).unwrap(), &code);
	}

	#[test]
	fn check_send() {
		fn assert_send<T: Send>() {}
		assert_send::<TestExternalities::<Blake2Hasher, u64>>();
	}
}
