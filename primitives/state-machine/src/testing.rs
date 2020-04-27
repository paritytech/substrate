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
use codec::Decode;
use hash_db::Hasher;
use crate::{
	backend::Backend, OverlayedChanges, StorageTransactionCache, ext::Ext, InMemoryBackend,
	StorageKey, StorageValue,
	changes_trie::{
		Configuration as ChangesTrieConfiguration,
		InMemoryStorage as ChangesTrieInMemoryStorage,
		BlockNumber as ChangesTrieBlockNumber,
		State as ChangesTrieState,
	},
};
use sp_core::{
	offchain::storage::OffchainOverlayedChanges,
	storage::{
		well_known_keys::{CHANGES_TRIE_CONFIG, CODE, HEAP_PAGES, is_child_storage_key},
		Storage,
	},
};
use codec::Encode;
use sp_externalities::{Extensions, Extension};

/// Simple HashMap-based Externalities impl.
pub struct TestExternalities<H: Hasher, N: ChangesTrieBlockNumber = u64>
where
	H::Out: codec::Codec + Ord,
{
	overlay: OverlayedChanges,
	offchain_overlay: OffchainOverlayedChanges,
	storage_transaction_cache: StorageTransactionCache<
		<InMemoryBackend<H> as Backend<H>>::Transaction, H, N
	>,
	backend: InMemoryBackend<H>,
	changes_trie_config: Option<ChangesTrieConfiguration>,
	changes_trie_storage: ChangesTrieInMemoryStorage<H, N>,
	extensions: Extensions,
}

impl<H: Hasher, N: ChangesTrieBlockNumber> TestExternalities<H, N>
	where
		H::Out: Ord + 'static + codec::Codec
{
	/// Get externalities implementation.
	pub fn ext(&mut self) -> Ext<H, N, InMemoryBackend<H>> {
		Ext::new(
			&mut self.overlay,
			&mut self.offchain_overlay,
			&mut self.storage_transaction_cache,
			&self.backend,
			match self.changes_trie_config.clone() {
				Some(config) => Some(ChangesTrieState {
					config,
					zero: 0.into(),
					storage: &self.changes_trie_storage,
				}),
				None => None,
			},
			Some(&mut self.extensions),
		)
	}

	/// Create a new instance of `TestExternalities` with storage.
	pub fn new(storage: Storage) -> Self {
		Self::new_with_code(&[], storage)
	}

	/// New empty test externalities.
	pub fn new_empty() -> Self {
		Self::new_with_code(&[], Storage::default())
	}

	/// Create a new instance of `TestExternalities` with code and storage.
	pub fn new_with_code(code: &[u8], mut storage: Storage) -> Self {
		let mut overlay = OverlayedChanges::default();
		let changes_trie_config = storage.top.get(CHANGES_TRIE_CONFIG)
			.and_then(|v| Decode::decode(&mut &v[..]).ok());
		overlay.set_collect_extrinsics(changes_trie_config.is_some());

		assert!(storage.top.keys().all(|key| !is_child_storage_key(key)));
		assert!(storage.children_default.keys().all(|key| is_child_storage_key(key)));

		storage.top.insert(HEAP_PAGES.to_vec(), 8u64.encode());
		storage.top.insert(CODE.to_vec(), code.to_vec());

		let offchain_overlay = OffchainOverlayedChanges::enabled();

		let mut extensions = Extensions::default();
		extensions.register(sp_core::traits::TaskExecutorExt(sp_core::tasks::executor()));


		TestExternalities {
			overlay,
			offchain_overlay,
			changes_trie_config,
			extensions,
			changes_trie_storage: ChangesTrieInMemoryStorage::new(),
			backend: storage.into(),
			storage_transaction_cache: Default::default(),
		}
	}

	/// Insert key/value into backend
	pub fn insert(&mut self, k: StorageKey, v: StorageValue) {
		self.backend.insert(vec![(None, vec![(k, Some(v))])]);
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
	pub fn commit_all(&self) -> InMemoryBackend<H> {
		let top: Vec<_> = self.overlay.committed.top.clone().into_iter()
			.chain(self.overlay.prospective.top.clone().into_iter())
			.map(|(k, v)| (k, v.value)).collect();
		let mut transaction = vec![(None, top)];

		self.overlay.committed.children_default.clone().into_iter()
			.chain(self.overlay.prospective.children_default.clone().into_iter())
			.for_each(|(_storage_key, (map, child_info))| {
				transaction.push((
					Some(child_info),
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

impl<H: Hasher, N: ChangesTrieBlockNumber> std::fmt::Debug for TestExternalities<H, N>
	where H::Out: Ord + codec::Codec,
{
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		write!(f, "overlay: {:?}\nbackend: {:?}", self.overlay, self.backend.pairs())
	}
}

impl<H: Hasher, N: ChangesTrieBlockNumber> PartialEq for TestExternalities<H, N>
	where
		H::Out: Ord + 'static + codec::Codec
{
	/// This doesn't test if they are in the same state, only if they contains the
	/// same data at this state
	fn eq(&self, other: &TestExternalities<H, N>) -> bool {
		self.commit_all().eq(&other.commit_all())
	}
}

impl<H: Hasher, N: ChangesTrieBlockNumber> Default for TestExternalities<H, N>
	where
		H::Out: Ord + 'static + codec::Codec,
{
	fn default() -> Self { Self::new(Default::default()) }
}

impl<H: Hasher, N: ChangesTrieBlockNumber> From<Storage> for TestExternalities<H, N>
	where
		H::Out: Ord + 'static + codec::Codec,
{
	fn from(storage: Storage) -> Self {
		Self::new(storage)
	}
}

impl<H, N> sp_externalities::ExtensionStore for TestExternalities<H, N> where
	H: Hasher,
	H::Out: Ord + codec::Codec,
	N: ChangesTrieBlockNumber,
{
	fn extension_by_type_id(&mut self, type_id: TypeId) -> Option<&mut dyn Any> {
		self.extensions.get_mut(type_id)
	}

	fn register_extension_with_type_id(
		&mut self,
		type_id: TypeId,
		extension: Box<dyn Extension>,
	) -> Result<(), sp_externalities::Error> {
		self.extensions.register_with_type_id(type_id, extension)
	}

	fn deregister_extension_by_type_id(&mut self, type_id: TypeId) -> Result<(), sp_externalities::Error> {
		self.extensions
			.deregister(type_id)
			.expect("There should be an extension we try to remove in TestExternalities");
		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use sp_core::traits::Externalities;
	use sp_runtime::traits::BlakeTwo256;
	use hex_literal::hex;

	#[test]
	fn commit_should_work() {
		let mut ext = TestExternalities::<BlakeTwo256, u64>::default();
		let mut ext = ext.ext();
		ext.set_storage(b"doe".to_vec(), b"reindeer".to_vec());
		ext.set_storage(b"dog".to_vec(), b"puppy".to_vec());
		ext.set_storage(b"dogglesworth".to_vec(), b"cat".to_vec());
		const ROOT: [u8; 32] = hex!("555d4777b52e9196e3f6373c556cc661e79cd463f881ab9e921e70fc30144bf4");
		assert_eq!(&ext.storage_root()[..], &ROOT);
	}

	#[test]
	fn set_and_retrieve_code() {
		let mut ext = TestExternalities::<BlakeTwo256, u64>::default();
		let mut ext = ext.ext();

		let code = vec![1, 2, 3];
		ext.set_storage(CODE.to_vec(), code.clone());

		assert_eq!(&ext.storage(CODE).unwrap(), &code);
	}

	#[test]
	fn check_send() {
		fn assert_send<T: Send>() {}
		assert_send::<TestExternalities::<BlakeTwo256, u64>>();
	}
}
