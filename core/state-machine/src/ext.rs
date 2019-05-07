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

//! Conrete externalities implementation.

use std::{error, fmt, cmp::Ord};
use log::warn;
use crate::backend::Backend;
use crate::changes_trie::{AnchorBlockId, Storage as ChangesTrieStorage, compute_changes_trie_root};
use crate::{Externalities, OverlayedChanges, OffchainExt, ChildStorageKey};
use hash_db::Hasher;
use primitives::storage::well_known_keys::is_child_storage_key;
use trie::{MemoryDB, TrieDBMut, TrieMut, default_child_trie_root};

const EXT_NOT_ALLOWED_TO_FAIL: &str = "Externalities not allowed to fail within runtime";

/// Errors that can occur when interacting with the externalities.
#[derive(Debug, Copy, Clone)]
pub enum Error<B, E> {
	/// Failure to load state data from the backend.
	#[allow(unused)]
	Backend(B),
	/// Failure to execute a function.
	#[allow(unused)]
	Executor(E),
}

impl<B: fmt::Display, E: fmt::Display> fmt::Display for Error<B, E> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match *self {
			Error::Backend(ref e) => write!(f, "Storage backend error: {}", e),
			Error::Executor(ref e) => write!(f, "Sub-call execution error: {}", e),
		}
	}
}

impl<B: error::Error, E: error::Error> error::Error for Error<B, E> {
	fn description(&self) -> &str {
		match *self {
			Error::Backend(..) => "backend error",
			Error::Executor(..) => "executor error",
		}
	}
}

/// Wraps a read-only backend, call executor, and current overlayed changes.
pub struct Ext<'a, H, B, T, O>
where
	H: Hasher,

	B: 'a + Backend<H>,
{
	/// The overlayed changes to write to.
	overlay: &'a mut OverlayedChanges,
	/// The storage backend to read from.
	backend: &'a B,
	/// The storage transaction necessary to commit to the backend. Is cached when
	/// `storage_root` is called and the cache is cleared on every subsequent change.
	storage_transaction: Option<(B::Transaction, H::Out)>,
	/// Changes trie storage to read from.
	changes_trie_storage: Option<&'a T>,
	/// The changes trie transaction necessary to commit to the changes trie backend.
	/// Set to Some when `storage_changes_root` is called. Could be replaced later
	/// by calling `storage_changes_root` again => never used as cache.
	/// This differs from `storage_transaction` behavior, because the moment when
	/// `storage_changes_root` is called matters + we need to remember additional
	/// data at this moment (block number).
	changes_trie_transaction: Option<(u64, MemoryDB<H>, H::Out)>,
	/// Additional externalities for offchain workers.
	///
	/// If None, some methods from the trait might not supported.
	offchain_externalities: Option<&'a mut O>,
}

impl<'a, H, B, T, O> Ext<'a, H, B, T, O>
where
	H: Hasher,
	B: 'a + Backend<H>,
	T: 'a + ChangesTrieStorage<H>,
	O: 'a + OffchainExt,
	H::Out: Ord,
{
	/// Create a new `Ext` from overlayed changes and read-only backend
	pub fn new(
		overlay: &'a mut OverlayedChanges,
		backend: &'a B,
		changes_trie_storage: Option<&'a T>,
		offchain_externalities: Option<&'a mut O>,
	) -> Self {
		Ext {
			overlay,
			backend,
			storage_transaction: None,
			changes_trie_storage,
			changes_trie_transaction: None,
			offchain_externalities,
		}
	}

	/// Get the transaction necessary to update the backend.
	pub fn transaction(mut self) -> (B::Transaction, Option<MemoryDB<H>>) {
		let _ = self.storage_root();

		let (storage_transaction, changes_trie_transaction) = (
			self.storage_transaction
				.expect("storage_transaction always set after calling storage root; qed"),
			self.changes_trie_transaction
				.map(|(_, tx, _)| tx),
		);

		(
			storage_transaction.0,
			changes_trie_transaction,
		)
	}

	/// Invalidates the currently cached storage root and the db transaction.
	///
	/// Called when there are changes that likely will invalidate the storage root.
	fn mark_dirty(&mut self) {
		self.storage_transaction = None;
	}

}

#[cfg(test)]
impl<'a, H, B, T, O> Ext<'a, H, B, T, O>
where
	H: Hasher,

	B: 'a + Backend<H>,
	T: 'a + ChangesTrieStorage<H>,
	O: 'a + OffchainExt,
{
	pub fn storage_pairs(&self) -> Vec<(Vec<u8>, Vec<u8>)> {
		use std::collections::HashMap;

		self.backend.pairs().iter()
			.map(|&(ref k, ref v)| (k.to_vec(), Some(v.to_vec())))
			.chain(self.overlay.committed.top.clone().into_iter().map(|(k, v)| (k, v.value)))
			.chain(self.overlay.prospective.top.clone().into_iter().map(|(k, v)| (k, v.value)))
			.collect::<HashMap<_, _>>()
			.into_iter()
			.filter_map(|(k, maybe_val)| maybe_val.map(|val| (k, val)))
			.collect()
	}
}

impl<'a, B, T, H, O> Externalities<H> for Ext<'a, H, B, T, O>
where
	H: Hasher,
	B: 'a + Backend<H>,
	T: 'a + ChangesTrieStorage<H>,
	O: 'a + OffchainExt,
	H::Out: Ord,
{
	fn storage(&self, key: &[u8]) -> Option<Vec<u8>> {
		let _guard = panic_handler::AbortGuard::new(true);
		self.overlay.storage(key).map(|x| x.map(|x| x.to_vec())).unwrap_or_else(||
			self.backend.storage(key).expect(EXT_NOT_ALLOWED_TO_FAIL))
	}

	fn storage_hash(&self, key: &[u8]) -> Option<H::Out> {
		let _guard = panic_handler::AbortGuard::new(true);
		self.overlay.storage(key).map(|x| x.map(|x| H::hash(x))).unwrap_or_else(||
			self.backend.storage_hash(key).expect(EXT_NOT_ALLOWED_TO_FAIL))
	}

	fn original_storage(&self, key: &[u8]) -> Option<Vec<u8>> {
		let _guard = panic_handler::AbortGuard::new(true);
		self.backend.storage(key).expect(EXT_NOT_ALLOWED_TO_FAIL)
	}

	fn original_storage_hash(&self, key: &[u8]) -> Option<H::Out> {
		let _guard = panic_handler::AbortGuard::new(true);
		self.backend.storage_hash(key).expect(EXT_NOT_ALLOWED_TO_FAIL)
	}

	fn child_storage(&self, storage_key: ChildStorageKey<H>, key: &[u8]) -> Option<Vec<u8>> {
		let _guard = panic_handler::AbortGuard::new(true);
		self.overlay.child_storage(storage_key.as_ref(), key).map(|x| x.map(|x| x.to_vec())).unwrap_or_else(||
			self.backend.child_storage(storage_key.as_ref(), key).expect(EXT_NOT_ALLOWED_TO_FAIL))
	}

	fn exists_storage(&self, key: &[u8]) -> bool {
		let _guard = panic_handler::AbortGuard::new(true);
		match self.overlay.storage(key) {
			Some(x) => x.is_some(),
			_ => self.backend.exists_storage(key).expect(EXT_NOT_ALLOWED_TO_FAIL),
		}
	}

	fn exists_child_storage(&self, storage_key: ChildStorageKey<H>, key: &[u8]) -> bool {
		let _guard = panic_handler::AbortGuard::new(true);

		match self.overlay.child_storage(storage_key.as_ref(), key) {
			Some(x) => x.is_some(),
			_ => self.backend.exists_child_storage(storage_key.as_ref(), key).expect(EXT_NOT_ALLOWED_TO_FAIL),
		}
	}

	fn place_storage(&mut self, key: Vec<u8>, value: Option<Vec<u8>>) {
		let _guard = panic_handler::AbortGuard::new(true);
		if is_child_storage_key(&key) {
			warn!(target: "trie", "Refuse to directly set child storage key");
			return;
		}

		self.mark_dirty();
		self.overlay.set_storage(key, value);
	}

	fn place_child_storage(&mut self, storage_key: ChildStorageKey<H>, key: Vec<u8>, value: Option<Vec<u8>>) {
		let _guard = panic_handler::AbortGuard::new(true);

		self.mark_dirty();
		self.overlay.set_child_storage(storage_key.into_owned(), key, value);
	}

	fn kill_child_storage(&mut self, storage_key: ChildStorageKey<H>) {
		let _guard = panic_handler::AbortGuard::new(true);

		self.mark_dirty();
		self.overlay.clear_child_storage(storage_key.as_ref());
		self.backend.for_keys_in_child_storage(storage_key.as_ref(), |key| {
			self.overlay.set_child_storage(storage_key.as_ref().to_vec(), key.to_vec(), None);
		});
	}

	fn clear_prefix(&mut self, prefix: &[u8]) {
		let _guard = panic_handler::AbortGuard::new(true);
		if is_child_storage_key(prefix) {
			warn!(target: "trie", "Refuse to directly clear prefix that is part of child storage key");
			return;
		}

		self.mark_dirty();
		self.overlay.clear_prefix(prefix);
		self.backend.for_keys_with_prefix(prefix, |key| {
			self.overlay.set_storage(key.to_vec(), None);
		});
	}

	fn chain_id(&self) -> u64 {
		42
	}

	fn storage_root(&mut self) -> H::Out {
		let _guard = panic_handler::AbortGuard::new(true);
		if let Some((_, ref root)) = self.storage_transaction {
			return root.clone();
		}

		let child_storage_keys =
			self.overlay.prospective.children.keys()
				.chain(self.overlay.committed.children.keys());

		let child_delta_iter = child_storage_keys.map(|storage_key|
			(storage_key.clone(), self.overlay.committed.children.get(storage_key)
				.into_iter()
				.flat_map(|map| map.1.iter().map(|(k, v)| (k.clone(), v.clone())))
				.chain(self.overlay.prospective.children.get(storage_key)
					.into_iter()
					.flat_map(|map| map.1.iter().map(|(k, v)| (k.clone(), v.clone()))))));


		// compute and memoize
		let delta = self.overlay.committed.top.iter().map(|(k, v)| (k.clone(), v.value.clone()))
			.chain(self.overlay.prospective.top.iter().map(|(k, v)| (k.clone(), v.value.clone())));

		let (root, transaction) = self.backend.full_storage_root(delta, child_delta_iter);
		self.storage_transaction = Some((transaction, root));
		root
	}

	fn child_storage_root(&mut self, storage_key: ChildStorageKey<H>) -> Vec<u8> {
		let _guard = panic_handler::AbortGuard::new(true);
		if self.storage_transaction.is_some() {
			self
				.storage(storage_key.as_ref())
				.unwrap_or(
					default_child_trie_root::<H>(storage_key.as_ref())
				)
		} else {
			let storage_key = storage_key.as_ref();

			let delta = self.overlay.committed.children.get(storage_key)
				.into_iter()
				.flat_map(|map| map.1.iter().map(|(k, v)| (k.clone(), v.clone())))
				.chain(self.overlay.prospective.children.get(storage_key)
						.into_iter()
						.flat_map(|map| map.1.iter().map(|(k, v)| (k.clone(), v.clone()))));

			let root = self.backend.child_storage_root(storage_key, delta).0;

			self.overlay.set_storage(storage_key.to_vec(), Some(root.to_vec()));

			root

		}
	}

	fn storage_changes_root(&mut self, parent: H::Out, parent_num: u64) -> Option<H::Out> {
		let _guard = panic_handler::AbortGuard::new(true);
		let root_and_tx = compute_changes_trie_root::<_, T, H>(
			self.backend,
			self.changes_trie_storage.clone(),
			self.overlay,
			&AnchorBlockId { hash: parent, number: parent_num },
		);
		let root_and_tx = root_and_tx.map(|(root, changes)| {
			let mut calculated_root = Default::default();
			let mut mdb = MemoryDB::default();
			{
				let mut trie = TrieDBMut::<H>::new(&mut mdb, &mut calculated_root);
				for (key, value) in changes {
					trie.insert(&key, &value).expect(EXT_NOT_ALLOWED_TO_FAIL);
				}
			}

			(parent_num + 1, mdb, root)
		});
		let root = root_and_tx.as_ref().map(|(_, _, root)| root.clone());
		self.changes_trie_transaction = root_and_tx;
		root
	}

	fn submit_extrinsic(&mut self, extrinsic: Vec<u8>) -> Result<(), ()> {
		let _guard = panic_handler::AbortGuard::new(true);
		if let Some(ext) = self.offchain_externalities.as_mut() {
			ext.submit_extrinsic(extrinsic);
			Ok(())
		} else {
			warn!("Call to submit_extrinsic without offchain externalities set.");
			Err(())
		}
	}
}

#[cfg(test)]
mod tests {
	use hex_literal::hex;
	use parity_codec::Encode;
	use primitives::{Blake2Hasher};
	use primitives::storage::well_known_keys::EXTRINSIC_INDEX;
	use crate::backend::InMemory;
	use crate::changes_trie::{Configuration as ChangesTrieConfiguration,
		InMemoryStorage as InMemoryChangesTrieStorage};
	use crate::overlayed_changes::OverlayedValue;
	use super::*;

	type TestBackend = InMemory<Blake2Hasher>;
	type TestChangesTrieStorage = InMemoryChangesTrieStorage<Blake2Hasher>;
	type TestExt<'a> = Ext<'a, Blake2Hasher, TestBackend, TestChangesTrieStorage, crate::NeverOffchainExt>;

	fn prepare_overlay_with_changes() -> OverlayedChanges {
		OverlayedChanges {
			prospective: vec![
				(EXTRINSIC_INDEX.to_vec(), OverlayedValue {
					value: Some(3u32.encode()),
					extrinsics: Some(vec![1].into_iter().collect())
				}),
				(vec![1], OverlayedValue {
					value: Some(vec![100].into_iter().collect()),
					extrinsics: Some(vec![1].into_iter().collect())
				}),
			].into_iter().collect(),
			committed: Default::default(),
			changes_trie_config: Some(ChangesTrieConfiguration {
				digest_interval: 0,
				digest_levels: 0,
			}),
		}
	}

	#[test]
	fn storage_changes_root_is_none_when_storage_is_not_provided() {
		let mut overlay = prepare_overlay_with_changes();
		let backend = TestBackend::default();
		let mut ext = TestExt::new(&mut overlay, &backend, None, None);
		assert_eq!(ext.storage_changes_root(Default::default(), 100), None);
	}

	#[test]
	fn storage_changes_root_is_none_when_extrinsic_changes_are_none() {
		let mut overlay = prepare_overlay_with_changes();
		overlay.changes_trie_config = None;
		let storage = TestChangesTrieStorage::new();
		let backend = TestBackend::default();
		let mut ext = TestExt::new(&mut overlay, &backend, Some(&storage), None);
		assert_eq!(ext.storage_changes_root(Default::default(), 100), None);
	}

	#[test]
	fn storage_changes_root_is_some_when_extrinsic_changes_are_non_empty() {
		let mut overlay = prepare_overlay_with_changes();
		let storage = TestChangesTrieStorage::new();
		let backend = TestBackend::default();
		let mut ext = TestExt::new(&mut overlay, &backend, Some(&storage), None);
		assert_eq!(ext.storage_changes_root(Default::default(), 99),
			Some(hex!("5b829920b9c8d554a19ee2a1ba593c4f2ee6fc32822d083e04236d693e8358d5").into()));
	}

	#[test]
	fn storage_changes_root_is_some_when_extrinsic_changes_are_empty() {
		let mut overlay = prepare_overlay_with_changes();
		overlay.prospective.top.get_mut(&vec![1]).unwrap().value = None;
		let storage = TestChangesTrieStorage::new();
		let backend = TestBackend::default();
		let mut ext = TestExt::new(&mut overlay, &backend, Some(&storage), None);
		assert_eq!(ext.storage_changes_root(Default::default(), 99),
			Some(hex!("bcf494e41e29a15c9ae5caa053fe3cb8b446ee3e02a254efbdec7a19235b76e4").into()));
	}
}
