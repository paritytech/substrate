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

//! Concrete externalities implementation.

use std::{error, fmt, cmp::Ord};
use log::warn;
use crate::backend::Backend;
use crate::changes_trie::{Storage as ChangesTrieStorage, build_changes_trie};
use crate::{Externalities, OverlayedChanges, OverlayedValueResult};
use hash_db::Hasher;
use primitives::{
	offchain,
	storage::well_known_keys::is_child_storage_key,
	traits::BareCryptoStorePtr,
	child_trie::{ChildTrie, ChildTrieReadRef}
};
use trie::{MemoryDB, default_child_trie_root};
use trie::trie_types::Layout;

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
pub struct Ext<'a, H, N, B, T, O>
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
	changes_trie_transaction: Option<(MemoryDB<H>, H::Out)>,
	/// Additional externalities for offchain workers.
	///
	/// If None, some methods from the trait might not be supported.
	offchain_externalities: Option<&'a mut O>,
	/// The keystore that manages the keys of the node.
	keystore: Option<BareCryptoStorePtr>,
	/// Dummy usage of N arg.
	_phantom: ::std::marker::PhantomData<N>,
}

impl<'a, H, N, B, T, O> Ext<'a, H, N, B, T, O>
where
	H: Hasher,
	B: 'a + Backend<H>,
	T: 'a + ChangesTrieStorage<H, N>,
	O: 'a + offchain::Externalities,
	H::Out: Ord + 'static,
	N: crate::changes_trie::BlockNumber,
{
	/// Create a new `Ext` from overlayed changes and read-only backend
	pub fn new(
		overlay: &'a mut OverlayedChanges,
		backend: &'a B,
		changes_trie_storage: Option<&'a T>,
		offchain_externalities: Option<&'a mut O>,
		keystore: Option<BareCryptoStorePtr>,
	) -> Self {
		Ext {
			overlay,
			backend,
			storage_transaction: None,
			changes_trie_storage,
			changes_trie_transaction: None,
			offchain_externalities,
			keystore,
			_phantom: Default::default(),
		}
	}

	/// Get the transaction necessary to update the backend.
	pub fn transaction(mut self) -> ((B::Transaction, H::Out), Option<MemoryDB<H>>) {
		let _ = self.storage_root();

		let (storage_transaction, changes_trie_transaction) = (
			self.storage_transaction
				.expect("storage_transaction always set after calling storage root; qed"),
			self.changes_trie_transaction
				.map(|(tx, _)| tx),
		);

		(
			storage_transaction,
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
impl<'a, H, N, B, T, O> Ext<'a, H, N, B, T, O>
where
	H: Hasher,
	B: 'a + Backend<H>,
	T: 'a + ChangesTrieStorage<H, N>,
	O: 'a + offchain::Externalities,
	N: crate::changes_trie::BlockNumber,
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

impl<'a, B, T, H, N, O> Externalities<H> for Ext<'a, H, N, B, T, O>
where
	H: Hasher,
	B: 'a + Backend<H>,
	T: 'a + ChangesTrieStorage<H, N>,
	O: 'a + offchain::Externalities,
	H::Out: Ord + 'static,
	N: crate::changes_trie::BlockNumber,
{
	fn storage(&self, key: &[u8]) -> Option<Vec<u8>> {
		let _guard = panic_handler::AbortGuard::force_abort();
		match self.overlay.storage(key) {
			OverlayedValueResult::NotFound =>
				self.backend.storage(key).expect(EXT_NOT_ALLOWED_TO_FAIL),
			OverlayedValueResult::Deleted => None,
			OverlayedValueResult::Modified(value) => Some(value.to_vec()),
		}
	}

	fn storage_hash(&self, key: &[u8]) -> Option<H::Out> {
		let _guard = panic_handler::AbortGuard::force_abort();
		match self.overlay.storage(key) {
			OverlayedValueResult::NotFound =>
				self.backend.storage_hash(key).expect(EXT_NOT_ALLOWED_TO_FAIL),
			OverlayedValueResult::Deleted => None,
			OverlayedValueResult::Modified(value) => Some( H::hash(value)),
		}
	}

	fn original_storage(&self, key: &[u8]) -> Option<Vec<u8>> {
		let _guard = panic_handler::AbortGuard::force_abort();
		self.backend.storage(key).expect(EXT_NOT_ALLOWED_TO_FAIL)
	}

	fn original_storage_hash(&self, key: &[u8]) -> Option<H::Out> {
		let _guard = panic_handler::AbortGuard::force_abort();
		self.backend.storage_hash(key).expect(EXT_NOT_ALLOWED_TO_FAIL)
	}

	fn child_trie(&self, storage_key: &[u8]) -> Option<ChildTrie> {
		let _guard = panic_handler::AbortGuard::force_abort();
		self.overlay.child_trie(storage_key).unwrap_or_else(||
			self.backend.child_trie(storage_key).expect(EXT_NOT_ALLOWED_TO_FAIL))
	}

	fn child_storage(&self, child_trie: ChildTrieReadRef, key: &[u8]) -> Option<Vec<u8>> {
		let _guard = panic_handler::AbortGuard::force_abort();
		match self.overlay.child_storage(child_trie.clone(), key) {
			OverlayedValueResult::NotFound =>
				self.backend.child_storage(child_trie, key).expect(EXT_NOT_ALLOWED_TO_FAIL),
			OverlayedValueResult::Deleted => None,
			OverlayedValueResult::Modified(value) => Some( value.to_vec()),
		}
	}

	fn exists_storage(&self, key: &[u8]) -> bool {
		let _guard = panic_handler::AbortGuard::force_abort();
		match self.overlay.storage(key) {
			OverlayedValueResult::NotFound =>
				self.backend.exists_storage(key).expect(EXT_NOT_ALLOWED_TO_FAIL),
			OverlayedValueResult::Deleted => false,
			OverlayedValueResult::Modified(_value) => true,
		}
	}

	fn exists_child_storage(&self, child_trie: ChildTrieReadRef, key: &[u8]) -> bool {
		let _guard = panic_handler::AbortGuard::force_abort();
		match self.overlay.child_storage(child_trie.clone(), key) {
			OverlayedValueResult::NotFound =>
				self.backend.exists_child_storage(child_trie, key).expect(EXT_NOT_ALLOWED_TO_FAIL),
			OverlayedValueResult::Deleted => false,
			OverlayedValueResult::Modified(_value) => true,
		}
	}

	fn place_storage(&mut self, key: Vec<u8>, value: Option<Vec<u8>>) {
		let _guard = panic_handler::AbortGuard::force_abort();
		if is_child_storage_key(&key) {
			warn!(target: "trie", "Refuse to directly set child storage key");
			return;
		}

		self.mark_dirty();
		self.overlay.set_storage(key, value);
	}

	fn place_child_storage(&mut self, child_trie: &ChildTrie, key: Vec<u8>, value: Option<Vec<u8>>) {
		let _guard = panic_handler::AbortGuard::force_abort();

		self.mark_dirty();
		self.overlay.set_child_storage(child_trie, key, value);
	}

	fn set_child_trie(&mut self, ct: ChildTrie) -> bool {
		let _guard = panic_handler::AbortGuard::force_abort();
		// do check for backend, theorically this could be skip
		// (`ChildTrie` being initiated from backend, this is
		// still here for safety but removal can be considered
		// in the future).
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

	fn kill_child_storage(&mut self, child_trie: &ChildTrie) {
		let _guard = panic_handler::AbortGuard::force_abort();

		self.mark_dirty();
		self.overlay.clear_child_storage(child_trie);
		self.backend.for_keys_in_child_storage(child_trie.node_ref(), |key| {
			self.overlay.set_child_storage(child_trie, key.to_vec(), None);
		});
	}

	fn clear_prefix(&mut self, prefix: &[u8]) {
		let _guard = panic_handler::AbortGuard::force_abort();
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
		let _guard = panic_handler::AbortGuard::force_abort();
		if let Some((_, ref root)) = self.storage_transaction {
			return root.clone();
		}

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

		let (root, transaction) = self.backend.full_storage_root(delta, child_delta_iter);
		self.storage_transaction = Some((transaction, root));
		root
	}

	fn child_storage_root(&mut self, child_trie: &ChildTrie) -> Vec<u8> {
		let _guard = panic_handler::AbortGuard::force_abort();

		if self.storage_transaction.is_some() {
			self.child_trie(child_trie.parent_slice())
				.and_then(|child_trie| child_trie.root_initial_value().clone())
				.unwrap_or(default_child_trie_root::<Layout<H>>())
		} else {
			let keyspace = child_trie.keyspace();
			let delta = self.overlay.committed.children.get(keyspace)
				.into_iter()
				.flat_map(|map| map.values.iter().map(|(k, v)| (k.clone(), v.clone())))
				.chain(self.overlay.prospective.children.get(keyspace)
					.into_iter()
					.flat_map(|map| map.values.clone().into_iter()));
			let root = self.backend.child_storage_root(child_trie, delta).0;

			self.overlay.set_storage(
				child_trie.parent_trie().clone(),
				Some(child_trie.encoded_with_root(&root[..]))
			);

			root
		}
	}

	fn storage_changes_root(&mut self, parent_hash: H::Out) -> Result<Option<H::Out>, ()> {
		let _guard = panic_handler::AbortGuard::force_abort();
		self.changes_trie_transaction = build_changes_trie::<_, T, H, N>(
			self.backend,
			self.changes_trie_storage.clone(),
			self.overlay,
			parent_hash,
		)?;
		Ok(self.changes_trie_transaction.as_ref().map(|(_, root)| root.clone()))
	}

	fn offchain(&mut self) -> Option<&mut dyn offchain::Externalities> {
		self.offchain_externalities.as_mut().map(|x| &mut **x as _)
	}

	fn keystore(&self) -> Option<BareCryptoStorePtr> {
		self.keystore.clone()
	}
}

#[cfg(test)]
mod tests {
	use hex_literal::hex;
	use codec::Encode;
	use primitives::{Blake2Hasher};
	use primitives::storage::well_known_keys::EXTRINSIC_INDEX;
	use crate::backend::InMemory;
	use crate::changes_trie::{Configuration as ChangesTrieConfiguration,
		InMemoryStorage as InMemoryChangesTrieStorage};
	use crate::overlayed_changes::OverlayedValue;
	use super::*;

	type TestBackend = InMemory<Blake2Hasher>;
	type TestChangesTrieStorage = InMemoryChangesTrieStorage<Blake2Hasher, u64>;
	type TestExt<'a> = Ext<'a, Blake2Hasher, u64, TestBackend, TestChangesTrieStorage, crate::NeverOffchainExt>;

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
		let mut ext = TestExt::new(&mut overlay, &backend, None, None, None);
		assert_eq!(ext.storage_changes_root(Default::default()).unwrap(), None);
	}

	#[test]
	fn storage_changes_root_is_none_when_extrinsic_changes_are_none() {
		let mut overlay = prepare_overlay_with_changes();
		overlay.changes_trie_config = None;
		let storage = TestChangesTrieStorage::with_blocks(vec![(100, Default::default())]);
		let backend = TestBackend::default();
		let mut ext = TestExt::new(&mut overlay, &backend, Some(&storage), None, None);
		assert_eq!(ext.storage_changes_root(Default::default()).unwrap(), None);
	}

	#[test]
	fn storage_changes_root_is_some_when_extrinsic_changes_are_non_empty() {
		let mut overlay = prepare_overlay_with_changes();
		let storage = TestChangesTrieStorage::with_blocks(vec![(99, Default::default())]);
		let backend = TestBackend::default();
		let mut ext = TestExt::new(&mut overlay, &backend, Some(&storage), None, None);
		assert_eq!(
			ext.storage_changes_root(Default::default()).unwrap(),
			Some(hex!("bb0c2ef6e1d36d5490f9766cfcc7dfe2a6ca804504c3bb206053890d6dd02376").into()),
		);
	}

	#[test]
	fn storage_changes_root_is_some_when_extrinsic_changes_are_empty() {
		let mut overlay = prepare_overlay_with_changes();
		overlay.prospective.top.get_mut(&vec![1]).unwrap().value = None;
		let storage = TestChangesTrieStorage::with_blocks(vec![(99, Default::default())]);
		let backend = TestBackend::default();
		let mut ext = TestExt::new(&mut overlay, &backend, Some(&storage), None, None);
		assert_eq!(
			ext.storage_changes_root(Default::default()).unwrap(),
			Some(hex!("96f5aae4690e7302737b6f9b7f8567d5bbb9eac1c315f80101235a92d9ec27f4").into()),
		);
	}
}
