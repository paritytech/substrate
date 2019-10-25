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

use crate::{
	backend::Backend, OverlayedChanges,
	changes_trie::{
		Storage as ChangesTrieStorage, CacheAction as ChangesTrieCacheAction, build_changes_trie,
	},
};

use hash_db::Hasher;
use primitives::{
	storage::{ChildStorageKey, well_known_keys::is_child_storage_key},
	traits::Externalities, hexdisplay::HexDisplay, hash::H256,
};
use trie::{trie_types::Layout, MemoryDB, default_child_trie_root};
use externalities::Extensions;

use std::{error, fmt, any::{Any, TypeId}};
use log::{warn, trace};

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
pub struct Ext<'a, H, N, B, T> where H: Hasher<Out=H256>, B: 'a + Backend<H> {
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
	changes_trie_transaction: Option<(MemoryDB<H>, H::Out, ChangesTrieCacheAction<H::Out, N>)>,
	/// Pseudo-unique id used for tracing.
	pub id: u16,
	/// Dummy usage of N arg.
	_phantom: std::marker::PhantomData<N>,
	/// Extensions registered with this instance.
	extensions: Option<&'a mut Extensions>,
}

impl<'a, H, N, B, T> Ext<'a, H, N, B, T>
where
	H: Hasher<Out=H256>,
	B: 'a + Backend<H>,
	T: 'a + ChangesTrieStorage<H, N>,
	N: crate::changes_trie::BlockNumber,
{

	/// Create a new `Ext` from overlayed changes and read-only backend
	pub fn new(
		overlay: &'a mut OverlayedChanges,
		backend: &'a B,
		changes_trie_storage: Option<&'a T>,
		extensions: Option<&'a mut Extensions>,
	) -> Self {
		Ext {
			overlay,
			backend,
			storage_transaction: None,
			changes_trie_storage,
			changes_trie_transaction: None,
			id: rand::random(),
			_phantom: Default::default(),
			extensions,
		}
	}

	/// Get the transaction necessary to update the backend.
	pub fn transaction(&mut self) -> (
		(B::Transaction, H256),
		Option<crate::ChangesTrieTransaction<H, N>>,
	) {
		let _ = self.storage_root();

		let (storage_transaction, changes_trie_transaction) = (
			self.storage_transaction
				.take()
				.expect("storage_transaction always set after calling storage root; qed"),
			self.changes_trie_transaction
				.take()
				.map(|(tx, _, cache)| (tx, cache)),
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
impl<'a, H, N, B, T> Ext<'a, H, N, B, T>
where
	H: Hasher<Out=H256>,
	B: 'a + Backend<H>,
	T: 'a + ChangesTrieStorage<H, N>,
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

impl<'a, H, B, T, N> Externalities for Ext<'a, H, N, B, T>
where
	H: Hasher<Out=H256>,
	B: 'a + Backend<H>,
	T: 'a + ChangesTrieStorage<H, N>,
	N: crate::changes_trie::BlockNumber,
{
	fn storage(&self, key: &[u8]) -> Option<Vec<u8>> {
		let _guard = panic_handler::AbortGuard::force_abort();
		let result = self.overlay.storage(key).map(|x| x.map(|x| x.to_vec())).unwrap_or_else(||
			self.backend.storage(key).expect(EXT_NOT_ALLOWED_TO_FAIL));
		trace!(target: "state-trace", "{:04x}: Get {}={:?}",
			self.id,
			HexDisplay::from(&key),
			result.as_ref().map(HexDisplay::from)
		);
		result
	}

	fn storage_hash(&self, key: &[u8]) -> Option<H256> {
		let _guard = panic_handler::AbortGuard::force_abort();
		let result = self.overlay
			.storage(key)
			.map(|x| x.map(|x| H::hash(x)))
			.unwrap_or_else(||
				self.backend.storage_hash(key).expect(EXT_NOT_ALLOWED_TO_FAIL)
			);
		trace!(target: "state-trace", "{:04x}: Hash {}={:?}",
			self.id,
			HexDisplay::from(&key),
			result,
		);
		result
	}

	fn original_storage(&self, key: &[u8]) -> Option<Vec<u8>> {
		let _guard = panic_handler::AbortGuard::force_abort();
		let result = self.backend.storage(key).expect(EXT_NOT_ALLOWED_TO_FAIL);
		trace!(target: "state-trace", "{:04x}: GetOriginal {}={:?}",
			self.id,
			HexDisplay::from(&key),
			result.as_ref().map(HexDisplay::from)
		);
		result
	}

	fn original_storage_hash(&self, key: &[u8]) -> Option<H256> {
		let _guard = panic_handler::AbortGuard::force_abort();
		let result = self.backend.storage_hash(key).expect(EXT_NOT_ALLOWED_TO_FAIL);
		trace!(target: "state-trace", "{:04x}: GetOriginalHash {}={:?}",
			self.id,
			HexDisplay::from(&key),
			result,
		);
		result
	}

	fn child_storage(&self, storage_key: ChildStorageKey, key: &[u8]) -> Option<Vec<u8>> {
		let _guard = panic_handler::AbortGuard::force_abort();
		let result = self.overlay
			.child_storage(storage_key.as_ref(), key)
			.map(|x| x.map(|x| x.to_vec()))
			.unwrap_or_else(||
				self.backend.child_storage(storage_key.as_ref(), key).expect(EXT_NOT_ALLOWED_TO_FAIL)
			);

		trace!(target: "state-trace", "{:04x}: GetChild({}) {}={:?}",
			self.id,
			HexDisplay::from(&storage_key.as_ref()),
			HexDisplay::from(&key),
			result.as_ref().map(HexDisplay::from)
		);

		result
	}

	fn child_storage_hash(&self, storage_key: ChildStorageKey, key: &[u8]) -> Option<H256> {
		let _guard = panic_handler::AbortGuard::force_abort();
		let result = self.overlay
			.child_storage(storage_key.as_ref(), key)
			.map(|x| x.map(|x| H::hash(x)))
			.unwrap_or_else(||
				self.backend.storage_hash(key).expect(EXT_NOT_ALLOWED_TO_FAIL)
			);

		trace!(target: "state-trace", "{:04x}: ChildHash({}) {}={:?}",
			self.id,
			HexDisplay::from(&storage_key.as_ref()),
			HexDisplay::from(&key),
			result,
		);

		result
	}

	fn original_child_storage(&self, storage_key: ChildStorageKey, key: &[u8]) -> Option<Vec<u8>> {
		let _guard = panic_handler::AbortGuard::force_abort();
		let result = self.backend
			.child_storage(storage_key.as_ref(), key)
			.expect(EXT_NOT_ALLOWED_TO_FAIL);

		trace!(target: "state-trace", "{:04x}: ChildOriginal({}) {}={:?}",
			self.id,
			HexDisplay::from(&storage_key.as_ref()),
			HexDisplay::from(&key),
			result.as_ref().map(HexDisplay::from),
		);
		result
	}

	fn original_child_storage_hash(&self, storage_key: ChildStorageKey, key: &[u8]) -> Option<H256> {
		let _guard = panic_handler::AbortGuard::force_abort();
		let result = self.backend
			.child_storage_hash(storage_key.as_ref(), key)
			.expect(EXT_NOT_ALLOWED_TO_FAIL);

		trace!(target: "state-trace", "{}: ChildHashOriginal({}) {}={:?}",
			self.id,
			HexDisplay::from(&storage_key.as_ref()),
			HexDisplay::from(&key),
			result,
		);
		result
	}

	fn exists_storage(&self, key: &[u8]) -> bool {
		let _guard = panic_handler::AbortGuard::force_abort();
		let result = match self.overlay.storage(key) {
			Some(x) => x.is_some(),
			_ => self.backend.exists_storage(key).expect(EXT_NOT_ALLOWED_TO_FAIL),
		};

		trace!(target: "state-trace", "{:04x}: Exists {}={:?}",
			self.id,
			HexDisplay::from(&key),
			result,
		);
		result

	}

	fn exists_child_storage(&self, storage_key: ChildStorageKey, key: &[u8]) -> bool {
		let _guard = panic_handler::AbortGuard::force_abort();

		let result = match self.overlay.child_storage(storage_key.as_ref(), key) {
			Some(x) => x.is_some(),
			_ => self.backend
				.exists_child_storage(storage_key.as_ref(), key)
				.expect(EXT_NOT_ALLOWED_TO_FAIL),
		};

		trace!(target: "state-trace", "{:04x}: ChildExists({}) {}={:?}",
			self.id,
			HexDisplay::from(&storage_key.as_ref()),
			HexDisplay::from(&key),
			result,
		);
		result
	}

	fn place_storage(&mut self, key: Vec<u8>, value: Option<Vec<u8>>) {
		trace!(target: "state-trace", "{:04x}: Put {}={:?}",
			self.id,
			HexDisplay::from(&key),
			value.as_ref().map(HexDisplay::from)
		);
		let _guard = panic_handler::AbortGuard::force_abort();
		if is_child_storage_key(&key) {
			warn!(target: "trie", "Refuse to directly set child storage key");
			return;
		}

		self.mark_dirty();
		self.overlay.set_storage(key, value);
	}

	fn place_child_storage(
		&mut self,
		storage_key: ChildStorageKey,
		key: Vec<u8>,
		value: Option<Vec<u8>>,
	) {
		trace!(target: "state-trace", "{:04x}: PutChild({}) {}={:?}",
			self.id,
			HexDisplay::from(&storage_key.as_ref()),
			HexDisplay::from(&key),
			value.as_ref().map(HexDisplay::from)
		);
		let _guard = panic_handler::AbortGuard::force_abort();

		self.mark_dirty();
		self.overlay.set_child_storage(storage_key.into_owned(), key, value);
	}

	fn kill_child_storage(&mut self, storage_key: ChildStorageKey) {
		trace!(target: "state-trace", "{:04x}: KillChild({})",
			self.id,
			HexDisplay::from(&storage_key.as_ref()),
		);
		let _guard = panic_handler::AbortGuard::force_abort();

		self.mark_dirty();
		self.overlay.clear_child_storage(storage_key.as_ref());
		self.backend.for_keys_in_child_storage(storage_key.as_ref(), |key| {
			self.overlay.set_child_storage(storage_key.as_ref().to_vec(), key.to_vec(), None);
		});
	}

	fn clear_prefix(&mut self, prefix: &[u8]) {
		trace!(target: "state-trace", "{:04x}: ClearPrefix {}",
			self.id,
			HexDisplay::from(&prefix),
		);
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

	fn clear_child_prefix(&mut self, storage_key: ChildStorageKey, prefix: &[u8]) {
		trace!(target: "state-trace", "{:04x}: ClearChildPrefix({}) {}",
			self.id,
			HexDisplay::from(&storage_key.as_ref()),
			HexDisplay::from(&prefix),
		);
		let _guard = panic_handler::AbortGuard::force_abort();

		self.mark_dirty();
		self.overlay.clear_child_prefix(storage_key.as_ref(), prefix);
		self.backend.for_child_keys_with_prefix(storage_key.as_ref(), prefix, |key| {
			self.overlay.set_child_storage(storage_key.as_ref().to_vec(), key.to_vec(), None);
		});
	}

	fn chain_id(&self) -> u64 {
		42
	}

	fn storage_root(&mut self) -> H256 {
		let _guard = panic_handler::AbortGuard::force_abort();
		if let Some((_, ref root)) = self.storage_transaction {
			trace!(target: "state-trace", "{:04x}: Root (cached) {}",
				self.id,
				HexDisplay::from(&root.as_ref()),
			);
			return root.clone();
		}

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

		let (root, transaction) = self.backend.full_storage_root(delta, child_delta_iter);
		self.storage_transaction = Some((transaction, root));
		trace!(target: "state-trace", "{:04x}: Root {}",
			self.id,
			HexDisplay::from(&root.as_ref()),
		);
		root
	}

	fn child_storage_root(&mut self, storage_key: ChildStorageKey) -> Vec<u8> {
		let _guard = panic_handler::AbortGuard::force_abort();
		if self.storage_transaction.is_some() {
			let root = self
				.storage(storage_key.as_ref())
				.unwrap_or(
					default_child_trie_root::<Layout<H>>(storage_key.as_ref())
				);
			trace!(target: "state-trace", "{:04x}: ChildRoot({}) (cached) {}",
				self.id,
				HexDisplay::from(&storage_key.as_ref()),
				HexDisplay::from(&root.as_ref()),
			);
			root
		} else {
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

			trace!(target: "state-trace", "{:04x}: ChildRoot({}) {}",
				self.id,
				HexDisplay::from(&storage_key.as_ref()),
				HexDisplay::from(&root.as_ref()),
			);
			root

		}
	}

	fn storage_changes_root(&mut self, parent_hash: H256) -> Result<Option<H256>, ()> {
		let _guard = panic_handler::AbortGuard::force_abort();
		self.changes_trie_transaction = build_changes_trie::<_, T, H, N>(
			self.backend,
			self.changes_trie_storage.clone(),
			self.overlay,
			parent_hash,
		)?;
		let result = Ok(self.changes_trie_transaction.as_ref().map(|(_, root, _)| root.clone()));
		trace!(target: "state-trace", "{:04x}: ChangesRoot({}) {:?}",
			self.id,
			HexDisplay::from(&parent_hash.as_ref()),
			result,
		);
		result
	}
}

impl<'a, H, B, T, N> externalities::ExtensionStore for Ext<'a, H, N, B, T>
where
	H: Hasher<Out=H256>,
	B: 'a + Backend<H>,
	T: 'a + ChangesTrieStorage<H, N>,
	N: crate::changes_trie::BlockNumber,
{
	fn extension_by_type_id(&mut self, type_id: TypeId) -> Option<&mut dyn Any> {
		self.extensions.as_mut().and_then(|exts| exts.get_mut(type_id))
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use hex_literal::hex;
	use codec::Encode;
	use primitives::{Blake2Hasher, storage::well_known_keys::EXTRINSIC_INDEX};
	use crate::{
		changes_trie::{
			Configuration as ChangesTrieConfiguration,
			InMemoryStorage as InMemoryChangesTrieStorage,
		}, backend::InMemory, overlayed_changes::OverlayedValue,
	};

	type TestBackend = InMemory<Blake2Hasher>;
	type TestChangesTrieStorage = InMemoryChangesTrieStorage<Blake2Hasher, u64>;
	type TestExt<'a> = Ext<'a, Blake2Hasher, u64, TestBackend, TestChangesTrieStorage>;

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
		assert_eq!(ext.storage_changes_root(Default::default()).unwrap(), None);
	}

	#[test]
	fn storage_changes_root_is_none_when_extrinsic_changes_are_none() {
		let mut overlay = prepare_overlay_with_changes();
		overlay.changes_trie_config = None;
		let storage = TestChangesTrieStorage::with_blocks(vec![(100, Default::default())]);
		let backend = TestBackend::default();
		let mut ext = TestExt::new(&mut overlay, &backend, Some(&storage), None);
		assert_eq!(ext.storage_changes_root(Default::default()).unwrap(), None);
	}

	#[test]
	fn storage_changes_root_is_some_when_extrinsic_changes_are_non_empty() {
		let mut overlay = prepare_overlay_with_changes();
		let storage = TestChangesTrieStorage::with_blocks(vec![(99, Default::default())]);
		let backend = TestBackend::default();
		let mut ext = TestExt::new(&mut overlay, &backend, Some(&storage), None);
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
		let mut ext = TestExt::new(&mut overlay, &backend, Some(&storage), None);
		assert_eq!(
			ext.storage_changes_root(Default::default()).unwrap(),
			Some(hex!("96f5aae4690e7302737b6f9b7f8567d5bbb9eac1c315f80101235a92d9ec27f4").into()),
		);
	}
}
