// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Concrete externalities implementation.

use crate::{
	StorageKey, StorageValue, OverlayedChanges, IndexOperation,
	backend::Backend, overlayed_changes::OverlayedExtensions,
};
use hash_db::Hasher;
use sp_core::{
	storage::{well_known_keys::is_child_storage_key, ChildInfo, TrackedStorageKey},
	hexdisplay::HexDisplay,
};
use sp_trie::{trie_types::Layout, empty_child_trie_root};
use sp_externalities::{
	Externalities, Extensions, Extension, ExtensionStore,
};
use codec::{Decode, Encode, EncodeAppend};

use sp_std::{fmt, any::{Any, TypeId}, vec::Vec, vec, boxed::Box};
use crate::{warn, trace, log_error};
#[cfg(feature = "std")]
use crate::changes_trie::State as ChangesTrieState;
use crate::StorageTransactionCache;
#[cfg(feature = "std")]
use std::error;

const EXT_NOT_ALLOWED_TO_FAIL: &str = "Externalities not allowed to fail within runtime";
const BENCHMARKING_FN: &str = "\
	This is a special fn only for benchmarking where a database commit happens from the runtime.
	For that reason client started transactions before calling into runtime are not allowed.
	Without client transactions the loop condition garantuees the success of the tx close.";


#[cfg(feature = "std")]
fn guard() -> sp_panic_handler::AbortGuard {
	sp_panic_handler::AbortGuard::force_abort()
}

#[cfg(not(feature = "std"))]
fn guard() -> () {
	()
}

/// Errors that can occur when interacting with the externalities.
#[cfg(feature = "std")]
#[derive(Debug, Copy, Clone)]
pub enum Error<B, E> {
	/// Failure to load state data from the backend.
	#[allow(unused)]
	Backend(B),
	/// Failure to execute a function.
	#[allow(unused)]
	Executor(E),
}

#[cfg(feature = "std")]
impl<B: fmt::Display, E: fmt::Display> fmt::Display for Error<B, E> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match *self {
			Error::Backend(ref e) => write!(f, "Storage backend error: {}", e),
			Error::Executor(ref e) => write!(f, "Sub-call execution error: {}", e),
		}
	}
}

#[cfg(feature = "std")]
impl<B: error::Error, E: error::Error> error::Error for Error<B, E> {
	fn description(&self) -> &str {
		match *self {
			Error::Backend(..) => "backend error",
			Error::Executor(..) => "executor error",
		}
	}
}

/// Wraps a read-only backend, call executor, and current overlayed changes.
pub struct Ext<'a, H, N, B>
	where
		H: Hasher,
		B: 'a + Backend<H>,
		N: crate::changes_trie::BlockNumber,
{
	/// The overlayed changes to write to.
	overlay: &'a mut OverlayedChanges,
	/// The storage backend to read from.
	backend: &'a B,
	/// The cache for the storage transactions.
	storage_transaction_cache: &'a mut StorageTransactionCache<B::Transaction, H, N>,
	/// Changes trie state to read from.
	#[cfg(feature = "std")]
	changes_trie_state: Option<ChangesTrieState<'a, H, N>>,
	/// Pseudo-unique id used for tracing.
	pub id: u16,
	/// Dummy usage of N arg.
	_phantom: sp_std::marker::PhantomData<N>,
	/// Extensions registered with this instance.
	#[cfg(feature = "std")]
	extensions: Option<OverlayedExtensions<'a>>,
}


impl<'a, H, N, B> Ext<'a, H, N, B>
	where
		H: Hasher,
		B: Backend<H>,
		N: crate::changes_trie::BlockNumber,
{
	/// Create a new `Ext`.
	#[cfg(not(feature = "std"))]
	pub fn new(
		overlay: &'a mut OverlayedChanges,
		storage_transaction_cache: &'a mut StorageTransactionCache<B::Transaction, H, N>,
		backend: &'a B,
	) -> Self {
		Ext {
			overlay,
			backend,
			id: 0,
			storage_transaction_cache,
			_phantom: Default::default(),
		}
	}

	/// Create a new `Ext` from overlayed changes and read-only backend
	#[cfg(feature = "std")]
	pub fn new(
		overlay: &'a mut OverlayedChanges,
		storage_transaction_cache: &'a mut StorageTransactionCache<B::Transaction, H, N>,
		backend: &'a B,
		changes_trie_state: Option<ChangesTrieState<'a, H, N>>,
		extensions: Option<&'a mut Extensions>,
	) -> Self {
		Self {
			overlay,
			backend,
			changes_trie_state,
			storage_transaction_cache,
			id: rand::random(),
			_phantom: Default::default(),
			extensions: extensions.map(OverlayedExtensions::new),
		}
	}

	/// Invalidates the currently cached storage root and the db transaction.
	///
	/// Called when there are changes that likely will invalidate the storage root.
	fn mark_dirty(&mut self) {
		self.storage_transaction_cache.reset();
	}
}

#[cfg(test)]
impl<'a, H, N, B> Ext<'a, H, N, B>
where
	H: Hasher,
	H::Out: Ord + 'static,
	B: 'a + Backend<H>,
	N: crate::changes_trie::BlockNumber,
{
	pub fn storage_pairs(&self) -> Vec<(StorageKey, StorageValue)> {
		use std::collections::HashMap;

		self.backend.pairs().iter()
			.map(|&(ref k, ref v)| (k.to_vec(), Some(v.to_vec())))
			.chain(self.overlay.changes().map(|(k, v)| (k.clone(), v.value().cloned())))
			.collect::<HashMap<_, _>>()
			.into_iter()
			.filter_map(|(k, maybe_val)| maybe_val.map(|val| (k, val)))
			.collect()
	}
}

impl<'a, H, N, B> Externalities for Ext<'a, H, N, B>
where
	H: Hasher,
	H::Out: Ord + 'static + codec::Codec,
	B: Backend<H>,
	N: crate::changes_trie::BlockNumber,
{
	fn set_offchain_storage(&mut self, key: &[u8], value: Option<&[u8]>) {
		self.overlay.set_offchain_storage(key, value)
	}

	fn storage(&self, key: &[u8]) -> Option<StorageValue> {
		let _guard = guard();
		let result = self.overlay.storage(key).map(|x| x.map(|x| x.to_vec())).unwrap_or_else(||
			self.backend.storage(key).expect(EXT_NOT_ALLOWED_TO_FAIL));
		trace!(target: "state", "{:04x}: Get {}={:?}",
			self.id,
			HexDisplay::from(&key),
			result.as_ref().map(HexDisplay::from)
		);
		result
	}

	fn storage_hash(&self, key: &[u8]) -> Option<Vec<u8>> {
		let _guard = guard();
		let result = self.overlay
			.storage(key)
			.map(|x| x.map(|x| H::hash(x)))
			.unwrap_or_else(|| self.backend.storage_hash(key).expect(EXT_NOT_ALLOWED_TO_FAIL));

		trace!(target: "state", "{:04x}: Hash {}={:?}",
			self.id,
			HexDisplay::from(&key),
			result,
		);
		result.map(|r| r.encode())
	}

	fn child_storage(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Option<StorageValue> {
		let _guard = guard();
		let result = self.overlay
			.child_storage(child_info, key)
			.map(|x| x.map(|x| x.to_vec()))
			.unwrap_or_else(||
				self.backend.child_storage(child_info, key)
					.expect(EXT_NOT_ALLOWED_TO_FAIL)
			);

		trace!(target: "state", "{:04x}: GetChild({}) {}={:?}",
			self.id,
			HexDisplay::from(&child_info.storage_key()),
			HexDisplay::from(&key),
			result.as_ref().map(HexDisplay::from)
		);

		result
	}

	fn child_storage_hash(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Option<Vec<u8>> {
		let _guard = guard();
		let result = self.overlay
			.child_storage(child_info, key)
			.map(|x| x.map(|x| H::hash(x)))
			.unwrap_or_else(||
				self.backend.child_storage_hash(child_info, key)
					.expect(EXT_NOT_ALLOWED_TO_FAIL)
			);

		trace!(target: "state", "{:04x}: ChildHash({}) {}={:?}",
			self.id,
			HexDisplay::from(&child_info.storage_key()),
			HexDisplay::from(&key),
			result,
		);

		result.map(|r| r.encode())
	}

	fn exists_storage(&self, key: &[u8]) -> bool {
		let _guard = guard();
		let result = match self.overlay.storage(key) {
			Some(x) => x.is_some(),
			_ => self.backend.exists_storage(key).expect(EXT_NOT_ALLOWED_TO_FAIL),
		};

		trace!(target: "state", "{:04x}: Exists {}={:?}",
			self.id,
			HexDisplay::from(&key),
			result,
		);

		result
	}

	fn exists_child_storage(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> bool {
		let _guard = guard();

		let result = match self.overlay.child_storage(child_info, key) {
			Some(x) => x.is_some(),
			_ => self.backend
				.exists_child_storage(child_info, key)
				.expect(EXT_NOT_ALLOWED_TO_FAIL),
		};

		trace!(target: "state", "{:04x}: ChildExists({}) {}={:?}",
			self.id,
			HexDisplay::from(&child_info.storage_key()),
			HexDisplay::from(&key),
			result,
		);
		result
	}

	fn next_storage_key(&self, key: &[u8]) -> Option<StorageKey> {
		let next_backend_key = self.backend.next_storage_key(key).expect(EXT_NOT_ALLOWED_TO_FAIL);
		let next_overlay_key_change = self.overlay.next_storage_key_change(key);

		match (next_backend_key, next_overlay_key_change) {
			(Some(backend_key), Some(overlay_key)) if &backend_key[..] < overlay_key.0 => Some(backend_key),
			(backend_key, None) => backend_key,
			(_, Some(overlay_key)) => if overlay_key.1.value().is_some() {
				Some(overlay_key.0.to_vec())
			} else {
				self.next_storage_key(&overlay_key.0[..])
			},
		}
	}

	fn next_child_storage_key(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Option<StorageKey> {
		let next_backend_key = self.backend
			.next_child_storage_key(child_info, key)
			.expect(EXT_NOT_ALLOWED_TO_FAIL);
		let next_overlay_key_change = self.overlay.next_child_storage_key_change(
			child_info.storage_key(),
			key
		);

		match (next_backend_key, next_overlay_key_change) {
			(Some(backend_key), Some(overlay_key)) if &backend_key[..] < overlay_key.0 => Some(backend_key),
			(backend_key, None) => backend_key,
			(_, Some(overlay_key)) => if overlay_key.1.value().is_some() {
				Some(overlay_key.0.to_vec())
			} else {
				self.next_child_storage_key(
					child_info,
					&overlay_key.0[..],
				)
			},
		}
	}

	fn place_storage(&mut self, key: StorageKey, value: Option<StorageValue>) {
		trace!(target: "state", "{:04x}: Put {}={:?}",
			self.id,
			HexDisplay::from(&key),
			value.as_ref().map(HexDisplay::from)
		);
		let _guard = guard();
		if is_child_storage_key(&key) {
			warn!(target: "trie", "Refuse to directly set child storage key");
			return;
		}

		self.mark_dirty();
		self.overlay.set_storage(key, value);
	}

	fn place_child_storage(
		&mut self,
		child_info: &ChildInfo,
		key: StorageKey,
		value: Option<StorageValue>,
	) {
		trace!(target: "state", "{:04x}: PutChild({}) {}={:?}",
			self.id,
			HexDisplay::from(&child_info.storage_key()),
			HexDisplay::from(&key),
			value.as_ref().map(HexDisplay::from)
		);
		let _guard = guard();

		self.mark_dirty();
		self.overlay.set_child_storage(child_info, key, value);
	}

	fn kill_child_storage(
		&mut self,
		child_info: &ChildInfo,
		limit: Option<u32>,
	) -> (bool, u32) {
		trace!(target: "state", "{:04x}: KillChild({})",
			self.id,
			HexDisplay::from(&child_info.storage_key()),
		);
		let _guard = guard();
		self.mark_dirty();
		self.overlay.clear_child_storage(child_info);
		let mut num_deleted: u32 = 0;

		if let Some(limit) = limit {
			let mut all_deleted = true;
			self.backend.apply_to_child_keys_while(child_info, |key| {
				if num_deleted == limit {
					all_deleted = false;
					return false;
				}
				if let Some(num) = num_deleted.checked_add(1) {
					num_deleted = num;
				} else {
					all_deleted = false;
					return false;
				}
				self.overlay.set_child_storage(child_info, key.to_vec(), None);
				true
			});
			(all_deleted, num_deleted)
		} else {
			self.backend.apply_to_child_keys_while(child_info, |key| {
				num_deleted = num_deleted.saturating_add(1);
				self.overlay.set_child_storage(child_info, key.to_vec(), None);
				true
			});
			(true, num_deleted)
		}
	}

	fn clear_prefix(&mut self, prefix: &[u8]) {
		trace!(target: "state", "{:04x}: ClearPrefix {}",
			self.id,
			HexDisplay::from(&prefix),
		);
		let _guard = guard();

		if sp_core::storage::well_known_keys::starts_with_child_storage_key(prefix) {
			warn!(target: "trie", "Refuse to directly clear prefix that is part or contains of child storage key");
			return;
		}

		self.mark_dirty();
		self.overlay.clear_prefix(prefix);
		self.backend.for_keys_with_prefix(prefix, |key| {
			self.overlay.set_storage(key.to_vec(), None);
		});
	}

	fn clear_child_prefix(
		&mut self,
		child_info: &ChildInfo,
		prefix: &[u8],
	) {
		trace!(target: "state", "{:04x}: ClearChildPrefix({}) {}",
			self.id,
			HexDisplay::from(&child_info.storage_key()),
			HexDisplay::from(&prefix),
		);
		let _guard = guard();

		self.mark_dirty();
		self.overlay.clear_child_prefix(child_info, prefix);
		self.backend.for_child_keys_with_prefix(child_info, prefix, |key| {
			self.overlay.set_child_storage(child_info, key.to_vec(), None);
		});
	}

	fn storage_append(
		&mut self,
		key: Vec<u8>,
		value: Vec<u8>,
	) {
		trace!(target: "state", "{:04x}: Append {}={}",
			self.id,
			HexDisplay::from(&key),
			HexDisplay::from(&value),
		);

		let _guard = guard();
		self.mark_dirty();

		let backend = &mut self.backend;
		let current_value = self.overlay.value_mut_or_insert_with(
			&key,
			|| backend.storage(&key).expect(EXT_NOT_ALLOWED_TO_FAIL).unwrap_or_default()
		);
		StorageAppend::new(current_value).append(value);
	}

	fn storage_root(&mut self) -> Vec<u8> {
		let _guard = guard();
		if let Some(ref root) = self.storage_transaction_cache.transaction_storage_root {
			trace!(target: "state", "{:04x}: Root(cached) {}",
				self.id,
				HexDisplay::from(&root.as_ref()),
			);
			return root.encode();
		}

		let root = self.overlay.storage_root(self.backend, self.storage_transaction_cache);
		trace!(target: "state", "{:04x}: Root {}", self.id, HexDisplay::from(&root.as_ref()));
		root.encode()
	}

	fn child_storage_root(
		&mut self,
		child_info: &ChildInfo,
	) -> Vec<u8> {
		let _guard = guard();
		let storage_key = child_info.storage_key();
		let prefixed_storage_key = child_info.prefixed_storage_key();
		if self.storage_transaction_cache.transaction_storage_root.is_some() {
			let root = self
				.storage(prefixed_storage_key.as_slice())
				.and_then(|k| Decode::decode(&mut &k[..]).ok())
				.unwrap_or_else(
					|| empty_child_trie_root::<Layout<H>>()
				);
			trace!(target: "state", "{:04x}: ChildRoot({})(cached) {}",
				self.id,
				HexDisplay::from(&storage_key),
				HexDisplay::from(&root.as_ref()),
			);
			root.encode()
		} else {
			let root = if let Some((changes, info)) = self.overlay.child_changes(storage_key) {
				let delta = changes.map(|(k, v)| (k.as_ref(), v.value().map(AsRef::as_ref)));
				Some(self.backend.child_storage_root(info, delta))
			} else {
				None
			};

			if let Some((root, is_empty, _)) = root {
				let root = root.encode();
				// We store update in the overlay in order to be able to use 'self.storage_transaction'
				// cache. This is brittle as it rely on Ext only querying the trie backend for
				// storage root.
				// A better design would be to manage 'child_storage_transaction' in a
				// similar way as 'storage_transaction' but for each child trie.
				if is_empty {
					self.overlay.set_storage(prefixed_storage_key.into_inner(), None);
				} else {
					self.overlay.set_storage(prefixed_storage_key.into_inner(), Some(root.clone()));
				}

				trace!(target: "state", "{:04x}: ChildRoot({}) {}",
					self.id,
					HexDisplay::from(&storage_key.as_ref()),
					HexDisplay::from(&root.as_ref()),
				);
				root
			} else {
				// empty overlay
				let root = self
					.storage(prefixed_storage_key.as_slice())
					.and_then(|k| Decode::decode(&mut &k[..]).ok())
					.unwrap_or_else(
						|| empty_child_trie_root::<Layout<H>>()
					);
				trace!(target: "state", "{:04x}: ChildRoot({})(no_change) {}",
					self.id,
					HexDisplay::from(&storage_key.as_ref()),
					HexDisplay::from(&root.as_ref()),
				);
				root.encode()
			}
		}
	}

	fn storage_index_transaction(&mut self, index: u32, offset: u32) {
		trace!(
			target: "state",
			"{:04x}: IndexTransaction ({}): [{}..]",
			self.id,
			index,
			offset,
		);
		self.overlay.add_transaction_index(IndexOperation::Insert {
			extrinsic: index,
			offset,
		});
	}

	/// Renew existing piece of data storage.
	fn storage_renew_transaction_index(&mut self, index: u32, hash: &[u8], size: u32) {
		trace!(
			target: "state",
			"{:04x}: RenewTransactionIndex ({}) {} bytes",
			self.id,
			HexDisplay::from(&hash),
			size,
		);
		self.overlay.add_transaction_index(IndexOperation::Renew {
			extrinsic: index,
			hash: hash.to_vec(),
			size
		});
	}

	#[cfg(not(feature = "std"))]
	fn storage_changes_root(&mut self, _parent_hash: &[u8]) -> Result<Option<Vec<u8>>, ()> {
		Ok(None)
	}

	#[cfg(feature = "std")]
	fn storage_changes_root(&mut self, parent_hash: &[u8]) -> Result<Option<Vec<u8>>, ()> {
		let _guard = guard();
		if let Some(ref root) = self.storage_transaction_cache.changes_trie_transaction_storage_root {
			trace!(
				target: "state",
				"{:04x}: ChangesRoot({})(cached) {:?}",
				self.id,
				HexDisplay::from(&parent_hash),
				root,
			);

			Ok(Some(root.encode()))
		} else {
			let root = self.overlay.changes_trie_root(
				self.backend,
				self.changes_trie_state.as_ref(),
				Decode::decode(&mut &parent_hash[..]).map_err(|e|
					trace!(
						target: "state",
						"Failed to decode changes root parent hash: {}",
						e,
					)
				)?,
				true,
				self.storage_transaction_cache,
			);

			trace!(
				target: "state",
				"{:04x}: ChangesRoot({}) {:?}",
				self.id,
				HexDisplay::from(&parent_hash),
				root,
			);

			root.map(|r| r.map(|o| o.encode()))
		}
	}

	fn storage_start_transaction(&mut self) {
		self.overlay.start_transaction()
	}

	fn storage_rollback_transaction(&mut self) -> Result<(), ()> {
		self.mark_dirty();
		self.overlay.rollback_transaction().map_err(|_| ())
	}

	fn storage_commit_transaction(&mut self) -> Result<(), ()> {
		self.overlay.commit_transaction().map_err(|_| ())
	}

	fn wipe(&mut self) {
		for _ in 0..self.overlay.transaction_depth() {
			self.overlay.rollback_transaction().expect(BENCHMARKING_FN);
		}
		self.overlay.drain_storage_changes(
			&self.backend,
			#[cfg(feature = "std")]
			None,
			Default::default(),
			self.storage_transaction_cache,
		).expect(EXT_NOT_ALLOWED_TO_FAIL);
		self.backend.wipe().expect(EXT_NOT_ALLOWED_TO_FAIL);
		self.mark_dirty();
		self.overlay
			.enter_runtime()
			.expect("We have reset the overlay above, so we can not be in the runtime; qed");
	}

	fn commit(&mut self) {
		for _ in 0..self.overlay.transaction_depth() {
			self.overlay.commit_transaction().expect(BENCHMARKING_FN);
		}
		let changes = self.overlay.drain_storage_changes(
			&self.backend,
			#[cfg(feature = "std")]
			None,
			Default::default(),
			self.storage_transaction_cache,
		).expect(EXT_NOT_ALLOWED_TO_FAIL);
		self.backend.commit(
			changes.transaction_storage_root,
			changes.transaction,
			changes.main_storage_changes,
			changes.child_storage_changes,
		).expect(EXT_NOT_ALLOWED_TO_FAIL);
		self.mark_dirty();
		self.overlay
			.enter_runtime()
			.expect("We have reset the overlay above, so we can not be in the runtime; qed");
	}

	fn read_write_count(&self) -> (u32, u32, u32, u32) {
		self.backend.read_write_count()
	}

	fn reset_read_write_count(&mut self) {
		self.backend.reset_read_write_count()
	}

	fn get_whitelist(&self) -> Vec<TrackedStorageKey> {
		self.backend.get_whitelist()
	}

	fn set_whitelist(&mut self, new: Vec<TrackedStorageKey>) {
		self.backend.set_whitelist(new)
	}

	fn proof_size(&self) -> Option<u32> {
		self.backend.proof_size()
	}
}

/// Implement `Encode` by forwarding the stored raw vec.
struct EncodeOpaqueValue(Vec<u8>);

impl Encode for EncodeOpaqueValue {
	fn using_encoded<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
		f(&self.0)
	}
}

/// Auxialiary structure for appending a value to a storage item.
pub(crate) struct StorageAppend<'a>(&'a mut Vec<u8>);

impl<'a> StorageAppend<'a> {
	/// Create a new instance using the given `storage` reference.
	pub fn new(storage: &'a mut Vec<u8>) -> Self {
		Self(storage)
	}

	/// Append the given `value` to the storage item.
	///
	/// If appending fails, `[value]` is stored in the storage item.
	pub fn append(&mut self, value: Vec<u8>) {
		let value = vec![EncodeOpaqueValue(value)];

		let item = sp_std::mem::take(self.0);

		*self.0 = match Vec::<EncodeOpaqueValue>::append_or_new(item, &value) {
			Ok(item) => item,
			Err(_) => {
				log_error!(
					target: "runtime",
					"Failed to append value, resetting storage item to `[value]`.",
				);
				value.encode()
			}
		};
	}
}

#[cfg(not(feature = "std"))]
impl<'a, H, N, B> ExtensionStore for Ext<'a, H, N, B>
where
	H: Hasher,
	H::Out: Ord + 'static + codec::Codec,
	B: Backend<H>,
	N: crate::changes_trie::BlockNumber,
{
	fn extension_by_type_id(&mut self, _type_id: TypeId) -> Option<&mut dyn Any> {
		None
	}

	fn register_extension_with_type_id(
		&mut self,
		_type_id: TypeId,
		_extension: Box<dyn Extension>,
	) -> Result<(), sp_externalities::Error> {
		Err(sp_externalities::Error::ExtensionsAreNotSupported)
	}

	fn deregister_extension_by_type_id(
		&mut self,
		_type_id: TypeId,
	) -> Result<(), sp_externalities::Error> {
		Err(sp_externalities::Error::ExtensionsAreNotSupported)
	}
}

#[cfg(feature = "std")]
impl<'a, H, N, B> ExtensionStore for Ext<'a, H, N, B>
where
	H: Hasher,
	B: 'a + Backend<H>,
	N: crate::changes_trie::BlockNumber,
{
	fn extension_by_type_id(&mut self, type_id: TypeId) -> Option<&mut dyn Any> {
		self.extensions.as_mut().and_then(|exts| exts.get_mut(type_id))
	}

	fn register_extension_with_type_id(
		&mut self,
		type_id: TypeId,
		extension: Box<dyn Extension>,
	) -> Result<(), sp_externalities::Error> {
		if let Some(ref mut extensions) = self.extensions {
			extensions.register(type_id, extension)
		} else {
			Err(sp_externalities::Error::ExtensionsAreNotSupported)
		}
	}

	fn deregister_extension_by_type_id(&mut self, type_id: TypeId) -> Result<(), sp_externalities::Error> {
		if let Some(ref mut extensions) = self.extensions {
			if extensions.deregister(type_id) {
				Ok(())
			} else {
				Err(sp_externalities::Error::ExtensionIsNotRegistered(type_id))
			}
		} else {
			Err(sp_externalities::Error::ExtensionsAreNotSupported)
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use hex_literal::hex;
	use num_traits::Zero;
	use codec::Encode;
	use sp_core::{
		H256,
		Blake2Hasher,
		map,
		storage::{
			Storage,
			StorageChild,
			well_known_keys::EXTRINSIC_INDEX,
		},
	};
	use crate::{
		changes_trie::{
			Configuration as ChangesTrieConfiguration,
			InMemoryStorage as TestChangesTrieStorage,
		}, InMemoryBackend,
	};

	type TestBackend = InMemoryBackend<Blake2Hasher>;
	type TestExt<'a> = Ext<'a, Blake2Hasher, u64, TestBackend>;

	fn prepare_overlay_with_changes() -> OverlayedChanges {
		let mut changes = OverlayedChanges::default();
		changes.set_collect_extrinsics(true);
		changes.set_extrinsic_index(1);
		changes.set_storage(vec![1], Some(vec![100]));
		changes.set_storage(EXTRINSIC_INDEX.to_vec(), Some(3u32.encode()));
		changes.set_offchain_storage(b"k1", Some(b"v1"));
		changes.set_offchain_storage(b"k2", Some(b"v2"));
		changes
	}

	fn changes_trie_config() -> ChangesTrieConfiguration {
		ChangesTrieConfiguration {
			digest_interval: 0,
			digest_levels: 0,
		}
	}

	#[test]
	fn storage_changes_root_is_none_when_storage_is_not_provided() {
		let mut overlay = prepare_overlay_with_changes();
		let mut cache = StorageTransactionCache::default();
		let backend = TestBackend::default();
		let mut ext = TestExt::new(&mut overlay, &mut cache, &backend, None, None);
		assert_eq!(ext.storage_changes_root(&H256::default().encode()).unwrap(), None);
	}

	#[test]
	fn storage_changes_root_is_none_when_state_is_not_provided() {
		let mut overlay = prepare_overlay_with_changes();
		let mut cache = StorageTransactionCache::default();
		let backend = TestBackend::default();
		let mut ext = TestExt::new(&mut overlay, &mut cache, &backend, None, None);
		assert_eq!(ext.storage_changes_root(&H256::default().encode()).unwrap(), None);
	}

	#[test]
	fn storage_changes_root_is_some_when_extrinsic_changes_are_non_empty() {
		let mut overlay = prepare_overlay_with_changes();
		let mut cache = StorageTransactionCache::default();
		let storage = TestChangesTrieStorage::with_blocks(vec![(99, Default::default())]);
		let state = Some(ChangesTrieState::new(changes_trie_config(), Zero::zero(), &storage));
		let backend = TestBackend::default();
		let mut ext = TestExt::new(&mut overlay, &mut cache, &backend, state, None);
		assert_eq!(
			ext.storage_changes_root(&H256::default().encode()).unwrap(),
			Some(hex!("bb0c2ef6e1d36d5490f9766cfcc7dfe2a6ca804504c3bb206053890d6dd02376").to_vec()),
		);
	}

	#[test]
	fn storage_changes_root_is_some_when_extrinsic_changes_are_empty() {
		let mut overlay = prepare_overlay_with_changes();
		let mut cache = StorageTransactionCache::default();
		overlay.set_collect_extrinsics(false);
		overlay.set_storage(vec![1], None);
		let storage = TestChangesTrieStorage::with_blocks(vec![(99, Default::default())]);
		let state = Some(ChangesTrieState::new(changes_trie_config(), Zero::zero(), &storage));
		let backend = TestBackend::default();
		let mut ext = TestExt::new(&mut overlay, &mut cache, &backend, state, None);
		assert_eq!(
			ext.storage_changes_root(&H256::default().encode()).unwrap(),
			Some(hex!("96f5aae4690e7302737b6f9b7f8567d5bbb9eac1c315f80101235a92d9ec27f4").to_vec()),
		);
	}

	#[test]
	fn next_storage_key_works() {
		let mut cache = StorageTransactionCache::default();
		let mut overlay = OverlayedChanges::default();
		overlay.set_storage(vec![20], None);
		overlay.set_storage(vec![30], Some(vec![31]));
		let backend = Storage {
			top: map![
				vec![10] => vec![10],
				vec![20] => vec![20],
				vec![40] => vec![40]
			],
			children_default: map![]
		}.into();

		let ext = TestExt::new(&mut overlay, &mut cache, &backend, None, None);

		// next_backend < next_overlay
		assert_eq!(ext.next_storage_key(&[5]), Some(vec![10]));

		// next_backend == next_overlay but next_overlay is a delete
		assert_eq!(ext.next_storage_key(&[10]), Some(vec![30]));

		// next_overlay < next_backend
		assert_eq!(ext.next_storage_key(&[20]), Some(vec![30]));

		// next_backend exist but next_overlay doesn't exist
		assert_eq!(ext.next_storage_key(&[30]), Some(vec![40]));

		drop(ext);
		overlay.set_storage(vec![50], Some(vec![50]));
		let ext = TestExt::new(&mut overlay, &mut cache, &backend, None, None);

		// next_overlay exist but next_backend doesn't exist
		assert_eq!(ext.next_storage_key(&[40]), Some(vec![50]));
	}

	#[test]
	fn next_child_storage_key_works() {
		let child_info = ChildInfo::new_default(b"Child1");
		let child_info = &child_info;

		let mut cache = StorageTransactionCache::default();
		let mut overlay = OverlayedChanges::default();
		overlay.set_child_storage(child_info, vec![20], None);
		overlay.set_child_storage(child_info, vec![30], Some(vec![31]));
		let backend = Storage {
			top: map![],
			children_default: map![
				child_info.storage_key().to_vec() => StorageChild {
					data: map![
						vec![10] => vec![10],
						vec![20] => vec![20],
						vec![40] => vec![40]
					],
					child_info: child_info.to_owned(),
				}
			],
		}.into();

		let ext = TestExt::new(&mut overlay, &mut cache, &backend, None, None);

		// next_backend < next_overlay
		assert_eq!(ext.next_child_storage_key(child_info, &[5]), Some(vec![10]));

		// next_backend == next_overlay but next_overlay is a delete
		assert_eq!(ext.next_child_storage_key(child_info, &[10]), Some(vec![30]));

		// next_overlay < next_backend
		assert_eq!(ext.next_child_storage_key(child_info, &[20]), Some(vec![30]));

		// next_backend exist but next_overlay doesn't exist
		assert_eq!(ext.next_child_storage_key(child_info, &[30]), Some(vec![40]));

		drop(ext);
		overlay.set_child_storage(child_info, vec![50], Some(vec![50]));
		let ext = TestExt::new(&mut overlay, &mut cache, &backend, None, None);

		// next_overlay exist but next_backend doesn't exist
		assert_eq!(ext.next_child_storage_key(child_info, &[40]), Some(vec![50]));
	}

	#[test]
	fn child_storage_works() {
		let child_info = ChildInfo::new_default(b"Child1");
		let child_info = &child_info;
		let mut cache = StorageTransactionCache::default();
		let mut overlay = OverlayedChanges::default();
		overlay.set_child_storage(child_info, vec![20], None);
		overlay.set_child_storage(child_info, vec![30], Some(vec![31]));
		let backend = Storage {
			top: map![],
			children_default: map![
				child_info.storage_key().to_vec() => StorageChild {
					data: map![
						vec![10] => vec![10],
						vec![20] => vec![20],
						vec![30] => vec![40]
					],
					child_info: child_info.to_owned(),
				}
			],
		}.into();

		let ext = TestExt::new(&mut overlay, &mut cache, &backend, None, None);

		assert_eq!(ext.child_storage(child_info, &[10]), Some(vec![10]));
		assert_eq!(
			ext.child_storage_hash(child_info, &[10]),
			Some(Blake2Hasher::hash(&[10]).as_ref().to_vec()),
		);

		assert_eq!(ext.child_storage(child_info, &[20]), None);
		assert_eq!(
			ext.child_storage_hash(child_info, &[20]),
			None,
		);

		assert_eq!(ext.child_storage(child_info, &[30]), Some(vec![31]));
		assert_eq!(
			ext.child_storage_hash(child_info, &[30]),
			Some(Blake2Hasher::hash(&[31]).as_ref().to_vec()),
		);
	}

	#[test]
	fn clear_prefix_cannot_delete_a_child_root() {
		let child_info = ChildInfo::new_default(b"Child1");
		let child_info = &child_info;
		let mut cache = StorageTransactionCache::default();
		let mut overlay = OverlayedChanges::default();
		let backend = Storage {
			top: map![],
			children_default: map![
				child_info.storage_key().to_vec() => StorageChild {
					data: map![
						vec![30] => vec![40]
					],
					child_info: child_info.to_owned(),
				}
			],
		}.into();

		let ext = TestExt::new(&mut overlay, &mut cache, &backend, None, None);

		use sp_core::storage::well_known_keys;
		let mut ext = ext;
		let mut not_under_prefix = well_known_keys::CHILD_STORAGE_KEY_PREFIX.to_vec();
		not_under_prefix[4] = 88;
		not_under_prefix.extend(b"path");
		ext.set_storage(not_under_prefix.clone(), vec![10]);

		ext.clear_prefix(&[]);
		ext.clear_prefix(&well_known_keys::CHILD_STORAGE_KEY_PREFIX[..4]);
		let mut under_prefix = well_known_keys::CHILD_STORAGE_KEY_PREFIX.to_vec();
		under_prefix.extend(b"path");
		ext.clear_prefix(&well_known_keys::CHILD_STORAGE_KEY_PREFIX[..4]);
		assert_eq!(ext.child_storage(child_info, &[30]), Some(vec![40]));
		assert_eq!(ext.storage(not_under_prefix.as_slice()), Some(vec![10]));
		ext.clear_prefix(&not_under_prefix[..5]);
		assert_eq!(ext.storage(not_under_prefix.as_slice()), None);
	}

	#[test]
	fn storage_append_works() {
		let mut data = Vec::new();
		let mut append = StorageAppend::new(&mut data);
		append.append(1u32.encode());
		append.append(2u32.encode());
		drop(append);

		assert_eq!(Vec::<u32>::decode(&mut &data[..]).unwrap(), vec![1, 2]);

		// Initialize with some invalid data
		let mut data = vec![1];
		let mut append = StorageAppend::new(&mut data);
		append.append(1u32.encode());
		append.append(2u32.encode());
		drop(append);

		assert_eq!(Vec::<u32>::decode(&mut &data[..]).unwrap(), vec![1, 2]);
	}
}
