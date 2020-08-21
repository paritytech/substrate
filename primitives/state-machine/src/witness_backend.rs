// This file is part of Substrate.

// Copyright (C) 2017-2020 Parity Technologies (UK) Ltd.
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

//! Substrate backend runing on a trie proof, no_std compatible.

use hash_db::Hasher;
use sp_externalities::{Externalities, ExtensionStore, Error, Extension};
use sp_core::storage::{ChildInfo, TrackedStorageKey};
use sp_std::{any::{TypeId, Any}};
use sp_std::boxed::Box;
use sp_std::vec::Vec;
use sp_trie::MemoryDB;
use crate::trie_backend::TrieBackend;


// TODO replace with use crate::StorageValue;
pub type StorageValue = Vec<u8>;
// TODO replace with use crate::StorageKey;
pub type StorageKey = Vec<u8>;
/// The backend runnig on a trie proof.
pub struct WitnessBackend<H: Hasher> {
//	overlay: OverlayedChangesNoChangeTrie,
	trie: TrieBackend<MemoryDB<H>, H>,
}

impl<H: Hasher> WitnessBackend<H>
	where
		H: Hasher,
		H::Out: Ord + 'static + codec::Codec,
{
	/// Create a new backend.
	pub fn new(db: MemoryDB<H>, root: H::Out) -> Self {
		WitnessBackend {
			trie: TrieBackend::new(db, root),
		}
	}
}

impl<H> Externalities for WitnessBackend<H>
	where
		H: Hasher,
		H::Out: Ord + 'static + codec::Codec,
{
	fn set_offchain_storage(&mut self, _key: &[u8], _value: Option<&[u8]>) {
		// no ops
	}

	fn storage(&self, key: &[u8]) -> Option<StorageValue> {
		unimplemented!()
/*		let result = self.overlay.storage(key).map(|x| x.map(|x| x.to_vec())).unwrap_or_else(||
			self.backend.storage(key).expect(EXT_NOT_ALLOWED_TO_FAIL));
		trace!(target: "state", "{:04x}: Get {}={:?}",
			self.id,
			HexDisplay::from(&key),
			result.as_ref().map(HexDisplay::from)
		);
		result*/
	}

	fn storage_hash(&self, key: &[u8]) -> Option<Vec<u8>> {
		unimplemented!()
/*		let result = self.overlay
			.storage(key)
			.map(|x| x.map(|x| H::hash(x)))
			.unwrap_or_else(|| self.backend.storage_hash(key).expect(EXT_NOT_ALLOWED_TO_FAIL));

		result.map(|r| r.encode())*/
	}

	fn child_storage(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Option<StorageValue> {
		unimplemented!()
/*		let result = self.overlay
			.child_storage(child_info, key)
			.map(|x| x.map(|x| x.to_vec()))
			.unwrap_or_else(||
				self.backend.child_storage(child_info, key)
					.expect(EXT_NOT_ALLOWED_TO_FAIL)
			);

		result
*/
	}

	fn child_storage_hash(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Option<Vec<u8>> {
		unimplemented!()
/*		let result = self.overlay
			.child_storage(child_info, key)
			.map(|x| x.map(|x| H::hash(x)))
			.unwrap_or_else(||
				self.backend.child_storage_hash(child_info, key)
					.expect(EXT_NOT_ALLOWED_TO_FAIL)
			);
		result.map(|r| r.encode())
*/
	}

	fn exists_storage(&self, key: &[u8]) -> bool {
		unimplemented!()
/*let result = match self.overlay.storage(key) {
			Some(x) => x.is_some(),
			_ => self.backend.exists_storage(key).expect(EXT_NOT_ALLOWED_TO_FAIL),
		};

		result*/
	}

	fn exists_child_storage(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> bool {
		unimplemented!()
/*
		let result = match self.overlay.child_storage(child_info, key) {
			Some(x) => x.is_some(),
			_ => self.backend
				.exists_child_storage(child_info, key)
				.expect(EXT_NOT_ALLOWED_TO_FAIL),
		};
		result*/
	}

	fn next_storage_key(&self, key: &[u8]) -> Option<StorageKey> {
		unimplemented!()
		/*
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
		*/
	}

	fn next_child_storage_key(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Option<StorageKey> {
		unimplemented!()
/*		let next_backend_key = self.backend
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
		}*/
	}

	fn place_storage(&mut self, key: StorageKey, value: Option<StorageValue>) {
		unimplemented!()
/*		if is_child_storage_key(&key) {
			return;
		}

		self.mark_dirty();
		self.overlay.set_storage(key, value);*/
	}

	fn place_child_storage(
		&mut self,
		child_info: &ChildInfo,
		key: StorageKey,
		value: Option<StorageValue>,
	) {
		unimplemented!()
/*
		self.mark_dirty();
		self.overlay.set_child_storage(child_info, key, value);
*/
	}

	fn kill_child_storage(
		&mut self,
		child_info: &ChildInfo,
	) {
		unimplemented!()
			/*
		self.mark_dirty();
		self.overlay.clear_child_storage(child_info);
		self.backend.for_keys_in_child_storage(child_info, |key| {
			self.overlay.set_child_storage(child_info, key.to_vec(), None);
		});
			*/
	}

	fn clear_prefix(&mut self, prefix: &[u8]) {
		unimplemented!()
/*
		if is_child_storage_key(prefix) {
			return;
		}

		self.mark_dirty();
		self.overlay.clear_prefix(prefix);
		self.backend.for_keys_with_prefix(prefix, |key| {
			self.overlay.set_storage(key.to_vec(), None);
		});
*/
	}

	fn clear_child_prefix(
		&mut self,
		child_info: &ChildInfo,
		prefix: &[u8],
	) {
		unimplemented!()
/*
		self.mark_dirty();
		self.overlay.clear_child_prefix(child_info, prefix);
		self.backend.for_child_keys_with_prefix(child_info, prefix, |key| {
			self.overlay.set_child_storage(child_info, key.to_vec(), None);
		});
*/
	}

	fn storage_append(
		&mut self,
		key: Vec<u8>,
		value: Vec<u8>,
	) {
		unimplemented!()
/*
		self.mark_dirty();

		let backend = &mut self.backend;
		let current_value = self.overlay.value_mut_or_insert_with(
			&key,
			|| backend.storage(&key).expect(EXT_NOT_ALLOWED_TO_FAIL).unwrap_or_default()
		);
		StorageAppend::new(current_value).append(value);
*/
	}

	fn chain_id(&self) -> u64 {
		42
	}

	fn storage_root(&mut self) -> Vec<u8> {
		unimplemented!()
		/*if let Some(ref root) = self.storage_transaction_cache.transaction_storage_root {
			return root.encode();
		}

		let root = self.overlay.storage_root(self.backend, self.storage_transaction_cache);
		root.encode()
		*/
	}

	fn child_storage_root(
		&mut self,
		child_info: &ChildInfo,
	) -> Vec<u8> {
		unimplemented!()
		/*
		let storage_key = child_info.storage_key();
		let prefixed_storage_key = child_info.prefixed_storage_key();
		if self.storage_transaction_cache.transaction_storage_root.is_some() {
			let root = self
				.storage(prefixed_storage_key.as_slice())
				.and_then(|k| Decode::decode(&mut &k[..]).ok())
				.unwrap_or_else(
					|| empty_child_trie_root::<Layout<H>>()
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
				if is_empty {
					self.overlay.set_storage(prefixed_storage_key.into_inner(), None);
				} else {
					self.overlay.set_storage(prefixed_storage_key.into_inner(), Some(root.clone()));
				}
				root
			} else {
				let root = self
					.storage(prefixed_storage_key.as_slice())
					.and_then(|k| Decode::decode(&mut &k[..]).ok())
					.unwrap_or_else(
						|| empty_child_trie_root::<Layout<H>>()
					);
				root.encode()
			}
		}
		*/
	}

	fn storage_changes_root(&mut self, parent_hash: &[u8]) -> Result<Option<Vec<u8>>, ()> {
		unimplemented!()
	}

	fn storage_start_transaction(&mut self) {
		unimplemented!()
		//self.overlay.start_transaction()
	}

	fn storage_rollback_transaction(&mut self) -> Result<(), ()> {
		unimplemented!()
		//self.mark_dirty();
		//self.overlay.rollback_transaction().map_err(|_| ())
	}

	fn storage_commit_transaction(&mut self) -> Result<(), ()> {
		unimplemented!()
		//self.overlay.commit_transaction().map_err(|_| ())
	}

	fn wipe(&mut self) {
		unimplemented!()
	}

	fn commit(&mut self) {
		unimplemented!()
	}

	fn read_write_count(&self) -> (u32, u32, u32, u32) {
		unimplemented!()
	}

	fn reset_read_write_count(&mut self) {
		unimplemented!()
	}

	fn get_whitelist(&self) -> Vec<TrackedStorageKey> {
		unimplemented!()
	}

	fn set_whitelist(&mut self, new: Vec<TrackedStorageKey>) {
		unimplemented!()
	}
}

impl<H> ExtensionStore for WitnessBackend<H>
where
	H: Hasher,
	H::Out: Ord + 'static + codec::Codec,
{
	fn extension_by_type_id(&mut self, _type_id: TypeId) -> Option<&mut dyn Any> {
		None
	}

	fn register_extension_with_type_id(
		&mut self,
		_type_id: TypeId,
		_extension: Box<dyn Extension>,
	) -> Result<(), Error> {
		Err(Error::ExtensionsAreNotSupported)
	}

	fn deregister_extension_by_type_id(
		&mut self,
		_type_id: TypeId,
	) -> Result<(), Error> {
		Err(Error::ExtensionsAreNotSupported)
	}
}
