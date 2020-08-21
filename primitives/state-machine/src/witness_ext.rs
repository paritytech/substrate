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
use crate::ext::{ExtInner, ExtInnerMut};
use crate::overlayed_changes::{OverlayedChanges, NoExtrinsics};
use crate::{StorageValue, StorageKey};

/// The backend runnig on a trie proof.
pub struct WitnessExt<H: Hasher> {
	/// The overlayed changes to write to.
	pub overlay: OverlayedChanges<NoExtrinsics>,
	/// The storage backend to read from.
	pub backend: TrieBackend<MemoryDB<H>, H>,
}

impl<H: Hasher> WitnessExt<H>
	where
		H: Hasher,
		H::Out: Ord + 'static + codec::Codec,
{
	/// Create a new backend.
	pub fn new(db: MemoryDB<H>, root: H::Out) -> Self {
		WitnessExt {
			backend: TrieBackend::new(db, root),
			overlay: OverlayedChanges::<NoExtrinsics>::default(),
		}
	}

	/// Access methods for `ExtInnerMut`.
	fn ext_inner_mut(&mut self) -> ExtInnerMut<H, TrieBackend<MemoryDB<H>, H>, NoExtrinsics> {
		ExtInnerMut {
			overlay: &mut self.overlay,
			backend: &self.backend,
			id: 0,
			_phantom: Default::default(),
		}
	}

	/// Access methods for `ExtInner`.
	fn ext_inner(&self) -> ExtInner<H, TrieBackend<MemoryDB<H>, H>, NoExtrinsics> {
		ExtInner {
			overlay: &self.overlay,
			backend: &self.backend,
			id: 0,
			_phantom: Default::default(),
		}
	}
}



impl<H> Externalities for WitnessExt<H>
	where
		H: Hasher,
		H::Out: Ord + 'static + codec::Codec,
{
	fn set_offchain_storage(&mut self, _key: &[u8], _value: Option<&[u8]>) {
		unimplemented!("Unsupported");
	}

	fn storage(&self, key: &[u8]) -> Option<StorageValue> {
		self.ext_inner().storage(key)
	}

	fn storage_hash(&self, key: &[u8]) -> Option<Vec<u8>> {
		self.ext_inner().storage_hash(key)
	}

	fn child_storage(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Option<StorageValue> {
		self.ext_inner().child_storage(child_info, key)
	}

	fn child_storage_hash(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Option<Vec<u8>> {
		self.ext_inner().child_storage_hash(child_info, key)
	}

	fn exists_storage(&self, key: &[u8]) -> bool {
		self.ext_inner().exists_storage(key)
	}

	fn exists_child_storage(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> bool {
		self.ext_inner().exists_child_storage(child_info, key)
	}

	fn next_storage_key(&self, key: &[u8]) -> Option<StorageKey> {
		self.ext_inner().next_storage_key(key)
	}

	fn next_child_storage_key(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Option<StorageKey> {
		self.ext_inner().next_child_storage_key(child_info, key)
	}

	fn place_storage(&mut self, key: StorageKey, value: Option<StorageValue>) {
		self.ext_inner_mut().place_storage(key, value)
	}

	fn place_child_storage(
		&mut self,
		child_info: &ChildInfo,
		key: StorageKey,
		value: Option<StorageValue>,
	) {
		self.ext_inner_mut().place_child_storage(child_info, key, value)
	}

	fn kill_child_storage(
		&mut self,
		child_info: &ChildInfo,
	) {
		self.ext_inner_mut().kill_child_storage(child_info)
	}

	fn clear_prefix(&mut self, prefix: &[u8]) {
		self.ext_inner_mut().clear_prefix(prefix)
	}

	fn clear_child_prefix(
		&mut self,
		child_info: &ChildInfo,
		prefix: &[u8],
	) {
		self.ext_inner_mut().clear_child_prefix(child_info, prefix)
	}

	fn storage_append(
		&mut self,
		key: Vec<u8>,
		value: Vec<u8>,
	) {
		self.ext_inner_mut().storage_append(key, value)
	}

	fn chain_id(&self) -> u64 {
		42
	}

	fn storage_root(&mut self) -> Vec<u8> {
		self.ext_inner_mut().storage_root()
	}

	fn child_storage_root(
		&mut self,
		child_info: &ChildInfo,
	) -> Vec<u8> {
		self.ext_inner_mut().child_storage_root(child_info)
	}

	fn storage_changes_root(&mut self, _parent_hash: &[u8]) -> Result<Option<Vec<u8>>, ()> {
		unimplemented!("Unsupported");
	}

	fn storage_start_transaction(&mut self) {
		self.ext_inner_mut().storage_start_transaction()
	}

	fn storage_rollback_transaction(&mut self) -> Result<(), ()> {
		self.ext_inner_mut().storage_rollback_transaction()
	}

	fn storage_commit_transaction(&mut self) -> Result<(), ()> {
		self.ext_inner_mut().storage_commit_transaction()
	}

	fn wipe(&mut self) {
		unimplemented!("Unsupported");
	}

	fn commit(&mut self) {
		unimplemented!("Unsupported");
	}

	fn read_write_count(&self) -> (u32, u32, u32, u32) {
		self.ext_inner().read_write_count()
	}

	fn reset_read_write_count(&mut self) {
		self.ext_inner_mut().reset_read_write_count()
	}

	fn get_whitelist(&self) -> Vec<TrackedStorageKey> {
		unimplemented!("Unsupported");
	}

	fn set_whitelist(&mut self, _new: Vec<TrackedStorageKey>) {
		unimplemented!("Unsupported");
	}
}

impl<H> ExtensionStore for WitnessExt<H>
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
