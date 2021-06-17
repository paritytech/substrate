// This file is part of Substrate.

// Copyright (C) 2020-2020 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! Externalities for workers.

use sp_std::{
	boxed::Box,
	any::{TypeId, Any},
	vec::Vec,
};
use sp_core::{
	storage::{ChildInfo, TrackedStorageKey},
};
use sp_externalities::{Externalities, TaskId,
	WorkerResult, AsyncExternalities};
use crate::{StorageValue, StorageKey};

/// Async view on state machine Ext.
/// It contains its own set of state and rules,
/// and returns its changes on `join`.
pub struct AsyncExt {
	spawn_id: TaskId,
}

#[cfg(feature = "std")]
impl std::fmt::Debug for AsyncExt
{
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "AsyncExt {:?}", self.spawn_id)
	}
}

/// Obtain externality for a child worker.
pub fn new_child_worker_async_ext(
	worker_id: u64,
) -> AsyncExt {
	AsyncExt {
		spawn_id: worker_id,
	}
}

impl Externalities for AsyncExt {
	fn set_offchain_storage(&mut self, _key: &[u8], _value: Option<&[u8]>) {
		panic!("`set_offchain_storage`: should not be used in async externalities!")
	}

	fn storage(&self, _key: &[u8]) -> Option<StorageValue> {
		panic!("`storage`: should not be used in async externalities!");
	}

	fn storage_hash(&self, _key: &[u8]) -> Option<Vec<u8>> {
		// TODO currently no hash function to avoid having to move the hasher trait
		// in AsyncExternalities extension.
		panic!("`storage_hash`: should not be used in async externalities!")
	}

	fn child_storage(
		&self,
		_child_info: &ChildInfo,
		_key: &[u8],
	) -> Option<StorageValue> {
		panic!(
			"`child_storage`: should not be used in async externalities!",
		);
	}

	fn child_storage_hash(
		&self,
		_child_info: &ChildInfo,
		_key: &[u8],
	) -> Option<Vec<u8>> {
		panic!("`child_storage_hash`: should not be used in async externalities!")
	}

	fn next_storage_key(&self, _key: &[u8]) -> Option<StorageKey> {
		panic!("`next_storage_key`: should not be used in async externalities!");
	}

	fn next_child_storage_key(
		&self,
		_child_info: &ChildInfo,
		_key: &[u8],
	) -> Option<StorageKey> {
		panic!(
			"`next_child_storage_key`: should not be used in async externalities!",
		);
	}

	fn place_storage(&mut self, _key: StorageKey, _maybe_value: Option<StorageValue>) {
		panic!("`place_storage`: should not be used in read only worker externalities!");
	}

	fn place_child_storage(
		&mut self,
		_child_info: &ChildInfo,
		_key: StorageKey,
		_value: Option<StorageValue>,
	) {
		panic!("`place_child_storage`: should not be used in read only worker externalities!");
	}

	fn kill_child_storage(
		&mut self,
		_child_info: &ChildInfo,
		_limit: Option<u32>,
	) -> (bool, u32) {
		panic!("`kill_child_storage`: should not be used in read only worker externalities!");
	}

	fn clear_prefix(&mut self, _prefix: &[u8], _limit: Option<u32>) -> (bool, u32) {
		panic!("`clear_prefix`: should not be used in read only worker externalities!");
	}

	fn clear_child_prefix(
		&mut self,
		_child_info: &ChildInfo,
		_prefix: &[u8],
		_limit: Option<u32>,
	) -> (bool, u32) {
		panic!("`clear_child_prefix`: should not be used in read only worker externalities!");
	}

	fn storage_append(
		&mut self,
		_key: Vec<u8>,
		_value: Vec<u8>,
	) {
		panic!("`storage_append`: should not be used in read only worker externalities!");
	}

	fn storage_root(&mut self) -> Vec<u8> {
		panic!("`storage_root`: should not be used in async externalities!")
	}

	fn child_storage_root(
		&mut self,
		_child_info: &ChildInfo,
	) -> Vec<u8> {
		panic!("`child_storage_root`: should not be used in async externalities!")
	}

	fn storage_changes_root(&mut self, _parent: &[u8]) -> Result<Option<Vec<u8>>, ()> {
		panic!("`storage_changes_root`: should not be used in async externalities!")
	}

	fn storage_start_transaction(&mut self) {
		panic!("`storage_start_transaction`: should not be used in read only worker externalities!");
	}

	fn storage_rollback_transaction(&mut self) -> Result<(), ()> {
		panic!("`storage_rollback_transaction`: should not be used in read only worker externalities!");
	}

	fn storage_commit_transaction(&mut self) -> Result<(), ()> {
		panic!("`storage_commit_transaction`: should not be used in read only worker externalities!");
	}

	fn wipe(&mut self) {}

	fn commit(&mut self) {}

	fn read_write_count(&self) -> (u32, u32, u32, u32) {
		unimplemented!("read_write_count is not supported in AsyncExternalities")
	}

	fn reset_read_write_count(&mut self) {
		unimplemented!("reset_read_write_count is not supported in AsyncExternalities")
	}

	fn get_whitelist(&self) -> Vec<TrackedStorageKey> {
		unimplemented!("get_whitelist is not supported in AsyncExternalities")
	}

	fn set_whitelist(&mut self, _: Vec<TrackedStorageKey>) {
		unimplemented!("set_whitelist is not supported in AsyncExternalities")
	}

	fn get_worker_externalities(
		&mut self,
		worker_id: TaskId,
	) -> Box<dyn AsyncExternalities> {
		Box::new(crate::async_ext::new_child_worker_async_ext(
			worker_id,
		))
	}
	
	fn resolve_worker_result(&mut self, result: WorkerResult) -> Option<Vec<u8>> {
		match result {
			WorkerResult::Valid(result) => Some(result),
			WorkerResult::Invalid => None,
			WorkerResult::RuntimePanic => {
				panic!("Runtime panic from a worker.")
			},
			WorkerResult::HardPanic => {
				panic!("Panic running a worker.")
			},
		}
	}

	fn dismiss_worker(&mut self, _id: TaskId) {
		// No worker persistence currently.
	}
}

impl sp_externalities::ExtensionStore for AsyncExt {
	fn extension_by_type_id(&mut self, _type_id: TypeId) -> Option<&mut dyn Any> {
		None
	}

	fn register_extension_with_type_id(
		&mut self,
		_type_id: TypeId,
		_extension: Box<dyn sp_externalities::Extension>,
	) -> Result<(), sp_externalities::Error> {
		Err(sp_externalities::Error::ExtensionsAreNotSupported)
	}

	fn deregister_extension_by_type_id(&mut self, _type_id: TypeId) -> Result<(), sp_externalities::Error> {
		Err(sp_externalities::Error::ExtensionsAreNotSupported)
	}
}

impl AsyncExternalities for AsyncExt { }
