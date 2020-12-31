// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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

//! Async externalities.
//!
//!
//!
//! Allowed ext function, cummulative (kind bellow got access to parent capability):
//!
//! - WorkerType::Stateless: None
//!		- extension (only thread extension if not inline) so purely technical
//!		(also true for all other kind).
//!		- resolve_worker_result
//! - WorkerType::ReadLastBlock
//!		- storage
//!		- child_storage
//!		- next_storage_key
//!		- next_child_storage_key
//!		- get_past_async_backend (warning this is only for this type, not inherited)
//! - WorkerType::ReadAtSpawn
//!		- get_async_backend
// TODO consider moving part of it to state machine (removing the current
// dep on state machine).
// TODO update and move doc to state-machine.

use sp_std::{
	boxed::Box,
	any::{TypeId, Any},
	vec::Vec,
};
use sp_core::{
	storage::{ChildInfo, TrackedStorageKey},
	traits::{SpawnNamed, TaskExecutorExt, RuntimeSpawnExt, RuntimeSpawn},
};
use sp_externalities::{
	Externalities, Extensions, ExternalitiesExt as _, TaskId, WorkerResult,
	WorkerDeclaration, AsyncExternalities as AsyncExternalitiesTrait,
};

/// Simple state-less externalities for use in async context.
///
/// Will panic if anything is accessing the storage.
pub struct AsyncExternalities {
	extensions: Extensions,
	state: Box<dyn AsyncExternalitiesTrait>,
}

/// New Async externalities.
#[cfg(feature = "std")]
pub fn new_async_externalities(
	scheduler: Box<dyn SpawnNamed>,
	async_ext: Box<dyn AsyncExternalitiesTrait>,
) -> Result<AsyncExternalities, &'static str> {
	let mut res = AsyncExternalities {
		extensions: Default::default(),
		state: async_ext,
	};
	let mut ext = &mut res as &mut dyn Externalities;
	ext.register_extension::<TaskExecutorExt>(TaskExecutorExt(scheduler.clone()))
		.map_err(|_| "Failed to register task executor extension.")?;

	Ok(res)
}

pub fn new_inline_only_externalities(
	async_ext: Box<dyn AsyncExternalitiesTrait>,
) -> Result<AsyncExternalities, &'static str> {
	Ok(AsyncExternalities {
		extensions: Default::default(),
		state: async_ext,
	})
}

impl AsyncExternalities {
	/// Extend async externalities with the ability to spawn wasm instances.
	pub fn with_runtime_spawn(
		mut self,
		runtime_ext: Box<dyn RuntimeSpawn>,
	) -> Result<Self, &'static str> {
		let mut ext = &mut self as &mut dyn Externalities;
		ext.register_extension::<RuntimeSpawnExt>(RuntimeSpawnExt(runtime_ext))
			.map_err(|_| "Failed to register task executor extension.")?;

		Ok(self)
	}
}

type StorageKey = Vec<u8>;

type StorageValue = Vec<u8>;

impl Externalities for AsyncExternalities {
	fn set_offchain_storage(&mut self, key: &[u8], value: Option<&[u8]>) {
		self.state.set_offchain_storage(key, value)
	}

	fn storage(&self, key: &[u8]) -> Option<StorageValue> {
		self.state.storage(key)
	}

	fn storage_hash(&self, key: &[u8]) -> Option<Vec<u8>> {
		self.state.storage_hash(key)
	}

	fn child_storage(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Option<StorageValue> {
		self.state.child_storage(child_info, key)
	}

	fn child_storage_hash(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Option<Vec<u8>> {
		self.state.child_storage_hash(child_info, key)
	}

	fn next_storage_key(&self, key: &[u8]) -> Option<StorageKey> {
		self.state.next_storage_key(key)
	}

	fn next_child_storage_key(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Option<StorageKey> {
		self.state.next_child_storage_key(child_info, key)
	}

	fn place_storage(&mut self, key: StorageKey, maybe_value: Option<StorageValue>) {
		self.state.place_storage(key, maybe_value)
	}

	fn place_child_storage(
		&mut self,
		child_info: &ChildInfo,
		key: StorageKey,
		value: Option<StorageValue>,
	) {
		self.state.place_child_storage(child_info, key, value)
	}

	fn kill_child_storage(
		&mut self,
		child_info: &ChildInfo,
	) {
		self.state.kill_child_storage(child_info)
	}

	fn clear_prefix(&mut self, prefix: &[u8]) {
		self.state.clear_prefix(prefix)
	}

	fn clear_child_prefix(
		&mut self,
		child_info: &ChildInfo,
		prefix: &[u8],
	) {
		self.state.clear_child_prefix(child_info, prefix)
	}

	fn storage_append(
		&mut self,
		key: Vec<u8>,
		value: Vec<u8>,
	) {
		self.state.storage_append(key, value)
	}

	fn chain_id(&self) -> u64 {
		self.state.chain_id()
	}

	fn storage_root(&mut self) -> Vec<u8> {
		self.state.storage_root()
	}

	fn child_storage_root(
		&mut self,
		child_info: &ChildInfo,
	) -> Vec<u8> {
		self.state.child_storage_root(child_info)
	}

	fn storage_changes_root(&mut self, parent: &[u8]) -> Result<Option<Vec<u8>>, ()> {
		self.state.storage_changes_root(parent)
	}

	fn storage_start_transaction(&mut self) {
		self.state.storage_start_transaction()
	}

	fn storage_rollback_transaction(&mut self) -> Result<Vec<TaskId>, ()> {
		self.state.storage_rollback_transaction()
	}

	fn storage_commit_transaction(&mut self) -> Result<Vec<TaskId>, ()> {
		self.state.storage_commit_transaction()
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
		worker_id: u64,
		declaration: WorkerDeclaration,
	) -> Box<dyn AsyncExternalitiesTrait> {
		self.state.get_worker_externalities(worker_id, declaration)
	}
	
	fn resolve_worker_result(&mut self, state_update: WorkerResult) -> Option<Vec<u8>> {
		self.state.resolve_worker_result(state_update)
	}

	fn dismiss_worker(&mut self, id: TaskId) {
		self.state.dismiss_worker(id)
	}
}

impl sp_externalities::ExtensionStore for AsyncExternalities {
	fn extension_by_type_id(&mut self, type_id: TypeId) -> Option<&mut dyn Any> {
		self.extensions.get_mut(type_id)
	}

	fn register_extension_with_type_id(
		&mut self,
		type_id: TypeId,
		extension: Box<dyn sp_externalities::Extension>,
	) -> Result<(), sp_externalities::Error> {
		self.extensions.register_with_type_id(type_id, extension)
	}

	fn deregister_extension_by_type_id(&mut self, type_id: TypeId) -> Result<(), sp_externalities::Error> {
		if self.extensions.deregister(type_id) {
			Ok(())
		} else {
			Err(sp_externalities::Error::ExtensionIsNotRegistered(type_id))
		}
	}
}

impl AsyncExternalitiesTrait for AsyncExternalities {
	fn need_resolve(&self) -> bool {
		self.state.need_resolve()
	}
	
	fn extract_delta(&mut self) -> Option<sp_externalities::StateDelta> {
		self.state.extract_delta()
	}

	fn extract_optimistic_log(&mut self) -> Option<sp_externalities::AccessLog> {
		self.state.extract_optimistic_log()
	}

	fn did_fail(&self) -> bool {
		self.state.did_fail()
	}
}


