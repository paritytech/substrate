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

pub use sp_state_machine::AsyncBackend;
use std::any::{TypeId, Any};
use sp_std::boxed::Box;
use sp_core::{
	storage::{ChildInfo, TrackedStorageKey},
	traits::{Externalities, SpawnNamed, TaskExecutorExt, RuntimeSpawnExt, RuntimeSpawn},
};
use sp_externalities::{Extensions, ExternalitiesExt as _};


/// TODO doc
pub enum AsyncState {
	/// Externalities do not access state, so we join
	None,
	/// Externalities access read only the backend unmodified state.
	ReadBefore(AsyncExt),
	/// Externalities access read only the backend unmodified state,
	/// and the change at the time of spawn.
	/// In this case when joining we return an identifier of the
	/// state at launch.
	ReadAtSpawn(AsyncExt),
}

impl Default for AsyncState {
	fn default() -> Self {
		AsyncState::None
	}
}

/// Type for `AsyncState`.
#[derive(Debug)]
enum AsyncStateType {
	None,
	ReadBefore,
	ReadAtSpawn,
}

impl Default for AsyncStateType {
	fn default() -> Self {
		AsyncStateType::None
	}
}

pub type CheckpointState = u64;

pub enum AsyncStateResult {
	/// Result is always valid, for `AsyncState::None`
	/// and `AsyncState::ReadBefore`.
	StateLess(Vec<u8>),
	ReadOnly(Vec<u8>, CheckpointState),
}

/// Async view on state machine Ext.
/// It contains its own set of state and rules,
/// and returns its changes on `join`.
/// TODO consider moving in state-machine crate
/// and have just `dyn Ext + Send + Sync`
pub struct AsyncExt {
	kind: AsyncStateType,
	overlay: sp_state_machine::OverlayedChanges,
	spawn_id: Option<CheckpointState>,
	backend: Option<Box<dyn AsyncBackend>>,
}

/// Simple state-less externalities for use in async context.
///
/// Will panic if anything is accessing the storage.
#[derive(Debug)]
pub struct AsyncExternalities {
	extensions: Extensions,
	state: AsyncExt,
}

#[cfg(feature = "std")]
impl std::fmt::Debug for AsyncExt
{
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "AsyncExt {:?} at {:?}", self.kind, self.spawn_id)
	}
}

/// New Async externalities.
pub fn new_async_externalities(
	scheduler: Box<dyn SpawnNamed>,
	backend: Option<Box<dyn AsyncBackend>>,
) -> Result<AsyncExternalities, &'static str> {
	let mut res = AsyncExternalities {
		extensions: Default::default(),
		// TODO as param
		state: AsyncExt {
			kind: Default::default(),
			overlay: Default::default(),
			spawn_id: None,
			backend,
		},
	};
	let mut ext = &mut res as &mut dyn Externalities;
	ext.register_extension::<TaskExecutorExt>(TaskExecutorExt(scheduler.clone()))
		.map_err(|_| "Failed to register task executor extension.")?;

	Ok(res)
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
	fn set_offchain_storage(&mut self, _key: &[u8], _value: Option<&[u8]>) {
		panic!("`set_offchain_storage`: should not be used in async externalities!")
	}

	fn storage(&self, _key: &[u8]) -> Option<StorageValue> {
		panic!("`storage`: should not be used in async externalities!")
	}

	fn storage_hash(&self, _key: &[u8]) -> Option<Vec<u8>> {
		panic!("`storage_hash`: should not be used in async externalities!")
	}

	fn child_storage(
		&self,
		_child_info: &ChildInfo,
		_key: &[u8],
	) -> Option<StorageValue> {
		panic!("`child_storage`: should not be used in async externalities!")
	}

	fn child_storage_hash(
		&self,
		_child_info: &ChildInfo,
		_key: &[u8],
	) -> Option<Vec<u8>> {
		panic!("`child_storage_hash`: should not be used in async externalities!")
	}

	fn next_storage_key(&self, _key: &[u8]) -> Option<StorageKey> {
		panic!("`next_storage_key`: should not be used in async externalities!")
	}

	fn next_child_storage_key(
		&self,
		_child_info: &ChildInfo,
		_key: &[u8],
	) -> Option<StorageKey> {
		panic!("`next_child_storage_key`: should not be used in async externalities!")
	}

	fn place_storage(&mut self, _key: StorageKey, _maybe_value: Option<StorageValue>) {
		panic!("`place_storage`: should not be used in async externalities!")
	}

	fn place_child_storage(
		&mut self,
		_child_info: &ChildInfo,
		_key: StorageKey,
		_value: Option<StorageValue>,
	) {
		panic!("`place_child_storage`: should not be used in async externalities!")
	}

	fn kill_child_storage(
		&mut self,
		_child_info: &ChildInfo,
	) {
		panic!("`kill_child_storage`: should not be used in async externalities!")
	}

	fn clear_prefix(&mut self, _prefix: &[u8]) {
		panic!("`clear_prefix`: should not be used in async externalities!")
	}

	fn clear_child_prefix(
		&mut self,
		_child_info: &ChildInfo,
		_prefix: &[u8],
	) {
		panic!("`clear_child_prefix`: should not be used in async externalities!")
	}

	fn storage_append(
		&mut self,
		_key: Vec<u8>,
		_value: Vec<u8>,
	) {
		panic!("`storage_append`: should not be used in async externalities!")
	}

	fn chain_id(&self) -> u64 { 42 }

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
		unimplemented!("Transactions are not supported by AsyncExternalities");
	}

	fn storage_rollback_transaction(&mut self) -> Result<(), ()> {
		unimplemented!("Transactions are not supported by AsyncExternalities");
	}

	fn storage_commit_transaction(&mut self) -> Result<(), ()> {
		unimplemented!("Transactions are not supported by AsyncExternalities");
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
