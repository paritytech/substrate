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
//! - AsyncStateType::Stateless: None
//!		- extension (only thread extension if not inline) so purely technical
//!		(also true for all other kind).
//! - AsyncStateType::ReadLastBlock
//!		- storage
//!		- child_storage
//!		- next_storage_key
//!		- next_child_storage_key
//!		- get_past_async_backend (warning this is only for this type, not inherited)
//! - AsyncStateType::ReadAtSpawn
//!		- get_async_backend
//!		- is_state_current
// TODO consider moving part of it to state machine (removing the current
// dep on state machine).

use sp_std::{
	boxed::Box,
	any::{TypeId, Any},
	vec::Vec,
};
use sp_core::{
	storage::{ChildInfo, TrackedStorageKey},
	traits::{SpawnNamed, TaskExecutorExt, RuntimeSpawnExt, RuntimeSpawn},
};
use sp_externalities::{Externalities, Extensions, ExternalitiesExt as _, TaskId, AsyncBackend};
use crate::AsyncStateType;
use sp_state_machine::ext_tools::{EXT_NOT_ALLOWED_TO_FAIL, guard};
use sp_state_machine::trace;
use sp_core::hexdisplay::HexDisplay;

const KIND_WITH_BACKEND: &str = "This async kind is only buildable with a backend.";

/// TODO doc
pub enum AsyncState {
	/// Externalities do not access state, so we join
	None,
	/// Externalities access read only the backend unmodified state.
	ReadLastBlock(AsyncExt),
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

pub enum AsyncStateResult {
	/// Result is always valid, for `AsyncState::None`
	/// and `AsyncState::ReadLastBlock`.
	StateLess(Vec<u8>),
	ReadOnly(Vec<u8>, TaskId),
}

/// Async view on state machine Ext.
/// It contains its own set of state and rules,
/// and returns its changes on `join`.
/// TODO consider moving in state-machine crate
/// and have just `dyn Ext + Send + Sync`
pub struct AsyncExt {
	kind: AsyncStateType,
	// Actually unused at this point, is for write variant.
	// TODO consider Optional, also this is copy, this could synch.
	overlay: sp_state_machine::OverlayedChanges,
	spawn_id: Option<TaskId>,
	// TODO consider non optional with dummy impl for None (is filter
	// by kind beforehand anyway).
	backend: Option<Box<dyn AsyncBackend>>,
}

impl AsyncExt {
	/// Spawn a thread with no state access.
	///
	/// No impact on master thread, no need to
	/// assert the thread did join.
	/// 
	/// (But there is no sense in runing if we do not join or kill).
	/// TODO remember that when inline we run at join or not at all
	/// for kill so using no panic handler is the same as transmitting
	/// panic to parent on join.
	/// TODO make panic in thread panic the master threaod too !!!
	pub fn stateless_ext() -> Self {
		AsyncExt {
			kind: AsyncStateType::Stateless,
			overlay: Default::default(),
			spawn_id: None,
			backend: None,
		}
	}

	/// Spawn a thread with access to previous
	/// block state only.
	///
	/// No impact on master thread, no need to
	/// assert the thread did join.
	pub fn previous_block_read(backend: Box<dyn AsyncBackend>) -> Self {
		AsyncExt {
			kind: AsyncStateType::ReadLastBlock,
			overlay: Default::default(),
			spawn_id: None,
			backend: Some(backend),
		}
	}

	/// Spawn a thread with access to state at
	/// the time the thread did spawn.
	/// This contains a copy of the overlay at the time of spawn.
	///
	/// A spawn id transaction is inserted before copy in the overlay and the parent
	/// thread will be able to know on join if it is on a the same transaction level.
	///
	/// Still there is no strong failure case, the master thread should choose behavior
	/// to adopt when receiving data that is not in synch with the original spawn_id.
	///
	/// TODO return original id on join plus a new ext on master (also on child for rec thread) to know if same tx or parent tx
	/// or dropped tx.
	pub fn state_at_spawn_read(
		backend: Box<dyn AsyncBackend>,
		spawn_id: TaskId,
	) -> Self {
		AsyncExt {
			kind: AsyncStateType::ReadAtSpawn,
			overlay: Default::default(),
			spawn_id: Some(spawn_id),
			backend: Some(backend),
		}
	}
}

/// Simple state-less externalities for use in async context.
///
/// Will panic if anything is accessing the storage.
#[cfg_attr(feature = "std", derive(Debug))]
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
#[cfg(feature = "std")]
pub fn new_async_externalities(
	scheduler: Box<dyn SpawnNamed>,
	async_ext: AsyncExt,
) -> Result<AsyncExternalities, &'static str> {
	let mut res = AsyncExternalities {
		extensions: Default::default(),
		// TODO as param
		state: async_ext,
	};
	let mut ext = &mut res as &mut dyn Externalities;
	ext.register_extension::<TaskExecutorExt>(TaskExecutorExt(scheduler.clone()))
		.map_err(|_| "Failed to register task executor extension.")?;

	Ok(res)
}

pub fn new_inline_only_externalities(
	async_ext: AsyncExt,
) -> Result<AsyncExternalities, &'static str> {
	Ok(AsyncExternalities {
		extensions: Default::default(),
		// TODO as param
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

impl AsyncExternalities {
	fn guard_stateless(&self, panic: &'static str) {
		match self.state.kind {
			AsyncStateType::Stateless => {
				panic!(panic)
			},
			AsyncStateType::ReadLastBlock
			| AsyncStateType::ReadAtSpawn => (),
		}
	}
}
impl Externalities for AsyncExternalities {
	fn set_offchain_storage(&mut self, _key: &[u8], _value: Option<&[u8]>) {
		panic!("`set_offchain_storage`: should not be used in async externalities!")
	}

	fn storage(&self, key: &[u8]) -> Option<StorageValue> {
		self.guard_stateless("`storage`: should not be used in async externalities!");
		let _guard = guard();
		let result = self.state.overlay.storage(key).map(|x| x.map(|x| x.to_vec())).unwrap_or_else(||
			self.state.backend.as_ref().expect(KIND_WITH_BACKEND).storage(key));
		trace!(target: "state", "{:?}: Th Get {}={:?}",
			self.state.spawn_id,
			HexDisplay::from(&key),
			result.as_ref().map(HexDisplay::from)
		);
		result
	}

	fn storage_hash(&self, _key: &[u8]) -> Option<Vec<u8>> {
		// TODO currently no hash function to avoid having to move the hasher trait
		// in AsyncExternalities extension.
		panic!("`storage_hash`: should not be used in async externalities!")
	}

	fn child_storage(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Option<StorageValue> {
		self.guard_stateless("`child_storage`: should not be used in async externalities!");
		let _guard = guard();
		let result = self.state.overlay
			.child_storage(child_info, key)
			.map(|x| x.map(|x| x.to_vec()))
			.unwrap_or_else(||
				self.state.backend.as_ref().expect(KIND_WITH_BACKEND).child_storage(child_info, key));

		trace!(target: "state", "{:?}: Th GetChild({}) {}={:?}",
			self.state.spawn_id,
			HexDisplay::from(&child_info.storage_key()),
			HexDisplay::from(&key),
			result.as_ref().map(HexDisplay::from)
		);

		result
	}

	fn child_storage_hash(
		&self,
		_child_info: &ChildInfo,
		_key: &[u8],
	) -> Option<Vec<u8>> {
		panic!("`child_storage_hash`: should not be used in async externalities!")
	}

	fn next_storage_key(&self, key: &[u8]) -> Option<StorageKey> {
		// TODO factor logic wit state machine Ext !!!
		self.guard_stateless("`next_storage_key`: should not be used in async externalities!");
		let next_backend_key = self.state.backend.as_ref().expect(KIND_WITH_BACKEND).next_storage_key(key);
		let next_overlay_key_change = self.state.overlay.next_storage_key_change(key);

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
		// TODO factor logic wit state machine Ext !!!
		self.guard_stateless("`next_child_storage_key`: should not be used in async externalities!");
		let next_backend_key = self.state.backend.as_ref().expect(KIND_WITH_BACKEND)
			.next_child_storage_key(child_info, key);
		let next_overlay_key_change = self.state.overlay.next_child_storage_key_change(
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
		// TODO currently no storage_root function to avoid having to move the hasher trait
		// in AsyncExternalities extension.
		panic!("`storage_root`: should not be used in async externalities!")
	}

	fn child_storage_root(
		&mut self,
		_child_info: &ChildInfo,
	) -> Vec<u8> {
		// TODO currently no storage_root function to avoid having to move the hasher trait
		// in AsyncExternalities extension.
		panic!("`child_storage_root`: should not be used in async externalities!")
	}

	fn storage_changes_root(&mut self, _parent: &[u8]) -> Result<Option<Vec<u8>>, ()> {
		panic!("`storage_changes_root`: should not be used in async externalities!")
	}

	fn storage_start_transaction(&mut self) {
		unimplemented!("Transactions are not supported by AsyncExternalities");
	}

	fn storage_rollback_transaction(&mut self) -> Result<Vec<TaskId>, ()> {
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

	// TODO this guard only make sense when renturning non optional
	// TODO change api.
	fn get_past_async_backend(&self) -> Option<Box<dyn AsyncBackend>> {
		match self.state.kind {
			AsyncStateType::Stateless
			| AsyncStateType::ReadAtSpawn => {
				panic!("Staking a ReadLastBlock worker is only possible from a ReadLastBlock worker");
			},
			AsyncStateType::ReadLastBlock => (),
		}

		self.state.backend.as_ref().expect(KIND_WITH_BACKEND).async_backend()
	}

	fn get_async_backend(&mut self, marker: TaskId) -> Option<Box<dyn AsyncBackend>> {
		match self.state.kind {
			AsyncStateType::Stateless
			| AsyncStateType::ReadLastBlock => {
				panic!("Staking a ReadAtSpawn worker is only possible from a ReadAtSpawn worker");
			},
			AsyncStateType::ReadAtSpawn => (),
		}

		self.state.overlay.set_marker(marker);
		// TODO Creating a new backend is only of any use for write
		/*let backend: Box<dyn AsyncBackend> = Box::new(crate::backend::AsyncBackendAt::new(
			backend,
			self.overlay,
		));*/

		self.state.backend.as_ref().expect(KIND_WITH_BACKEND).async_backend()
	}

	fn is_state_current(&self, marker: TaskId) -> bool {
		match self.state.kind {
			AsyncStateType::Stateless
			| AsyncStateType::ReadLastBlock => {
				panic!("Staking a ReadAtSpawn worker is only possible from a ReadAtSpawn worker");
			},
			AsyncStateType::ReadAtSpawn => (),
		}

		self.state.overlay.is_state_current(marker)
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
