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

use sp_std::{
	boxed::Box,
	any::{TypeId, Any},
	vec::Vec,
};
use sp_core::{
	storage::{ChildInfo, TrackedStorageKey},
	traits::{SpawnNamed, TaskExecutorExt, RuntimeSpawnExt, RuntimeSpawn},
};
use sp_externalities::{Externalities, Extensions, ExternalitiesExt as _, TaskId, AsyncBackend,
	WorkerResult, WorkerDeclaration};
use crate::WorkerType;
use sp_state_machine::ext_guard as guard;
use sp_state_machine::trace;
use sp_core::hexdisplay::HexDisplay;

/// Async view on state machine Ext.
/// It contains its own set of state and rules,
/// and returns its changes on `join`.
pub struct AsyncExt {
	kind: WorkerType,
	// Actually unused at this point, is for write variant.
	overlay: sp_state_machine::OverlayedChanges,
	spawn_id: Option<TaskId>,
	backend: Box<dyn AsyncBackend>,
}

impl AsyncExt {
	/// Spawn a thread with no state access.
	///
	/// No impact on master thread, no need to
	/// assert the thread did join.
	///
	/// (But there is no sense in runing if we do not join or dismiss).
	/// TODO remember that when inline we run at join or not at all
	/// for dismiss so using no panic handler is the same as transmitting
	/// panic to parent on join.
	pub fn stateless_ext() -> Self {
		AsyncExt {
			kind: WorkerType::Stateless,
			overlay: Default::default(),
			spawn_id: None,
			backend: Box::new(()),
		}
	}

	/// Spawn a thread with access to previous
	/// block state only.
	///
	/// No impact on master thread, no need to
	/// assert the thread did join.
	pub fn previous_block_read(backend: Box<dyn AsyncBackend>) -> Self {
		AsyncExt {
			kind: WorkerType::ReadLastBlock,
			overlay: Default::default(),
			spawn_id: None,
			backend,
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
	pub fn state_at_spawn_read(
		backend: Box<dyn AsyncBackend>,
		spawn_id: TaskId,
	) -> Self {
		AsyncExt {
			kind: WorkerType::ReadAtSpawn,
			overlay: Default::default(),
			spawn_id: Some(spawn_id),
			backend: backend,
		}
	}

	/// Depending on kind the result may be already
	/// valid, in this case we do not need to resolve
	/// it.
	pub fn need_resolve(&self) -> bool {
		self.kind.need_resolve()
	}

	/// For optimistic worker, we extract logs from the overlay.
	/// When call on a non optimistic worker returns `None`.
	pub fn extract_optimistic_log(&mut self) -> Option<sp_externalities::AccessLog> {
		self.overlay.extract_optimistic_log()
	}

	/// Extract changes made to state for this worker.
	fn extract_delta(&mut self) -> sp_externalities::StateDelta {
		self.overlay.extract_delta()
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
	fn guard_stateless(
		&self,
		panic: &'static str,
	) {
		match self.state.kind {
			WorkerType::Stateless => {
				panic!(panic)
			},
			_ => (),
		}
	}

	fn guard_read_only(
		&self,
		panic: &'static str,
	) {
		if !self.write_access() {
			panic!(panic)
		}
	}

	/// Depending on kind the result may be already
	/// valid, in this case we do not need to resolve
	/// it.
	pub fn need_resolve(&self) -> bool {
		self.state.need_resolve()
	}

	/// For optimistic worker, we extract logs from the overlay.
	/// When call on a non optimistic worker returns `None`.
	pub fn extract_optimistic_log(&mut self) -> Option<sp_externalities::AccessLog> {
		self.state.extract_optimistic_log()
	}

	/// Check if externality can write.
	/// This does not indicate that a given write will
	/// be allowend or will not result in an invalid
	/// worker execution.
	pub fn write_access(&self) -> bool {
		match self.state.kind {
			WorkerType::Stateless
			| WorkerType::ReadLastBlock
			| WorkerType::ReadAtSpawn
			| WorkerType::ReadAtJoinOptimistic
			| WorkerType::ReadAtJoinDeclarative => false,
			WorkerType::WriteAtSpawn
			| WorkerType::WriteOptimistic
			| WorkerType::WriteDeclarative
			| WorkerType::WriteAtJoinOptimistic
			| WorkerType::WriteAtJoinDeclarative => true,
		}
	}

	/// Extract changes made to state for this worker.
	pub fn extract_delta(&mut self) -> Option<sp_externalities::StateDelta> {
		if self.write_access() {
			Some(self.state.extract_delta())
		} else {
			None
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
			self.state.backend.storage(key));
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
		self.guard_stateless(
			"`child_storage`: should not be used in async externalities!",
		);
		let _guard = guard();
		let result = self.state.overlay
			.child_storage(child_info, key)
			.map(|x| x.map(|x| x.to_vec()))
			.unwrap_or_else(||
				self.state.backend.child_storage(child_info, key));

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
		self.guard_stateless("`next_storage_key`: should not be used in async externalities!");
		let next_backend_key = self.state.backend.next_storage_key(key);
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
		self.guard_stateless(
			"`next_child_storage_key`: should not be used in async externalities!",
		);
		let next_backend_key = self.state.backend.next_child_storage_key(child_info, key);
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

	fn place_storage(&mut self, key: StorageKey, maybe_value: Option<StorageValue>) {
		self.guard_read_only("`place_storage`: should not be used in read only worker externalities!");
		self.state.overlay.set_storage(key, maybe_value);
	}

	fn place_child_storage(
		&mut self,
		child_info: &ChildInfo,
		key: StorageKey,
		value: Option<StorageValue>,
	) {
		self.guard_read_only("`place_child_storage`: should not be used in read only worker externalities!");
		self.state.overlay.set_child_storage(child_info, key, value);
	}

	fn kill_child_storage(
		&mut self,
		child_info: &ChildInfo,
	) {
		self.guard_read_only("`kill_child_storage`: should not be used in read only worker externalities!");
		self.state.overlay.clear_child_storage(child_info);
		for key in self.state.backend.child_storage_keys(child_info) {
			self.state.overlay.set_child_storage(child_info, key.to_vec(), None);
		}
	}

	fn clear_prefix(&mut self, prefix: &[u8]) {
		self.guard_read_only("`clear_prefix`: should not be used in read only worker externalities!");
		if sp_core::storage::well_known_keys::contains_child_storage_key(prefix) {
			return;
		}

		self.state.overlay.clear_prefix(prefix);
		for key in self.state.backend.keys_with_prefix(prefix) {
			self.state.overlay.set_storage(key.to_vec(), None);
		}
	}

	fn clear_child_prefix(
		&mut self,
		child_info: &ChildInfo,
		prefix: &[u8],
	) {
		self.guard_read_only("`clear_child_prefix`: should not be used in read only worker externalities!");
		self.state.overlay.clear_child_prefix(child_info, prefix);
		for key in self.state.backend.child_storage_keys_with_prefix(child_info, prefix) {
			self.state.overlay.set_child_storage(child_info, key.to_vec(), None);
		}
	}

	fn storage_append(
		&mut self,
		key: Vec<u8>,
		value: Vec<u8>,
	) {
		self.guard_read_only("`storage_append`: should not be used in read only worker externalities!");
		let backend = &mut self.state.backend;
		let current_value = self.state.overlay.value_mut_or_insert_with(
			&key,
			|| backend.storage(&key).unwrap_or_default()
		);
		sp_state_machine::StorageAppend::new(current_value).append(value);
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
		self.guard_read_only("`storage_start_transaction`: should not be used in read only worker externalities!");
		self.state.overlay.start_transaction()
	}

	fn storage_rollback_transaction(&mut self) -> Result<Vec<TaskId>, ()> {
		self.guard_read_only("`storage_rollback_transaction`: should not be used in read only worker externalities!");
		self.state.overlay.rollback_transaction().map_err(|_| ())
	}

	fn storage_commit_transaction(&mut self) -> Result<Vec<TaskId>, ()> {
		self.guard_read_only("`storage_commit_transaction`: should not be used in read only worker externalities!");
		self.state.overlay.commit_transaction().map_err(|_| ())
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

	fn get_past_async_backend(&self) -> Box<dyn AsyncBackend> {
		match self.state.kind {
			WorkerType::ReadLastBlock => (),
			_ => {
				panic!("Spawning a ReadLastBlock worker is only possible from a ReadLastBlock worker");
			},
		}

		self.state.backend.async_backend()
	}

	fn get_async_backend(
		&mut self,
		marker: TaskId,
		declaration: WorkerDeclaration,
	) -> Box<dyn AsyncBackend> {
		match self.state.kind {
			WorkerType::Stateless
			| WorkerType::ReadLastBlock => {
				panic!("Spawning a ReadAtSpawn worker is only possible from a ReadAtSpawn worker");
			},
			WorkerType::WriteAtJoinDeclarative => match &declaration {
// TODO				WorkerDeclaration::ChildWriteRead(..) => (),
				_ => {
					panic!("Incorrect declaration with declarative worker");
				},
			},
			WorkerType::WriteDeclarative => match &declaration {
// TODO				WorkerDeclaration::ChildWrite(..) => (),
				_ => {
					panic!("Incorrect declaration with declarative worker");
				},
			},
			WorkerType::ReadAtJoinDeclarative => match &declaration {
				WorkerDeclaration::ChildRead(..) => (),
				_ => {
					panic!("Incorrect declaration with declarative worker");
				},
			},
			WorkerType::ReadAtJoinOptimistic
			| WorkerType::WriteAtJoinOptimistic
			| WorkerType::WriteOptimistic => match &declaration {
				WorkerDeclaration::Optimistic => (),
				_ => {
					panic!("Incorrect declaration for optimistic worker");
				},
			},
		}

		let backend = self.state.backend.async_backend();
		let backend: Box<dyn AsyncBackend> = Box::new(sp_state_machine::backend::AsyncBackendAt::new(
			backend,
			&self.state.overlay,
			&declaration,
		));
		self.state.overlay.set_parent_declaration(marker, declaration);

		backend
	}

	fn resolve_worker_result(&mut self, state_update: WorkerResult) -> Option<Vec<u8>> {
		self.state.overlay.resolve_worker_result(state_update)
	}

	fn dismiss_worker(&mut self, id: TaskId) {
		self.state.overlay.dismiss_worker(id)
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
