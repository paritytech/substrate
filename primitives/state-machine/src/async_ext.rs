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

use crate::overlayed_changes::OverlayedChanges;
use sp_std::{
	boxed::Box,
	any::{TypeId, Any},
	vec::Vec,
};
use sp_core::{
	storage::{ChildInfo, TrackedStorageKey},
};
use sp_externalities::{Externalities, TaskId, AsyncBackend,
	WorkerResult, WorkerDeclaration, WorkerType, AsyncExternalities};
use sp_core::hexdisplay::HexDisplay;
use crate::ext::guard;
use crate::{StorageValue, StorageKey, trace};

/// Async view on state machine Ext.
/// It contains its own set of state and rules,
/// and returns its changes on `join`.
pub struct AsyncExt {
	kind: WorkerType,
	// Actually unused at this point, is for write variant.
	overlay: OverlayedChanges,
	spawn_id: Option<TaskId>,
	backend: Box<dyn AsyncBackend>,
}

#[cfg(feature = "std")]
impl std::fmt::Debug for AsyncExt
{
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "AsyncExt {:?} at {:?}", self.kind, self.spawn_id)
	}
}

/// Obtain externality and get id for worker.
/// TODO consider having declaration param only for kind declarative and uses default when not
/// here.
/// TODO consider moving it 
/// TODO renma
pub fn spawn_call_ext(
	worker_id: u64,
	declaration: WorkerDeclaration,
	backend: Box<dyn AsyncBackend>,
	parent_overlay: Option<&mut OverlayedChanges>, 
) -> AsyncExt {
	let mut result = match &declaration {
		WorkerDeclaration::Stateless => {
			return AsyncExt {
				kind: WorkerType::Stateless,
				overlay: Default::default(),
				spawn_id: None,
				backend: Box::new(()),
			}
		},
		WorkerDeclaration::ReadLastBlock => {
			return AsyncExt {
				kind: declaration.get_type(),
				overlay: Default::default(),
				spawn_id: None,
				backend,
			}
		},
		_ => {
			AsyncExt {
				kind: declaration.get_type(),
				overlay: Default::default(),
				spawn_id: Some(worker_id),
				backend: backend,
			}
		},
	};
	parent_overlay.map(|overlay| {
		result.overlay = overlay.clone();
		// TODO can also clean past data or get a specific one layer overlay
		result.overlay.start_transaction();
		overlay.set_parent_declaration(worker_id, declaration.clone());
	});
	result.overlay.set_child_declaration(declaration);
	result
}

impl AsyncExt {
	fn guard_stateless(
		&self,
		panic: &'static str,
	) {
		match self.kind {
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

	/// Check if externality can write.
	/// This does not indicate that a given write will
	/// be allowend or will not result in an invalid
	/// worker execution.
	pub fn write_access(&self) -> bool {
		match self.kind {
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

}

impl Externalities for AsyncExt {
	fn set_offchain_storage(&mut self, _key: &[u8], _value: Option<&[u8]>) {
		panic!("`set_offchain_storage`: should not be used in async externalities!")
	}

	fn storage(&self, key: &[u8]) -> Option<StorageValue> {
		self.guard_stateless("`storage`: should not be used in async externalities!");
		let _guard = guard();
		let result = self.overlay.storage(key).map(|x| x.map(|x| x.to_vec())).unwrap_or_else(||
			self.backend.storage(key));
		trace!(target: "state", "{:?}: Th Get {}={:?}",
			self.spawn_id,
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
		let result = self.overlay
			.child_storage(child_info, key)
			.map(|x| x.map(|x| x.to_vec()))
			.unwrap_or_else(||
				self.backend.child_storage(child_info, key));

		trace!(target: "state", "{:?}: Th GetChild({}) {}={:?}",
			self.spawn_id,
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
		let next_backend_key = self.backend.next_storage_key(key);
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
		self.guard_stateless(
			"`next_child_storage_key`: should not be used in async externalities!",
		);
		let next_backend_key = self.backend.next_child_storage_key(child_info, key);
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

	fn place_storage(&mut self, key: StorageKey, maybe_value: Option<StorageValue>) {
		self.guard_read_only("`place_storage`: should not be used in read only worker externalities!");
		self.overlay.set_storage(key, maybe_value);
	}

	fn place_child_storage(
		&mut self,
		child_info: &ChildInfo,
		key: StorageKey,
		value: Option<StorageValue>,
	) {
		self.guard_read_only("`place_child_storage`: should not be used in read only worker externalities!");
		self.overlay.set_child_storage(child_info, key, value);
	}

	fn kill_child_storage(
		&mut self,
		_child_info: &ChildInfo,
	) {
		panic!("`kill_child_storage`: should not be used in read only worker externalities!");
	}

	fn clear_prefix(&mut self, _prefix: &[u8]) {
		panic!("`clear_prefix`: should not be used in read only worker externalities!");
	}

	fn clear_child_prefix(
		&mut self,
		_child_info: &ChildInfo,
		_prefix: &[u8],
	) {
		panic!("`clear_child_prefix`: should not be used in read only worker externalities!");
	}

	fn storage_append(
		&mut self,
		key: Vec<u8>,
		value: Vec<u8>,
	) {
		self.guard_read_only("`storage_append`: should not be used in read only worker externalities!");
		let backend = &mut self.backend;
		let current_value = self.overlay.value_mut_or_insert_with(
			&key,
			|| backend.storage(&key).unwrap_or_default()
		);
		crate::ext::StorageAppend::new(current_value).append(value);
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
		self.overlay.start_transaction()
	}

	fn storage_rollback_transaction(&mut self) -> Result<Vec<TaskId>, ()> {
		self.guard_read_only("`storage_rollback_transaction`: should not be used in read only worker externalities!");
		self.overlay.rollback_transaction().map_err(|_| ())
	}

	fn storage_commit_transaction(&mut self) -> Result<Vec<TaskId>, ()> {
		self.guard_read_only("`storage_commit_transaction`: should not be used in read only worker externalities!");
		self.overlay.commit_transaction().map_err(|_| ())
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
	) -> Box<dyn AsyncExternalities> {
		let backend = self.backend.async_backend();
		self.kind.guard_compatible_child_workers(declaration.get_type());
		Box::new(crate::async_ext::spawn_call_ext(
			worker_id,
			declaration,
			backend,
			Some(&mut self.overlay),
		))
	}
	
	fn resolve_worker_result(&mut self, state_update: WorkerResult) -> Option<Vec<u8>> {
		self.overlay.resolve_worker_result(state_update)
	}

	fn dismiss_worker(&mut self, id: TaskId) {
		self.overlay.dismiss_worker(id)
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

impl AsyncExternalities for AsyncExt {
	fn need_resolve(&self) -> bool {
		self.kind.need_resolve()
	}
	
	fn extract_delta(&mut self) -> Option<sp_externalities::StateDelta> {
		if self.write_access() {
			Some(self.overlay.extract_delta())
		} else {
			None
		}
	}

	fn extract_optimistic_log(&mut self) -> Option<sp_externalities::AccessLog> {
		self.overlay.extract_optimistic_log()
	}
}
