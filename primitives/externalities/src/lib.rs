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

#![cfg_attr(not(feature = "std"), no_std)]

//! Substrate externalities abstraction
//!
//! The externalities mainly provide access to storage and to registered extensions. Extensions
//! are for example the keystore or the offchain externalities. These externalities are used to
//! access the node from the runtime via the runtime interfaces.
//!
//! This crate exposes the main [`Externalities`] trait.

use sp_std::{any::{Any, TypeId}, vec::Vec, boxed::Box};

use sp_storage::{ChildInfo, TrackedStorageKey};

pub use scope_limited::{set_and_run_with_externalities, with_externalities};
pub use extensions::{Extension, Extensions, ExtensionStore};

mod extensions;
mod scope_limited;

/// Externalities error.
#[derive(Debug)]
pub enum Error {
	/// Same extension cannot be registered twice.
	ExtensionAlreadyRegistered,
	/// Extensions are not supported.
	ExtensionsAreNotSupported,
	/// Extension `TypeId` is not registered.
	ExtensionIsNotRegistered(TypeId),
	/// Failed to update storage,
	StorageUpdateFailed(&'static str),
}

/// The Substrate externalities.
///
/// Provides access to the storage and to other registered extensions.
pub trait Externalities: ExtensionStore {
	/// Write a key value pair to the offchain storage database.
	fn set_offchain_storage(&mut self, key: &[u8], value: Option<&[u8]>);

	/// Read runtime storage.
	fn storage(&self, key: &[u8]) -> Option<Vec<u8>>;

	/// Get storage value hash.
	///
	/// This may be optimized for large values.
	fn storage_hash(&self, key: &[u8]) -> Option<Vec<u8>>;

	/// Get child storage value hash.
	///
	/// This may be optimized for large values.
	///
	/// Returns an `Option` that holds the SCALE encoded hash.
	fn child_storage_hash(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Option<Vec<u8>>;

	/// Read child runtime storage.
	///
	/// Returns an `Option` that holds the SCALE encoded hash.
	fn child_storage(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Option<Vec<u8>>;

	/// Set storage entry `key` of current contract being called (effective immediately).
	fn set_storage(&mut self, key: Vec<u8>, value: Vec<u8>) {
		self.place_storage(key, Some(value));
	}

	/// Set child storage entry `key` of current contract being called (effective immediately).
	fn set_child_storage(
		&mut self,
		child_info: &ChildInfo,
		key: Vec<u8>,
		value: Vec<u8>,
	) {
		self.place_child_storage(child_info, key, Some(value))
	}

	/// Clear a storage entry (`key`) of current contract being called (effective immediately).
	fn clear_storage(&mut self, key: &[u8]) {
		self.place_storage(key.to_vec(), None);
	}

	/// Clear a child storage entry (`key`) of current contract being called (effective immediately).
	fn clear_child_storage(
		&mut self,
		child_info: &ChildInfo,
		key: &[u8],
	) {
		self.place_child_storage(child_info, key.to_vec(), None)
	}

	/// Whether a storage entry exists.
	fn exists_storage(&self, key: &[u8]) -> bool {
		self.storage(key).is_some()
	}

	/// Whether a child storage entry exists.
	fn exists_child_storage(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> bool {
		self.child_storage(child_info, key).is_some()
	}

	/// Returns the key immediately following the given key, if it exists.
	fn next_storage_key(&self, key: &[u8]) -> Option<Vec<u8>>;

	/// Returns the key immediately following the given key, if it exists, in child storage.
	fn next_child_storage_key(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Option<Vec<u8>>;

	/// Clear an entire child storage.
	///
	/// Deletes all keys from the overlay and up to `limit` keys from the backend. No
	/// limit is applied if `limit` is `None`. Returns `true` if the child trie was
	/// removed completely and `false` if there are remaining keys after the function
	/// returns.
	///
	/// # Note
	///
	/// An implementation is free to delete more keys than the specified limit as long as
	/// it is able to do that in constant time.
	fn kill_child_storage(&mut self, child_info: &ChildInfo, limit: Option<u32>) -> bool;

	/// Clear storage entries which keys are start with the given prefix.
	fn clear_prefix(&mut self, prefix: &[u8]);

	/// Clear child storage entries which keys are start with the given prefix.
	fn clear_child_prefix(
		&mut self,
		child_info: &ChildInfo,
		prefix: &[u8],
	);

	/// Set or clear a storage entry (`key`) of current contract being called (effective immediately).
	fn place_storage(&mut self, key: Vec<u8>, value: Option<Vec<u8>>);

	/// Set or clear a child storage entry.
	fn place_child_storage(
		&mut self,
		child_info: &ChildInfo,
		key: Vec<u8>,
		value: Option<Vec<u8>>,
	);

	/// Get the trie root of the current storage map.
	///
	/// This will also update all child storage keys in the top-level storage map.
	///
	/// The returned hash is defined by the `Block` and is SCALE encoded.
	fn storage_root(&mut self) -> Vec<u8>;

	/// Get the trie root of a child storage map.
	///
	/// This will also update the value of the child storage keys in the top-level storage map.
	///
	/// If the storage root equals the default hash as defined by the trie, the key in the top-level
	/// storage map will be removed.
	fn child_storage_root(
		&mut self,
		child_info: &ChildInfo,
	) -> Vec<u8>;

	/// Append storage item.
	///
	/// This assumes specific format of the storage item. Also there is no way to undo this operation.
	fn storage_append(
		&mut self,
		key: Vec<u8>,
		value: Vec<u8>,
	);

	/// Get the changes trie root of the current storage overlay at a block with given `parent`.
	///
	/// `parent` expects a SCALE encoded hash.
	///
	/// The returned hash is defined by the `Block` and is SCALE encoded.
	fn storage_changes_root(&mut self, parent: &[u8]) -> Result<Option<Vec<u8>>, ()>;

	/// Start a new nested transaction.
	///
	/// This allows to either commit or roll back all changes made after this call to the
	/// top changes or the default child changes. For every transaction there cam be a
	/// matching call to either `storage_rollback_transaction` or `storage_commit_transaction`.
	/// Any transactions that are still open after returning from runtime are committed
	/// automatically.
	///
	/// Changes made without any open transaction are committed immediately.
	fn storage_start_transaction(&mut self);

	/// Rollback the last transaction started by `storage_start_transaction`.
	///
	/// Any changes made during that storage transaction are discarded. Returns an error when
	/// no transaction is open that can be closed.
	///
	/// Return possible task ids of tasks that will not be in synch with the thread to allow
	/// early kill.
	/// TODO remove the task id (not directly use here, but is part of the mechanism)? would
	/// think good to have.
	fn storage_rollback_transaction(&mut self) -> Result<Vec<TaskId>, ()>;

	/// Commit the last transaction started by `storage_start_transaction`.
	///
	/// Any changes made during that storage transaction are committed. Returns an error when
	/// no transaction is open that can be closed.
	///
	/// Return possible task ids of tasks that will not be in synch with the thread to allow
	/// early kill.
	fn storage_commit_transaction(&mut self) -> Result<Vec<TaskId>, ()>;

	/// !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
	/// Benchmarking related functionality and shouldn't be used anywhere else!
	/// !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
	///
	/// Wipes all changes from caches and the database.
	///
	/// The state will be reset to genesis.
	fn wipe(&mut self);

	/// !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
	/// Benchmarking related functionality and shouldn't be used anywhere else!
	/// !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
	///
	/// Commits all changes to the database and clears all caches.
	fn commit(&mut self);

	/// !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
	/// Benchmarking related functionality and shouldn't be used anywhere else!
	/// !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
	///
	/// Gets the current read/write count for the benchmarking process.
	fn read_write_count(&self) -> (u32, u32, u32, u32);

	/// !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
	/// Benchmarking related functionality and shouldn't be used anywhere else!
	/// !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
	///
	/// Resets read/write count for the benchmarking process.
	fn reset_read_write_count(&mut self);

	/// !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
	/// Benchmarking related functionality and shouldn't be used anywhere else!
	/// !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
	///
	/// Gets the current DB tracking whitelist.
	fn get_whitelist(&self) -> Vec<TrackedStorageKey>;

	/// !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
	/// Benchmarking related functionality and shouldn't be used anywhere else!
	/// !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
	///
	/// Adds new storage keys to the DB tracking whitelist.
	fn set_whitelist(&mut self, new: Vec<TrackedStorageKey>);

	/// Get externalities to use with a future worker.
	fn get_worker_externalities(
		&mut self,
		worker_id: u64,
		declaration: WorkerDeclaration,
	) -> Box<dyn AsyncExternalities>;

	/// Resolve worker result does update externality state
	/// and also apply rules relative to the exernality state.
	///
	/// This method must be call before processing any worker result,
	/// for instance from a worker point of view the result may be valid,
	/// but after checking against parent externalities, it may change
	/// to invalid (`None`).
	fn resolve_worker_result(&mut self, result: WorkerResult) -> Option<Vec<u8>>;

	/// Worker result have been dissmiss, inner externality state and constraint
	/// needs to be lifted.
	/// TODO consider making it a worker result variant and only have 'resolve_worker_result'.
	fn dismiss_worker(&mut self, id: TaskId);
}

/// Substrate externalities that can be use within a worker context.
pub trait AsyncExternalities: Externalities + Send {
	/// Extract changes made to state by this worker.
	fn extract_delta(&mut self) -> Option<StateDelta>;

	/// After execution, we call back async externalities to check
	/// produce worker result.
	fn extract_state(&mut self) -> AsyncExternalitiesPostExecution;
}

/// State of async externality of a child worker after 'join' is called.
pub enum AsyncExternalitiesPostExecution {
	/// Some condition fails and the state is invalid.
	/// With an invalid state we consider that worker
	/// execution, even if it did finish is invalid.
	/// Therefore 'join' implementation should never
	/// return result when externality is in this state.
	Invalid,

	/// Assuming that child worker state is valid, we can
	/// return the result to the parent worker on 'join'.
	Valid,

	/// This requires to check the result against
	/// parent worker externalities with `resolve_worker_result`.
	NeedResolve,

	/// Optimistic worker state accesses to be checked
	/// against other worker results.
	/// This can result in 'join' returning an invalid
	/// result.
	Optimistic(AccessLog),
}

/// Result from worker execution.
///
/// Note that an error that is expected should
/// be serialize in a `Valid` result payload.
#[derive(codec::Encode, codec::Decode)]
pub enum WorkerResult {
	/// Payload resulting from a successfull
	/// call that is guaranted to be valid
	/// at this point.
	/// eg. a stateless worker.
	Valid(Vec<u8>, Option<StateDelta>),
	/// Result that require to be checked against
	/// its parent externality state.
	CallAt(Vec<u8>, Option<StateDelta>, TaskId),
	/// Optimistic strategy call reply, it contains
	/// a log of accessed keys during child execution.
	Optimistic(Vec<u8>, Option<StateDelta>, TaskId, AccessLog),
	/// A worker execution that is not valid.
	/// For instance when asumption on state
	/// are required.
	Invalid,
	/// Internal panic when runing the worker.
	/// This propagate panic in caller.
	RuntimePanic,
	/// Technical panic when runing the worker.
	/// This propagate panic in caller, and also
	/// indicate the process should be stop. 
	HardPanic,
}

/// Changes to state made by a worker.
///
/// At this point this is only a placeholder.
/// FIXME: Complete the code to record access
/// in state machine (see https://github.com/paritytech/substrate/pull/7687).
#[derive(codec::Encode, codec::Decode)]
pub struct StateDelta;

impl Default for StateDelta {
	fn default() -> Self {
		StateDelta
	}
}

impl StateDelta {
	/// Does state delta contain change.
	pub fn is_empty(&self) -> bool {
		// FIXME: Complete when actual worker backend with write.
		true
	}
}

/// Log of a given worker call.
///
/// At this point this is only a placeholder.
/// FIXME: Complete the code to record access
/// in state machine (see https://github.com/paritytech/substrate/pull/7687).
#[derive(codec::Encode, codec::Decode, Default)]
pub struct AccessLog;

/// A unique identifier type for a child worker.
/// This is not unique between nested worker (their
/// unique id would an array of the nested task id).
pub type TaskId = u64;

/// Differents workers execution mode.
/// Internally defining the worker type can result in differents `AsyncExt` externality.
#[derive(Debug)]
#[repr(u8)]
pub enum WorkerType {
	/// Worker panic on state access from externalities.
	Stateless = 0,
}

impl Default for WorkerType {
	fn default() -> Self {
		WorkerType::Stateless
	}
}

impl WorkerType {
	/// Similar purpose as `TryFrom<u8>`.
	pub fn from_u8(kind: u8) -> Option<WorkerType> {
		Some(match kind {
			0 => WorkerType::Stateless,
			_ => return None,
		})
	}

	/// Depending on concurrency management strategy
	/// we may need to resolve the result against
	/// parent externalities.
	pub fn need_resolve(&self) -> bool {
		match *self {
			WorkerType::Stateless => false,
		}
	}

	/// Panic if spawning a child worker of a given type is not possible
	/// regarding current parent worker.
	/// Eg: spawning a worker with state from a worker without state
	/// is fundamentally wrong.
	pub fn guard_compatible_child_workers(&self, kind: WorkerType) {
		match kind {
			// A stateless worker is always spawnable.
			WorkerType::Stateless => (),
		}
	}
}

/// Enum wrapping `WorkerType` to include additional
/// information.
///
/// FIXME: at this point this is mainly a place holder.
/// In https://github.com/paritytech/substrate/pull/7687
/// it is mainly use to attach state access assumption.
#[derive(Debug, Clone, codec::Encode, codec::Decode)]
pub enum WorkerDeclaration {
	/// Declaration for `WorkerType::Stateless`, no content.
	Stateless,
}

impl WorkerDeclaration {
	/// Extract type from declaration.
	pub fn get_type(&self) -> WorkerType {
		match self {
			WorkerDeclaration::Stateless => WorkerType::Stateless,
		}
	}
}

/// Extension for the [`Externalities`] trait.
pub trait ExternalitiesExt {
	/// Tries to find a registered extension and returns a mutable reference.
	fn extension<T: Any + Extension>(&mut self) -> Option<&mut T>;

	/// Register extension `ext`.
	///
	/// Should return error if extension is already registered or extensions are not supported.
	fn register_extension<T: Extension>(&mut self, ext: T) -> Result<(), Error>;

	/// Deregister and drop extension of `T` type.
	///
	/// Should return error if extension of type `T` is not registered or
	/// extensions are not supported.
	fn deregister_extension<T: Extension>(&mut self) -> Result<(), Error>;
}

impl ExternalitiesExt for &mut dyn Externalities {
	fn extension<T: Any + Extension>(&mut self) -> Option<&mut T> {
		self.extension_by_type_id(TypeId::of::<T>()).and_then(Any::downcast_mut)
	}

	fn register_extension<T: Extension>(&mut self, ext: T) -> Result<(), Error> {
		self.register_extension_with_type_id(TypeId::of::<T>(), Box::new(ext))
	}

	fn deregister_extension<T: Extension>(&mut self) -> Result<(), Error> {
		self.deregister_extension_by_type_id(TypeId::of::<T>())
	}
}
