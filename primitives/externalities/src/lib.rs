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
	fn kill_child_storage(&mut self, child_info: &ChildInfo);

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

	/// Get the identity of the chain.
	fn chain_id(&self) -> u64;

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
	/// Return possible task id of task that will not be in synch with the thread to allow
	/// early kill.
	fn storage_rollback_transaction(&mut self) -> Result<Vec<TaskId>, ()>;

	/// Commit the last transaction started by `storage_start_transaction`.
	///
	/// Any changes made during that storage transaction are committed. Returns an error when
	/// no transaction is open that can be closed.
	fn storage_commit_transaction(&mut self) -> Result<(), ()>;

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

	/// Get async backend that do not contains current changes.
	/// (state for previous block).
	///
	/// Note that when we return none, primitive for starting thread
	/// should return a handle with an inline version.
	/// The inline version here will not require additional data.
	fn get_past_async_backend(&self) -> Option<Box<dyn AsyncBackend>>;

	/// Get current async backend, and set a marker on the current state
	/// to be able to identify changes.
	/// Adding this checkpoint state allows externalities to kill all tasks
	/// associated with this state if it gets dropped (by transactional
	/// rollback).
	///
	///	Note that when we return none, primitive for starting thread
	/// should return a handle with an inline version.
	/// The inline version here will not require a snapshot of the current
	/// state, and the marker should be still registerd by this call.
	fn get_async_backend(&mut self, marker: TaskId) -> Option<Box<dyn AsyncBackend>>;

	/// Check if state is the same as when an AsyncBackend was acquired.
	/// TODO actually if we kill, this is not needed (except if we want
	/// to avoid a panic on a join, but we would most likely return enum
	/// on join for case where thread has been killed).
	fn is_state_current(&self, marker: TaskId) -> bool;
}

/// A unique indentifier for a transactional level.
pub type TaskId = u64;

/// Backend to use with threads.
/// This trait must be usable as `dyn AsyncBackend`,
/// which is not the case for Backend trait.
pub trait AsyncBackend: Send {
	/// TODO
	fn storage(&self, key: &[u8]) -> Option<Vec<u8>>;

	/// TODO
	fn child_storage(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Option<Vec<u8>>;

	/// TODO
	fn next_storage_key(&self, key: &[u8]) -> Option<Vec<u8>>;

	/// TODO
	fn next_child_storage_key(
		&self,
		child_info: &ChildInfo,
		key: &[u8]
	) -> Option<Vec<u8>>;

	/// TODO this is just some way to clone without having
	/// AsyncBackend: Clone.
	/// With no_std dyn clone, we could remove it.
	fn async_backend(&self) -> Option<Box<dyn AsyncBackend>>;

}

/// This act as `AsyncBackend` but not `Sync`
/// or `Send` it can be build with a pointer
/// to externalities.
/// TODO this will require that &mut ext
/// is passed as parameter to join (same as call).
/// TODO actually this could be probably implemented
/// just from an handle to current backend and a struct.
/// TODO in fact we just need to wrap a new externalities
/// when calling inline, this externalities running over
/// state snapshot. -> ext would need same set as asyncbackend.
/// -> it means being able to call with_externalities over &'a
/// which is not doable with proto containing &mut dyn Externalities
/// (dyn require static).
/// -> TODO make a externalities function 'set_inline' with this
/// as parameter that reset after call.
/// enum {
///   Disable
///   PreviousBlock, // calls directly on backend of ext
///   PreviousAt(Overlay), // calls the overlay then the backend
/// }
///
/// then still put a set_with_ext but just to filter calls that
/// are not doable with AsyncExternalities (actually may be able
/// to reuse async Ext?? by using commpon trait with asyncbackend).
/// in fact it is same as externalities wrapping externalities with
/// access to &backend the subset of async backen without Send.
///
/// TODO consider to macro `AsyncExt` code (in sp_tasks) with
/// a non send `InlineExt` variant. Same for associated ext
pub trait InlineBackend {
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
