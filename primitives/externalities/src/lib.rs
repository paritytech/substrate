// Copyright 2017-2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Substrate externalities abstraction
//!
//! The externalities mainly provide access to storage and to registered extensions. Extensions
//! are for example the keystore or the offchain externalities. These externalities are used to
//! access the node from the runtime via the runtime interfaces.
//!
//! This crate exposes the main [`Externalities`] trait.

use std::any::{Any, TypeId};

use sp_storage::{ChildStorageKey, ChildInfo};

pub use scope_limited::{set_and_run_with_externalities, with_externalities};
pub use extensions::{Extension, Extensions, ExtensionStore};

mod extensions;
mod scope_limited;

/// The Substrate externalities.
///
/// Provides access to the storage and to other registered extensions.
pub trait Externalities: ExtensionStore {
	/// Read runtime storage.
	fn storage(&self, key: &[u8]) -> Option<Vec<u8>>;

	/// Get storage value hash. This may be optimized for large values.
	fn storage_hash(&self, key: &[u8]) -> Option<Vec<u8>>;

	/// Get child storage value hash. This may be optimized for large values.
	///
	/// Returns an `Option` that holds the SCALE encoded hash.
	fn child_storage_hash(
		&self,
		storage_key: ChildStorageKey,
		child_info: ChildInfo,
		key: &[u8],
	) -> Option<Vec<u8>>;

	/// Read child runtime storage.
	///
	/// Returns an `Option` that holds the SCALE encoded hash.
	fn child_storage(
		&self,
		storage_key: ChildStorageKey,
		child_info: ChildInfo,
		key: &[u8],
	) -> Option<Vec<u8>>;

	/// Set storage entry `key` of current contract being called (effective immediately).
	fn set_storage(&mut self, key: Vec<u8>, value: Vec<u8>) {
		self.place_storage(key, Some(value));
	}

	/// Set child storage entry `key` of current contract being called (effective immediately).
	fn set_child_storage(
		&mut self,
		storage_key: ChildStorageKey,
		child_info: ChildInfo,
		key: Vec<u8>,
		value: Vec<u8>,
	) {
		self.place_child_storage(storage_key, child_info, key, Some(value))
	}

	/// Clear a storage entry (`key`) of current contract being called (effective immediately).
	fn clear_storage(&mut self, key: &[u8]) {
		self.place_storage(key.to_vec(), None);
	}

	/// Clear a child storage entry (`key`) of current contract being called (effective immediately).
	fn clear_child_storage(
		&mut self,
		storage_key: ChildStorageKey,
		child_info: ChildInfo,
		key: &[u8],
	) {
		self.place_child_storage(storage_key, child_info, key.to_vec(), None)
	}

	/// Whether a storage entry exists.
	fn exists_storage(&self, key: &[u8]) -> bool {
		self.storage(key).is_some()
	}

	/// Whether a child storage entry exists.
	fn exists_child_storage(
		&self,
		storage_key: ChildStorageKey,
		child_info: ChildInfo,
		key: &[u8],
	) -> bool {
		self.child_storage(storage_key, child_info, key).is_some()
	}

	/// Returns the key immediately following the given key, if it exists.
	fn next_storage_key(&self, key: &[u8]) -> Option<Vec<u8>>;

	/// Returns the key immediately following the given key, if it exists, in child storage.
	fn next_child_storage_key(
		&self,
		storage_key: ChildStorageKey,
		child_info: ChildInfo,
		key: &[u8],
	) -> Option<Vec<u8>>;

	/// Clear an entire child storage.
	fn kill_child_storage(&mut self, storage_key: ChildStorageKey, child_info: ChildInfo);

	/// Clear storage entries which keys are start with the given prefix.
	fn clear_prefix(&mut self, prefix: &[u8]);

	/// Clear child storage entries which keys are start with the given prefix.
	fn clear_child_prefix(
		&mut self,
		storage_key: ChildStorageKey,
		child_info: ChildInfo,
		prefix: &[u8],
	);

	/// Set or clear a storage entry (`key`) of current contract being called (effective immediately).
	fn place_storage(&mut self, key: Vec<u8>, value: Option<Vec<u8>>);

	/// Set or clear a child storage entry. Return whether the operation succeeds.
	fn place_child_storage(
		&mut self,
		storage_key: ChildStorageKey,
		child_info: ChildInfo,
		key: Vec<u8>,
		value: Option<Vec<u8>>,
	);

	/// Get the identity of the chain.
	fn chain_id(&self) -> u64;

	/// Get the trie root of the current storage map. This will also update all child storage keys
	/// in the top-level storage map.
	///
	/// The hash is defined by the `Block`.
	///
	/// Returns the SCALE encoded hash.
	fn storage_root(&mut self) -> Vec<u8>;

	/// Get the trie root of a child storage map. This will also update the value of the child
	/// storage keys in the top-level storage map.
	/// If the storage root equals the default hash as defined by the trie, the key in the top-level
	/// storage map will be removed.
	fn child_storage_root(
		&mut self,
		storage_key: ChildStorageKey,
	) -> Vec<u8>;

	/// Get the change trie root of the current storage overlay at a block with given parent.
	/// `parent` is expects a SCALE encoded hash.
	///
	/// The hash is defined by the `Block`.
	///
	/// Returns the SCALE encoded hash.
	fn storage_changes_root(&mut self, parent: &[u8]) -> Result<Option<Vec<u8>>, ()>;

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
}

/// Extension for the [`Externalities`] trait.
pub trait ExternalitiesExt {
	/// Tries to find a registered extension and returns a mutable reference.
	fn extension<T: Any + Extension>(&mut self) -> Option<&mut T>;
}

impl ExternalitiesExt for &mut dyn Externalities {
	fn extension<T: Any + Extension>(&mut self) -> Option<&mut T> {
		self.extension_by_type_id(TypeId::of::<T>()).and_then(Any::downcast_mut)
	}
}
