// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

//! Primitive types for storage related stuff.

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "std")]
use serde::{Serialize, Deserialize};
use substrate_debug_derive::RuntimeDebug;

use rstd::{vec::Vec, borrow::Cow};

/// Storage key.
#[derive(PartialEq, Eq, RuntimeDebug)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Hash, PartialOrd, Ord, Clone))]
pub struct StorageKey(
	#[cfg_attr(feature = "std", serde(with="impl_serde::serialize"))]
	pub Vec<u8>,
);

/// Storage data associated to a [`StorageKey`].
#[derive(PartialEq, Eq, RuntimeDebug)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Hash, PartialOrd, Ord, Clone))]
pub struct StorageData(
	#[cfg_attr(feature = "std", serde(with="impl_serde::serialize"))]
	pub Vec<u8>,
);

/// A set of key value pairs for storage.
#[cfg(feature = "std")]
pub type StorageOverlay = std::collections::HashMap<Vec<u8>, Vec<u8>>;

/// A set of key value pairs for children storage;
#[cfg(feature = "std")]
pub type ChildrenStorageOverlay = std::collections::HashMap<Vec<u8>, StorageOverlay>;

/// Storage change set
#[derive(RuntimeDebug)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, PartialEq, Eq))]
#[cfg_attr(feature = "std", serde(rename_all = "camelCase"))]
pub struct StorageChangeSet<Hash> {
	/// Block hash
	pub block: Hash,
	/// A list of changes
	pub changes: Vec<(StorageKey, Option<StorageData>)>,
}

/// List of all well known keys and prefixes in storage.
pub mod well_known_keys {
	/// Wasm code of the runtime.
	///
	/// Stored as a raw byte vector. Required by substrate.
	pub const CODE: &'static [u8] = b":code";

	/// Number of wasm linear memory pages required for execution of the runtime.
	///
	/// The type of this value is encoded `u64`.
	pub const HEAP_PAGES: &'static [u8] = b":heappages";

	/// Current extrinsic index (u32) is stored under this key.
	pub const EXTRINSIC_INDEX: &'static [u8] = b":extrinsic_index";

	/// Changes trie configuration is stored under this key.
	pub const CHANGES_TRIE_CONFIG: &'static [u8] = b":changes_trie";

	/// Prefix of child storage keys.
	pub const CHILD_STORAGE_KEY_PREFIX: &'static [u8] = b":child_storage:";

	/// Whether a key is a child storage key.
	///
	/// This is convenience function which basically checks if the given `key` starts
	/// with `CHILD_STORAGE_KEY_PREFIX` and doesn't do anything apart from that.
	pub fn is_child_storage_key(key: &[u8]) -> bool {
		// Other code might depend on this, so be careful changing this.
		key.starts_with(CHILD_STORAGE_KEY_PREFIX)
	}

	/// Determine whether a child trie key is valid.
	///
	/// For now, the only valid child trie keys are those starting with `:child_storage:default:`.
	///
	/// `child_trie_root` and `child_delta_trie_root` can panic if invalid value is provided to them.
	pub fn is_child_trie_key_valid(storage_key: &[u8]) -> bool {
		let has_right_prefix = storage_key.starts_with(b":child_storage:default:");
		if has_right_prefix {
			// This is an attempt to catch a change of `is_child_storage_key`, which
			// just checks if the key has prefix `:child_storage:` at the moment of writing.
			debug_assert!(
				is_child_storage_key(&storage_key),
				"`is_child_trie_key_valid` is a subset of `is_child_storage_key`",
			);
		}
		has_right_prefix
	}
}

/// A wrapper around a child storage key.
///
/// This wrapper ensures that the child storage key is correct and properly used. It is
/// impossible to create an instance of this struct without providing a correct `storage_key`.
pub struct ChildStorageKey<'a> {
	storage_key: Cow<'a, [u8]>,
}

impl<'a> ChildStorageKey<'a> {
	/// Create new instance of `Self`.
	fn new(storage_key: Cow<'a, [u8]>) -> Option<Self> {
		if well_known_keys::is_child_trie_key_valid(&storage_key) {
			Some(ChildStorageKey { storage_key })
		} else {
			None
		}
	}

	/// Create a new `ChildStorageKey` from a vector.
	///
	/// `storage_key` need to start with `:child_storage:default:`
	/// See `is_child_trie_key_valid` for more details.
	pub fn from_vec(key: Vec<u8>) -> Option<Self> {
		Self::new(Cow::Owned(key))
	}

	/// Create a new `ChildStorageKey` from a slice.
	///
	/// `storage_key` need to start with `:child_storage:default:`
	/// See `is_child_trie_key_valid` for more details.
	pub fn from_slice(key: &'a [u8]) -> Option<Self> {
		Self::new(Cow::Borrowed(key))
	}

	/// Get access to the byte representation of the storage key.
	///
	/// This key is guaranteed to be correct.
	pub fn as_ref(&self) -> &[u8] {
		&*self.storage_key
	}

	/// Destruct this instance into an owned vector that represents the storage key.
	///
	/// This key is guaranteed to be correct.
	pub fn into_owned(self) -> Vec<u8> {
		self.storage_key.into_owned()
	}
}
