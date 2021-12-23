// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

//! Operation on runtime child storages.
//!
//! This module is a currently only a variant of unhashed with additional `child_info`.
// NOTE: could replace unhashed by having only one kind of storage (top trie being the child info
// of null length parent storage key).

pub use crate::sp_io::KillStorageResult;
use crate::sp_std::prelude::*;
use codec::{Codec, Decode, Encode};
pub use sp_core::storage::{ChildInfo, ChildType};

/// Return the value of the item in storage under `key`, or `None` if there is no explicit entry.
pub fn get<T: Decode + Sized>(child_info: &ChildInfo, key: &[u8]) -> Option<T> {
	match child_info.child_type() {
		ChildType::ParentKeyId => {
			let storage_key = child_info.storage_key();
			sp_io::default_child_storage::get(storage_key, key).and_then(|v| {
				Decode::decode(&mut &v[..]).map(Some).unwrap_or_else(|_| {
					// TODO #3700: error should be handleable.
					crate::runtime_print!(
						"ERROR: Corrupted state in child trie at {:?}/{:?}",
						storage_key,
						key,
					);
					None
				})
			})
		},
	}
}

/// Return the value of the item in storage under `key`, or the type's default if there is no
/// explicit entry.
pub fn get_or_default<T: Decode + Sized + Default>(child_info: &ChildInfo, key: &[u8]) -> T {
	get(child_info, key).unwrap_or_else(Default::default)
}

/// Return the value of the item in storage under `key`, or `default_value` if there is no
/// explicit entry.
pub fn get_or<T: Decode + Sized>(child_info: &ChildInfo, key: &[u8], default_value: T) -> T {
	get(child_info, key).unwrap_or(default_value)
}

/// Return the value of the item in storage under `key`, or `default_value()` if there is no
/// explicit entry.
pub fn get_or_else<T: Decode + Sized, F: FnOnce() -> T>(
	child_info: &ChildInfo,
	key: &[u8],
	default_value: F,
) -> T {
	get(child_info, key).unwrap_or_else(default_value)
}

/// Put `value` in storage under `key`.
pub fn put<T: Encode>(child_info: &ChildInfo, key: &[u8], value: &T) {
	match child_info.child_type() {
		ChildType::ParentKeyId => value.using_encoded(|slice| {
			sp_io::default_child_storage::set(child_info.storage_key(), key, slice)
		}),
	}
}

/// Remove `key` from storage, returning its value if it had an explicit entry or `None` otherwise.
pub fn take<T: Decode + Sized>(child_info: &ChildInfo, key: &[u8]) -> Option<T> {
	let r = get(child_info, key);
	if r.is_some() {
		kill(child_info, key);
	}
	r
}

/// Remove `key` from storage, returning its value, or, if there was no explicit entry in storage,
/// the default for its type.
pub fn take_or_default<T: Codec + Sized + Default>(child_info: &ChildInfo, key: &[u8]) -> T {
	take(child_info, key).unwrap_or_else(Default::default)
}

/// Return the value of the item in storage under `key`, or `default_value` if there is no
/// explicit entry. Ensure there is no explicit entry on return.
pub fn take_or<T: Codec + Sized>(child_info: &ChildInfo, key: &[u8], default_value: T) -> T {
	take(child_info, key).unwrap_or(default_value)
}

/// Return the value of the item in storage under `key`, or `default_value()` if there is no
/// explicit entry. Ensure there is no explicit entry on return.
pub fn take_or_else<T: Codec + Sized, F: FnOnce() -> T>(
	child_info: &ChildInfo,
	key: &[u8],
	default_value: F,
) -> T {
	take(child_info, key).unwrap_or_else(default_value)
}

/// Check to see if `key` has an explicit entry in storage.
pub fn exists(child_info: &ChildInfo, key: &[u8]) -> bool {
	match child_info.child_type() {
		ChildType::ParentKeyId =>
			sp_io::default_child_storage::exists(child_info.storage_key(), key),
	}
}

/// Remove all `storage_key` key/values
///
/// Deletes all keys from the overlay and up to `limit` keys from the backend if
/// it is set to `Some`. No limit is applied when `limit` is set to `None`.
///
/// The limit can be used to partially delete a child trie in case it is too large
/// to delete in one go (block).
///
/// # Note
///
/// Please note that keys that are residing in the overlay for that child trie when
/// issuing this call are all deleted without counting towards the `limit`. Only keys
/// written during the current block are part of the overlay. Deleting with a `limit`
/// mostly makes sense with an empty overlay for that child trie.
///
/// Calling this function multiple times per block for the same `storage_key` does
/// not make much sense because it is not cumulative when called inside the same block.
/// Use this function to distribute the deletion of a single child trie across multiple
/// blocks.
pub fn kill_storage(child_info: &ChildInfo, limit: Option<u32>) -> KillStorageResult {
	match child_info.child_type() {
		ChildType::ParentKeyId =>
			sp_io::default_child_storage::storage_kill(child_info.storage_key(), limit),
	}
}

/// Ensure `key` has no explicit entry in storage.
pub fn kill(child_info: &ChildInfo, key: &[u8]) {
	match child_info.child_type() {
		ChildType::ParentKeyId => {
			sp_io::default_child_storage::clear(child_info.storage_key(), key);
		},
	}
}

/// Get a Vec of bytes from storage.
pub fn get_raw(child_info: &ChildInfo, key: &[u8]) -> Option<Vec<u8>> {
	match child_info.child_type() {
		ChildType::ParentKeyId => sp_io::default_child_storage::get(child_info.storage_key(), key),
	}
}

/// Put a raw byte slice into storage.
pub fn put_raw(child_info: &ChildInfo, key: &[u8], value: &[u8]) {
	match child_info.child_type() {
		ChildType::ParentKeyId =>
			sp_io::default_child_storage::set(child_info.storage_key(), key, value),
	}
}

/// Calculate current child root value.
pub fn root(child_info: &ChildInfo) -> Vec<u8> {
	match child_info.child_type() {
		ChildType::ParentKeyId => sp_io::default_child_storage::root(child_info.storage_key()),
	}
}

/// Return the length in bytes of the value without reading it. `None` if it does not exist.
pub fn len(child_info: &ChildInfo, key: &[u8]) -> Option<u32> {
	match child_info.child_type() {
		ChildType::ParentKeyId => {
			let mut buffer = [0; 0];
			sp_io::default_child_storage::read(child_info.storage_key(), key, &mut buffer, 0)
		},
	}
}
