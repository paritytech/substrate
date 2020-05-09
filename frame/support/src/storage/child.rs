// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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

//! Operation on runtime child storages.
//!
//! This module is a currently only a variant of unhashed with additional `child_info`.
// NOTE: could replace unhashed by having only one kind of storage (top trie being the child info
// of null length parent storage key).

use crate::sp_std::prelude::*;
use codec::{Codec, Encode, Decode};
pub use sp_core::storage::{ChildInfo, ChildType};

/// Return the value of the item in storage under `key`, or `None` if there is no explicit entry.
pub fn get<T: Decode + Sized>(
	child_info: &ChildInfo,
	key: &[u8],
) -> Option<T> {
	match child_info.child_type() {
		ChildType::ParentKeyId => {
			let storage_key = child_info.storage_key();
			sp_io::default_child_storage::get(
				storage_key,
				key,
			).and_then(|v| {
				Decode::decode(&mut &v[..]).map(Some).unwrap_or_else(|_| {
					// TODO #3700: error should be handleable.
					runtime_print!("ERROR: Corrupted state in child trie at {:?}/{:?}", storage_key, key);
					None
				})
			})
		},
	}
}

/// Return the value of the item in storage under `key`, or the type's default if there is no
/// explicit entry.
pub fn get_or_default<T: Decode + Sized + Default>(
	child_info: &ChildInfo,
	key: &[u8],
) -> T {
	get(child_info, key).unwrap_or_else(Default::default)
}

/// Return the value of the item in storage under `key`, or `default_value` if there is no
/// explicit entry.
pub fn get_or<T: Decode + Sized>(
	child_info: &ChildInfo,
	key: &[u8],
	default_value: T,
) -> T {
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
pub fn put<T: Encode>(
	child_info: &ChildInfo,
	key: &[u8],
	value: &T,
) {
	match child_info.child_type() {
		ChildType::ParentKeyId => value.using_encoded(|slice|
			sp_io::default_child_storage::set(
				child_info.storage_key(),
				key,
				slice,
			)
		),
	}
}

/// Remove `key` from storage, returning its value if it had an explicit entry or `None` otherwise.
pub fn take<T: Decode + Sized>(
	child_info: &ChildInfo,
	key: &[u8],
) -> Option<T> {
	let r = get(child_info, key);
	if r.is_some() {
		kill(child_info, key);
	}
	r
}

/// Remove `key` from storage, returning its value, or, if there was no explicit entry in storage,
/// the default for its type.
pub fn take_or_default<T: Codec + Sized + Default>(
	child_info: &ChildInfo,
	key: &[u8],
) -> T {
	take(child_info, key).unwrap_or_else(Default::default)
}

/// Return the value of the item in storage under `key`, or `default_value` if there is no
/// explicit entry. Ensure there is no explicit entry on return.
pub fn take_or<T: Codec + Sized>(
	child_info: &ChildInfo,
	key: &[u8],
	default_value: T,
) -> T {
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
pub fn exists(
	child_info: &ChildInfo,
	key: &[u8],
) -> bool {
	match child_info.child_type() {
		ChildType::ParentKeyId => sp_io::default_child_storage::read(
			child_info.storage_key(),
			key, &mut [0;0][..], 0,
		).is_some(),
	}
}

/// Remove all `storage_key` key/values
pub fn kill_storage(
	child_info: &ChildInfo,
) {
	match child_info.child_type() {
		ChildType::ParentKeyId => sp_io::default_child_storage::storage_kill(
			child_info.storage_key(),
		),
	}
}

/// Ensure `key` has no explicit entry in storage.
pub fn kill(
	child_info: &ChildInfo,
	key: &[u8],
) {
	match child_info.child_type() {
		ChildType::ParentKeyId => {
			sp_io::default_child_storage::clear(
				child_info.storage_key(),
				key,
			);
		},
	}
}

/// Get a Vec of bytes from storage.
pub fn get_raw(
	child_info: &ChildInfo,
	key: &[u8],
) -> Option<Vec<u8>> {
	match child_info.child_type() {
		ChildType::ParentKeyId => sp_io::default_child_storage::get(
			child_info.storage_key(),
			key,
		),
	}
}

/// Put a raw byte slice into storage.
pub fn put_raw(
	child_info: &ChildInfo,
	key: &[u8],
	value: &[u8],
) {
	match child_info.child_type() {
		ChildType::ParentKeyId => sp_io::default_child_storage::set(
			child_info.storage_key(),
			key,
			value,
		),
	}
}

/// Calculate current child root value.
pub fn root(
	child_info: &ChildInfo,
) -> Vec<u8> {
	match child_info.child_type() {
		ChildType::ParentKeyId => sp_io::default_child_storage::root(
			child_info.storage_key(),
		),
	}
}
