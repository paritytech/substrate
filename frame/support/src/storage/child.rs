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
//! This module is a currently only a variant of unhashed with additional `storage_key`.
//! Note that `storage_key` must be unique and strong (strong in the sense of being long enough to
//! avoid collision from a resistant hash function (which unique implies)).
//!
//! A **key collision free** unique id is required as parameter to avoid key collision
//! between child tries.
//! This unique id management and generation responsability is delegated to pallet module.
// NOTE: could replace unhashed by having only one kind of storage (root being null storage key (storage_key can become Option<&[u8]>).

use crate::sp_std::prelude::*;
use codec::{Codec, Encode, Decode};
pub use sp_core::storage::ChildInfo;

/// Return the value of the item in storage under `key`, or `None` if there is no explicit entry.
pub fn get<T: Decode + Sized>(
	storage_key: &[u8],
	child_info: ChildInfo,
	key: &[u8],
) -> Option<T> {
	let (data, child_type) = child_info.info();
	sp_io::storage::child_get(
		storage_key,
		data,
		child_type,
		key,
	).and_then(|v| {
		Decode::decode(&mut &v[..]).map(Some).unwrap_or_else(|_| {
			// TODO #3700: error should be handleable.
			runtime_print!("ERROR: Corrupted state in child trie at {:?}/{:?}", storage_key, key);
			None
		})
	})
}

/// Return the value of the item in storage under `key`, or the type's default if there is no
/// explicit entry.
pub fn get_or_default<T: Decode + Sized + Default>(
	storage_key: &[u8],
	child_info: ChildInfo,
	key: &[u8],
) -> T {
	get(storage_key, child_info, key).unwrap_or_else(Default::default)
}

/// Return the value of the item in storage under `key`, or `default_value` if there is no
/// explicit entry.
pub fn get_or<T: Decode + Sized>(
	storage_key: &[u8],
	child_info: ChildInfo,
	key: &[u8],
	default_value: T,
) -> T {
	get(storage_key, child_info, key).unwrap_or(default_value)
}

/// Return the value of the item in storage under `key`, or `default_value()` if there is no
/// explicit entry.
pub fn get_or_else<T: Decode + Sized, F: FnOnce() -> T>(
	storage_key: &[u8],
	child_info: ChildInfo,
	key: &[u8],
	default_value: F,
) -> T {
	get(storage_key, child_info, key).unwrap_or_else(default_value)
}

/// Put `value` in storage under `key`.
pub fn put<T: Encode>(
	storage_key: &[u8],
	child_info: ChildInfo,
	key: &[u8],
	value: &T,
) {
	let (data, child_type) = child_info.info();
	value.using_encoded(|slice|
		sp_io::storage::child_set(
			storage_key,
			data,
			child_type,
			key,
			slice,
		)
	);
}

/// Remove `key` from storage, returning its value if it had an explicit entry or `None` otherwise.
pub fn take<T: Decode + Sized>(
	storage_key: &[u8],
	child_info: ChildInfo,
	key: &[u8],
) -> Option<T> {
	let r = get(storage_key, child_info, key);
	if r.is_some() {
		kill(storage_key, child_info, key);
	}
	r
}

/// Remove `key` from storage, returning its value, or, if there was no explicit entry in storage,
/// the default for its type.
pub fn take_or_default<T: Codec + Sized + Default>(
	storage_key: &[u8],
	child_info: ChildInfo,
	key: &[u8],
) -> T {
	take(storage_key, child_info, key).unwrap_or_else(Default::default)
}

/// Return the value of the item in storage under `key`, or `default_value` if there is no
/// explicit entry. Ensure there is no explicit entry on return.
pub fn take_or<T: Codec + Sized>(
	storage_key: &[u8],
	child_info: ChildInfo,
	key: &[u8],
	default_value: T,
) -> T {
	take(storage_key, child_info, key).unwrap_or(default_value)
}

/// Return the value of the item in storage under `key`, or `default_value()` if there is no
/// explicit entry. Ensure there is no explicit entry on return.
pub fn take_or_else<T: Codec + Sized, F: FnOnce() -> T>(
	storage_key: &[u8],
	child_info: ChildInfo,
	key: &[u8],
	default_value: F,
) -> T {
	take(storage_key, child_info, key).unwrap_or_else(default_value)
}

/// Check to see if `key` has an explicit entry in storage.
pub fn exists(
	storage_key: &[u8],
	child_info: ChildInfo,
	key: &[u8],
) -> bool {
	let (data, child_type) = child_info.info();
	sp_io::storage::child_read(
		storage_key, data, child_type,
		key, &mut [0;0][..], 0,
	).is_some()
}

/// Remove all `storage_key` key/values
pub fn kill_storage(
	storage_key: &[u8],
	child_info: ChildInfo,
) {
	let (data, child_type) = child_info.info();
	sp_io::storage::child_storage_kill(
		storage_key,
		data,
		child_type,
	)
}

/// Ensure `key` has no explicit entry in storage.
pub fn kill(
	storage_key: &[u8],
	child_info: ChildInfo,
	key: &[u8],
) {
	let (data, child_type) = child_info.info();
	sp_io::storage::child_clear(
		storage_key,
		data,
		child_type,
		key,
	);
}

/// Get a Vec of bytes from storage.
pub fn get_raw(
	storage_key: &[u8],
	child_info: ChildInfo,
	key: &[u8],
) -> Option<Vec<u8>> {
	let (data, child_type) = child_info.info();
	sp_io::storage::child_get(
		storage_key,
		data,
		child_type,
		key,
	)
}

/// Put a raw byte slice into storage.
pub fn put_raw(
	storage_key: &[u8],
	child_info: ChildInfo,
	key: &[u8],
	value: &[u8],
) {
	let (data, child_type) = child_info.info();
	sp_io::storage::child_set(
		storage_key,
		data,
		child_type,
		key,
		value,
	)
}

/// Calculate current child root value.
pub fn child_root(
	storage_key: &[u8],
) -> Vec<u8> {
	sp_io::storage::child_root(
		storage_key,
	)
}
