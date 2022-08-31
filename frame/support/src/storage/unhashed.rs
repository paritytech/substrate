// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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

//! Operation on unhashed runtime storage.

use codec::{Decode, Encode};
use sp_std::prelude::*;

/// Return the value of the item in storage under `key`, or `None` if there is no explicit entry.
pub fn get<T: Decode + Sized>(key: &[u8]) -> Option<T> {
	sp_io::storage::get(key).and_then(|val| {
		Decode::decode(&mut &val[..]).map(Some).unwrap_or_else(|_| {
			// TODO #3700: error should be handleable.
			log::error!(
				target: "runtime::storage",
				"Corrupted state at {:?}",
				key,
			);
			None
		})
	})
}

/// Return the value of the item in storage under `key`, or the type's default if there is no
/// explicit entry.
pub fn get_or_default<T: Decode + Sized + Default>(key: &[u8]) -> T {
	get(key).unwrap_or_default()
}

/// Return the value of the item in storage under `key`, or `default_value` if there is no
/// explicit entry.
pub fn get_or<T: Decode + Sized>(key: &[u8], default_value: T) -> T {
	get(key).unwrap_or(default_value)
}

/// Return the value of the item in storage under `key`, or `default_value()` if there is no
/// explicit entry.
pub fn get_or_else<T: Decode + Sized, F: FnOnce() -> T>(key: &[u8], default_value: F) -> T {
	get(key).unwrap_or_else(default_value)
}

/// Put `value` in storage under `key`.
pub fn put<T: Encode + ?Sized>(key: &[u8], value: &T) {
	value.using_encoded(|slice| sp_io::storage::set(key, slice));
}

/// Remove `key` from storage, returning its value if it had an explicit entry or `None` otherwise.
pub fn take<T: Decode + Sized>(key: &[u8]) -> Option<T> {
	let r = get(key);
	if r.is_some() {
		kill(key);
	}
	r
}

/// Remove `key` from storage, returning its value, or, if there was no explicit entry in storage,
/// the default for its type.
pub fn take_or_default<T: Decode + Sized + Default>(key: &[u8]) -> T {
	take(key).unwrap_or_default()
}

/// Return the value of the item in storage under `key`, or `default_value` if there is no
/// explicit entry. Ensure there is no explicit entry on return.
pub fn take_or<T: Decode + Sized>(key: &[u8], default_value: T) -> T {
	take(key).unwrap_or(default_value)
}

/// Return the value of the item in storage under `key`, or `default_value()` if there is no
/// explicit entry. Ensure there is no explicit entry on return.
pub fn take_or_else<T: Decode + Sized, F: FnOnce() -> T>(key: &[u8], default_value: F) -> T {
	take(key).unwrap_or_else(default_value)
}

/// Check to see if `key` has an explicit entry in storage.
pub fn exists(key: &[u8]) -> bool {
	sp_io::storage::exists(key)
}

/// Ensure `key` has no explicit entry in storage.
pub fn kill(key: &[u8]) {
	sp_io::storage::clear(key);
}

/// Ensure keys with the given `prefix` have no entries in storage.
#[deprecated = "Use `clear_prefix` instead"]
pub fn kill_prefix(prefix: &[u8], limit: Option<u32>) -> sp_io::KillStorageResult {
	// TODO: Once the network has upgraded to include the new host functions, this code can be
	// enabled.
	// clear_prefix(prefix, limit).into()
	sp_io::storage::clear_prefix(prefix, limit)
}

/// Partially clear the storage of all keys under a common `prefix`.
///
/// # Limit
///
/// A *limit* should always be provided through `maybe_limit`. This is one fewer than the
/// maximum number of backend iterations which may be done by this operation and as such
/// represents the maximum number of backend deletions which may happen. A *limit* of zero
/// implies that no keys will be deleted, though there may be a single iteration done.
///
/// The limit can be used to partially delete storage items in case it is too large or costly
/// to delete all in a single operation.
///
/// # Cursor
///
/// A *cursor* may be passed in to this operation with `maybe_cursor`. `None` should only be
/// passed once (in the initial call) for any attempt to clear storage. In general, subsequent calls
/// operating on the same prefix should pass `Some` and this value should be equal to the
/// previous call result's `maybe_cursor` field. The only exception to this is when you can
/// guarantee that the subsequent call is in a new block; in this case the previous call's result
/// cursor need not be passed in an a `None` may be passed instead. This exception may be useful
/// then making this call solely from a block-hook such as `on_initialize`.
///
/// Returns [`MultiRemovalResults`](sp_io::MultiRemovalResults) to inform about the result. Once the
/// resultant `maybe_cursor` field is `None`, then no further items remain to be deleted.
///
/// NOTE: After the initial call for any given child storage, it is important that no keys further
/// keys are inserted. If so, then they may or may not be deleted by subsequent calls.
///
/// # Note
///
/// Please note that keys which are residing in the overlay for the child are deleted without
/// counting towards the `limit`.
pub fn clear_prefix(
	prefix: &[u8],
	maybe_limit: Option<u32>,
	_maybe_cursor: Option<&[u8]>,
) -> sp_io::MultiRemovalResults {
	// TODO: Once the network has upgraded to include the new host functions, this code can be
	// enabled.
	// sp_io::storage::clear_prefix(prefix, maybe_limit, maybe_cursor)
	use sp_io::{KillStorageResult::*, MultiRemovalResults};
	#[allow(deprecated)]
	let (maybe_cursor, i) = match kill_prefix(prefix, maybe_limit) {
		AllRemoved(i) => (None, i),
		SomeRemaining(i) => (Some(prefix.to_vec()), i),
	};
	MultiRemovalResults { maybe_cursor, backend: i, unique: i, loops: i }
}

/// Get a Vec of bytes from storage.
pub fn get_raw(key: &[u8]) -> Option<Vec<u8>> {
	sp_io::storage::get(key)
}

/// Put a raw byte slice into storage.
///
/// **WARNING**: If you set the storage of the Substrate Wasm (`well_known_keys::CODE`),
/// you should also call `frame_system::RuntimeUpgraded::put(true)` to trigger the
/// `on_runtime_upgrade` logic.
pub fn put_raw(key: &[u8], value: &[u8]) {
	sp_io::storage::set(key, value)
}
