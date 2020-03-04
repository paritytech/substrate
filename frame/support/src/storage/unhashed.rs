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

//! Operation on unhashed runtime storage.

use sp_std::prelude::*;
use codec::{Encode, Decode};

/// Return the value of the item in storage under `key`, or `None` if there is no explicit entry.
pub fn get<T: Decode + Sized>(key: &[u8]) -> Option<T> {
	sp_io::storage::get(key).and_then(|val| {
		Decode::decode(&mut &val[..]).map(Some).unwrap_or_else(|_| {
			// TODO #3700: error should be handleable.
			runtime_print!("ERROR: Corrupted state at {:?}", key);
			None
		})
	})
}

/// Return the value of the item in storage under `key`, or the type's default if there is no
/// explicit entry.
pub fn get_or_default<T: Decode + Sized + Default>(key: &[u8]) -> T {
	get(key).unwrap_or_else(Default::default)
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
	take(key).unwrap_or_else(Default::default)
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
	sp_io::storage::read(key, &mut [0;0][..], 0).is_some()
}

/// Ensure `key` has no explicit entry in storage.
pub fn kill(key: &[u8]) {
	sp_io::storage::clear(key);
}

/// Ensure keys with the given `prefix` have no entries in storage.
pub fn kill_prefix(prefix: &[u8]) {
	sp_io::storage::clear_prefix(prefix);
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
