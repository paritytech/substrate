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

//! Operation on runtime storage using hashed keys.

use super::unhashed;
use sp_std::prelude::*;
use codec::{Encode, Decode};

/// Return the value of the item in storage under `key`, or `None` if there is no explicit entry.
pub fn get<T, HashFn, R>(hash: &HashFn, key: &[u8]) -> Option<T>
where
	T: Decode + Sized,
	HashFn: Fn(&[u8]) -> R,
	R: AsRef<[u8]>,
{
	unhashed::get(&hash(key).as_ref())
}

/// Return the value of the item in storage under `key`, or the type's default if there is no
/// explicit entry.
pub fn get_or_default<T, HashFn, R>(hash: &HashFn, key: &[u8]) -> T
where
	T: Decode + Sized + Default,
	HashFn: Fn(&[u8]) -> R,
	R: AsRef<[u8]>,
{
	unhashed::get_or_default(&hash(key).as_ref())
}

/// Return the value of the item in storage under `key`, or `default_value` if there is no
/// explicit entry.
pub fn get_or<T, HashFn, R>(hash: &HashFn, key: &[u8], default_value: T) -> T
where
	T: Decode + Sized,
	HashFn: Fn(&[u8]) -> R,
	R: AsRef<[u8]>,
{
	unhashed::get_or(&hash(key).as_ref(), default_value)
}

/// Return the value of the item in storage under `key`, or `default_value()` if there is no
/// explicit entry.
pub fn get_or_else<T, F, HashFn, R>(hash: &HashFn, key: &[u8], default_value: F) -> T
where
	T: Decode + Sized,
	F: FnOnce() -> T,
	HashFn: Fn(&[u8]) -> R,
	R: AsRef<[u8]>,
{
	unhashed::get_or_else(&hash(key).as_ref(), default_value)
}

/// Put `value` in storage under `key`.
pub fn put<T, HashFn, R>(hash: &HashFn, key: &[u8], value: &T)
where
	T: Encode,
	HashFn: Fn(&[u8]) -> R,
	R: AsRef<[u8]>,
{
	unhashed::put(&hash(key).as_ref(), value)
}

/// Remove `key` from storage, returning its value if it had an explicit entry or `None` otherwise.
pub fn take<T, HashFn, R>(hash: &HashFn, key: &[u8]) -> Option<T>
where
	T: Decode + Sized,
	HashFn: Fn(&[u8]) -> R,
	R: AsRef<[u8]>,
{
	unhashed::take(&hash(key).as_ref())
}

/// Remove `key` from storage, returning its value, or, if there was no explicit entry in storage,
/// the default for its type.
pub fn take_or_default<T, HashFn, R>(hash: &HashFn, key: &[u8]) -> T
where
	T: Decode + Sized + Default,
	HashFn: Fn(&[u8]) -> R,
	R: AsRef<[u8]>,
{
	unhashed::take_or_default(&hash(key).as_ref())
}

/// Return the value of the item in storage under `key`, or `default_value` if there is no
/// explicit entry. Ensure there is no explicit entry on return.
pub fn take_or<T, HashFn, R>(hash: &HashFn, key: &[u8], default_value: T) -> T
where
	T: Decode + Sized,
	HashFn: Fn(&[u8]) -> R,
	R: AsRef<[u8]>,
{
	unhashed::take_or(&hash(key).as_ref(), default_value)
}

/// Return the value of the item in storage under `key`, or `default_value()` if there is no
/// explicit entry. Ensure there is no explicit entry on return.
pub fn take_or_else<T, F, HashFn, R>(hash: &HashFn, key: &[u8], default_value: F) -> T
where
	T: Decode + Sized,
	F: FnOnce() -> T,
	HashFn: Fn(&[u8]) -> R,
	R: AsRef<[u8]>,
{
	unhashed::take_or_else(&hash(key).as_ref(), default_value)
}

/// Check to see if `key` has an explicit entry in storage.
pub fn exists<HashFn, R>(hash: &HashFn, key: &[u8]) -> bool
where
	HashFn: Fn(&[u8]) -> R,
	R: AsRef<[u8]>,
{
	unhashed::exists(&hash(key).as_ref())
}

/// Ensure `key` has no explicit entry in storage.
pub fn kill<HashFn, R>(hash: &HashFn, key: &[u8])
where
	HashFn: Fn(&[u8]) -> R,
	R: AsRef<[u8]>,
{
	unhashed::kill(&hash(key).as_ref())
}

/// Get a Vec of bytes from storage.
pub fn get_raw<HashFn, R>(hash: &HashFn, key: &[u8]) -> Option<Vec<u8>>
where
	HashFn: Fn(&[u8]) -> R,
	R: AsRef<[u8]>,
{
	unhashed::get_raw(&hash(key).as_ref())
}

/// Put a raw byte slice into storage.
pub fn put_raw<HashFn, R>(hash: &HashFn, key: &[u8], value: &[u8])
where
	HashFn: Fn(&[u8]) -> R,
	R: AsRef<[u8]>,
{
	unhashed::put_raw(&hash(key).as_ref(), value)
}
