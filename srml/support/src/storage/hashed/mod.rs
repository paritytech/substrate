// Copyright 2019 Parity Technologies (UK) Ltd.
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

pub mod generator;
use super::unhashed;
use crate::rstd::prelude::*;
use crate::rstd::borrow::Borrow;
use runtime_io::{self, twox_128};
use crate::codec::{Codec, Encode, Decode, KeyedVec};

/// Return the value of the item in storage under `key`, or `None` if there is no explicit entry.
pub fn get<T: Decode + Sized, HashFn: Fn(&[u8]) -> R, R: AsRef<[u8]>>(hash: &HashFn, key: &[u8]) -> Option<T> {
	unhashed::get(&hash(key).as_ref())
}

/// Return the value of the item in storage under `key`, or the type's default if there is no
/// explicit entry.
pub fn get_or_default<T: Decode + Sized + Default, HashFn: Fn(&[u8]) -> R, R: AsRef<[u8]>>(hash: &HashFn, key: &[u8]) -> T {
	unhashed::get_or_default(&hash(key).as_ref())
}

/// Return the value of the item in storage under `key`, or `default_value` if there is no
/// explicit entry.
pub fn get_or<T: Decode + Sized, HashFn: Fn(&[u8]) -> R, R: AsRef<[u8]>>(hash: &HashFn, key: &[u8], default_value: T) -> T {
	unhashed::get_or(&hash(key).as_ref(), default_value)
}

/// Return the value of the item in storage under `key`, or `default_value()` if there is no
/// explicit entry.
pub fn get_or_else<T: Decode + Sized, F: FnOnce() -> T, HashFn: Fn(&[u8]) -> R, R: AsRef<[u8]>>(hash: &HashFn, key: &[u8], default_value: F) -> T {
	unhashed::get_or_else(&hash(key).as_ref(), default_value)
}

/// Put `value` in storage under `key`.
pub fn put<T: Encode, HashFn: Fn(&[u8]) -> R, R: AsRef<[u8]>>(hash: &HashFn, key: &[u8], value: &T) {
	unhashed::put(&hash(key).as_ref(), value)
}

/// Remove `key` from storage, returning its value if it had an explicit entry or `None` otherwise.
pub fn take<T: Decode + Sized, HashFn: Fn(&[u8]) -> R, R: AsRef<[u8]>>(hash: &HashFn, key: &[u8]) -> Option<T> {
	unhashed::take(&hash(key).as_ref())
}

/// Remove `key` from storage, returning its value, or, if there was no explicit entry in storage,
/// the default for its type.
pub fn take_or_default<T: Decode + Sized + Default, HashFn: Fn(&[u8]) -> R, R: AsRef<[u8]>>(hash: &HashFn, key: &[u8]) -> T {
	unhashed::take_or_default(&hash(key).as_ref())
}

/// Return the value of the item in storage under `key`, or `default_value` if there is no
/// explicit entry. Ensure there is no explicit entry on return.
pub fn take_or<T: Decode + Sized, HashFn: Fn(&[u8]) -> R, R: AsRef<[u8]>>(hash: &HashFn, key: &[u8], default_value: T) -> T {
	unhashed::take_or(&hash(key).as_ref(), default_value)
}

/// Return the value of the item in storage under `key`, or `default_value()` if there is no
/// explicit entry. Ensure there is no explicit entry on return.
pub fn take_or_else<T: Decode + Sized, F: FnOnce() -> T, HashFn: Fn(&[u8]) -> R, R: AsRef<[u8]>>(hash: &HashFn, key: &[u8], default_value: F) -> T {
	unhashed::take_or_else(&hash(key).as_ref(), default_value)
}

/// Check to see if `key` has an explicit entry in storage.
pub fn exists<HashFn: Fn(&[u8]) -> R, R: AsRef<[u8]>>(hash: &HashFn, key: &[u8]) -> bool {
	unhashed::exists(&hash(key).as_ref())
}

/// Ensure `key` has no explicit entry in storage.
pub fn kill<HashFn: Fn(&[u8]) -> R, R: AsRef<[u8]>>(hash: &HashFn, key: &[u8]) {
	unhashed::kill(&hash(key).as_ref())
}

/// Get a Vec of bytes from storage.
pub fn get_raw<HashFn: Fn(&[u8]) -> R, R: AsRef<[u8]>>(hash: &HashFn, key: &[u8]) -> Option<Vec<u8>> {
	unhashed::get_raw(&hash(key).as_ref())
}

/// Put a raw byte slice into storage.
pub fn put_raw<HashFn: Fn(&[u8]) -> R, R: AsRef<[u8]>>(hash: &HashFn, key: &[u8], value: &[u8]) {
	unhashed::put_raw(&hash(key).as_ref(), value)
}

/// A trait to conveniently store a vector of storable data.
///
/// It uses twox_128 hasher. Final keys in trie are `twox_128(concatenation(PREFIX,count))`
pub trait StorageVec {
	type Item: Default + Sized + Codec;
	const PREFIX: &'static [u8];

	/// Get the current set of items.
	fn items() -> Vec<Self::Item> {
		(0..Self::count()).into_iter().map(Self::item).collect()
	}

	/// Set the current set of items.
	fn set_items<I, T>(items: I)
		where
			I: IntoIterator<Item=T>,
			T: Borrow<Self::Item>,
	{
		let mut count: u32 = 0;

		for i in items.into_iter() {
			put(&twox_128, &count.to_keyed_vec(Self::PREFIX), i.borrow());
			count = count.checked_add(1).expect("exceeded runtime storage capacity");
		}

		Self::set_count(count);
	}

	/// Push an item.
	fn push(item: &Self::Item) {
		let len = Self::count();
		put(&twox_128, &len.to_keyed_vec(Self::PREFIX), item);
		Self::set_count(len + 1);
	}

	fn set_item(index: u32, item: &Self::Item) {
		if index < Self::count() {
			put(&twox_128, &index.to_keyed_vec(Self::PREFIX), item);
		}
	}

	fn clear_item(index: u32) {
		if index < Self::count() {
			kill(&twox_128, &index.to_keyed_vec(Self::PREFIX));
		}
	}

	fn item(index: u32) -> Self::Item {
		get_or_default(&twox_128, &index.to_keyed_vec(Self::PREFIX))
	}

	fn set_count(count: u32) {
		(count..Self::count()).for_each(Self::clear_item);
		put(&twox_128, &b"len".to_keyed_vec(Self::PREFIX), &count);
	}

	fn count() -> u32 {
		get_or_default(&twox_128, &b"len".to_keyed_vec(Self::PREFIX))
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use runtime_io::{twox_128, TestExternalities, with_externalities};

	#[test]
	fn integers_can_be_stored() {
		let mut t = TestExternalities::default();
		with_externalities(&mut t, || {
			let x = 69u32;
			put(&twox_128, b":test", &x);
			let y: u32 = get(&twox_128, b":test").unwrap();
			assert_eq!(x, y);
		});
		with_externalities(&mut t, || {
			let x = 69426942i64;
			put(&twox_128, b":test", &x);
			let y: i64 = get(&twox_128, b":test").unwrap();
			assert_eq!(x, y);
		});
	}

	#[test]
	fn bools_can_be_stored() {
		let mut t = TestExternalities::default();
		with_externalities(&mut t, || {
			let x = true;
			put(&twox_128, b":test", &x);
			let y: bool = get(&twox_128, b":test").unwrap();
			assert_eq!(x, y);
		});

		with_externalities(&mut t, || {
			let x = false;
			put(&twox_128, b":test", &x);
			let y: bool = get(&twox_128, b":test").unwrap();
			assert_eq!(x, y);
		});
	}

	#[test]
	fn vecs_can_be_retrieved() {
		let mut t = TestExternalities::default();
		with_externalities(&mut t, || {
			runtime_io::set_storage(&twox_128(b":test"), b"\x2cHello world");
			let x = b"Hello world".to_vec();
			let y = get::<Vec<u8>, _, _>(&twox_128, b":test").unwrap();
			assert_eq!(x, y);
		});
	}

	#[test]
	fn vecs_can_be_stored() {
		let mut t = TestExternalities::default();
		let x = b"Hello world".to_vec();

		with_externalities(&mut t, || {
			put(&twox_128, b":test", &x);
		});

		with_externalities(&mut t, || {
			let y: Vec<u8> = get(&twox_128, b":test").unwrap();
			assert_eq!(x, y);
		});
	}
}
