// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! Stuff to do with the runtime's storage.

use rstd::prelude::*;
use runtime_io::{self, twox_128};
use codec::{Slicable, KeyedVec, Input};

// TODO: consider using blake256 to avoid possible preimage attack.

struct IncrementalInput<'a> {
	key: &'a [u8],
	pos: usize,
}

impl<'a> Input for IncrementalInput<'a> {
	fn read(&mut self, into: &mut [u8]) -> usize {
		let len = runtime_io::read_storage(self.key, into, self.pos).unwrap_or(0);
		let read = ::rstd::cmp::min(len, into.len());
		self.pos += read;
		read
	}
}

 /// Return the value of the item in storage under `key`, or `None` if there is no explicit entry.
pub fn get<T: Slicable + Sized>(key: &[u8]) -> Option<T> {
	let key = twox_128(key);
	runtime_io::read_storage(&key[..], &mut [0; 0][..], 0).map(|_| {
		let mut input = IncrementalInput {
			key: &key[..],
			pos: 0,
		};
		Slicable::decode(&mut input).expect("stroage is not null, therefore must be a valid type")
	})
}

/// Return the value of the item in storage under `key`, or the type's default if there is no
/// explicit entry.
pub fn get_or_default<T: Slicable + Sized + Default>(key: &[u8]) -> T {
	get(key).unwrap_or_else(Default::default)
}

/// Return the value of the item in storage under `key`, or `default_value` if there is no
/// explicit entry.
pub fn get_or<T: Slicable + Sized>(key: &[u8], default_value: T) -> T {
	get(key).unwrap_or(default_value)
}

/// Return the value of the item in storage under `key`, or `default_value()` if there is no
/// explicit entry.
pub fn get_or_else<T: Slicable + Sized, F: FnOnce() -> T>(key: &[u8], default_value: F) -> T {
	get(key).unwrap_or_else(default_value)
}

/// Please `value` in storage under `key`.
pub fn put<T: Slicable>(key: &[u8], value: &T) {
	value.using_encoded(|slice| runtime_io::set_storage(&twox_128(key)[..], slice));
}

/// Please `value` in storage under `key`.
pub fn place<T: Slicable>(key: &[u8], value: T) {
	value.using_encoded(|slice| runtime_io::set_storage(&twox_128(key)[..], slice));
}

/// Remove `key` from storage, returning its value if it had an explicit entry or `None` otherwise.
pub fn take<T: Slicable + Sized>(key: &[u8]) -> Option<T> {
	let r = get(key);
	if r.is_some() {
		kill(key);
	}
	r
}

/// Remove `key` from storage, returning its value, or, if there was no explicit entry in storage,
/// the default for its type.
pub fn take_or_default<T: Slicable + Sized + Default>(key: &[u8]) -> T {
	take(key).unwrap_or_else(Default::default)
}

/// Return the value of the item in storage under `key`, or `default_value` if there is no
/// explicit entry. Ensure there is no explicit entry on return.
pub fn take_or<T: Slicable + Sized>(key: &[u8], default_value: T) -> T {
	take(key).unwrap_or(default_value)
}

/// Return the value of the item in storage under `key`, or `default_value()` if there is no
/// explicit entry. Ensure there is no explicit entry on return.
pub fn take_or_else<T: Slicable + Sized, F: FnOnce() -> T>(key: &[u8], default_value: F) -> T {
	take(key).unwrap_or_else(default_value)
}

/// Check to see if `key` has an explicit entry in storage.
pub fn exists(key: &[u8]) -> bool {
	let mut x = [0u8; 0];
	runtime_io::read_storage(&twox_128(key)[..], &mut x[..], 0).is_some()
}

/// Ensure `key` has no explicit entry in storage.
pub fn kill(key: &[u8]) {
	runtime_io::clear_storage(&twox_128(key)[..]);
}

/// Get a Vec of bytes from storage.
pub fn get_raw(key: &[u8]) -> Option<Vec<u8>> {
	runtime_io::storage(&twox_128(key)[..])
}

/// Put a raw byte slice into storage.
pub fn put_raw(key: &[u8], value: &[u8]) {
	runtime_io::set_storage(&twox_128(key)[..], value)
}

/// A trait to conveniently store a vector of storable data.
// TODO: add iterator support
pub trait StorageVec {
	type Item: Default + Sized + Slicable;
	const PREFIX: &'static [u8];

	/// Get the current set of items.
	fn items() -> Vec<Self::Item> {
		(0..Self::count()).into_iter().map(Self::item).collect()
	}

	/// Set the current set of items.
	fn set_items(items: &[Self::Item]) {
		Self::set_count(items.len() as u32);
		items.iter().enumerate().for_each(|(v, ref i)| Self::set_item(v as u32, i));
	}

	fn set_item(index: u32, item: &Self::Item) {
		if index < Self::count() {
			put(&index.to_keyed_vec(Self::PREFIX), item);
		}
	}

	fn clear_item(index: u32) {
		if index < Self::count() {
			kill(&index.to_keyed_vec(Self::PREFIX));
		}
	}

	fn item(index: u32) -> Self::Item {
		get_or_default(&index.to_keyed_vec(Self::PREFIX))
	}

	fn set_count(count: u32) {
		(count..Self::count()).for_each(Self::clear_item);
		put(&b"len".to_keyed_vec(Self::PREFIX), &count);
	}

	fn count() -> u32 {
		get_or_default(&b"len".to_keyed_vec(Self::PREFIX))
	}
}

pub mod unhashed {
	use super::{runtime_io, Slicable, KeyedVec, Vec, IncrementalInput};

	/// Return the value of the item in storage under `key`, or `None` if there is no explicit entry.
	pub fn get<T: Slicable + Sized>(key: &[u8]) -> Option<T> {
		runtime_io::read_storage(key, &mut [0; 0][..], 0).map(|_| {
			let mut input = IncrementalInput {
				key,
				pos: 0,
			};
			Slicable::decode(&mut input).expect("stroage is not null, therefore must be a valid type")
		})
	}

	/// Return the value of the item in storage under `key`, or the type's default if there is no
	/// explicit entry.
	pub fn get_or_default<T: Slicable + Sized + Default>(key: &[u8]) -> T {
		get(key).unwrap_or_else(Default::default)
	}

	/// Return the value of the item in storage under `key`, or `default_value` if there is no
	/// explicit entry.
	pub fn get_or<T: Slicable + Sized>(key: &[u8], default_value: T) -> T {
		get(key).unwrap_or(default_value)
	}

	/// Return the value of the item in storage under `key`, or `default_value()` if there is no
	/// explicit entry.
	pub fn get_or_else<T: Slicable + Sized, F: FnOnce() -> T>(key: &[u8], default_value: F) -> T {
		get(key).unwrap_or_else(default_value)
	}

	/// Please `value` in storage under `key`.
	pub fn put<T: Slicable>(key: &[u8], value: &T) {
		value.using_encoded(|slice| runtime_io::set_storage(key, slice));
	}

	/// Please `value` in storage under `key`.
	pub fn place<T: Slicable>(key: &[u8], value: T) {
		value.using_encoded(|slice| runtime_io::set_storage(key, slice));
	}

	/// Remove `key` from storage, returning its value if it had an explicit entry or `None` otherwise.
	pub fn take<T: Slicable + Sized>(key: &[u8]) -> Option<T> {
		let r = get(key);
		if r.is_some() {
			kill(key);
		}
		r
	}

	/// Remove `key` from storage, returning its value, or, if there was no explicit entry in storage,
	/// the default for its type.
	pub fn take_or_default<T: Slicable + Sized + Default>(key: &[u8]) -> T {
		take(key).unwrap_or_else(Default::default)
	}

	/// Return the value of the item in storage under `key`, or `default_value` if there is no
	/// explicit entry. Ensure there is no explicit entry on return.
	pub fn take_or<T: Slicable + Sized>(key: &[u8], default_value: T) -> T {
		take(key).unwrap_or(default_value)
	}

	/// Return the value of the item in storage under `key`, or `default_value()` if there is no
	/// explicit entry. Ensure there is no explicit entry on return.
	pub fn take_or_else<T: Slicable + Sized, F: FnOnce() -> T>(key: &[u8], default_value: F) -> T {
		take(key).unwrap_or_else(default_value)
	}

	/// Check to see if `key` has an explicit entry in storage.
	pub fn exists(key: &[u8]) -> bool {
		runtime_io::read_storage(key, &mut [0;0][..], 0).is_some()
	}

	/// Ensure `key` has no explicit entry in storage.
	pub fn kill(key: &[u8]) {
		runtime_io::clear_storage(key);
	}

	/// Get a Vec of bytes from storage.
	pub fn get_raw(key: &[u8]) -> Option<Vec<u8>> {
		runtime_io::storage(key)
	}

	/// Put a raw byte slice into storage.
	pub fn put_raw(key: &[u8], value: &[u8]) {
		runtime_io::set_storage(key, value)
	}

	/// A trait to conveniently store a vector of storable data.
	// TODO: add iterator support
	pub trait StorageVec {
		type Item: Default + Sized + Slicable;
		const PREFIX: &'static [u8];

		/// Get the current set of items.
		fn items() -> Vec<Self::Item> {
			(0..Self::count()).into_iter().map(Self::item).collect()
		}

		/// Set the current set of items.
		fn set_items(items: &[Self::Item]) {
			Self::set_count(items.len() as u32);
			items.iter().enumerate().for_each(|(v, ref i)| Self::set_item(v as u32, i));
		}

		fn set_item(index: u32, item: &Self::Item) {
			if index < Self::count() {
				put(&index.to_keyed_vec(Self::PREFIX), item);
			}
		}

		fn clear_item(index: u32) {
			if index < Self::count() {
				kill(&index.to_keyed_vec(Self::PREFIX));
			}
		}

		fn item(index: u32) -> Self::Item {
			get_or_default(&index.to_keyed_vec(Self::PREFIX))
		}

		fn set_count(count: u32) {
			(count..Self::count()).for_each(Self::clear_item);
			put(&b"len".to_keyed_vec(Self::PREFIX), &count);
		}

		fn count() -> u32 {
			get_or_default(&b"len".to_keyed_vec(Self::PREFIX))
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use primitives::hexdisplay::HexDisplay;
	use runtime_io::{storage, twox_128, TestExternalities, with_externalities};

	#[test]
	fn integers_can_be_stored() {
		let mut t = TestExternalities::new();
		with_externalities(&mut t, || {
			let x = 69u32;
			put(b":test", &x);
			let y: u32 = get(b":test").unwrap();
			assert_eq!(x, y);
		});
		with_externalities(&mut t, || {
			let x = 69426942i64;
			put(b":test", &x);
			let y: i64 = get(b":test").unwrap();
			assert_eq!(x, y);
		});
	}

	#[test]
	fn bools_can_be_stored() {
		let mut t = TestExternalities::new();
		with_externalities(&mut t, || {
			let x = true;
			put(b":test", &x);
			let y: bool = get(b":test").unwrap();
			assert_eq!(x, y);
		});

		with_externalities(&mut t, || {
			let x = false;
			put(b":test", &x);
			let y: bool = get(b":test").unwrap();
			assert_eq!(x, y);
		});
	}

	#[test]
	fn vecs_can_be_retrieved() {
		let mut t = TestExternalities::new();
		with_externalities(&mut t, || {
			runtime_io::set_storage(&twox_128(b":test"), b"\x0b\0\0\0Hello world");
			let x = b"Hello world".to_vec();
			println!("Hex: {}", HexDisplay::from(&storage(&twox_128(b":test")).unwrap()));
			let y = get::<Vec<u8>>(b":test").unwrap();
			assert_eq!(x, y);

		});
	}

	#[test]
	fn vecs_can_be_stored() {
		let mut t = TestExternalities::new();
		let x = b"Hello world".to_vec();

		with_externalities(&mut t, || {
			put(b":test", &x);
		});

		println!("Ext is {:?}", t);
		with_externalities(&mut t, || {
			println!("Hex: {}", HexDisplay::from(&storage(&twox_128(b":test")).unwrap()));
			let y: Vec<u8> = get(b":test").unwrap();
			assert_eq!(x, y);
		});
	}
}
