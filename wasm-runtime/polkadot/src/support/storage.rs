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

use runtime_std::prelude::*;
use runtime_std::{self, twox_128};
use codec::{Slicable, KeyedVec};

// TODO: consider using blake256 to avoid possible preimage attack.

/// Return the value of the item in storage under `key`, or `None` if there is no explicit entry.
pub fn get<T: Slicable + Sized>(key: &[u8]) -> Option<T> {
	Slicable::set_as_slice(|out, offset|
		runtime_std::read_storage(&twox_128(key)[..], out, offset) >= out.len()
	)
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
	value.as_slice_then(|slice| runtime_std::set_storage(&twox_128(key)[..], slice));
}

/// Please `value` in storage under `key`.
pub fn place<T: Slicable>(key: &[u8], value: T) {
	value.as_slice_then(|slice| runtime_std::set_storage(&twox_128(key)[..], slice));
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
	let mut x = [0u8; 1];
	runtime_std::read_storage(&twox_128(key)[..], &mut x[..], 0) >= 1
}

/// Ensure `key` has no explicit entry in storage.
pub fn kill(key: &[u8]) {
	runtime_std::set_storage(&twox_128(key)[..], b"");
}

/// Get a Vec of bytes from storage.
pub fn get_raw(key: &[u8]) -> Vec<u8> {
	runtime_std::storage(&twox_128(key)[..])
}

/// Put a raw byte slice into storage.
pub fn put_raw(key: &[u8], value: &[u8]) {
	runtime_std::set_storage(&twox_128(key)[..], value)
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

	fn item(index: u32) -> Self::Item {
		get_or_default(&index.to_keyed_vec(Self::PREFIX))
	}

	fn set_count(count: u32) {
		(count..Self::count()).for_each(|i| Self::set_item(i, &Self::Item::default()));
		put(&b"len".to_keyed_vec(Self::PREFIX), &count);
	}

	fn count() -> u32 {
		get_or_default(&b"len".to_keyed_vec(Self::PREFIX))
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use std::collections::HashMap;
	use support::HexDisplay;
	use runtime_std::{storage, twox_128, TestExternalities, with_externalities};

	#[test]
	fn integers_can_be_stored() {
		let mut t = TestExternalities { storage: HashMap::new(), };
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
		let mut t = TestExternalities { storage: HashMap::new(), };
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
		let mut t = TestExternalities { storage: HashMap::new(), };
		with_externalities(&mut t, || {
			runtime_std::set_storage(&twox_128(b":test"), b"\x0b\0\0\0Hello world");
			let x = b"Hello world".to_vec();
			println!("Hex: {}", HexDisplay::from(&storage(&twox_128(b":test"))));
			let y = get::<Vec<u8>>(b":test").unwrap();
			assert_eq!(x, y);

		});
	}

	#[test]
	fn vecs_can_be_stored() {
		let mut t = TestExternalities { storage: HashMap::new(), };
		let x = b"Hello world".to_vec();

		with_externalities(&mut t, || {
			put(b":test", &x);
		});

		println!("Ext is {:?}", t);
		with_externalities(&mut t, || {
			println!("Hex: {}", HexDisplay::from(&storage(&twox_128(b":test"))));
			let y: Vec<u8> = get(b":test").unwrap();
			assert_eq!(x, y);
		});
	}

	#[test]
	fn proposals_can_be_stored() {
		use primitives::{Proposal, InternalFunction};
		let mut t = TestExternalities { storage: HashMap::new(), };
		with_externalities(&mut t, || {
			let x = Proposal { function: InternalFunction::StakingSetSessionsPerEra, input_data: b"Hello world".to_vec() };
			put(b":test", &x);
			let y: Proposal = get(b":test").unwrap();
			assert_eq!(x, y);
		});
	}
}
