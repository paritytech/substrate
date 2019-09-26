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

//! Storage vec abstraction on top of runtime storage.

use rstd::{prelude::*, borrow::Borrow};
use super::unhashed;
use codec::{Codec, KeyedVec};

/// A trait to conveniently store a vector of storable data.
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
			unhashed::put(&count.to_keyed_vec(Self::PREFIX), i.borrow());
			count = count.checked_add(1).expect("exceeded runtime storage capacity");
		}

		Self::set_count(count);
	}

	fn set_item(index: u32, item: &Self::Item) {
		if index < Self::count() {
			unhashed::put(&index.to_keyed_vec(Self::PREFIX), item);
		}
	}

	fn clear_item(index: u32) {
		if index < Self::count() {
			unhashed::kill(&index.to_keyed_vec(Self::PREFIX));
		}
	}

	fn item(index: u32) -> Self::Item {
		unhashed::get_or_default(&index.to_keyed_vec(Self::PREFIX))
	}

	fn set_count(count: u32) {
		(count..Self::count()).for_each(Self::clear_item);
		unhashed::put(&b"len".to_keyed_vec(Self::PREFIX), &count);
	}

	fn count() -> u32 {
		unhashed::get_or_default(&b"len".to_keyed_vec(Self::PREFIX))
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use runtime_io::{TestExternalities, with_externalities};

	#[test]
	fn integers_can_be_stored() {
		let mut t = TestExternalities::default();
		with_externalities(&mut t, || {
			let x = 69u32;
			unhashed::put(b":test", &x);
			let y: u32 = unhashed::get(b":test").unwrap();
			assert_eq!(x, y);
		});
		with_externalities(&mut t, || {
			let x = 69426942i64;
			unhashed::put(b":test", &x);
			let y: i64 = unhashed::get(b":test").unwrap();
			assert_eq!(x, y);
		});
	}

	#[test]
	fn bools_can_be_stored() {
		let mut t = TestExternalities::default();
		with_externalities(&mut t, || {
			let x = true;
			unhashed::put(b":test", &x);
			let y: bool = unhashed::get(b":test").unwrap();
			assert_eq!(x, y);
		});

		with_externalities(&mut t, || {
			let x = false;
			unhashed::put(b":test", &x);
			let y: bool = unhashed::get(b":test").unwrap();
			assert_eq!(x, y);
		});
	}

	#[test]
	fn vecs_can_be_retrieved() {
		let mut t = TestExternalities::default();
		with_externalities(&mut t, || {
			runtime_io::set_storage(b":test", b"\x2cHello world");
			let x = b"Hello world".to_vec();
			let y = unhashed::get::<Vec<u8>>(b":test").unwrap();
			assert_eq!(x, y);
		});
	}

	#[test]
	fn vecs_can_be_stored() {
		let mut t = TestExternalities::default();
		let x = b"Hello world".to_vec();

		with_externalities(&mut t, || {
			unhashed::put(b":test", &x);
		});

		with_externalities(&mut t, || {
			let y: Vec<u8> = unhashed::get(b":test").unwrap();
			assert_eq!(x, y);
		});
	}
}
