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

/// Trait for a value which may be stored in the storage DB.
pub trait Storable {
	/// Lookup the value in storage and deserialise, giving a default value if not found.
	fn lookup_default(key: &[u8]) -> Self where Self: Sized + Default {
		Self::lookup(key).unwrap_or_else(Default::default)
	}

	/// Lookup `Some` value in storage and deserialise; `None` if it's not there.
	fn lookup(_key: &[u8]) -> Option<Self> where Self: Sized {
		unimplemented!()
	}

	/// Retrives and returns the serialised value of a key from storage, removing it immediately.
	fn take(key: &[u8]) -> Option<Self> where Self: Sized {
		if let Some(value) = Self::lookup(key) {
			kill(key);
			Some(value)
		} else {
			None
		}
	}

	/// Place the value in storage under `key`.
	fn store(&self, key: &[u8]);
}

// TODO: consider using blake256 to avoid possible preimage attack.

/// Remove `key` from storage.
pub fn kill(key: &[u8]) {
	runtime_std::set_storage(&twox_128(key)[..], b"");
}

impl<T: Sized + Slicable> Storable for T {
	fn lookup(key: &[u8]) -> Option<Self> {
		Slicable::set_as_slice(&|out, offset|
			runtime_std::read_storage(&twox_128(key)[..], out, offset) >= out.len()
		)
	}
	fn store(&self, key: &[u8]) {
		self.as_slice_then(|slice| runtime_std::set_storage(&twox_128(key)[..], slice));
	}
}

impl Storable for [u8] {
	fn store(&self, key: &[u8]) {
		runtime_std::set_storage(&twox_128(key)[..], self)
	}
}

/// A trait to conveniently store a vector of storable data.
// TODO: add iterator support
pub trait StorageVec {
	type Item: Default + Sized + Storable;
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
		item.store(&index.to_keyed_vec(Self::PREFIX));
	}

	fn item(index: u32) -> Self::Item {
		Storable::lookup_default(&index.to_keyed_vec(Self::PREFIX))
	}

	fn set_count(count: u32) {
		(count..Self::count()).for_each(|i| Self::set_item(i, &Self::Item::default()));
		count.store(&b"len".to_keyed_vec(Self::PREFIX));
	}

	fn count() -> u32 {
		Storable::lookup_default(&b"len".to_keyed_vec(Self::PREFIX))
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use std::collections::HashMap;
	use runtime_std::with_externalities;
	use testing::{TestExternalities, HexDisplay};
	use runtime_std::{storage, twox_128};

	#[test]
	fn integers_can_be_stored() {
		let mut t = TestExternalities { storage: HashMap::new(), };
		with_externalities(&mut t, || {
			let x = 69u32;
			x.store(b":test");
			let y = u32::lookup(b":test").unwrap();
			assert_eq!(x, y);
		});
		with_externalities(&mut t, || {
			let x = 69426942i64;
			x.store(b":test");
			let y = i64::lookup(b":test").unwrap();
			assert_eq!(x, y);
		});
	}

	#[test]
	fn bools_can_be_stored() {
		let mut t = TestExternalities { storage: HashMap::new(), };
		with_externalities(&mut t, || {
			let x = true;
			x.store(b":test");
			let y = bool::lookup(b":test").unwrap();
			assert_eq!(x, y);
		});

		with_externalities(&mut t, || {
			let x = false;
			x.store(b":test");
			let y = bool::lookup(b":test").unwrap();
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
			let y = <Vec<u8>>::lookup(b":test").unwrap();
			assert_eq!(x, y);

		});
	}

	#[test]
	fn vecs_can_be_stored() {
		let mut t = TestExternalities { storage: HashMap::new(), };
		let x = b"Hello world".to_vec();

		with_externalities(&mut t, || {
			x.store(b":test");
		});

		println!("Ext is {:?}", t);
		with_externalities(&mut t, || {
			println!("Hex: {}", HexDisplay::from(&storage(&twox_128(b":test"))));
			let y = <Vec<u8>>::lookup(b":test").unwrap();
			assert_eq!(x, y);
		});
	}

	#[test]
	fn proposals_can_be_stored() {
		use proposal::{Proposal, InternalFunction};
		let mut t = TestExternalities { storage: HashMap::new(), };
		with_externalities(&mut t, || {
			let x = Proposal { function: InternalFunction::StakingSetSessionsPerEra, input_data: b"Hello world".to_vec() };
			x.store(b":test");
			let y = Proposal::lookup(b":test").unwrap();
			assert_eq!(x, y);
		});
	}
}
