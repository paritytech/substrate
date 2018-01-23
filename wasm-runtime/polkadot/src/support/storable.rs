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

use slicable::Slicable;
use endiansensitive::EndianSensitive;
use keyedvec::KeyedVec;
use runtime_support::{self, twox_128, Vec};

/// Trait for a value which may be stored in the storage DB.
pub trait Storable {
	/// Lookup the value in storage and deserialise, giving a default value if not found.
	fn lookup_default(key: &[u8]) -> Self where Self: Sized + Default { Self::lookup(key).unwrap_or_else(Default::default) }
	/// Lookup `Some` value in storage and deserialise; `None` if it's not there.
	fn lookup(_key: &[u8]) -> Option<Self> where Self: Sized { unimplemented!() }
	/// Place the value in storage under `key`.
	fn store(&self, key: &[u8]);
}

// TODO: consider using blake256 to avoid possible eclipse attack.

/// Remove `key` from storage.
pub fn kill(key: &[u8]) { runtime_support::set_storage(&twox_128(key)[..], b""); }

impl<T: Default + Sized + EndianSensitive> Storable for T {
	fn lookup(key: &[u8]) -> Option<Self> {
		Slicable::set_as_slice(|out| runtime_support::read_storage(&twox_128(key)[..], out) == out.len())
	}
	fn store(&self, key: &[u8]) {
		self.as_slice_then(|slice| runtime_support::set_storage(&twox_128(key)[..], slice));
	}
}

impl Storable for [u8] {
	fn store(&self, key: &[u8]) {
		runtime_support::set_storage(&twox_128(key)[..], self)
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
