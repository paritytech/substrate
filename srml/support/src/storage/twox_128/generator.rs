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

//! Abstract storage to use on Twox128Storage trait

use crate::codec;
use crate::rstd::vec::Vec;
#[cfg(feature = "std")]
use crate::storage::unhashed::generator::UnhashedStorage;
#[cfg(feature = "std")]
use runtime_io::twox_128;

/// Abstraction around storage.
pub trait Twox128Storage {
	/// true if the key exists in storage.
	fn exists(&self, key: &[u8]) -> bool;

	/// Load the bytes of a key from storage. Can panic if the type is incorrect.
	fn get<T: codec::Decode>(&self, key: &[u8]) -> Option<T>;

	/// Load the bytes of a key from storage. Can panic if the type is incorrect. Will panic if
	/// it's not there.
	fn require<T: codec::Decode>(&self, key: &[u8]) -> T { self.get(key).expect("Required values must be in storage") }

	/// Load the bytes of a key from storage. Can panic if the type is incorrect. The type's
	/// default is returned if it's not there.
	fn get_or_default<T: codec::Decode + Default>(&self, key: &[u8]) -> T { self.get(key).unwrap_or_default() }

	/// Put a value in under a key.
	fn put<T: codec::Encode>(&self, key: &[u8], val: &T);

	/// Remove the bytes of a key from storage.
	fn kill(&self, key: &[u8]);

	/// Take a value from storage, deleting it after reading.
	fn take<T: codec::Decode>(&self, key: &[u8]) -> Option<T> {
		let value = self.get(key);
		self.kill(key);
		value
	}

	/// Take a value from storage, deleting it after reading.
	fn take_or_panic<T: codec::Decode>(&self, key: &[u8]) -> T { self.take(key).expect("Required values must be in storage") }

	/// Take a value from storage, deleting it after reading.
	fn take_or_default<T: codec::Decode + Default>(&self, key: &[u8]) -> T { self.take(key).unwrap_or_default() }
}

// We use a construct like this during when genesis storage is being built.
#[cfg(feature = "std")]
impl Twox128Storage for crate::rstd::cell::RefCell<&mut sr_primitives::StorageOverlay> {
	fn exists(&self, key: &[u8]) -> bool {
		UnhashedStorage::exists(self, &twox_128(key))
	}

	fn get<T: codec::Decode>(&self, key: &[u8]) -> Option<T> {
		UnhashedStorage::get(self, &twox_128(key))
	}

	fn put<T: codec::Encode>(&self, key: &[u8], val: &T) {
		UnhashedStorage::put(self, &twox_128(key), val)
	}

	fn kill(&self, key: &[u8]) {
		UnhashedStorage::kill(self, &twox_128(key))
	}
}

/// A strongly-typed value kept in storage.
pub trait StorageValue<T: codec::Codec> {
	/// The type that get/take returns.
	type Query;

	/// Get the storage key.
	fn key() -> &'static [u8];

	/// true if the value is defined in storage.
	fn exists<S: Twox128Storage>(storage: &S) -> bool {
		storage.exists(Self::key())
	}

	/// Load the value from the provided storage instance.
	fn get<S: Twox128Storage>(storage: &S) -> Self::Query;

	/// Take a value from storage, removing it afterwards.
	fn take<S: Twox128Storage>(storage: &S) -> Self::Query;

	/// Store a value under this key into the provided storage instance.
	fn put<S: Twox128Storage>(val: &T, storage: &S) {
		storage.put(Self::key(), val)
	}

	/// Mutate this value
	fn mutate<R, F: FnOnce(&mut Self::Query) -> R, S: Twox128Storage>(f: F, storage: &S) -> R;

	/// Clear the storage value.
	fn kill<S: Twox128Storage>(storage: &S) {
		storage.kill(Self::key())
	}
}

/// A strongly-typed list in storage.
pub trait StorageList<T: codec::Codec> {
	/// Get the prefix key in storage.
	fn prefix() -> &'static [u8];

	/// Get the key used to put the length field.
	fn len_key() -> Vec<u8>;

	/// Get the storage key used to fetch a value at a given index.
	fn key_for(index: u32) -> Vec<u8>;

	/// Read out all the items.
	fn items<S: Twox128Storage>(storage: &S) -> Vec<T>;

	/// Set the current set of items.
	fn set_items<S: Twox128Storage>(items: &[T], storage: &S);

	/// Set the item at the given index.
	fn set_item<S: Twox128Storage>(index: u32, item: &T, storage: &S);

	/// Load the value at given index. Returns `None` if the index is out-of-bounds.
	fn get<S: Twox128Storage>(index: u32, storage: &S) -> Option<T>;

	/// Load the length of the list
	fn len<S: Twox128Storage>(storage: &S) -> u32;

	/// Clear the list.
	fn clear<S: Twox128Storage>(storage: &S);
}
