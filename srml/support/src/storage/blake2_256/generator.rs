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

//! Abstract storage to use on Blake2_256Storage trait

use crate::codec;
use crate::rstd::prelude::{Vec, Box};
#[cfg(feature = "std")]
use crate::storage::unhashed::generator::UnhashedStorage;
#[cfg(feature = "std")]
use runtime_io::blake2_256;

/// Abstraction around storage.
pub trait Blake2_256Storage {
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
impl Blake2_256Storage for crate::rstd::cell::RefCell<&mut sr_primitives::StorageOverlay> {
	fn exists(&self, key: &[u8]) -> bool {
		UnhashedStorage::exists(self, &blake2_256(key))
	}

	fn get<T: codec::Decode>(&self, key: &[u8]) -> Option<T> {
		UnhashedStorage::get(self, &blake2_256(key))
	}

	fn put<T: codec::Encode>(&self, key: &[u8], val: &T) {
		UnhashedStorage::put(self, &blake2_256(key), val)
	}

	fn kill(&self, key: &[u8]) {
		UnhashedStorage::kill(self, &blake2_256(key))
	}
}

/// A strongly-typed map in storage.
pub trait StorageMap<K: codec::Codec, V: codec::Codec> {
	/// The type that get/take returns.
	type Query;

	/// Get the prefix key in storage.
	fn prefix() -> &'static [u8];

	/// Get the storage key used to fetch a value corresponding to a specific key.
	fn key_for(x: &K) -> Vec<u8>;

	/// true if the value is defined in storage.
	fn exists<S: Blake2_256Storage>(key: &K, storage: &S) -> bool {
		storage.exists(&Self::key_for(key)[..])
	}

	/// Load the value associated with the given key from the map.
	fn get<S: Blake2_256Storage>(key: &K, storage: &S) -> Self::Query;

	/// Take the value under a key.
	fn take<S: Blake2_256Storage>(key: &K, storage: &S) -> Self::Query;

	/// Store a value to be associated with the given key from the map.
	fn insert<S: Blake2_256Storage>(key: &K, val: &V, storage: &S) {
		storage.put(&Self::key_for(key)[..], val);
	}

	/// Remove the value under a key.
	fn remove<S: Blake2_256Storage>(key: &K, storage: &S) {
		storage.kill(&Self::key_for(key)[..]);
	}

	/// Mutate the value under a key.
	fn mutate<R, F: FnOnce(&mut Self::Query) -> R, S: Blake2_256Storage>(key: &K, f: F, storage: &S) -> R;
}

/// A `StorageMap` with enumerable entries.
pub trait EnumerableStorageMap<K: codec::Codec, V: codec::Codec>: StorageMap<K, V> {
	/// Return current head element.
	fn head<S: Blake2_256Storage>(storage: &S) -> Option<K>;

	/// Enumerate all elements in the map.
	fn enumerate<'a, S: Blake2_256Storage>(storage: &'a S) -> Box<dyn Iterator<Item = (K, V)> + 'a> where K: 'a, V: 'a;
}
