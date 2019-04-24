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

//! Abstract storage to use on HashedStorage trait

use crate::codec;
use crate::rstd::prelude::{Vec, Box};
#[cfg(feature = "std")]
use crate::storage::unhashed::generator::UnhashedStorage;
use runtime_io::{twox_64, twox_128, blake2_128, twox_256, blake2_256};

pub trait StorageHasher: 'static {
	type Output: AsRef<[u8]>;
	fn hash(x: &[u8]) -> Self::Output;
}

/// Hash storage keys with `concat(twox128(key), key)`
pub struct Twox64Concat;
impl StorageHasher for Twox64Concat {
	type Output = Vec<u8>;
	fn hash(x: &[u8]) -> Vec<u8> {
		twox_64(x)
			.into_iter()
			.chain(x.into_iter())
			.cloned()
			.collect::<Vec<_>>()
	}
}

#[test]
fn test_twox_64_concat() {
	let r = Twox64Concat::hash(b"foo");
	assert_eq!(r.split_at(8), (&twox_128(b"foo")[..8], &b"foo"[..]))
}

/// Hash storage keys with blake2 128
pub struct Blake2_128;
impl StorageHasher for Blake2_128 {
	type Output = [u8; 16];
	fn hash(x: &[u8]) -> [u8; 16] {
		blake2_128(x)
	}
}

/// Hash storage keys with blake2 256
pub struct Blake2_256;
impl StorageHasher for Blake2_256 {
	type Output = [u8; 32];
	fn hash(x: &[u8]) -> [u8; 32] {
		blake2_256(x)
	}
}

/// Hash storage keys with twox 128
pub struct Twox128;
impl StorageHasher for Twox128 {
	type Output = [u8; 16];
	fn hash(x: &[u8]) -> [u8; 16] {
		twox_128(x)
	}
}

/// Hash storage keys with twox 256
pub struct Twox256;
impl StorageHasher for Twox256 {
	type Output = [u8; 32];
	fn hash(x: &[u8]) -> [u8; 32] {
		twox_256(x)
	}
}

/// Abstraction around storage.
pub trait HashedStorage<H: StorageHasher> {
	/// true if the key exists in storage.
	fn exists(&self, key: &[u8]) -> bool;

	/// Load the bytes of a key from storage. Can panic if the type is incorrect.
	fn get<T: codec::Decode>(&self, key: &[u8]) -> Option<T>;

	/// Load the bytes of a key from storage. Can panic if the type is incorrect. Will panic if
	/// it's not there.
	fn require<T: codec::Decode>(&self, key: &[u8]) -> T {
		self.get(key).expect("Required values must be in storage")
	}

	/// Load the bytes of a key from storage. Can panic if the type is incorrect. The type's
	/// default is returned if it's not there.
	fn get_or_default<T: codec::Decode + Default>(&self, key: &[u8]) -> T {
		self.get(key).unwrap_or_default()
	}

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
	fn take_or_panic<T: codec::Decode>(&self, key: &[u8]) -> T {
		self.take(key).expect("Required values must be in storage")
	}

	/// Take a value from storage, deleting it after reading.
	fn take_or_default<T: codec::Decode + Default>(&self, key: &[u8]) -> T {
		self.take(key).unwrap_or_default()
	}

	/// Get a Vec of bytes from storage.
	fn get_raw(&self, key: &[u8]) -> Option<Vec<u8>>;

	/// Put a raw byte slice into storage.
	fn put_raw(&self, key: &[u8], value: &[u8]);
}

// We use a construct like this during when genesis storage is being built.
#[cfg(feature = "std")]
impl<H: StorageHasher> HashedStorage<H> for std::cell::RefCell<&mut sr_primitives::StorageOverlay> {
	fn exists(&self, key: &[u8]) -> bool {
		UnhashedStorage::exists(self, &H::hash(key).as_ref())
	}

	fn get<T: codec::Decode>(&self, key: &[u8]) -> Option<T> {
		UnhashedStorage::get(self, &H::hash(key).as_ref())
	}

	fn put<T: codec::Encode>(&self, key: &[u8], val: &T) {
		UnhashedStorage::put(self, &H::hash(key).as_ref(), val)
	}

	fn kill(&self, key: &[u8]) {
		UnhashedStorage::kill(self, &H::hash(key).as_ref())
	}

	fn get_raw(&self, key: &[u8]) -> Option<Vec<u8>> {
		UnhashedStorage::get_raw(self, &H::hash(key).as_ref())
	}

	fn put_raw(&self, key: &[u8], value: &[u8]) {
		UnhashedStorage::put_raw(self, &H::hash(key).as_ref(), value)
	}
}

/// A strongly-typed value kept in storage.
pub trait StorageValue<T: codec::Codec> {
	/// The type that get/take returns.
	type Query;

	/// Get the storage key.
	fn key() -> &'static [u8];

	/// true if the value is defined in storage.
	fn exists<S: HashedStorage<Twox128>>(storage: &S) -> bool {
		storage.exists(Self::key())
	}

	/// Load the value from the provided storage instance.
	fn get<S: HashedStorage<Twox128>>(storage: &S) -> Self::Query;

	/// Take a value from storage, removing it afterwards.
	fn take<S: HashedStorage<Twox128>>(storage: &S) -> Self::Query;

	/// Store a value under this key into the provided storage instance.
	fn put<S: HashedStorage<Twox128>>(val: &T, storage: &S) {
		storage.put(Self::key(), val)
	}

	/// Mutate this value
	fn mutate<R, F: FnOnce(&mut Self::Query) -> R, S: HashedStorage<Twox128>>(f: F, storage: &S) -> R;

	/// Clear the storage value.
	fn kill<S: HashedStorage<Twox128>>(storage: &S) {
		storage.kill(Self::key())
	}

	/// Append the given items to the value in the storage.
	///
	/// `T` is required to implement `codec::EncodeAppend`.
	fn append<S: HashedStorage<Twox128>, I: codec::Encode>(
		items: &[I], storage: &S
	) -> Result<(), &'static str> where T: codec::EncodeAppend<Item=I> {
		let new_val = <T as codec::EncodeAppend>::append(
			storage.get_raw(Self::key()).unwrap_or_default(),
			items,
		).ok_or_else(|| "Could not append given item")?;
		storage.put_raw(Self::key(), &new_val);
		Ok(())
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
	fn items<S: HashedStorage<Twox128>>(storage: &S) -> Vec<T>;

	/// Set the current set of items.
	fn set_items<S: HashedStorage<Twox128>>(items: &[T], storage: &S);

	/// Set the item at the given index.
	fn set_item<S: HashedStorage<Twox128>>(index: u32, item: &T, storage: &S);

	/// Load the value at given index. Returns `None` if the index is out-of-bounds.
	fn get<S: HashedStorage<Twox128>>(index: u32, storage: &S) -> Option<T>;

	/// Load the length of the list
	fn len<S: HashedStorage<Twox128>>(storage: &S) -> u32;

	/// Clear the list.
	fn clear<S: HashedStorage<Twox128>>(storage: &S);
}

/// A strongly-typed map in storage.
pub trait StorageMap<K: codec::Codec, V: codec::Codec> {
	/// The type that get/take returns.
	type Query;

	type Hasher: StorageHasher;

	/// Get the prefix key in storage.
	fn prefix() -> &'static [u8];

	/// Get the storage key used to fetch a value corresponding to a specific key.
	fn key_for(x: &K) -> Vec<u8>;

	/// true if the value is defined in storage.
	fn exists<S: HashedStorage<Self::Hasher>>(key: &K, storage: &S) -> bool {
		storage.exists(&Self::key_for(key)[..])
	}

	/// Load the value associated with the given key from the map.
	fn get<S: HashedStorage<Self::Hasher>>(key: &K, storage: &S) -> Self::Query;

	/// Take the value under a key.
	fn take<S: HashedStorage<Self::Hasher>>(key: &K, storage: &S) -> Self::Query;

	/// Store a value to be associated with the given key from the map.
	fn insert<S: HashedStorage<Self::Hasher>>(key: &K, val: &V, storage: &S) {
		storage.put(&Self::key_for(key)[..], val);
	}

	/// Remove the value under a key.
	fn remove<S: HashedStorage<Self::Hasher>>(key: &K, storage: &S) {
		storage.kill(&Self::key_for(key)[..]);
	}

	/// Mutate the value under a key.
	fn mutate<R, F: FnOnce(&mut Self::Query) -> R, S: HashedStorage<Self::Hasher>>(key: &K, f: F, storage: &S) -> R;
}

/// A `StorageMap` with enumerable entries.
pub trait EnumerableStorageMap<K: codec::Codec, V: codec::Codec>: StorageMap<K, V> {
	/// Return current head element.
	fn head<S: HashedStorage<Self::Hasher>>(storage: &S) -> Option<K>;

	/// Enumerate all elements in the map.
	fn enumerate<'a, S: HashedStorage<Self::Hasher>>(storage: &'a S) -> Box<dyn Iterator<Item = (K, V)> + 'a> where K: 'a, V: 'a;
}
