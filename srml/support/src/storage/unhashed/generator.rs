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

use crate::codec;
use crate::rstd::vec::Vec;

/// Abstraction around storage with unhashed access.
pub trait UnhashedStorage {
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
	fn put<T: codec::Encode>(&mut self, key: &[u8], val: &T);

	/// Remove the bytes of a key from storage.
	fn kill(&mut self, key: &[u8]);

	/// Remove the bytes of a key from storage.
	fn kill_prefix(&mut self, prefix: &[u8]);

	/// Take a value from storage, deleting it after reading.
	fn take<T: codec::Decode>(&mut self, key: &[u8]) -> Option<T> {
		let value = self.get(key);
		self.kill(key);
		value
	}

	/// Take a value from storage, deleting it after reading.
	fn take_or_panic<T: codec::Decode>(&mut self, key: &[u8]) -> T {
		self.take(key).expect("Required values must be in storage")
	}

	/// Take a value from storage, deleting it after reading.
	fn take_or_default<T: codec::Decode + Default>(&mut self, key: &[u8]) -> T {
		self.take(key).unwrap_or_default()
	}

	/// Get a Vec of bytes from storage.
	fn get_raw(&self, key: &[u8]) -> Option<Vec<u8>>;

	/// Put a raw byte slice into storage.
	fn put_raw(&mut self, key: &[u8], value: &[u8]);
}

// We use a construct like this during when genesis storage is being built.
#[cfg(feature = "std")]
impl UnhashedStorage for sr_primitives::StorageOverlay {
	fn exists(&self, key: &[u8]) -> bool {
		self.contains_key(key)
	}

	fn get<T: codec::Decode>(&self, key: &[u8]) -> Option<T> {
		self.get(key)
			.map(|x| codec::Decode::decode(&mut x.as_slice()).expect("Unable to decode expected type."))
	}

	fn put<T: codec::Encode>(&mut self, key: &[u8], val: &T) {
		self.insert(key.to_vec(), codec::Encode::encode(val));
	}

	fn kill(&mut self, key: &[u8]) {
		self.remove(key);
	}

	fn kill_prefix(&mut self, prefix: &[u8]) {
		self.retain(|key, _| {
			!key.starts_with(prefix)
		})
	}

	fn get_raw(&self, key: &[u8]) -> Option<Vec<u8>> {
		self.get(key).cloned()
	}

	fn put_raw(&mut self, key: &[u8], value: &[u8]) {
		self.insert(key.to_vec(), value.to_vec());
	}
}

/// An implementation of a map with a two keys.
///
/// It provides an important ability to efficiently remove all entries
/// that have a common first key.
///
/// # Mapping of keys to a storage path
///
/// The storage key (i.e. the key under which the `Value` will be stored) is created from two parts.
/// The first part is a hash of a concatenation of the `PREFIX` and `Key1`. And the second part
/// is a hash of a `Key2`.
///
/// /!\ be careful while choosing the Hash, indeed malicious could craft second keys to lower the trie.
pub trait StorageDoubleMap<K1: codec::Codec, K2: codec::Codec, V: codec::Codec> {
	/// The type that get/take returns.
	type Query;

	/// Get the prefix key in storage.
	fn prefix() -> &'static [u8];

	/// Get the storage key used to fetch a value corresponding to a specific key.
	fn key_for(k1: &K1, k2: &K2) -> Vec<u8>;

	/// Get the storage prefix used to fetch keys corresponding to a specific key1.
	fn prefix_for(k1: &K1) -> Vec<u8>;

	/// true if the value is defined in storage.
	fn exists<S: UnhashedStorage>(k1: &K1, k2: &K2, storage: &S) -> bool {
		storage.exists(&Self::key_for(k1, k2))
	}

	/// Load the value associated with the given key from the map.
	fn get<S: UnhashedStorage>(k1: &K1, k2: &K2, storage: &S) -> Self::Query;

	/// Take the value under a key.
	fn take<S: UnhashedStorage>(k1: &K1, k2: &K2, storage: &mut S) -> Self::Query;

	/// Store a value to be associated with the given key from the map.
	fn insert<S: UnhashedStorage>(k1: &K1, k2: &K2, val: &V, storage: &mut S) {
		storage.put(&Self::key_for(k1, k2), val);
	}

	/// Remove the value under a key.
	fn remove<S: UnhashedStorage>(k1: &K1, k2: &K2, storage: &mut S) {
		storage.kill(&Self::key_for(k1, k2));
	}

	/// Removes all entries that shares the `k1` as the first key.
	fn remove_prefix<S: UnhashedStorage>(k1: &K1, storage: &mut S) {
		storage.kill_prefix(&Self::prefix_for(k1));
	}

	/// Mutate the value under a key.
	fn mutate<R, F: FnOnce(&mut Self::Query) -> R, S: UnhashedStorage>(k1: &K1, k2: &K2, f: F, storage: &mut S) -> R;

	/// Append the given items to the value under the key specified.
	fn append<I, S: UnhashedStorage>(
		k1: &K1,
		k2: &K2,
		items: &[I],
		storage: &mut S,
	) -> Result<(), &'static str>
	where
		I: codec::Encode,
		V: codec::EncodeAppend<Item=I>,
	{
		let key = Self::key_for(k1, k2);
		let new_val = <V as codec::EncodeAppend>::append(
			storage.get_raw(&key).unwrap_or_default(),
			items,
		).ok_or_else(|| "Could not append given item")?;
		storage.put_raw(&key, &new_val);
		Ok(())
	}
}
