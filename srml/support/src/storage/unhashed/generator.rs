// Copyright 2017-2019 Parity Technologies (UK) Ltd
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
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
	fn require<T: codec::Decode>(&self, key: &[u8]) -> T { self.get(key).expect("Required values must be in storage") }

	/// Load the bytes of a key from storage. Can panic if the type is incorrect. The type's
	/// default is returned if it's not there.
	fn get_or_default<T: codec::Decode + Default>(&self, key: &[u8]) -> T { self.get(key).unwrap_or_default() }

	/// Put a value in under a key.
	fn put<T: codec::Encode>(&self, key: &[u8], val: &T);

	/// Remove the bytes of a key from storage.
	fn kill(&self, key: &[u8]);

	/// Remove the bytes of a key from storage.
	fn kill_prefix(&self, prefix: &[u8]);

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
impl UnhashedStorage for std::cell::RefCell<&mut sr_primitives::StorageOverlay> {
	fn exists(&self, key: &[u8]) -> bool {
		self.borrow().contains_key(key)
	}

	fn get<T: codec::Decode>(&self, key: &[u8]) -> Option<T> {
		self.borrow().get(key)
			.map(|x| codec::Decode::decode(&mut x.as_slice()).expect("Unable to decode expected type."))
	}

	fn put<T: codec::Encode>(&self, key: &[u8], val: &T) {
		self.borrow_mut().insert(key.to_vec(), codec::Encode::encode(val));
	}

	fn kill(&self, key: &[u8]) {
		self.borrow_mut().remove(key);
	}

	fn kill_prefix(&self, prefix: &[u8]) {
		self.borrow_mut().retain(|key, _| {
			!key.starts_with(prefix)
		})
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
	fn take<S: UnhashedStorage>(k1: &K1, k2: &K2, storage: &S) -> Self::Query;

	/// Store a value to be associated with the given key from the map.
	fn insert<S: UnhashedStorage>(k1: &K1, k2: &K2, val: &V, storage: &S) {
		storage.put(&Self::key_for(k1, k2), val);
	}

	/// Remove the value under a key.
	fn remove<S: UnhashedStorage>(k1: &K1, k2: &K2, storage: &S) {
		storage.kill(&Self::key_for(k1, k2));
	}

	/// Removes all entries that shares the `k1` as the first key.
	fn remove_prefix<S: UnhashedStorage>(k1: &K1, storage: &S) {
		storage.kill_prefix(&Self::prefix_for(k1));
	}

	/// Mutate the value under a key.
	fn mutate<R, F: FnOnce(&mut Self::Query) -> R, S: UnhashedStorage>(k1: &K1, k2: &K2, f: F, storage: &S) -> R;
}
