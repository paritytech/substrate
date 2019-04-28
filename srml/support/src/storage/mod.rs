// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

//! Stuff to do with the runtime's storage.

use crate::rstd::prelude::*;
use crate::rstd::borrow::Borrow;
use codec::{Codec, Encode, Decode, KeyedVec, Input, EncodeAppend};
use hashed::generator::{HashedStorage, StorageHasher};
use unhashed::generator::UnhashedStorage;

#[macro_use]
pub mod storage_items;
pub mod unhashed;
pub mod hashed;

struct IncrementalInput<'a> {
	key: &'a [u8],
	pos: usize,
}

impl<'a> Input for IncrementalInput<'a> {
	fn read(&mut self, into: &mut [u8]) -> usize {
		let len = runtime_io::read_storage(self.key, into, self.pos).unwrap_or(0);
		let read = crate::rstd::cmp::min(len, into.len());
		self.pos += read;
		read
	}
}

struct IncrementalChildInput<'a> {
	storage_key: &'a [u8],
	key: &'a [u8],
	pos: usize,
}

impl<'a> Input for IncrementalChildInput<'a> {
	fn read(&mut self, into: &mut [u8]) -> usize {
		let len = runtime_io::read_child_storage(self.storage_key, self.key, into, self.pos).unwrap_or(0);
		let read = crate::rstd::cmp::min(len, into.len());
		self.pos += read;
		read
	}
}

/// The underlying runtime storage.
pub struct RuntimeStorage;

impl<H: StorageHasher> HashedStorage<H> for RuntimeStorage {
	fn exists(&self, key: &[u8]) -> bool {
		hashed::exists(&H::hash, key)
	}

	/// Load the bytes of a key from storage. Can panic if the type is incorrect.
	fn get<T: Decode>(&self, key: &[u8]) -> Option<T> {
		hashed::get(&H::hash, key)
	}

	/// Put a value in under a key.
	fn put<T: Encode>(&self, key: &[u8], val: &T) {
		hashed::put(&H::hash, key, val)
	}

	/// Remove the bytes of a key from storage.
	fn kill(&self, key: &[u8]) {
		hashed::kill(&H::hash, key)
	}

	/// Take a value from storage, deleting it after reading.
	fn take<T: Decode>(&self, key: &[u8]) -> Option<T> {
		hashed::take(&H::hash, key)
	}

	fn get_raw(&self, key: &[u8]) -> Option<Vec<u8>> {
		hashed::get_raw(&H::hash, key)
	}

	fn put_raw(&self, key: &[u8], value: &[u8]) {
		hashed::put_raw(&H::hash, key, value)
	}
}

impl UnhashedStorage for RuntimeStorage {
	fn exists(&self, key: &[u8]) -> bool {
		unhashed::exists(key)
	}

	/// Load the bytes of a key from storage. Can panic if the type is incorrect.
	fn get<T: Decode>(&self, key: &[u8]) -> Option<T> {
		unhashed::get(key)
	}

	/// Put a value in under a key.
	fn put<T: Encode>(&self, key: &[u8], val: &T) {
		unhashed::put(key, val)
	}

	/// Remove the bytes of a key from storage.
	fn kill(&self, key: &[u8]) {
		unhashed::kill(key)
	}

	/// Remove the bytes of a key from storage.
	fn kill_prefix(&self, prefix: &[u8]) {
		unhashed::kill_prefix(prefix)
	}

	/// Take a value from storage, deleting it after reading.
	fn take<T: Decode>(&self, key: &[u8]) -> Option<T> {
		unhashed::take(key)
	}

	fn get_raw(&self, key: &[u8]) -> Option<Vec<u8>> {
		unhashed::get_raw(key)
	}

	fn put_raw(&self, key: &[u8], value: &[u8]) {
		unhashed::put_raw(key, value)
	}
}

/// A trait for working with macro-generated storage values under the substrate storage API.
pub trait StorageValue<T: Codec> {
	/// The type that get/take return.
	type Query;

	/// Get the storage key.
	fn key() -> &'static [u8];

	/// Does the value (explicitly) exist in storage?
	fn exists() -> bool;

	/// Load the value from the provided storage instance.
	fn get() -> Self::Query;

	/// Store a value under this key into the provided storage instance.
	fn put<Arg: Borrow<T>>(val: Arg);

	/// Mutate the value
	fn mutate<R, F: FnOnce(&mut Self::Query) -> R>(f: F) -> R;

	/// Clear the storage value.
	fn kill();

	/// Take a value from storage, removing it afterwards.
	fn take() -> Self::Query;

	/// Append the given item to the value in the storage.
	///
	/// `T` is required to implement `codec::EncodeAppend`.
	fn append<I: Encode>(items: &[I]) -> Result<(), &'static str>
		where T: EncodeAppend<Item=I>;
}

impl<T: Codec, U> StorageValue<T> for U where U: hashed::generator::StorageValue<T> {
	type Query = U::Query;

	fn key() -> &'static [u8] {
		<U as hashed::generator::StorageValue<T>>::key()
	}
	fn exists() -> bool {
		U::exists(&RuntimeStorage)
	}
	fn get() -> Self::Query {
		U::get(&RuntimeStorage)
	}
	fn put<Arg: Borrow<T>>(val: Arg) {
		U::put(val.borrow(), &RuntimeStorage)
	}
	fn mutate<R, F: FnOnce(&mut Self::Query) -> R>(f: F) -> R {
		U::mutate(f, &RuntimeStorage)
	}
	fn kill() {
		U::kill(&RuntimeStorage)
	}
	fn take() -> Self::Query {
		U::take(&RuntimeStorage)
	}
	fn append<I: Encode>(items: &[I]) -> Result<(), &'static str>
		where T: EncodeAppend<Item=I>
	{
		U::append(items, &RuntimeStorage)
	}
}

/// A strongly-typed list in storage.
pub trait StorageList<T: Codec> {
	/// Get the prefix key in storage.
	fn prefix() -> &'static [u8];

	/// Get the key used to store the length field.
	fn len_key() -> Vec<u8>;

	/// Get the storage key used to fetch a value at a given index.
	fn key_for(index: u32) -> Vec<u8>;

	/// Read out all the items.
	fn items() -> Vec<T>;

	/// Set the current set of items.
	fn set_items(items: &[T]);

	/// Set the item at the given index.
	fn set_item<Arg: Borrow<T>>(index: u32, val: Arg);

	/// Load the value at given index. Returns `None` if the index is out-of-bounds.
	fn get(index: u32) -> Option<T>;

	/// Load the length of the list
	fn len() -> u32;

	/// Clear the list.
	fn clear();
}

impl<T: Codec, U> StorageList<T> for U where U: hashed::generator::StorageList<T> {
	fn prefix() -> &'static [u8] {
		<U as hashed::generator::StorageList<T>>::prefix()
	}

	fn len_key() -> Vec<u8> {
		<U as hashed::generator::StorageList<T>>::len_key()
	}

	fn key_for(index: u32) -> Vec<u8> {
		<U as hashed::generator::StorageList<T>>::key_for(index)
	}

	fn items() -> Vec<T> {
		U::items(&RuntimeStorage)
	}

	fn set_items(items: &[T]) {
		U::set_items(items, &RuntimeStorage)
	}

	fn set_item<Arg: Borrow<T>>(index: u32, val: Arg) {
		U::set_item(index, val.borrow(), &RuntimeStorage)
	}

	fn get(index: u32) -> Option<T> {
		U::get(index, &RuntimeStorage)
	}

	fn len() -> u32 {
		U::len(&RuntimeStorage)
	}

	fn clear() {
		U::clear(&RuntimeStorage)
	}
}

/// A strongly-typed map in storage.
pub trait StorageMap<K: Codec, V: Codec> {
	/// The type that get/take return.
	type Query;

	/// Get the prefix key in storage.
	fn prefix() -> &'static [u8];

	/// Get the storage key used to fetch a value corresponding to a specific key.
	fn key_for<KeyArg: Borrow<K>>(key: KeyArg) -> Vec<u8>;

	/// Does the value (explicitly) exist in storage?
	fn exists<KeyArg: Borrow<K>>(key: KeyArg) -> bool;

	/// Load the value associated with the given key from the map.
	fn get<KeyArg: Borrow<K>>(key: KeyArg) -> Self::Query;

	/// Store a value to be associated with the given key from the map.
	fn insert<KeyArg: Borrow<K>, ValArg: Borrow<V>>(key: KeyArg, val: ValArg);

	/// Remove the value under a key.
	fn remove<KeyArg: Borrow<K>>(key: KeyArg);

	/// Mutate the value under a key.
	fn mutate<KeyArg: Borrow<K>, R, F: FnOnce(&mut Self::Query) -> R>(key: KeyArg, f: F) -> R;

	/// Take the value under a key.
	fn take<KeyArg: Borrow<K>>(key: KeyArg) -> Self::Query;
}

impl<K: Codec, V: Codec, U> StorageMap<K, V> for U where U: hashed::generator::StorageMap<K, V> {
	type Query = U::Query;

	fn prefix() -> &'static [u8] {
		<U as hashed::generator::StorageMap<K, V>>::prefix()
	}

	fn key_for<KeyArg: Borrow<K>>(key: KeyArg) -> Vec<u8> {
		<U as hashed::generator::StorageMap<K, V>>::key_for(key.borrow())
	}

	fn exists<KeyArg: Borrow<K>>(key: KeyArg) -> bool {
		U::exists(key.borrow(), &RuntimeStorage)
	}

	fn get<KeyArg: Borrow<K>>(key: KeyArg) -> Self::Query {
		U::get(key.borrow(), &RuntimeStorage)
	}

	fn insert<KeyArg: Borrow<K>, ValArg: Borrow<V>>(key: KeyArg, val: ValArg) {
		U::insert(key.borrow(), val.borrow(), &RuntimeStorage)
	}

	fn remove<KeyArg: Borrow<K>>(key: KeyArg) {
		U::remove(key.borrow(), &RuntimeStorage)
	}

	fn mutate<KeyArg: Borrow<K>, R, F: FnOnce(&mut Self::Query) -> R>(key: KeyArg, f: F) -> R {
		U::mutate(key.borrow(), f, &RuntimeStorage)
	}

	fn take<KeyArg: Borrow<K>>(key: KeyArg) -> Self::Query {
		U::take(key.borrow(), &RuntimeStorage)
	}
}

/// A storage map that can be enumerated.
///
/// Note that type is primarily useful for off-chain computations.
/// Runtime implementors should avoid enumerating storage entries.
pub trait EnumerableStorageMap<K: Codec, V: Codec>: StorageMap<K, V> {
	/// Return current head element.
	fn head() -> Option<K>;

	/// Enumerate all elements in the map.
	fn enumerate() -> Box<dyn Iterator<Item = (K, V)>> where K: 'static, V: 'static;
}

impl<K: Codec, V: Codec, U> EnumerableStorageMap<K, V> for U where U: hashed::generator::EnumerableStorageMap<K, V> {
	fn head() -> Option<K> {
		<U as hashed::generator::EnumerableStorageMap<K, V>>::head(&RuntimeStorage)
	}

	fn enumerate() -> Box<dyn Iterator<Item = (K, V)>> where K: 'static, V: 'static {
		<U as hashed::generator::EnumerableStorageMap<K, V>>::enumerate(&RuntimeStorage)
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
pub trait StorageDoubleMap<K1: Codec, K2: Codec, V: Codec> {
	/// The type that get/take returns.
	type Query;

	/// Get the prefix key in storage.
	fn prefix() -> &'static [u8];

	/// Get the storage key used to fetch a value corresponding to a specific key.
	fn key_for<KArg1: Borrow<K1>, KArg2: Borrow<K2>>(k1: KArg1, k2: KArg2) -> Vec<u8>;

	/// Get the storage prefix used to fetch keys corresponding to a specific key1.
	fn prefix_for<KArg1: Borrow<K1>>(k1: KArg1) -> Vec<u8>;

	/// true if the value is defined in storage.
	fn exists<KArg1: Borrow<K1>, KArg2: Borrow<K2>>(k1: KArg1, k2: KArg2) -> bool;

	/// Load the value associated with the given key from the map.
	fn get<KArg1: Borrow<K1>, KArg2: Borrow<K2>>(k1: KArg1, k2: KArg2) -> Self::Query;

	/// Take the value under a key.
	fn take<KArg1: Borrow<K1>, KArg2: Borrow<K2>>(k1: KArg1, k2: KArg2) -> Self::Query;

	/// Store a value to be associated with the given key from the map.
	fn insert<KArg1: Borrow<K1>, KArg2: Borrow<K2>, VArg: Borrow<V>>(k1: KArg1, k2: KArg2, val: VArg);

	/// Remove the value under a key.
	fn remove<KArg1: Borrow<K1>, KArg2: Borrow<K2>>(k1: KArg1, k2: KArg2);

	/// Removes all entries that shares the `k1` as the first key.
	fn remove_prefix<KArg1: Borrow<K1>>(k1: KArg1);

	/// Mutate the value under a key.
	fn mutate<KArg1, KArg2, R, F>(k1: KArg1, k2: KArg2, f: F) -> R
	where
		KArg1: Borrow<K1>,
		KArg2: Borrow<K2>,
		F: FnOnce(&mut Self::Query) -> R;
}

impl<K1: Codec, K2: Codec, V: Codec, U> StorageDoubleMap<K1, K2, V> for U
where
	U: unhashed::generator::StorageDoubleMap<K1, K2, V>
{
	type Query = U::Query;

	fn prefix() -> &'static [u8] {
		<U as unhashed::generator::StorageDoubleMap<K1, K2, V>>::prefix()
	}

	fn key_for<KArg1: Borrow<K1>, KArg2: Borrow<K2>>(k1: KArg1, k2: KArg2) -> Vec<u8> {
		<U as unhashed::generator::StorageDoubleMap<K1, K2, V>>::key_for(k1.borrow(), k2.borrow())
	}

	fn prefix_for<KArg1: Borrow<K1>>(k1: KArg1) -> Vec<u8> {
		<U as unhashed::generator::StorageDoubleMap<K1, K2, V>>::prefix_for(k1.borrow())
	}

	fn exists<KArg1: Borrow<K1>, KArg2: Borrow<K2>>(k1: KArg1, k2: KArg2) -> bool {
		U::exists(k1.borrow(), k2.borrow(), &RuntimeStorage)
	}

	fn get<KArg1: Borrow<K1>, KArg2: Borrow<K2>>(k1: KArg1, k2: KArg2) -> Self::Query {
		U::get(k1.borrow(), k2.borrow(), &RuntimeStorage)
	}

	fn take<KArg1: Borrow<K1>, KArg2: Borrow<K2>>(k1: KArg1, k2: KArg2) -> Self::Query {
		U::take(k1.borrow(), k2.borrow(), &RuntimeStorage)
	}

	fn insert<KArg1: Borrow<K1>, KArg2: Borrow<K2>, VArg: Borrow<V>>(k1: KArg1, k2: KArg2, val: VArg) {
		U::insert(k1.borrow(), k2.borrow(), val.borrow(), &RuntimeStorage)
	}

	fn remove<KArg1: Borrow<K1>, KArg2: Borrow<K2>>(k1: KArg1, k2: KArg2) {
		U::remove(k1.borrow(), k2.borrow(), &RuntimeStorage)
	}

	fn remove_prefix<KArg1: Borrow<K1>>(k1: KArg1) {
		U::remove_prefix(k1.borrow(), &RuntimeStorage)
	}

	fn mutate<KArg1, KArg2, R, F>(k1: KArg1, k2: KArg2, f: F) -> R
	where
		KArg1: Borrow<K1>,
		KArg2: Borrow<K2>,
		F: FnOnce(&mut Self::Query) -> R
	{
		U::mutate(k1.borrow(), k2.borrow(), f, &RuntimeStorage)
	}
}

/// child storage NOTE could replace unhashed by having only one kind of storage (root being null storage
/// key (storage_key can become Option<&[u8]>).
/// This module is a currently only a variant of unhashed with additional `storage_key`.
/// Note that `storage_key` must be unique and strong (strong in the sense of being long enough to
/// avoid collision from a resistant hash function (which unique implies)).
pub mod child {
	use super::{Codec, Decode, Vec, IncrementalChildInput};

	/// Return the value of the item in storage under `key`, or `None` if there is no explicit entry.
	pub fn get<T: Codec + Sized>(storage_key: &[u8], key: &[u8]) -> Option<T> {
		runtime_io::read_child_storage(storage_key, key, &mut [0; 0][..], 0).map(|_| {
			let mut input = IncrementalChildInput {
				storage_key,
				key,
				pos: 0,
			};
			Decode::decode(&mut input).expect("storage is not null, therefore must be a valid type")
		})
	}

	/// Return the value of the item in storage under `key`, or the type's default if there is no
	/// explicit entry.
	pub fn get_or_default<T: Codec + Sized + Default>(storage_key: &[u8], key: &[u8]) -> T {
		get(storage_key, key).unwrap_or_else(Default::default)
	}

	/// Return the value of the item in storage under `key`, or `default_value` if there is no
	/// explicit entry.
	pub fn get_or<T: Codec + Sized>(storage_key: &[u8], key: &[u8], default_value: T) -> T {
		get(storage_key, key).unwrap_or(default_value)
	}

	/// Return the value of the item in storage under `key`, or `default_value()` if there is no
	/// explicit entry.
	pub fn get_or_else<T: Codec + Sized, F: FnOnce() -> T>(storage_key: &[u8], key: &[u8], default_value: F) -> T {
		get(storage_key, key).unwrap_or_else(default_value)
	}

	/// Put `value` in storage under `key`.
	pub fn put<T: Codec>(storage_key: &[u8], key: &[u8], value: &T) {
		value.using_encoded(|slice| runtime_io::set_child_storage(storage_key, key, slice));
	}

	/// Remove `key` from storage, returning its value if it had an explicit entry or `None` otherwise.
	pub fn take<T: Codec + Sized>(storage_key: &[u8], key: &[u8]) -> Option<T> {
		let r = get(storage_key, key);
		if r.is_some() {
			kill(storage_key, key);
		}
		r
	}

	/// Remove `key` from storage, returning its value, or, if there was no explicit entry in storage,
	/// the default for its type.
	pub fn take_or_default<T: Codec + Sized + Default>(storage_key: &[u8], key: &[u8]) -> T {
		take(storage_key, key).unwrap_or_else(Default::default)
	}

	/// Return the value of the item in storage under `key`, or `default_value` if there is no
	/// explicit entry. Ensure there is no explicit entry on return.
	pub fn take_or<T: Codec + Sized>(storage_key: &[u8],key: &[u8], default_value: T) -> T {
		take(storage_key, key).unwrap_or(default_value)
	}

	/// Return the value of the item in storage under `key`, or `default_value()` if there is no
	/// explicit entry. Ensure there is no explicit entry on return.
	pub fn take_or_else<T: Codec + Sized, F: FnOnce() -> T>(storage_key: &[u8], key: &[u8], default_value: F) -> T {
		take(storage_key, key).unwrap_or_else(default_value)
	}

	/// Check to see if `key` has an explicit entry in storage.
	pub fn exists(storage_key: &[u8], key: &[u8]) -> bool {
		runtime_io::read_child_storage(storage_key, key, &mut [0;0][..], 0).is_some()
	}

	/// Remove all `storage_key` key/values
	pub fn kill_storage(storage_key: &[u8]) {
		runtime_io::kill_child_storage(storage_key)
	}

	/// Ensure `key` has no explicit entry in storage.
	pub fn kill(storage_key: &[u8], key: &[u8]) {
		runtime_io::clear_child_storage(storage_key, key);
	}

	/// Get a Vec of bytes from storage.
	pub fn get_raw(storage_key: &[u8], key: &[u8]) -> Option<Vec<u8>> {
		runtime_io::child_storage(storage_key, key)
	}

	/// Put a raw byte slice into storage.
	pub fn put_raw(storage_key: &[u8], key: &[u8], value: &[u8]) {
		runtime_io::set_child_storage(storage_key, key, value)
	}

	pub use super::unhashed::StorageVec;
}
