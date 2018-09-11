// Copyright 2017 Parity Technologies (UK) Ltd.
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

use rstd::prelude::*;
use rstd::borrow::Borrow;
use runtime_io::{self, twox_128};
use codec::{Codec, Decode, KeyedVec, Input};

#[macro_use]
pub mod generator;

// TODO: consider using blake256 to avoid possible preimage attack.

struct IncrementalInput<'a> {
	key: &'a [u8],
	pos: usize,
}

impl<'a> Input for IncrementalInput<'a> {
	fn read(&mut self, into: &mut [u8]) -> usize {
		let len = runtime_io::read_storage(self.key, into, self.pos).unwrap_or(0);
		let read = ::rstd::cmp::min(len, into.len());
		self.pos += read;
		read
	}
}

 /// Return the value of the item in storage under `key`, or `None` if there is no explicit entry.
pub fn get<T: Codec + Sized>(key: &[u8]) -> Option<T> {
	let key = twox_128(key);
	runtime_io::read_storage(&key[..], &mut [0; 0][..], 0).map(|_| {
		let mut input = IncrementalInput {
			key: &key[..],
			pos: 0,
		};
		Decode::decode(&mut input).expect("storage is not null, therefore must be a valid type")
	})
}

/// Return the value of the item in storage under `key`, or the type's default if there is no
/// explicit entry.
pub fn get_or_default<T: Codec + Sized + Default>(key: &[u8]) -> T {
	get(key).unwrap_or_else(Default::default)
}

/// Return the value of the item in storage under `key`, or `default_value` if there is no
/// explicit entry.
pub fn get_or<T: Codec + Sized>(key: &[u8], default_value: T) -> T {
	get(key).unwrap_or(default_value)
}

/// Return the value of the item in storage under `key`, or `default_value()` if there is no
/// explicit entry.
pub fn get_or_else<T: Codec + Sized, F: FnOnce() -> T>(key: &[u8], default_value: F) -> T {
	get(key).unwrap_or_else(default_value)
}

/// Put `value` in storage under `key`.
pub fn put<T: Codec>(key: &[u8], value: &T) {
	value.using_encoded(|slice| runtime_io::set_storage(&twox_128(key)[..], slice));
}

/// Remove `key` from storage, returning its value if it had an explicit entry or `None` otherwise.
pub fn take<T: Codec + Sized>(key: &[u8]) -> Option<T> {
	let r = get(key);
	if r.is_some() {
		kill(key);
	}
	r
}

/// Remove `key` from storage, returning its value, or, if there was no explicit entry in storage,
/// the default for its type.
pub fn take_or_default<T: Codec + Sized + Default>(key: &[u8]) -> T {
	take(key).unwrap_or_else(Default::default)
}

/// Return the value of the item in storage under `key`, or `default_value` if there is no
/// explicit entry. Ensure there is no explicit entry on return.
pub fn take_or<T: Codec + Sized>(key: &[u8], default_value: T) -> T {
	take(key).unwrap_or(default_value)
}

/// Return the value of the item in storage under `key`, or `default_value()` if there is no
/// explicit entry. Ensure there is no explicit entry on return.
pub fn take_or_else<T: Codec + Sized, F: FnOnce() -> T>(key: &[u8], default_value: F) -> T {
	take(key).unwrap_or_else(default_value)
}

/// Check to see if `key` has an explicit entry in storage.
pub fn exists(key: &[u8]) -> bool {
	runtime_io::exists_storage(&twox_128(key)[..])
}

/// Ensure `key` has no explicit entry in storage.
pub fn kill(key: &[u8]) {
	runtime_io::clear_storage(&twox_128(key)[..]);
}

/// Get a Vec of bytes from storage.
pub fn get_raw(key: &[u8]) -> Option<Vec<u8>> {
	runtime_io::storage(&twox_128(key)[..])
}

/// Put a raw byte slice into storage.
pub fn put_raw(key: &[u8], value: &[u8]) {
	runtime_io::set_storage(&twox_128(key)[..], value)
}

/// The underlying runtime storage.
pub struct RuntimeStorage;

impl ::GenericStorage for RuntimeStorage {
	fn exists(&self, key: &[u8]) -> bool {
		super::storage::exists(key)
	}

	/// Load the bytes of a key from storage. Can panic if the type is incorrect.
	fn get<T: Codec>(&self, key: &[u8]) -> Option<T> {
		super::storage::get(key)
	}

	/// Put a value in under a key.
	fn put<T: Codec>(&self, key: &[u8], val: &T) {
		super::storage::put(key, val)
	}

	/// Remove the bytes of a key from storage.
	fn kill(&self, key: &[u8]) {
		super::storage::kill(key)
	}

	/// Take a value from storage, deleting it after reading.
	fn take<T: Codec>(&self, key: &[u8]) -> Option<T> {
		super::storage::take(key)
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
	fn mutate<F: FnOnce(&mut Self::Query)>(f: F);

	/// Clear the storage value.
	fn kill();

	/// Take a value from storage, removing it afterwards.
	fn take() -> Self::Query;
}

impl<T: Codec, U> StorageValue<T> for U where U: generator::StorageValue<T> {
	type Query = U::Query;

	fn key() -> &'static [u8] {
		<U as generator::StorageValue<T>>::key()
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
	fn mutate<F: FnOnce(&mut Self::Query)>(f: F) {
		U::mutate(f, &RuntimeStorage)
	}
	fn kill() {
		U::kill(&RuntimeStorage)
	}
	fn take() -> Self::Query {
		U::take(&RuntimeStorage)
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

impl<T: Codec, U> StorageList<T> for U where U: generator::StorageList<T> {
	fn prefix() -> &'static [u8] {
		<U as generator::StorageList<T>>::prefix()
	}

	fn len_key() -> Vec<u8> {
		<U as generator::StorageList<T>>::len_key()
	}

	fn key_for(index: u32) -> Vec<u8> {
		<U as generator::StorageList<T>>::key_for(index)
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
	fn mutate<KeyArg: Borrow<K>, F: FnOnce(&mut Self::Query)>(key: KeyArg, f: F);

	/// Take the value under a key.
	fn take<KeyArg: Borrow<K>>(key: KeyArg) -> Self::Query;
}

impl<K: Codec, V: Codec, U> StorageMap<K, V> for U where U: generator::StorageMap<K, V> {
	type Query = U::Query;

	fn prefix() -> &'static [u8] {
		<U as generator::StorageMap<K, V>>::prefix()
	}

	fn key_for<KeyArg: Borrow<K>>(key: KeyArg) -> Vec<u8> {
		<U as generator::StorageMap<K, V>>::key_for(key.borrow())
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

	fn mutate<KeyArg: Borrow<K>, F: FnOnce(&mut Self::Query)>(key: KeyArg, f: F) {
		U::mutate(key.borrow(), f, &RuntimeStorage)
	}

	fn take<KeyArg: Borrow<K>>(key: KeyArg) -> Self::Query {
		U::take(key.borrow(), &RuntimeStorage)
	}
}

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
			put(&count.to_keyed_vec(Self::PREFIX), i.borrow());
			count = count.checked_add(1).expect("exceeded runtime storage capacity");
		}

		Self::set_count(count);
	}

	/// Push an item.
	fn push(item: &Self::Item) {
		let len = Self::count();
		put(&len.to_keyed_vec(Self::PREFIX), item);
		Self::set_count(len + 1);
	}

	fn set_item(index: u32, item: &Self::Item) {
		if index < Self::count() {
			put(&index.to_keyed_vec(Self::PREFIX), item);
		}
	}

	fn clear_item(index: u32) {
		if index < Self::count() {
			kill(&index.to_keyed_vec(Self::PREFIX));
		}
	}

	fn item(index: u32) -> Self::Item {
		get_or_default(&index.to_keyed_vec(Self::PREFIX))
	}

	fn set_count(count: u32) {
		(count..Self::count()).for_each(Self::clear_item);
		put(&b"len".to_keyed_vec(Self::PREFIX), &count);
	}

	fn count() -> u32 {
		get_or_default(&b"len".to_keyed_vec(Self::PREFIX))
	}
}

pub mod unhashed {
	use rstd::borrow::Borrow;
	use super::{runtime_io, Codec, Decode, KeyedVec, Vec, IncrementalInput};

	/// Return the value of the item in storage under `key`, or `None` if there is no explicit entry.
	pub fn get<T: Codec + Sized>(key: &[u8]) -> Option<T> {
		runtime_io::read_storage(key, &mut [0; 0][..], 0).map(|_| {
			let mut input = IncrementalInput {
				key,
				pos: 0,
			};
			Decode::decode(&mut input).expect("storage is not null, therefore must be a valid type")
		})
	}

	/// Return the value of the item in storage under `key`, or the type's default if there is no
	/// explicit entry.
	pub fn get_or_default<T: Codec + Sized + Default>(key: &[u8]) -> T {
		get(key).unwrap_or_else(Default::default)
	}

	/// Return the value of the item in storage under `key`, or `default_value` if there is no
	/// explicit entry.
	pub fn get_or<T: Codec + Sized>(key: &[u8], default_value: T) -> T {
		get(key).unwrap_or(default_value)
	}

	/// Return the value of the item in storage under `key`, or `default_value()` if there is no
	/// explicit entry.
	pub fn get_or_else<T: Codec + Sized, F: FnOnce() -> T>(key: &[u8], default_value: F) -> T {
		get(key).unwrap_or_else(default_value)
	}

	/// Put `value` in storage under `key`.
	pub fn put<T: Codec>(key: &[u8], value: &T) {
		value.using_encoded(|slice| runtime_io::set_storage(key, slice));
	}

	/// Remove `key` from storage, returning its value if it had an explicit entry or `None` otherwise.
	pub fn take<T: Codec + Sized>(key: &[u8]) -> Option<T> {
		let r = get(key);
		if r.is_some() {
			kill(key);
		}
		r
	}

	/// Remove `key` from storage, returning its value, or, if there was no explicit entry in storage,
	/// the default for its type.
	pub fn take_or_default<T: Codec + Sized + Default>(key: &[u8]) -> T {
		take(key).unwrap_or_else(Default::default)
	}

	/// Return the value of the item in storage under `key`, or `default_value` if there is no
	/// explicit entry. Ensure there is no explicit entry on return.
	pub fn take_or<T: Codec + Sized>(key: &[u8], default_value: T) -> T {
		take(key).unwrap_or(default_value)
	}

	/// Return the value of the item in storage under `key`, or `default_value()` if there is no
	/// explicit entry. Ensure there is no explicit entry on return.
	pub fn take_or_else<T: Codec + Sized, F: FnOnce() -> T>(key: &[u8], default_value: F) -> T {
		take(key).unwrap_or_else(default_value)
	}

	/// Check to see if `key` has an explicit entry in storage.
	pub fn exists(key: &[u8]) -> bool {
		runtime_io::read_storage(key, &mut [0;0][..], 0).is_some()
	}

	/// Ensure `key` has no explicit entry in storage.
	pub fn kill(key: &[u8]) {
		runtime_io::clear_storage(key);
	}

	/// Ensure keys with the given `prefix` have no entries in storage.
	pub fn kill_prefix(prefix: &[u8]) {
		runtime_io::clear_prefix(prefix);
	}

	/// Get a Vec of bytes from storage.
	pub fn get_raw(key: &[u8]) -> Option<Vec<u8>> {
		runtime_io::storage(key)
	}

	/// Put a raw byte slice into storage.
	pub fn put_raw(key: &[u8], value: &[u8]) {
		runtime_io::set_storage(key, value)
	}

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
				put(&count.to_keyed_vec(Self::PREFIX), i.borrow());
				count = count.checked_add(1).expect("exceeded runtime storage capacity");
			}

			Self::set_count(count);
		}

		fn set_item(index: u32, item: &Self::Item) {
			if index < Self::count() {
				put(&index.to_keyed_vec(Self::PREFIX), item);
			}
		}

		fn clear_item(index: u32) {
			if index < Self::count() {
				kill(&index.to_keyed_vec(Self::PREFIX));
			}
		}

		fn item(index: u32) -> Self::Item {
			get_or_default(&index.to_keyed_vec(Self::PREFIX))
		}

		fn set_count(count: u32) {
			(count..Self::count()).for_each(Self::clear_item);
			put(&b"len".to_keyed_vec(Self::PREFIX), &count);
		}

		fn count() -> u32 {
			get_or_default(&b"len".to_keyed_vec(Self::PREFIX))
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use runtime_io::{twox_128, TestExternalities, with_externalities};

	#[test]
	fn integers_can_be_stored() {
		let mut t = TestExternalities::new();
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
		let mut t = TestExternalities::new();
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
		let mut t = TestExternalities::new();
		with_externalities(&mut t, || {
			runtime_io::set_storage(&twox_128(b":test"), b"\x0b\0\0\0Hello world");
			let x = b"Hello world".to_vec();
			let y = get::<Vec<u8>>(b":test").unwrap();
			assert_eq!(x, y);

		});
	}

	#[test]
	fn vecs_can_be_stored() {
		let mut t = TestExternalities::new();
		let x = b"Hello world".to_vec();

		with_externalities(&mut t, || {
			put(b":test", &x);
		});

		with_externalities(&mut t, || {
			let y: Vec<u8> = get(b":test").unwrap();
			assert_eq!(x, y);
		});
	}
}
