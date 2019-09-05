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
use crate::rstd::{borrow::Borrow, iter::FromIterator};
use codec::{Codec, Encode, Decode, KeyedVec, EncodeAppend};
<<<<<<< HEAD
use hashed::generator::{HashedStorage, StorageHasher};
use unhashed::generator::UnhashedStorage;
use crate::traits::{StorageDefault, Len};
use primitives::child_trie::ChildTrie;
use primitives::child_trie::ChildTrieReadRef;
use primitives::storage::well_known_keys;
=======
use crate::traits::Len;
>>>>>>> master

#[macro_use]
pub mod storage_items;
pub mod unhashed;
pub mod hashed;
pub mod child;
pub mod generator;

/// A trait for working with macro-generated storage values under the substrate storage API.
pub trait StorageValue<T: Codec> {
	/// The type that get/take return.
	type Query;

	/// Get the storage key.
	fn hashed_key() -> [u8; 16];

	/// Does the value (explicitly) exist in storage?
	fn exists() -> bool;

	/// Load the value from the provided storage instance.
	fn get() -> Self::Query;

	/// Store a value under this key into the provided storage instance.
	fn put<Arg: Borrow<T>>(val: Arg);

	/// Store a value under this key into the provided storage instance; this can take any reference
	/// type that derefs to `T` (and has `Encode` implemented).
	fn put_ref<Arg: ?Sized + Encode>(val: &Arg) where T: AsRef<Arg>;

	/// Mutate the value
	fn mutate<R, F: FnOnce(&mut Self::Query) -> R>(f: F) -> R;

	/// Clear the storage value.
	fn kill();

	/// Take a value from storage, removing it afterwards.
	fn take() -> Self::Query;

	/// Append the given item to the value in the storage.
	///
	/// `T` is required to implement `codec::EncodeAppend`.
	fn append<'a, I, R>(items: R) -> Result<(), &'static str> where
		I: 'a + Encode,
		T: EncodeAppend<Item=I>,
		R: IntoIterator<Item=&'a I>,
		R::IntoIter: ExactSizeIterator;

	/// Append the given items to the value in the storage.
	///
	/// `T` is required to implement `Codec::EncodeAppend`.
	///
	/// Upon any failure, it replaces `items` as the new value (assuming that the previous stored
	/// data is simply corrupt and no longer usable).
	///
	/// ### WARNING
	///
	/// use with care; if your use-case is not _exactly_ as what this function is doing,
	/// you should use append and sensibly handle failure within the runtime code if it happens.
	fn append_or_put<'a, I, R>(items: R) where
		I: 'a + Encode + Clone,
		T: EncodeAppend<Item=I> + FromIterator<I>,
		R: IntoIterator<Item=&'a I> + Clone,
		R::IntoIter: ExactSizeIterator;

	/// Read the length of the value in a fast way, without decoding the entire value.
	///
	/// `T` is required to implement `Codec::DecodeLength`.
	fn decode_len() -> Result<usize, &'static str>
		where T: codec::DecodeLength + Len;
}

/// A strongly-typed map in storage.
pub trait StorageMap<K: Codec, V: Codec> {
	/// The type that get/take return.
	type Query;

	/// Get the storage key used to fetch a value corresponding to a specific key.
	fn hashed_key_for<KeyArg: Borrow<K>>(key: KeyArg) -> Vec<u8>;

	/// Does the value (explicitly) exist in storage?
	fn exists<KeyArg: Borrow<K>>(key: KeyArg) -> bool;

	/// Load the value associated with the given key from the map.
	fn get<KeyArg: Borrow<K>>(key: KeyArg) -> Self::Query;

	/// Swap the values of two keys.
	fn swap<KeyArg1: Borrow<K>, KeyArg2: Borrow<K>>(key1: KeyArg1, key2: KeyArg2);

	/// Store a value to be associated with the given key from the map.
	fn insert<KeyArg: Borrow<K>, ValArg: Borrow<V>>(key: KeyArg, val: ValArg);

	/// Store a value under this key into the provided storage instance; this can take any reference
	/// type that derefs to `T` (and has `Encode` implemented).
	fn insert_ref<KeyArg: Borrow<K>, ValArg: ?Sized + Encode>(key: KeyArg, val: &ValArg) where V: AsRef<ValArg>;

	/// Remove the value under a key.
	fn remove<KeyArg: Borrow<K>>(key: KeyArg);

	/// Mutate the value under a key.
	fn mutate<KeyArg: Borrow<K>, R, F: FnOnce(&mut Self::Query) -> R>(key: KeyArg, f: F) -> R;

	/// Take the value under a key.
	fn take<KeyArg: Borrow<K>>(key: KeyArg) -> Self::Query;

	/// Append the given items to the value in the storage.
	///
	/// `V` is required to implement `codec::EncodeAppend`.
	fn append<'a, I, R, KeyArg>(key: KeyArg, items: R) -> Result<(), &'static str>
	where
		KeyArg: Borrow<K>,
		I: 'a + codec::Encode,
		V: codec::EncodeAppend<Item=I>,
		R: IntoIterator<Item=&'a I> + Clone,
		R::IntoIter: ExactSizeIterator;

	/// Safely append the given items to the value in the storage. If a codec error occurs, then the
	/// old (presumably corrupt) value is replaced with the given `items`.
	///
	/// `T` is required to implement `codec::EncodeAppend`.
	fn append_or_insert<'a, I, R, KeyArg>(key: KeyArg, items: R)
	where
		KeyArg: Borrow<K>,
		I: 'a + codec::Encode + Clone,
		V: codec::EncodeAppend<Item=I> + crate::rstd::iter::FromIterator<I>,
		R: IntoIterator<Item=&'a I> + Clone,
		R::IntoIter: ExactSizeIterator;

	/// Read the length of the value in a fast way, without decoding the entire value.
	///
	/// `T` is required to implement `Codec::DecodeLength`.
	///
	/// Note that `0` is returned as the default value if no encoded value exists at the given key.
	/// Therefore, this function cannot be used as a sign of _existence_. use the `::exists()`
	/// function for this purpose.
	fn decode_len<KeyArg: Borrow<K>>(key: KeyArg) -> Result<usize, &'static str>
		where V: codec::DecodeLength + Len;
}

/// A strongly-typed linked map in storage.
///
/// Similar to `StorageMap` but allows to enumerate other elements and doesn't implement append.
pub trait StorageLinkedMap<K: Codec, V: Codec> {
	/// The type that get/take return.
	type Query;

	/// The type that iterates over all `(key, value)`.
	type Enumerator: Iterator<Item = (K, V)>;

	/// Does the value (explicitly) exist in storage?
	fn exists<KeyArg: Borrow<K>>(key: KeyArg) -> bool;

	/// Load the value associated with the given key from the map.
	fn get<KeyArg: Borrow<K>>(key: KeyArg) -> Self::Query;

	/// Swap the values of two keys.
	fn swap<KeyArg1: Borrow<K>, KeyArg2: Borrow<K>>(key1: KeyArg1, key2: KeyArg2);

	/// Store a value to be associated with the given key from the map.
	fn insert<KeyArg: Borrow<K>, ValArg: Borrow<V>>(key: KeyArg, val: ValArg);

	/// Store a value under this key into the provided storage instance; this can take any reference
	/// type that derefs to `T` (and has `Encode` implemented).
	fn insert_ref<KeyArg: Borrow<K>, ValArg: ?Sized + Encode>(key: KeyArg, val: &ValArg) where V: AsRef<ValArg>;

	/// Remove the value under a key.
	fn remove<KeyArg: Borrow<K>>(key: KeyArg);

	/// Mutate the value under a key.
	fn mutate<KeyArg: Borrow<K>, R, F: FnOnce(&mut Self::Query) -> R>(key: KeyArg, f: F) -> R;

	/// Take the value under a key.
	fn take<KeyArg: Borrow<K>>(key: KeyArg) -> Self::Query;

	/// Return current head element.
	fn head() -> Option<K>;

	/// Enumerate all elements in the map.
	fn enumerate() -> Self::Enumerator;

	/// Read the length of the value in a fast way, without decoding the entire value.
	///
	/// `T` is required to implement `Codec::DecodeLength`.
	///
	/// Note that `0` is returned as the default value if no encoded value exists at the given key.
	/// Therefore, this function cannot be used as a sign of _existence_. use the `::exists()`
	/// function for this purpose.
	fn decode_len<KeyArg: Borrow<K>>(key: KeyArg) -> Result<usize, &'static str>
		where V: codec::DecodeLength + Len;
}

/// An implementation of a map with a two keys.
///
/// It provides an important ability to efficiently remove all entries
/// that have a common first key.
pub trait StorageDoubleMap<K1: Encode, K2: Encode, V: Codec> {
	/// The type that get/take returns.
	type Query;

	fn exists<KArg1, KArg2>(k1: &KArg1, k2: &KArg2) -> bool
	where
		K1: Borrow<KArg1>,
		K2: Borrow<KArg2>,
		KArg1: ?Sized + Encode,
		KArg2: ?Sized + Encode;

	fn get<KArg1, KArg2>(k1: &KArg1, k2: &KArg2) -> Self::Query
	where
		K1: Borrow<KArg1>,
		K2: Borrow<KArg2>,
		KArg1: ?Sized + Encode,
		KArg2: ?Sized + Encode;

	fn take<KArg1, KArg2>(k1: &KArg1, k2: &KArg2) -> Self::Query
	where
		K1: Borrow<KArg1>,
		K2: Borrow<KArg2>,
		KArg1: ?Sized + Encode,
		KArg2: ?Sized + Encode;

	fn insert<KArg1, KArg2, VArg>(k1: &KArg1, k2: &KArg2, val: &VArg)
	where
		K1: Borrow<KArg1>,
		K2: Borrow<KArg2>,
		V: Borrow<VArg>,
		KArg1: ?Sized + Encode,
		KArg2: ?Sized + Encode,
		VArg: ?Sized + Encode;

	fn remove<KArg1, KArg2>(k1: &KArg1, k2: &KArg2)
	where
		K1: Borrow<KArg1>,
		K2: Borrow<KArg2>,
		KArg1: ?Sized + Encode,
		KArg2: ?Sized + Encode;

	fn remove_prefix<KArg1>(k1: &KArg1) where KArg1: ?Sized + Encode, K1: Borrow<KArg1>;

	fn mutate<KArg1, KArg2, R, F>(k1: &KArg1, k2: &KArg2, f: F) -> R
	where
		K1: Borrow<KArg1>,
		K2: Borrow<KArg2>,
		KArg1: ?Sized + Encode,
		KArg2: ?Sized + Encode,
		F: FnOnce(&mut Self::Query) -> R;

	fn append<KArg1, KArg2, I>(
		k1: &KArg1,
		k2: &KArg2,
		items: &[I],
	) -> Result<(), &'static str>
	where
		K1: Borrow<KArg1>,
		K2: Borrow<KArg2>,
		KArg1: ?Sized + Encode,
		KArg2: ?Sized + Encode,
		I: codec::Encode,
		V: EncodeAppend<Item=I>;
}
<<<<<<< HEAD

impl<K1: Encode, K2: Encode, V: Codec, U> StorageDoubleMap<K1, K2, V> for U
where
	U: unhashed::generator::StorageDoubleMap<K1, K2, V>
{
	type Query = U::Query;

	fn prefix() -> &'static [u8] {
		<U as unhashed::generator::StorageDoubleMap<K1, K2, V>>::prefix()
	}

	fn key_for<KArg1, KArg2>(k1: &KArg1, k2: &KArg2) -> Vec<u8>
	where
		K1: Borrow<KArg1>,
		K2: Borrow<KArg2>,
		KArg1: ?Sized + Encode,
		KArg2: ?Sized + Encode,
	{
		<U as unhashed::generator::StorageDoubleMap<K1, K2, V>>::key_for(k1, k2)
	}

	fn prefix_for<KArg1>(k1: &KArg1) -> Vec<u8> where KArg1: ?Sized + Encode, K1: Borrow<KArg1> {
		<U as unhashed::generator::StorageDoubleMap<K1, K2, V>>::prefix_for(k1)
	}

	fn exists<KArg1, KArg2>(k1: &KArg1, k2: &KArg2) -> bool
	where
		K1: Borrow<KArg1>,
		K2: Borrow<KArg2>,
		KArg1: ?Sized + Encode,
		KArg2: ?Sized + Encode,
	{
		U::exists(k1, k2, &RuntimeStorage)
	}

	fn get<KArg1, KArg2>(k1: &KArg1, k2: &KArg2) -> Self::Query
	where
		K1: Borrow<KArg1>,
		K2: Borrow<KArg2>,
		KArg1: ?Sized + Encode,
		KArg2: ?Sized + Encode,
	{
		U::get(k1, k2, &RuntimeStorage)
	}

	fn take<KArg1, KArg2>(k1: &KArg1, k2: &KArg2) -> Self::Query
	where
		K1: Borrow<KArg1>,
		K2: Borrow<KArg2>,
		KArg1: ?Sized + Encode,
		KArg2: ?Sized + Encode,
	{
		U::take(k1.borrow(), k2.borrow(), &mut RuntimeStorage)
	}

	fn insert<KArg1, KArg2, VArg>(k1: &KArg1, k2: &KArg2, val: &VArg)
	where
		K1: Borrow<KArg1>,
		K2: Borrow<KArg2>,
		V: Borrow<VArg>,
		KArg1: ?Sized + Encode,
		KArg2: ?Sized + Encode,
		VArg: ?Sized + Encode,
	{
		U::insert(k1, k2, val, &mut RuntimeStorage)
	}

	fn remove<KArg1, KArg2>(k1: &KArg1, k2: &KArg2)
	where
		K1: Borrow<KArg1>,
		K2: Borrow<KArg2>,
		KArg1: ?Sized + Encode,
		KArg2: ?Sized + Encode,
	{
		U::remove(k1, k2, &mut RuntimeStorage)
	}

	fn remove_prefix<KArg1>(k1: &KArg1) where KArg1: ?Sized + Encode, K1: Borrow<KArg1> {
		U::remove_prefix(k1, &mut RuntimeStorage)
	}

	fn mutate<KArg1, KArg2, R, F>(k1: &KArg1, k2: &KArg2, f: F) -> R
	where
		K1: Borrow<KArg1>,
		K2: Borrow<KArg2>,
		KArg1: ?Sized + Encode,
		KArg2: ?Sized + Encode,
		F: FnOnce(&mut Self::Query) -> R
	{
		U::mutate(k1, k2, f, &mut RuntimeStorage)
	}

	fn append<KArg1, KArg2, I>(
		k1: &KArg1,
		k2: &KArg2,
		items: &[I],
	) -> Result<(), &'static str>
	where
		K1: Borrow<KArg1>,
		K2: Borrow<KArg2>,
		KArg1: ?Sized + Encode,
		KArg2: ?Sized + Encode,
		I: codec::Encode,
		V: EncodeAppend<Item=I>,
	{
		U::append(k1, k2, items, &mut RuntimeStorage)
	}
}

/// child storage NOTE could replace unhashed by having only one kind of storage (root being null storage
/// key (storage_key can become Option<&[u8]>).
/// This module is a currently only a variant of unhashed with additional `storage_key`.
/// Note that `storage_key` must be unique and strong (strong in the sense of being long enough to
/// avoid collision from a resistant hash function (which unique implies)).
pub mod child {
	use super::{Codec, Decode, Vec, ChildTrie,
		ChildTrieReadRef, well_known_keys};

	/// Method for fetching or initiating a new child trie.
	pub fn next_keyspace() -> u128 {
		let key = well_known_keys::CHILD_STORAGE_KEYSPACE_COUNTER;
		// do start at 1 (0 is reserved for top trie)
		let previous = super::unhashed::get(key).unwrap_or(0u128);
		let new = previous + 1;
		super::unhashed::put(key, &new);
		new
	}

	/// Method for fetching or initiating a new child trie.
	pub fn fetch_or_new(
		parent: &[u8],
	) -> ChildTrie {
		ChildTrie::fetch_or_new(
			|pk| { child_trie(pk) },
			|ct| {
				let updated = set_child_trie(ct);
				// fetch or new create a new child trie
				// so the child trie creation condition
				// cannot fail at this point.
				debug_assert!(updated);
			},
			parent,
			|| next_keyspace(),
		)
	}

	/// Fetch a child trie return None if no child trie for
	/// this storage key.
	pub fn child_trie(storage_key: &[u8]) -> Option<ChildTrie> {
		runtime_io::child_trie(storage_key)
	}

	/// Update or create an existing child trie.
	/// Warning in case of update this function does not allow:
	/// - root change
	/// Return false and do nothing in those cases.
	pub fn set_child_trie(ct: ChildTrie) -> bool {
		runtime_io::set_child_trie(ct)
	}

	/// Return the value of the item in storage under `key`, or `None` if there is no explicit entry.
	pub fn get<T: Codec + Sized>(child_trie: ChildTrieReadRef, key: &[u8]) -> Option<T> {
		runtime_io::child_storage(child_trie.clone(), key).map(|v| {
			Decode::decode(&mut &v[..]).expect("storage is not null, therefore must be a valid type")
		})
	}

	/// Return the value of the item in storage under `key`, or the type's default if there is no
	/// explicit entry.
	pub fn get_or_default<T: Codec + Sized + Default>(child_trie: ChildTrieReadRef, key: &[u8]) -> T {
		get(child_trie, key).unwrap_or_else(Default::default)
	}

	/// Return the value of the item in storage under `key`, or `default_value` if there is no
	/// explicit entry.
	pub fn get_or<T: Codec + Sized>(child_trie: ChildTrieReadRef, key: &[u8], default_value: T) -> T {
		get(child_trie, key).unwrap_or(default_value)
	}

	/// Return the value of the item in storage under `key`, or `default_value()` if there is no
	/// explicit entry.
	pub fn get_or_else<T: Codec + Sized, F: FnOnce() -> T>(
		child_trie: ChildTrieReadRef,
		key: &[u8],
		default_value: F,
	) -> T {
		get(child_trie, key).unwrap_or_else(default_value)
	}

	/// Put `value` in storage under `key`.
	pub fn put<T: Codec>(child_trie: &ChildTrie, key: &[u8], value: &T) {
		value.using_encoded(|slice| runtime_io::set_child_storage(child_trie, key, slice));
	}

	/// Remove `key` from storage, returning its value if it had an explicit entry
	/// or `None` otherwise.
	pub fn take<T: Codec + Sized>(child_trie: &ChildTrie, key: &[u8]) -> Option<T> {
		let r = get(child_trie.node_ref(), key);
		if r.is_some() {
			kill(child_trie, key);
		}
		r
	}

	/// Remove `key` from storage, returning its value, or, if there was no explicit entry in storage,
	/// the default for its type.
	pub fn take_or_default<T: Codec + Sized + Default>(child_trie: &ChildTrie, key: &[u8]) -> T {
		take(child_trie, key).unwrap_or_else(Default::default)
	}

	/// Return the value of the item in storage under `key`, or `default_value` if there is no
	/// explicit entry. Ensure there is no explicit entry on return.
	pub fn take_or<T: Codec + Sized>(child_trie: &ChildTrie,key: &[u8], default_value: T) -> T {
		take(child_trie, key).unwrap_or(default_value)
	}

	/// Return the value of the item in storage under `key`, or `default_value()` if there is no
	/// explicit entry. Ensure there is no explicit entry on return.
	pub fn take_or_else<T: Codec + Sized, F: FnOnce() -> T>(
		child_trie: &ChildTrie,
		key: &[u8],
		default_value: F,
	) -> T {
		take(child_trie, key).unwrap_or_else(default_value)
	}

	/// Check to see if `key` has an explicit entry in storage.
	pub fn exists(child_trie: ChildTrieReadRef, key: &[u8]) -> bool {
		runtime_io::read_child_storage(child_trie, key, &mut [0;0][..], 0).is_some()
	}

	/// Remove all `child_trie` key/values
	pub fn kill_storage(child_trie: &ChildTrie) {
		runtime_io::kill_child_storage(child_trie)
	}

	/// Ensure `key` has no explicit entry in storage.
	pub fn kill(child_trie: &ChildTrie, key: &[u8]) {
		runtime_io::clear_child_storage(child_trie, key);
	}

	/// Get a Vec of bytes from storage.
	pub fn get_raw(child_trie: ChildTrieReadRef, key: &[u8]) -> Option<Vec<u8>> {
		runtime_io::child_storage(child_trie, key)
	}

	/// Put a raw byte slice into storage.
	pub fn put_raw(child_trie: &ChildTrie, key: &[u8], value: &[u8]) {
		runtime_io::set_child_storage(child_trie, key, value)
	}

	pub use super::unhashed::StorageVec;
}
=======
>>>>>>> master
