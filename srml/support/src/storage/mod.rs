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
use codec::{Codec, Encode, Decode, KeyedVec, EncodeAppend};

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
	fn key() -> Vec<u8>;

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
	fn append<I: Encode>(items: &[I]) -> Result<(), &'static str>
		where T: EncodeAppend<Item=I>;
}

/// A strongly-typed map in storage.
pub trait StorageMap<K: Codec, V: Codec> {
	/// The type that get/take return.
	type Query;

	/// Get the storage key used to fetch a value corresponding to a specific key.
	fn key_for<KeyArg: Borrow<K>>(key: KeyArg) -> Vec<u8>;

	/// Does the value (explicitly) exist in storage?
	fn exists<KeyArg: Borrow<K>>(key: KeyArg) -> bool;

	/// Load the value associated with the given key from the map.
	fn get<KeyArg: Borrow<K>>(key: KeyArg) -> Self::Query;

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

	/// Append the given item to the value in the storage.
	///
	/// `T` is required to implement `codec::EncodeAppend`.
	fn append<KeyArg: Borrow<K>, I: Encode>(key: KeyArg, items: &[I]) -> Result<(), &'static str>
		where V: EncodeAppend<Item=I>;
}

/// A strongly-typed map in storage.
pub trait StorageLinkedMap<K: Codec, V: Codec> {
	/// The type that get/take return.
	type Query;

	/// Does the value (explicitly) exist in storage?
	fn exists<KeyArg: Borrow<K>>(key: KeyArg) -> bool;

	/// Load the value associated with the given key from the map.
	fn get<KeyArg: Borrow<K>>(key: KeyArg) -> Self::Query;

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
	fn enumerate() -> Box<dyn Iterator<Item = (K, V)>> where K: 'static, V: 'static, Self: 'static;
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
