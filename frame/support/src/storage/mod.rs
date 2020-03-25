// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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

use sp_std::prelude::*;
use codec::{FullCodec, FullEncode, Encode, EncodeAppend, EncodeLike, Decode};
use crate::{traits::Len, hash::{StorageHasher, ReversibleStorageHasher}};

pub mod unhashed;
pub mod hashed;
pub mod child;
#[doc(hidden)]
pub mod generator;
pub mod migration;

/// A trait for working with macro-generated storage values under the substrate storage API.
///
/// Details on implementation can be found at
/// [`generator::StorageValue`]
pub trait StorageValue<T: FullCodec> {
	/// The type that get/take return.
	type Query;

	/// Get the storage key.
	fn hashed_key() -> [u8; 32];

	/// Does the value (explicitly) exist in storage?
	fn exists() -> bool;

	/// Load the value from the provided storage instance.
	fn get() -> Self::Query;

	/// Try to get the underlying value from the provided storage instance; `Ok` if it exists,
	/// `Err` if not.
	fn try_get() -> Result<T, ()>;

	/// Translate a value from some previous type (`O`) to the current type.
	///
	/// `f: F` is the translation function.
	///
	/// Returns `Err` if the storage item could not be interpreted as the old type, and Ok, along
	/// with the new value if it could.
	///
	/// NOTE: This operates from and to `Option<_>` types; no effort is made to respect the default
	/// value of the original type.
	///
	/// # Warning
	///
	/// This function must be used with care, before being updated the storage still contains the
	/// old type, thus other calls (such as `get`) will fail at decoding it.
	///
	/// # Usage
	///
	/// This would typically be called inside the module implementation of on_runtime_upgrade, while
	/// ensuring **no usage of this storage are made before the call to `on_runtime_upgrade`**. (More
	/// precisely prior initialized modules doesn't make use of this storage).
	fn translate<O: Decode, F: FnOnce(Option<O>) -> Option<T>>(f: F) -> Result<Option<T>, ()>;

	/// Store a value under this key into the provided storage instance.
	fn put<Arg: EncodeLike<T>>(val: Arg);

	/// Store a value under this key into the provided storage instance; this uses the query
	/// type rather than the underlying value.
	fn set(val: Self::Query);

	/// Mutate the value
	fn mutate<R, F: FnOnce(&mut Self::Query) -> R>(f: F) -> R;

	/// Clear the storage value.
	fn kill();

	/// Take a value from storage, removing it afterwards.
	fn take() -> Self::Query;

	/// Append the given item to the value in the storage.
	///
	/// `T` is required to implement `codec::EncodeAppend`.
	fn append<Items, Item, EncodeLikeItem>(items: Items) -> Result<(), &'static str>
	where
		Item: Encode,
		EncodeLikeItem: EncodeLike<Item>,
		T: EncodeAppend<Item=Item>,
		Items: IntoIterator<Item=EncodeLikeItem>,
		Items::IntoIter: ExactSizeIterator;

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
	fn append_or_put<Items, Item, EncodeLikeItem>(items: Items) where
		Item: Encode,
		EncodeLikeItem: EncodeLike<Item>,
		T: EncodeAppend<Item=Item>,
		Items: IntoIterator<Item=EncodeLikeItem> + Clone + EncodeLike<T>,
		Items::IntoIter: ExactSizeIterator;


	/// Read the length of the value in a fast way, without decoding the entire value.
	///
	/// `T` is required to implement `Codec::DecodeLength`.
	fn decode_len() -> Result<usize, &'static str>
		where T: codec::DecodeLength + Len;
}

/// A strongly-typed map in storage.
///
/// Details on implementation can be found at
/// [`generator::StorageMap`]
pub trait StorageMap<K: FullEncode, V: FullCodec> {
	/// The type that get/take return.
	type Query;

	/// Hasher used to hash the key.
	type Hasher;

	/// Get the storage key used to fetch a value corresponding to a specific key.
	fn hashed_key_for<KeyArg: EncodeLike<K>>(key: KeyArg) -> Vec<u8>;

	/// Does the value (explicitly) exist in storage?
	fn contains_key<KeyArg: EncodeLike<K>>(key: KeyArg) -> bool;

	/// Load the value associated with the given key from the map.
	fn get<KeyArg: EncodeLike<K>>(key: KeyArg) -> Self::Query;

	/// Swap the values of two keys.
	fn swap<KeyArg1: EncodeLike<K>, KeyArg2: EncodeLike<K>>(key1: KeyArg1, key2: KeyArg2);

	/// Store a value to be associated with the given key from the map.
	fn insert<KeyArg: EncodeLike<K>, ValArg: EncodeLike<V>>(key: KeyArg, val: ValArg);

	/// Remove the value under a key.
	fn remove<KeyArg: EncodeLike<K>>(key: KeyArg);

	/// Remove all values.
	fn remove_all();

	/// Mutate the value under a key.
	fn mutate<KeyArg: EncodeLike<K>, R, F: FnOnce(&mut Self::Query) -> R>(key: KeyArg, f: F) -> R;

	/// Mutate the item, only if an `Ok` value is returned.
	fn try_mutate<KeyArg: EncodeLike<K>, R, E, F: FnOnce(&mut Self::Query) -> Result<R, E>>(
		key: KeyArg,
		f: F,
	) -> Result<R, E>;

	/// Mutate the value under a key. Deletes the item if mutated to a `None`.
	fn mutate_exists<KeyArg: EncodeLike<K>, R, F: FnOnce(&mut Option<V>) -> R>(key: KeyArg, f: F) -> R;

	/// Mutate the item, only if an `Ok` value is returned. Deletes the item if mutated to a `None`.
	fn try_mutate_exists<KeyArg: EncodeLike<K>, R, E, F: FnOnce(&mut Option<V>) -> Result<R, E>>(
		key: KeyArg,
		f: F,
	) -> Result<R, E>;

	/// Take the value under a key.
	fn take<KeyArg: EncodeLike<K>>(key: KeyArg) -> Self::Query;

	/// Append the given items to the value in the storage.
	///
	/// `V` is required to implement `codec::EncodeAppend`.
	fn append<Items, Item, EncodeLikeItem, KeyArg>(key: KeyArg, items: Items) -> Result<(), &'static str> where
		KeyArg: EncodeLike<K>,
		Item: Encode,
		EncodeLikeItem: EncodeLike<Item>,
		V: EncodeAppend<Item=Item>,
		Items: IntoIterator<Item=EncodeLikeItem>,
		Items::IntoIter: ExactSizeIterator;

	/// Safely append the given items to the value in the storage. If a codec error occurs, then the
	/// old (presumably corrupt) value is replaced with the given `items`.
	///
	/// `V` is required to implement `codec::EncodeAppend`.
	fn append_or_insert<Items, Item, EncodeLikeItem, KeyArg>(key: KeyArg, items: Items) where
		KeyArg: EncodeLike<K>,
		Item: Encode,
		EncodeLikeItem: EncodeLike<Item>,
		V: EncodeAppend<Item=Item>,
		Items: IntoIterator<Item=EncodeLikeItem> + Clone + EncodeLike<V>,
		Items::IntoIter: ExactSizeIterator;

	/// Read the length of the value in a fast way, without decoding the entire value.
	///
	/// `T` is required to implement `Codec::DecodeLength`.
	///
	/// Note that `0` is returned as the default value if no encoded value exists at the given key.
	/// Therefore, this function cannot be used as a sign of _existence_. use the `::contains_key()`
	/// function for this purpose.
	fn decode_len<KeyArg: EncodeLike<K>>(key: KeyArg) -> Result<usize, &'static str>
		where V: codec::DecodeLength + Len;

	/// Migrate an item with the given `key` from a defunct `OldHasher` to the current hasher.
	///
	/// If the key doesn't exist, then it's a no-op. If it does, then it returns its value.
	fn migrate_key<OldHasher: StorageHasher, KeyArg: EncodeLike<K>>(key: KeyArg) -> Option<V>;

	/// Migrate an item with the given `key` from a `blake2_256` hasher to the current hasher.
	///
	/// If the key doesn't exist, then it's a no-op. If it does, then it returns its value.
	fn migrate_key_from_blake<KeyArg: EncodeLike<K>>(key: KeyArg) -> Option<V> {
		Self::migrate_key::<crate::hash::Blake2_256, KeyArg>(key)
	}

	/// Enumerate all elements in the map in no particular order. If you alter the map while doing
	/// this, you'll get undefined results.
	fn iter() -> PrefixIterator<(K, V)> where Self::Hasher: ReversibleStorageHasher;

	/// Remove all elements from the map and iterate through them in no particular order. If you
	/// add elements to the map while doing this, you'll get undefined results.
	fn drain() -> PrefixIterator<(K, V)> where Self::Hasher: ReversibleStorageHasher;

	/// Enumerate all elements in the map in no particular order. If you alter the map while doing
	/// this, you'll get undefined results.
	fn iter_values() -> PrefixIterator<V>;

	/// Translate the values of all elements by a function `f`, in the map in no particular order.
	/// By returning `None` from `f` for an element, you'll remove it from the map.
	fn translate<O: Decode, F: Fn(K, O) -> Option<V>>(f: F) where
		Self::Hasher: ReversibleStorageHasher;

	/// Translate the values from some previous `OldValue` to the current type.
	///
	/// `TV` translates values.
	///
	/// Returns `Err` if the map could not be interpreted as the old type, and Ok if it could.
	/// The `Err` contains the number of value that couldn't be interpreted, those value are
	/// removed from the map.
	///
	/// # Warning
	///
	/// This function must be used with care, before being updated the storage still contains the
	/// old type, thus other calls (such as `get`) will fail at decoding it.
	///
	/// # Usage
	///
	/// This would typically be called inside the module implementation of on_runtime_upgrade, while
	/// ensuring **no usage of this storage are made before the call to `on_runtime_upgrade`**. (More
	/// precisely prior initialized modules doesn't make use of this storage).
	fn translate_values<OldV, TranslateV>(translate_val: TranslateV) -> Result<(), u32>
		where OldV: Decode, TranslateV: Fn(OldV) -> V;
}

/// An implementation of a map with a two keys.
///
/// It provides an important ability to efficiently remove all entries
/// that have a common first key.
///
/// Details on implementation can be found at
/// [`generator::StorageDoubleMap`]
pub trait StorageDoubleMap<K1: FullEncode, K2: FullEncode, V: FullCodec> {
	/// The type that get/take returns.
	type Query;

	/// Hasher used to hash first key.
	type Hasher1;

	/// Hasher used to hash second key.
	type Hasher2;

	fn hashed_key_for<KArg1, KArg2>(k1: KArg1, k2: KArg2) -> Vec<u8>
	where
		KArg1: EncodeLike<K1>,
		KArg2: EncodeLike<K2>;

	fn contains_key<KArg1, KArg2>(k1: KArg1, k2: KArg2) -> bool
	where
		KArg1: EncodeLike<K1>,
		KArg2: EncodeLike<K2>;

	fn get<KArg1, KArg2>(k1: KArg1, k2: KArg2) -> Self::Query
	where
		KArg1: EncodeLike<K1>,
		KArg2: EncodeLike<K2>;

	fn take<KArg1, KArg2>(k1: KArg1, k2: KArg2) -> Self::Query
	where
		KArg1: EncodeLike<K1>,
		KArg2: EncodeLike<K2>;

	/// Swap the values of two key-pairs.
	fn swap<XKArg1, XKArg2, YKArg1, YKArg2>(x_k1: XKArg1, x_k2: XKArg2, y_k1: YKArg1, y_k2: YKArg2)
	where
		XKArg1: EncodeLike<K1>,
		XKArg2: EncodeLike<K2>,
		YKArg1: EncodeLike<K1>,
		YKArg2: EncodeLike<K2>;

	fn insert<KArg1, KArg2, VArg>(k1: KArg1, k2: KArg2, val: VArg)
	where
		KArg1: EncodeLike<K1>,
		KArg2: EncodeLike<K2>,
		VArg: EncodeLike<V>;

	fn remove<KArg1, KArg2>(k1: KArg1, k2: KArg2)
	where
		KArg1: EncodeLike<K1>,
		KArg2: EncodeLike<K2>;

	fn remove_prefix<KArg1>(k1: KArg1) where KArg1: ?Sized + EncodeLike<K1>;

	fn remove_all();

	fn mutate<KArg1, KArg2, R, F>(k1: KArg1, k2: KArg2, f: F) -> R
	where
		KArg1: EncodeLike<K1>,
		KArg2: EncodeLike<K2>,
		F: FnOnce(&mut Self::Query) -> R;

	fn append<Items, Item, EncodeLikeItem, KArg1, KArg2>(
		k1: KArg1,
		k2: KArg2,
		items: Items,
	) -> Result<(), &'static str>
	where
		KArg1: EncodeLike<K1>,
		KArg2: EncodeLike<K2>,
		Item: Encode,
		EncodeLikeItem: EncodeLike<Item>,
		V: EncodeAppend<Item=Item>,
		Items: IntoIterator<Item=EncodeLikeItem>,
		Items::IntoIter: ExactSizeIterator;

	fn append_or_insert<Items, Item, EncodeLikeItem, KArg1, KArg2>(
		k1: KArg1,
		k2: KArg2,
		items: Items,
	)
	where
		KArg1: EncodeLike<K1>,
		KArg2: EncodeLike<K2>,
		Item: Encode,
		EncodeLikeItem: EncodeLike<Item>,
		V: EncodeAppend<Item=Item>,
		Items: IntoIterator<Item=EncodeLikeItem> + Clone + EncodeLike<V>,
		Items::IntoIter: ExactSizeIterator;

	/// Read the length of the value in a fast way, without decoding the entire value.
	///
	/// `V` is required to implement `Codec::DecodeLength`.
	///
	/// Note that `0` is returned as the default value if no encoded value exists at the given key.
	/// Therefore, this function cannot be used as a sign of _existence_. use the `::contains_key()`
	/// function for this purpose.
	fn decode_len<KArg1, KArg2>(key1: KArg1, key2: KArg2) -> Result<usize, &'static str>
		where
			KArg1: EncodeLike<K1>,
			KArg2: EncodeLike<K2>,
			V: codec::DecodeLength + Len;

	/// Migrate an item with the given `key1` and `key2` from defunct `OldHasher1` and
	/// `OldHasher2` to the current hashers.
	///
	/// If the key doesn't exist, then it's a no-op. If it does, then it returns its value.
	fn migrate_keys<
		OldHasher1: StorageHasher,
		OldHasher2: StorageHasher,
		KeyArg1: EncodeLike<K1>,
		KeyArg2: EncodeLike<K2>,
	>(key1: KeyArg1, key2: KeyArg2) -> Option<V>;

	/// Translate the values of all elements by a function `f`, in the map in no particular order.
	/// By returning `None` from `f` for an element, you'll remove it from the map.
	fn translate_values<O: Decode, F: Fn(O) -> Option<V>>(f: F);

	/// Enumerate all elements in the map with first key `k1` in no particular order. If you add or
	/// remove values whose first key is `k1` to the map while doing this, you'll get undefined
	/// results.
	fn iter_prefix(k1: impl EncodeLike<K1>) -> PrefixIterator<(K2, V)> where
		Self::Hasher2: ReversibleStorageHasher;

	/// Remove all elements from the map with first key `k1` and iterate through them in no
	/// particular order. If you add elements with first key `k1` to the map while doing this,
	/// you'll get undefined results.
	fn drain_prefix(k1: impl EncodeLike<K1>) -> PrefixIterator<(K2, V)> where
		Self::Hasher2: ReversibleStorageHasher;

	/// Iter over all value associated to the first key.
	fn iter_prefix_values<KArg1>(k1: KArg1) -> PrefixIterator<V> where
		KArg1: ?Sized + EncodeLike<K1>;

	/// Iter over all value and decode the first key and the second key.
	fn iter() -> PrefixIterator<(K1, K2, V)> where
		Self::Hasher1: ReversibleStorageHasher,
		Self::Hasher2: ReversibleStorageHasher;

	/// Iter over all value.
	fn iter_values() -> PrefixIterator<V>;
}

/// Iterate over a prefix and decode raw_key and raw_value into `T`.
pub struct PrefixIterator<T> {
	prefix: Vec<u8>,
	previous_key: Vec<u8>,
	/// If true then value are removed while iterating
	drain: bool,
	/// Function that take `(raw_key_without_prefix, raw_value)` and decode `T`.
	/// `raw_key_without_prefix` is the raw storage key without the prefix iterated on.
	closure: fn(&[u8], &[u8]) -> Result<T, codec::Error>,
}

impl<T> Iterator for PrefixIterator<T> {
	type Item = T;

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			let maybe_next = sp_io::storage::next_key(&self.previous_key)
				.filter(|n| n.starts_with(&self.prefix));
			break match maybe_next {
				Some(next) => {
					self.previous_key = next;
					match unhashed::get_raw(&self.previous_key) {
						Some(raw_value) => {
							if self.drain {
								unhashed::kill(&self.previous_key)
							}
							let raw_key_without_prefix = &self.previous_key[self.prefix.len()..];
							match (self.closure)(raw_key_without_prefix, &raw_value[..]) {
								Ok(t) => Some(t),
								Err(e) => {
									crate::debug::error!(
										"(key, value) failed to decode at {:?}: {:?}",
										self.previous_key, e
									);
									continue
								}
							}
						}
						None => {
							crate::debug::error!(
								"next_key returned a key with no value at {:?}",
								self.previous_key
							);
							continue
						}
					}
				}
				None => None,
			}
		}
	}
}
