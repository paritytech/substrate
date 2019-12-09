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

use rstd::{prelude::*, marker::PhantomData};
use codec::{FullCodec, FullEncode, Encode, EncodeAppend, EncodeLike, Decode};
use crate::{traits::Len, hash::{Twox128, StorageHasher}};

pub mod unhashed;
pub mod hashed;
pub mod child;
pub mod generator;

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
	/// This would typically be called inside the module implementation of on_initialize, while
	/// ensuring **no usage of this storage are made before the call to `on_initialize`**. (More
	/// precisely prior initialized modules doesn't make use of this storage).
	fn translate<O: Decode, F: FnOnce(Option<O>) -> Option<T>>(f: F) -> Result<Option<T>, ()>;

	/// Store a value under this key into the provided storage instance.
	fn put<Arg: EncodeLike<T>>(val: Arg);

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

	/// Get the storage key used to fetch a value corresponding to a specific key.
	fn hashed_key_for<KeyArg: EncodeLike<K>>(key: KeyArg) -> Vec<u8>;

	/// Does the value (explicitly) exist in storage?
	fn exists<KeyArg: EncodeLike<K>>(key: KeyArg) -> bool;

	/// Load the value associated with the given key from the map.
	fn get<KeyArg: EncodeLike<K>>(key: KeyArg) -> Self::Query;

	/// Swap the values of two keys.
	fn swap<KeyArg1: EncodeLike<K>, KeyArg2: EncodeLike<K>>(key1: KeyArg1, key2: KeyArg2);

	/// Store a value to be associated with the given key from the map.
	fn insert<KeyArg: EncodeLike<K>, ValArg: EncodeLike<V>>(key: KeyArg, val: ValArg);

	/// Remove the value under a key.
	fn remove<KeyArg: EncodeLike<K>>(key: KeyArg);

	/// Mutate the value under a key.
	fn mutate<KeyArg: EncodeLike<K>, R, F: FnOnce(&mut Self::Query) -> R>(key: KeyArg, f: F) -> R;

	/// Take the value under a key.
	fn take<KeyArg: EncodeLike<K>>(key: KeyArg) -> Self::Query;

	/// Append the given items to the value in the storage.
	///
	/// `V` is required to implement `codec::EncodeAppend`.
	fn append<Items, Item, EncodeLikeItem, KeyArg>(key: KeyArg, items: Items) -> Result<(), &'static str>
	where
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
	fn append_or_insert<Items, Item, EncodeLikeItem, KeyArg>(key: KeyArg, items: Items)
	where
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
	/// Therefore, this function cannot be used as a sign of _existence_. use the `::exists()`
	/// function for this purpose.
	fn decode_len<KeyArg: EncodeLike<K>>(key: KeyArg) -> Result<usize, &'static str>
		where V: codec::DecodeLength + Len;
}

/// A strongly-typed linked map in storage.
///
/// Similar to `StorageMap` but allows to enumerate other elements and doesn't implement append.
///
/// Details on implementation can be found at
/// [`generator::StorageLinkedMap`]
pub trait StorageLinkedMap<K: FullCodec, V: FullCodec> {
	/// The type that get/take return.
	type Query;

	/// The type that iterates over all `(key, value)`.
	type Enumerator: Iterator<Item = (K, V)>;

	/// Does the value (explicitly) exist in storage?
	fn exists<KeyArg: EncodeLike<K>>(key: KeyArg) -> bool;

	/// Load the value associated with the given key from the map.
	fn get<KeyArg: EncodeLike<K>>(key: KeyArg) -> Self::Query;

	/// Swap the values of two keys.
	fn swap<KeyArg1: EncodeLike<K>, KeyArg2: EncodeLike<K>>(key1: KeyArg1, key2: KeyArg2);

	/// Store a value to be associated with the given key from the map.
	fn insert<KeyArg: EncodeLike<K>, ValArg: EncodeLike<V>>(key: KeyArg, val: ValArg);

	/// Remove the value under a key.
	fn remove<KeyArg: EncodeLike<K>>(key: KeyArg);

	/// Mutate the value under a key.
	fn mutate<KeyArg: EncodeLike<K>, R, F: FnOnce(&mut Self::Query) -> R>(key: KeyArg, f: F) -> R;

	/// Take the value under a key.
	fn take<KeyArg: EncodeLike<K>>(key: KeyArg) -> Self::Query;

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
	fn decode_len<KeyArg: EncodeLike<K>>(key: KeyArg) -> Result<usize, &'static str>
		where V: codec::DecodeLength + Len;

	/// Translate the keys and values from some previous `(K2, V2)` to the current type.
	///
	/// `TK` translates keys from the old type, and `TV` translates values.
	///
	/// Returns `Err` if the map could not be interpreted as the old type, and Ok if it could.
	/// The `Err` contains the first key which could not be migrated, or `None` if the
	/// head of the list could not be read.
	///
	/// # Warning
	///
	/// This function must be used with care, before being updated the storage still contains the
	/// old type, thus other calls (such as `get`) will fail at decoding it.
	///
	/// # Usage
	///
	/// This would typically be called inside the module implementation of on_initialize, while
	/// ensuring **no usage of this storage are made before the call to `on_initialize`**. (More
	/// precisely prior initialized modules doesn't make use of this storage).
	fn translate<K2, V2, TK, TV>(translate_key: TK, translate_val: TV) -> Result<(), Option<K2>>
		where K2: FullCodec + Clone, V2: Decode, TK: Fn(K2) -> K, TV: Fn(V2) -> V;
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

	fn hashed_key_for<KArg1, KArg2>(k1: KArg1, k2: KArg2) -> Vec<u8>
	where
		KArg1: EncodeLike<K1>,
		KArg2: EncodeLike<K2>;

	fn exists<KArg1, KArg2>(k1: KArg1, k2: KArg2) -> bool
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
	/// Therefore, this function cannot be used as a sign of _existence_. use the `::exists()`
	/// function for this purpose.
	fn decode_len<KArg1, KArg2>(key1: KArg1, key2: KArg2) -> Result<usize, &'static str>
		where
			KArg1: EncodeLike<K1>,
			KArg2: EncodeLike<K2>,
			V: codec::DecodeLength + Len;
}

/// Iterator for prefixed map.
pub struct PrefixIterator<Value> {
	prefix: Vec<u8>,
	previous_key: Vec<u8>,
	phantom_data: PhantomData<Value>,
}

impl<Value: Decode> Iterator for PrefixIterator<Value> {
	type Item = Value;

	fn next(&mut self) -> Option<Self::Item> {
		match runtime_io::storage::next_key(&self.previous_key) {
			Some(next_key) if next_key.starts_with(&self.prefix[..]) => {
				let value = unhashed::get(&next_key);

				if value.is_none() {
					runtime_print!(
						"ERROR: returned next_key has no value:\nkey is {:?}\nnext_key is {:?}",
						&self.previous_key, &next_key,
					);
				}

				self.previous_key = next_key;

				value
			},
			_ => None,
		}
	}
}

/// Trait for maps that store all its value after a unique prefix.
///
/// By default the final prefix is:
/// ```nocompile
/// Twox128(module_prefix) ++ Twox128(storage_prefix)
/// ```
pub trait StoragePrefixedMap<Value: FullCodec> {

	/// Module prefix. Used for generating final key.
	fn module_prefix() -> &'static [u8];

	/// Storage prefix. Used for generating final key.
	fn storage_prefix() -> &'static [u8];

	fn final_prefix() -> [u8; 32] {
		let mut final_key = [0u8; 32];
		final_key[0..16].copy_from_slice(&Twox128::hash(Self::module_prefix()));
		final_key[16..32].copy_from_slice(&Twox128::hash(Self::storage_prefix()));
		final_key
	}

	fn remove_all() {
		runtime_io::storage::clear_prefix(&Self::final_prefix())
	}

	fn iter() -> PrefixIterator<Value> {
		let prefix = Self::final_prefix();
		PrefixIterator {
			prefix: prefix.to_vec(),
			previous_key: prefix.to_vec(),
			phantom_data: Default::default(),
		}
	}
}

#[cfg(test)]
mod test {
	use primitives::hashing::twox_128;
	use runtime_io::TestExternalities;
	use crate::storage::{unhashed, StoragePrefixedMap};

	#[test]
	fn prefixed_map_works() {
		TestExternalities::default().execute_with(|| {
			struct MyStorage;
			impl StoragePrefixedMap<u64> for MyStorage {
				fn module_prefix() -> &'static [u8] {
					b"MyModule"
				}

				fn storage_prefix() -> &'static [u8] {
					b"MyStorage"
				}
			}

			let key_before = {
				let mut k = MyStorage::final_prefix();
				let last = k.iter_mut().last().unwrap();
				*last = last.checked_sub(1).unwrap();
				k
			};
			let key_after = {
				let mut k = MyStorage::final_prefix();
				let last = k.iter_mut().last().unwrap();
				*last = last.checked_add(1).unwrap();
				k
			};

			unhashed::put(&key_before[..], &32u64);
			unhashed::put(&key_after[..], &33u64);

			let k = [twox_128(b"MyModule"), twox_128(b"MyStorage")].concat();
			assert_eq!(MyStorage::final_prefix().to_vec(), k);

			assert_eq!(MyStorage::iter().collect::<Vec<_>>(), vec![]);

			unhashed::put(&[&k[..], &vec![1][..]].concat(), &1u64);
			unhashed::put(&[&k[..], &vec![1, 1][..]].concat(), &2u64);
			unhashed::put(&[&k[..], &vec![8][..]].concat(), &3u64);
			unhashed::put(&[&k[..], &vec![10][..]].concat(), &4u64);

			assert_eq!(MyStorage::iter().collect::<Vec<_>>(), vec![1, 2, 3, 4]);

			MyStorage::remove_all();

			assert_eq!(MyStorage::iter().collect::<Vec<_>>(), vec![]);
			assert_eq!(unhashed::get(&key_before[..]), Some(32u64));
			assert_eq!(unhashed::get(&key_after[..]), Some(33u64));
		});
	}
}
