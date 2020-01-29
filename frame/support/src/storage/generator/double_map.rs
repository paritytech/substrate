// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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

use sp_std::prelude::*;
use sp_std::borrow::Borrow;
use codec::{Ref, FullCodec, FullEncode, Encode, EncodeLike, EncodeAppend};
use crate::{storage::{top, generator::PrefixIterator}, hash::{StorageHasher, Twox128}, traits::Len};

/// An implementation of a map with a two keys.
///
/// It provides an important ability to efficiently remove all entries
/// that have a common first key.
///
/// # Mapping of keys to a storage path
///
/// The storage key (i.e. the key under which the `Value` will be stored) is created from two parts.
/// The first part is a hash of a concatenation of the `key1_prefix` and `Key1`. And the second part
/// is a hash of a `Key2`.
///
/// Thus value for (key1, key2) is stored at:
/// ```nocompile
/// Twox128(module_prefix) ++ Twox128(storage_prefix) ++ Hasher1(encode(key1)) ++ Hasher2(encode(key2))
/// ```
///
/// # Warning
///
/// If the key1s are not trusted (e.g. can be set by a user), a cryptographic `hasher` such as
/// `blake2_256` must be used for Hasher1. Otherwise, other values in storage can be compromised.
/// If the key2s are not trusted (e.g. can be set by a user), a cryptographic `hasher` such as
/// `blake2_256` must be used for Hasher2. Otherwise, other items in storage with the same first
/// key can be compromised.
pub trait StorageDoubleMap {
	/// The type of the first key.
	type Key1: FullEncode;

	/// The type of the second key.
	type Key2: FullEncode;

	/// The type of the value stored in storage.
	type Value: FullCodec;

	/// The type that get/take returns.
	type Query;

	/// Hasher for the first key.
	type Hasher1: StorageHasher;

	/// Hasher for the second key.
	type Hasher2: StorageHasher;

	/// Module prefix. Used for generating final key.
	fn module_prefix() -> &'static [u8];

	/// Storage prefix. Used for generating final key.
	fn storage_prefix() -> &'static [u8];

	/// Convert an optional value retrieved from storage to the type queried.
	fn from_optional_value_to_query(v: Option<Self::Value>) -> Self::Query;

	/// Convert a query to an optional value into storage.
	fn from_query_to_optional_value(v: Self::Query) -> Option<Self::Value>;

	/// Generate the first part of the key used in top storage.
	fn top_trie_key1_prefix<KArg1>(k1: KArg1) -> Vec<u8>
	where
		KArg1: EncodeLike<Self::Key1>,
	{
		let module_prefix_hashed = Twox128::hash(Self::module_prefix());
		let storage_prefix_hashed = Twox128::hash(Self::storage_prefix());
		let key_hashed = k1.borrow().using_encoded(Self::Hasher1::hash);

		let mut final_key = Vec::with_capacity(
			module_prefix_hashed.len() + storage_prefix_hashed.len() + key_hashed.as_ref().len()
		);

		final_key.extend_from_slice(&module_prefix_hashed[..]);
		final_key.extend_from_slice(&storage_prefix_hashed[..]);
		final_key.extend_from_slice(key_hashed.as_ref());

		final_key
	}

	/// Generate the full key used in top storage.
	fn top_trie_key<KArg1, KArg2>(k1: KArg1, k2: KArg2) -> Vec<u8>
	where
		KArg1: EncodeLike<Self::Key1>,
		KArg2: EncodeLike<Self::Key2>,
	{
		let mut final_key = Self::top_trie_key1_prefix(k1);
		final_key.extend_from_slice(k2.using_encoded(Self::Hasher2::hash).as_ref());
		final_key
	}

	fn exists<KArg1, KArg2>(k1: KArg1, k2: KArg2) -> bool
	where
		KArg1: EncodeLike<Self::Key1>,
		KArg2: EncodeLike<Self::Key2>,
	{
		top::exists(&Self::top_trie_key(k1, k2))
	}

	fn get<KArg1, KArg2>(k1: KArg1, k2: KArg2) -> Self::Query
	where
		KArg1: EncodeLike<Self::Key1>,
		KArg2: EncodeLike<Self::Key2>,
	{
		Self::from_optional_value_to_query(top::get(&Self::top_trie_key(k1, k2)))
	}

	fn take<KArg1, KArg2>(k1: KArg1, k2: KArg2) -> Self::Query
	where
		KArg1: EncodeLike<Self::Key1>,
		KArg2: EncodeLike<Self::Key2>,
	{
		let final_key = Self::top_trie_key(k1, k2);

		let value = top::take(&final_key);
		Self::from_optional_value_to_query(value)
	}

	/// Swap the values of two key-pairs.
	fn swap<XKArg1, XKArg2, YKArg1, YKArg2>(x_k1: XKArg1, x_k2: XKArg2, y_k1: YKArg1, y_k2: YKArg2)
	where
		XKArg1: EncodeLike<Self::Key1>,
		XKArg2: EncodeLike<Self::Key2>,
		YKArg1: EncodeLike<Self::Key1>,
		YKArg2: EncodeLike<Self::Key2>
	{
		let final_x_key = Self::top_trie_key(x_k1, x_k2);
		let final_y_key = Self::top_trie_key(y_k1, y_k2);

		let v1 = top::get_raw(&final_x_key);
		if let Some(val) = top::get_raw(&final_y_key) {
			top::put_raw(&final_x_key, &val);
		} else {
			top::kill(&final_x_key)
		}
		if let Some(val) = v1 {
			top::put_raw(&final_y_key, &val);
		} else {
			top::kill(&final_y_key)
		}
	}

	fn insert<KArg1, KArg2, VArg>(k1: KArg1, k2: KArg2, val: VArg)
	where
		KArg1: EncodeLike<Self::Key1>,
		KArg2: EncodeLike<Self::Key2>,
		VArg: EncodeLike<Self::Value>,
	{
		top::put(&Self::top_trie_key(k1, k2), &val.borrow())
	}

	fn remove<KArg1, KArg2>(k1: KArg1, k2: KArg2)
	where
		KArg1: EncodeLike<Self::Key1>,
		KArg2: EncodeLike<Self::Key2>,
	{
		top::kill(&Self::top_trie_key(k1, k2))
	}

	fn remove_prefix<KArg1>(k1: KArg1) where KArg1: EncodeLike<Self::Key1> {
		top::kill_prefix(Self::top_trie_key1_prefix(k1).as_ref())
	}

	fn iter_prefix<KArg1>(k1: KArg1) -> PrefixIterator<Self::Value>
		where KArg1: ?Sized + EncodeLike<Self::Key1>
	{
		let prefix = Self::top_trie_key1_prefix(k1);
		PrefixIterator::<Self::Value> {
			prefix: prefix.clone(),
			previous_key: prefix,
			phantom_data: Default::default(),
		}
	}

	fn mutate<KArg1, KArg2, R, F>(k1: KArg1, k2: KArg2, f: F) -> R
	where
		KArg1: EncodeLike<Self::Key1>,
		KArg2: EncodeLike<Self::Key2>,
		F: FnOnce(&mut Self::Query) -> R,
	{
		let final_key = Self::top_trie_key(k1, k2);
		let mut val = Self::from_optional_value_to_query(top::get(final_key.as_ref()));

		let ret = f(&mut val);
		match Self::from_query_to_optional_value(val) {
			Some(ref val) => top::put(final_key.as_ref(), val),
			None => top::kill(final_key.as_ref()),
		}
		ret
	}

	fn append<Items, Item, EncodeLikeItem, KArg1, KArg2>(
		k1: KArg1,
		k2: KArg2,
		items: Items,
	) -> Result<(), &'static str>
	where
		KArg1: EncodeLike<Self::Key1>,
		KArg2: EncodeLike<Self::Key2>,
		Item: Encode,
		EncodeLikeItem: EncodeLike<Item>,
		Self::Value: EncodeAppend<Item=Item>,
		Items: IntoIterator<Item=EncodeLikeItem>,
		Items::IntoIter: ExactSizeIterator
	{
		let final_key = Self::top_trie_key(k1, k2);

		let encoded_value = top::get_raw(&final_key)
			.unwrap_or_else(|| {
				match Self::from_query_to_optional_value(Self::from_optional_value_to_query(None)) {
					Some(value) => value.encode(),
					None => Vec::new(),
				}
			});

		let new_val = Self::Value::append_or_new(
			encoded_value,
			items,
		).map_err(|_| "Could not append given item")?;
		top::put_raw(&final_key, &new_val);

		Ok(())
	}

	fn append_or_insert<Items, Item, EncodeLikeItem, KArg1, KArg2>(
		k1: KArg1,
		k2: KArg2,
		items: Items,
	)
	where
		KArg1: EncodeLike<Self::Key1>,
		KArg2: EncodeLike<Self::Key2>,
		Item: Encode,
		EncodeLikeItem: EncodeLike<Item>,
		Self::Value: EncodeAppend<Item=Item>,
		Items: IntoIterator<Item=EncodeLikeItem> + Clone + EncodeLike<Self::Value>,
		Items::IntoIter: ExactSizeIterator
	{
		Self::append(Ref::from(&k1), Ref::from(&k2), items.clone())
			.unwrap_or_else(|_| Self::insert(k1, k2, items));
	}

	/// Read the length of the value in a fast way, without decoding the entire value.
	///
	/// `Self::Value` is required to implement `Codec::DecodeLength`.
	///
	/// Note that `0` is returned as the default value if no encoded value exists at the given key.
	/// Therefore, this function cannot be used as a sign of _existence_. use the `::exists()`
	/// function for this purpose.
	fn decode_len<KArg1, KArg2>(key1: KArg1, key2: KArg2) -> Result<usize, &'static str>
		where KArg1: EncodeLike<Self::Key1>,
		      KArg2: EncodeLike<Self::Key2>,
		      Self::Value: codec::DecodeLength + Len,
	{
		let final_key = Self::top_trie_key(key1, key2);
		if let Some(v) = top::get_raw(&final_key) {
			<Self::Value as codec::DecodeLength>::len(&v).map_err(|e| e.what())
		} else {
			let len = Self::from_query_to_optional_value(Self::from_optional_value_to_query(None))
				.map(|v| v.len())
				.unwrap_or(0);

			Ok(len)
		}
	}
}

#[cfg(test)]
mod test {
	use sp_io::TestExternalities;
	use crate::{StorageDoubleMap, storage};
	use crate::hash::Twox128;

	#[test]
	fn iter_prefix_works() {
		TestExternalities::default().execute_with(|| {
			struct MyStorage;
			impl storage::generator::StorageDoubleMap for MyStorage {
				type Key1 = u64;
				type Key2 = u64;
				type Value = u64;
				type Query = Option<u64>;
				fn module_prefix() -> &'static [u8] { b"MyModule" }
				fn storage_prefix() -> &'static [u8] { b"MyStorage" }
				type Hasher1 = Twox128;
				type Hasher2 = Twox128;
				fn from_optional_value_to_query(v: Option<u64>) -> Self::Query { v }
				fn from_query_to_optional_value(v: Self::Query) -> Option<u64> { v }
			}

			MyStorage::insert(1, 3, 7);
			MyStorage::insert(1, 4, 8);
			MyStorage::insert(2, 5, 9);
			MyStorage::insert(2, 6, 10);

			assert_eq!(MyStorage::iter_prefix(1).collect::<Vec<_>>(), vec![7, 8]);
			assert_eq!(MyStorage::iter_prefix(2).collect::<Vec<_>>(), vec![10, 9]);
		});
	}
}
