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

#[cfg(not(feature = "std"))]
use sp_std::prelude::*;
use sp_std::borrow::Borrow;
use codec::{FullCodec, FullEncode, Encode, EncodeLike, Ref, EncodeAppend};
use crate::{storage::top, hash::{StorageHasher, Twox128}, traits::Len};

/// A strongly-typed map in storage.
///
/// By default each key value is stored at:
/// ```nocompile
/// Twox128(module_prefix) ++ Twox128(storage_prefix) ++ Hasher(encode(key))
/// ```
///
/// # Warning
///
/// If the keys are not trusted (e.g. can be set by a user), a cryptographic `hasher` such as
/// `blake2_256` must be used.  Otherwise, other values in storage can be compromised.
pub trait StorageMap<K: FullEncode, V: FullCodec> {
	/// The type that get/take returns.
	type Query;

	/// Hasher. Used for generating final key.
	type Hasher: StorageHasher;

	/// Module prefix. Used for generating final key.
	fn module_prefix() -> &'static [u8];

	/// Storage prefix. Used for generating final key.
	fn storage_prefix() -> &'static [u8];

	/// Convert an optional value retrieved from storage to the type queried.
	fn from_optional_value_to_query(v: Option<V>) -> Self::Query;

	/// Convert a query to an optional value into storage.
	fn from_query_to_optional_value(v: Self::Query) -> Option<V>;

	/// Generate the full key used in top storage.
	fn storage_map_final_key<KeyArg>(key: KeyArg) -> Vec<u8>
	where
		KeyArg: EncodeLike<K>,
	{
		let module_prefix_hashed = Twox128::hash(Self::module_prefix());
		let storage_prefix_hashed = Twox128::hash(Self::storage_prefix());
		let key_hashed = key.borrow().using_encoded(Self::Hasher::hash);

		let mut final_key = Vec::with_capacity(
			module_prefix_hashed.len() + storage_prefix_hashed.len() + key_hashed.as_ref().len()
		);

		final_key.extend_from_slice(&module_prefix_hashed[..]);
		final_key.extend_from_slice(&storage_prefix_hashed[..]);
		final_key.extend_from_slice(key_hashed.as_ref());

		final_key
	}

	/// Swap the values of two keys.
	fn swap<KeyArg1: EncodeLike<K>, KeyArg2: EncodeLike<K>>(key1: KeyArg1, key2: KeyArg2) {
		let k1 = Self::storage_map_final_key(key1);
		let k2 = Self::storage_map_final_key(key2);

		let v1 = top::get_raw(k1.as_ref());
		if let Some(val) = top::get_raw(k2.as_ref()) {
			top::put_raw(k1.as_ref(), &val);
		} else {
			top::kill(k1.as_ref())
		}
		if let Some(val) = v1 {
			top::put_raw(k2.as_ref(), &val);
		} else {
			top::kill(k2.as_ref())
		}
	}

	/// Does the value (explicitly) exist in storage?
	fn exists<KeyArg: EncodeLike<K>>(key: KeyArg) -> bool {
		top::exists(Self::storage_map_final_key(key).as_ref())
	}

	/// Load the value associated with the given key from the map.
	fn get<KeyArg: EncodeLike<K>>(key: KeyArg) -> Self::Query {
		Self::from_optional_value_to_query(top::get(Self::storage_map_final_key(key).as_ref()))
	}

	/// Store a value to be associated with the given key from the map.
	fn insert<KeyArg: EncodeLike<K>, ValArg: EncodeLike<V>>(key: KeyArg, val: ValArg) {
		top::put(Self::storage_map_final_key(key).as_ref(), &val.borrow())
	}

	/// Remove the value under a key.
	fn remove<KeyArg: EncodeLike<K>>(key: KeyArg) {
		top::kill(Self::storage_map_final_key(key).as_ref())
	}

	/// Mutate the value under a key.
	fn mutate<KeyArg: EncodeLike<K>, R, F: FnOnce(&mut Self::Query) -> R>(key: KeyArg, f: F) -> R {
		let final_key = Self::storage_map_final_key(key);
		let mut val = Self::from_optional_value_to_query(top::get(final_key.as_ref()));

		let ret = f(&mut val);
		match Self::from_query_to_optional_value(val) {
			Some(ref val) => top::put(final_key.as_ref(), &val.borrow()),
			None => top::kill(final_key.as_ref()),
		}
		ret
	}

	/// Take the value under a key.
	fn take<KeyArg: EncodeLike<K>>(key: KeyArg) -> Self::Query {
		let key = Self::storage_map_final_key(key);
		let value = top::take(key.as_ref());
		Self::from_optional_value_to_query(value)
	}

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
		Items::IntoIter: ExactSizeIterator,
	{
		let key = Self::storage_map_final_key(key);
		let encoded_value = top::get_raw(key.as_ref())
			.unwrap_or_else(|| {
				match Self::from_query_to_optional_value(Self::from_optional_value_to_query(None)) {
					Some(value) => value.encode(),
					None => Vec::new(),
				}
			});

		let new_val = V::append_or_new(
			encoded_value,
			items,
		).map_err(|_| "Could not append given item")?;
		top::put_raw(key.as_ref(), &new_val);
		Ok(())
	}

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
		Items::IntoIter: ExactSizeIterator,
	{
		Self::append(Ref::from(&key), items.clone())
			.unwrap_or_else(|_| Self::insert(key, items));
	}

	/// Read the length of the value in a fast way, without decoding the entire value.
	///
	/// `T` is required to implement `Codec::DecodeLength`.
	///
	/// Note that `0` is returned as the default value if no encoded value exists at the given key.
	/// Therefore, this function cannot be used as a sign of _existence_. use the `::exists()`
	/// function for this purpose.
	fn decode_len<KeyArg: EncodeLike<K>>(key: KeyArg) -> Result<usize, &'static str>
		where V: codec::DecodeLength + Len
	{
		let key = Self::storage_map_final_key(key);
		if let Some(v) = top::get_raw(key.as_ref()) {
			<V as codec::DecodeLength>::len(&v).map_err(|e| e.what())
		} else {
			let len = Self::from_query_to_optional_value(Self::from_optional_value_to_query(None))
				.map(|v| v.len())
				.unwrap_or(0);

			Ok(len)
		}
	}
}
