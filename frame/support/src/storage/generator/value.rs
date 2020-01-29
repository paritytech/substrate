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
use codec::{FullCodec, Encode, EncodeAppend, EncodeLike, Decode};
use crate::{storage::top, hash::{Twox128, StorageHasher}, traits::Len};

/// A trait for working with macro-generated storage values under the substrate storage API.
///
/// Store a value at some key in the top trie.
///
/// By default value is stored at:
/// ```nocompile
/// Twox128(module_prefix) ++ Twox128(storage_prefix)
/// ```
pub trait StorageValue {
	/// The type of the value stored in storage.
	type Value: FullCodec;

	/// The type that get/take returns.
	type Query;

	/// Module prefix. Used for generating final key.
	fn module_prefix() -> &'static [u8];

	/// Storage prefix. Used for generating final key.
	fn storage_prefix() -> &'static [u8];

	/// Convert an optional value retrieved from storage to the type queried.
	fn from_optional_value_to_query(v: Option<Self::Value>) -> Self::Query;

	/// Convert a query to an optional value into storage.
	fn from_query_to_optional_value(v: Self::Query) -> Option<Self::Value>;

	/// Generate the full key used in top storage.
	fn top_trie_key() -> [u8; 32] {
		let mut final_key = [0u8; 32];
		final_key[0..16].copy_from_slice(&Twox128::hash(Self::module_prefix()));
		final_key[16..32].copy_from_slice(&Twox128::hash(Self::storage_prefix()));
		final_key
	}

	/// Does the value (explicitly) exist in storage?
	fn exists() -> bool {
		top::exists(&Self::top_trie_key())
	}

	/// Load the value from the provided storage instance.
	fn get() -> Self::Query {
		let value = top::get(&Self::top_trie_key());
		Self::from_optional_value_to_query(value)
	}

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
	fn translate<O: Decode, F: FnOnce(Option<O>) -> Option<Self::Value>>(f: F) -> Result<Option<Self::Value>, ()> {
		let key = Self::top_trie_key();

		// attempt to get the length directly.
		let maybe_old = match top::get_raw(&key) {
			Some(old_data) => Some(O::decode(&mut &old_data[..]).map_err(|_| ())?),
			None => None,
		};
		let maybe_new = f(maybe_old);
		if let Some(new) = maybe_new.as_ref() {
			new.using_encoded(|d| top::put_raw(&key, d));
		} else {
			top::kill(&key);
		}
		Ok(maybe_new)
	}

	/// Store a value under this key into the provided storage instance.
	fn put<Arg: EncodeLike<Self::Value>>(val: Arg) {
		top::put(&Self::top_trie_key(), &val)
	}

	/// Clear the storage value.
	fn kill() {
		top::kill(&Self::top_trie_key())
	}

	/// Mutate the value
	fn mutate<R, F: FnOnce(&mut Self::Query) -> R>(f: F) -> R {
		let mut val = Self::get();

		let ret = f(&mut val);
		match Self::from_query_to_optional_value(val) {
			Some(ref val) => Self::put(val),
			None => Self::kill(),
		}
		ret
	}

	/// Take a value from storage, removing it afterwards.
	fn take() -> Self::Query {
		let key = Self::top_trie_key();
		let value = top::get(&key);
		if value.is_some() {
			top::kill(&key)
		}
		Self::from_optional_value_to_query(value)
	}

	/// Append the given items to the value in the storage.
	///
	/// `Self::Value` is required to implement `codec::EncodeAppend`.
	fn append<Items, Item, EncodeLikeItem>(items: Items) -> Result<(), &'static str>
	where
		Item: Encode,
		EncodeLikeItem: EncodeLike<Item>,
		Self::Value: EncodeAppend<Item=Item>,
		Items: IntoIterator<Item=EncodeLikeItem>,
		Items::IntoIter: ExactSizeIterator,
	{
		let key = Self::top_trie_key();
		let encoded_value = top::get_raw(&key)
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
		top::put_raw(&key, &new_val);
		Ok(())
	}

	/// `Self::Value` is required to implement `codec::EncodeAppend`.
	///
	/// Append the given items to the value in the storage.
	///
	/// `Self::Value` is required to implement `Codec::EncodeAppend`.
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
		Self::Value: EncodeAppend<Item=Item>,
		Items: IntoIterator<Item=EncodeLikeItem> + Clone + EncodeLike<Self::Value>,
		Items::IntoIter: ExactSizeIterator
	{
		Self::append(items.clone()).unwrap_or_else(|_| Self::put(items));
	}

	/// Read the length of the value in a fast way, without decoding the entire value.
	///
	/// `Self::Value` is required to implement `Codec::DecodeLength`.
	///
	/// Note that `0` is returned as the default value if no encoded value exists at the given key.
	/// Therefore, this function cannot be used as a sign of _existence_. use the `::exists()`
	/// function for this purpose.
	fn decode_len() -> Result<usize, &'static str> where Self::Value: codec::DecodeLength, Self::Value: Len {
		let key = Self::top_trie_key();

		// attempt to get the length directly.
		if let Some(k) = top::get_raw(&key) {
			<Self::Value as codec::DecodeLength>::len(&k).map_err(|e| e.what())
		} else {
			let len = Self::from_query_to_optional_value(Self::from_optional_value_to_query(None))
				.map(|v| v.len())
				.unwrap_or(0);

			Ok(len)
		}
	}
}
