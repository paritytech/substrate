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
use crate::{storage::{self, unhashed}, hash::{Twox128, StorageHasher}, traits::Len};

/// Generator for `StorageValue` used by `decl_storage`.
///
/// By default value is stored at:
/// ```nocompile
/// Twox128(module_prefix) ++ Twox128(storage_prefix)
/// ```
pub trait StorageValue<T: FullCodec> {
	/// The type that get/take returns.
	type Query;

	/// Module prefix. Used for generating final key.
	fn module_prefix() -> &'static [u8];

	/// Storage prefix. Used for generating final key.
	fn storage_prefix() -> &'static [u8];

	/// Convert an optional value retrieved from storage to the type queried.
	fn from_optional_value_to_query(v: Option<T>) -> Self::Query;

	/// Convert a query to an optional value into storage.
	fn from_query_to_optional_value(v: Self::Query) -> Option<T>;

	/// Generate the full key used in top storage.
	fn storage_value_final_key() -> [u8; 32] {
		let mut final_key = [0u8; 32];
		final_key[0..16].copy_from_slice(&Twox128::hash(Self::module_prefix()));
		final_key[16..32].copy_from_slice(&Twox128::hash(Self::storage_prefix()));
		final_key
	}
}

impl<T: FullCodec, G: StorageValue<T>> storage::StorageValue<T> for G {
	type Query = G::Query;

	fn hashed_key() -> [u8; 32] {
		Self::storage_value_final_key()
	}

	fn exists() -> bool {
		unhashed::exists(&Self::storage_value_final_key())
	}

	fn get() -> Self::Query {
		let value = unhashed::get(&Self::storage_value_final_key());
		G::from_optional_value_to_query(value)
	}

	fn try_get() -> Result<T, ()> {
		unhashed::get(&Self::storage_value_final_key()).ok_or(())
	}

	fn translate<O: Decode, F: FnOnce(Option<O>) -> Option<T>>(f: F) -> Result<Option<T>, ()> {
		let key = Self::storage_value_final_key();

		// attempt to get the length directly.
		let maybe_old = match unhashed::get_raw(&key) {
			Some(old_data) => Some(O::decode(&mut &old_data[..]).map_err(|_| ())?),
			None => None,
		};
		let maybe_new = f(maybe_old);
		if let Some(new) = maybe_new.as_ref() {
			new.using_encoded(|d| unhashed::put_raw(&key, d));
		} else {
			unhashed::kill(&key);
		}
		Ok(maybe_new)
	}

	fn put<Arg: EncodeLike<T>>(val: Arg) {
		unhashed::put(&Self::storage_value_final_key(), &val)
	}

	fn set(maybe_val: Self::Query) {
		if let Some(val) = G::from_query_to_optional_value(maybe_val) {
			unhashed::put(&Self::storage_value_final_key(), &val)
		} else {
			unhashed::kill(&Self::storage_value_final_key())
		}
	}

	fn kill() {
		unhashed::kill(&Self::storage_value_final_key())
	}

	fn mutate<R, F: FnOnce(&mut G::Query) -> R>(f: F) -> R {
		let mut val = G::get();

		let ret = f(&mut val);
		match G::from_query_to_optional_value(val) {
			Some(ref val) => G::put(val),
			None => G::kill(),
		}
		ret
	}

	fn take() -> G::Query {
		let key = Self::storage_value_final_key();
		let value = unhashed::get(&key);
		if value.is_some() {
			unhashed::kill(&key)
		}
		G::from_optional_value_to_query(value)
	}

	/// Append the given items to the value in the storage.
	///
	/// `T` is required to implement `codec::EncodeAppend`.
	fn append<Items, Item, EncodeLikeItem>(items: Items) -> Result<(), &'static str>
	where
		Item: Encode,
		EncodeLikeItem: EncodeLike<Item>,
		T: EncodeAppend<Item=Item>,
		Items: IntoIterator<Item=EncodeLikeItem>,
		Items::IntoIter: ExactSizeIterator,
	{
		let key = Self::storage_value_final_key();
		let encoded_value = unhashed::get_raw(&key)
			.unwrap_or_else(|| {
				match G::from_query_to_optional_value(G::from_optional_value_to_query(None)) {
					Some(value) => value.encode(),
					None => Vec::new(),
				}
			});

		let new_val = T::append_or_new(
			encoded_value,
			items,
		).map_err(|_| "Could not append given item")?;
		unhashed::put_raw(&key, &new_val);
		Ok(())
	}

	/// Safely append the given items to the value in the storage. If a codec error occurs, then the
	/// old (presumably corrupt) value is replaced with the given `items`.
	///
	/// `T` is required to implement `codec::EncodeAppend`.
	fn append_or_put<Items, Item, EncodeLikeItem>(items: Items) where
		Item: Encode,
		EncodeLikeItem: EncodeLike<Item>,
		T: EncodeAppend<Item=Item>,
		Items: IntoIterator<Item=EncodeLikeItem> + Clone + EncodeLike<T>,
		Items::IntoIter: ExactSizeIterator
	{
		Self::append(items.clone()).unwrap_or_else(|_| Self::put(items));
	}

	/// Read the length of the value in a fast way, without decoding the entire value.
	///
	/// `T` is required to implement `Codec::DecodeLength`.
	///
	/// Note that `0` is returned as the default value if no encoded value exists at the given key.
	/// Therefore, this function cannot be used as a sign of _existence_. use the `::exists()`
	/// function for this purpose.
	fn decode_len() -> Result<usize, &'static str> where T: codec::DecodeLength, T: Len {
		let key = Self::storage_value_final_key();

		// attempt to get the length directly.
		if let Some(k) = unhashed::get_raw(&key) {
			<T as codec::DecodeLength>::len(&k).map_err(|e| e.what())
		} else {
			let len = G::from_query_to_optional_value(G::from_optional_value_to_query(None))
				.map(|v| v.len())
				.unwrap_or(0);

			Ok(len)
		}
	}
}
