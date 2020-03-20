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
use codec::{Ref, FullCodec, Decode, Encode, EncodeLike, EncodeAppend};
use crate::{storage::{self, unhashed}, traits::Len};
use crate::hash::{StorageHasher, Twox128, StorageHasherInfo};

/// Generator for `StorageDoubleMap` used by `decl_storage`.
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
pub trait StorageDoubleMap<K1: FullCodec, K2: FullCodec, V: FullCodec> {
	/// The type that get/take returns.
	type Query;

	/// Hasher for the first key.
	type Hasher1: StorageHasher + StorageHasherInfo<K1>;

	/// Hasher for the second key.
	type Hasher2: StorageHasher + StorageHasherInfo<K2>;

	/// Module prefix. Used for generating final key.
	fn module_prefix() -> &'static [u8];

	/// Storage prefix. Used for generating final key.
	fn storage_prefix() -> &'static [u8];

	/// The full prefix; just the hash of `module_prefix` concatenated to the hash of
	/// `storage_prefix`.
	fn prefix_hash() -> Vec<u8> {
		let module_prefix_hashed = Twox128::hash(Self::module_prefix());
		let storage_prefix_hashed = Twox128::hash(Self::storage_prefix());

		let mut result = Vec::with_capacity(
			module_prefix_hashed.len() + storage_prefix_hashed.len()
		);

		result.extend_from_slice(&module_prefix_hashed[..]);
		result.extend_from_slice(&storage_prefix_hashed[..]);

		result
	}

	/// Convert an optional value retrieved from storage to the type queried.
	fn from_optional_value_to_query(v: Option<V>) -> Self::Query;

	/// Convert a query to an optional value into storage.
	fn from_query_to_optional_value(v: Self::Query) -> Option<V>;

	/// Generate the first part of the key used in top storage.
	fn storage_double_map_final_key1<KArg1>(k1: KArg1) -> Vec<u8> where
		KArg1: EncodeLike<K1>,
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
	fn storage_double_map_final_key<KArg1, KArg2>(k1: KArg1, k2: KArg2) -> Vec<u8> where
		KArg1: EncodeLike<K1>,
		KArg2: EncodeLike<K2>,
	{
		let module_prefix_hashed = Twox128::hash(Self::module_prefix());
		let storage_prefix_hashed = Twox128::hash(Self::storage_prefix());
		let key1_hashed = k1.borrow().using_encoded(Self::Hasher1::hash);
		let key2_hashed = k2.borrow().using_encoded(Self::Hasher2::hash);

		let mut final_key = Vec::with_capacity(
			module_prefix_hashed.len()
				+ storage_prefix_hashed.len()
				+ key1_hashed.as_ref().len()
				+ key2_hashed.as_ref().len()
		);

		final_key.extend_from_slice(&module_prefix_hashed[..]);
		final_key.extend_from_slice(&storage_prefix_hashed[..]);
		final_key.extend_from_slice(key1_hashed.as_ref());
		final_key.extend_from_slice(key2_hashed.as_ref());

		final_key
	}
}

impl<K1, K2, V, G> storage::StorageDoubleMap<K1, K2, V> for G where
	K1: FullCodec,
	K2: FullCodec,
	V: FullCodec,
	G: StorageDoubleMap<K1, K2, V>,
{
	type Query = G::Query;
	type Hasher1 = G::Hasher1;
	type Hasher2 = G::Hasher2;

	fn hashed_key_for<KArg1, KArg2>(k1: KArg1, k2: KArg2) -> Vec<u8> where
		KArg1: EncodeLike<K1>,
		KArg2: EncodeLike<K2>,
	{
		Self::storage_double_map_final_key(k1, k2)
	}

	fn contains_key<KArg1, KArg2>(k1: KArg1, k2: KArg2) -> bool where
		KArg1: EncodeLike<K1>,
		KArg2: EncodeLike<K2>,
	{
		unhashed::exists(&Self::storage_double_map_final_key(k1, k2))
	}

	fn get<KArg1, KArg2>(k1: KArg1, k2: KArg2) -> Self::Query where
		KArg1: EncodeLike<K1>,
		KArg2: EncodeLike<K2>,
	{
		G::from_optional_value_to_query(unhashed::get(&Self::storage_double_map_final_key(k1, k2)))
	}

	fn take<KArg1, KArg2>(k1: KArg1, k2: KArg2) -> Self::Query where
		KArg1: EncodeLike<K1>,
		KArg2: EncodeLike<K2>,
	{
		let final_key = Self::storage_double_map_final_key(k1, k2);

		let value = unhashed::take(&final_key);
		G::from_optional_value_to_query(value)
	}

	fn swap<XKArg1, XKArg2, YKArg1, YKArg2>(
		x_k1: XKArg1,
		x_k2: XKArg2,
		y_k1: YKArg1,
		y_k2: YKArg2
	) where
		XKArg1: EncodeLike<K1>,
		XKArg2: EncodeLike<K2>,
		YKArg1: EncodeLike<K1>,
		YKArg2: EncodeLike<K2>
	{
		let final_x_key = Self::storage_double_map_final_key(x_k1, x_k2);
		let final_y_key = Self::storage_double_map_final_key(y_k1, y_k2);

		let v1 = unhashed::get_raw(&final_x_key);
		if let Some(val) = unhashed::get_raw(&final_y_key) {
			unhashed::put_raw(&final_x_key, &val);
		} else {
			unhashed::kill(&final_x_key)
		}
		if let Some(val) = v1 {
			unhashed::put_raw(&final_y_key, &val);
		} else {
			unhashed::kill(&final_y_key)
		}
	}

	fn insert<KArg1, KArg2, VArg>(k1: KArg1, k2: KArg2, val: VArg) where
		KArg1: EncodeLike<K1>,
		KArg2: EncodeLike<K2>,
		VArg: EncodeLike<V>,
	{
		unhashed::put(&Self::storage_double_map_final_key(k1, k2), &val.borrow())
	}

	fn remove<KArg1, KArg2>(k1: KArg1, k2: KArg2) where
		KArg1: EncodeLike<K1>,
		KArg2: EncodeLike<K2>,
	{
		unhashed::kill(&Self::storage_double_map_final_key(k1, k2))
	}

	fn remove_prefix<KArg1>(k1: KArg1) where KArg1: EncodeLike<K1> {
		unhashed::kill_prefix(Self::storage_double_map_final_key1(k1).as_ref())
	}

	fn remove_all() {
		sp_io::storage::clear_prefix(&Self::prefix_hash())
	}

	fn iter_prefix_value<KArg1>(k1: KArg1) -> storage::PrefixIterator<V> where
		KArg1: ?Sized + EncodeLike<K1>
	{
		let prefix = Self::storage_double_map_final_key1(k1);
		storage::PrefixIterator {
			prefix: prefix.clone(),
			previous_key: prefix,
			drain: false,
			closure: |_raw_key, mut raw_value| V::decode(&mut raw_value),
		}
	}

	fn mutate<KArg1, KArg2, R, F>(k1: KArg1, k2: KArg2, f: F) -> R where
		KArg1: EncodeLike<K1>,
		KArg2: EncodeLike<K2>,
		F: FnOnce(&mut Self::Query) -> R,
	{
		let final_key = Self::storage_double_map_final_key(k1, k2);
		let mut val = G::from_optional_value_to_query(unhashed::get(final_key.as_ref()));

		let ret = f(&mut val);
		match G::from_query_to_optional_value(val) {
			Some(ref val) => unhashed::put(final_key.as_ref(), val),
			None => unhashed::kill(final_key.as_ref()),
		}
		ret
	}

	fn append<Items, Item, EncodeLikeItem, KArg1, KArg2>(
		k1: KArg1,
		k2: KArg2,
		items: Items,
	) -> Result<(), &'static str> where
		KArg1: EncodeLike<K1>,
		KArg2: EncodeLike<K2>,
		Item: Encode,
		EncodeLikeItem: EncodeLike<Item>,
		V: EncodeAppend<Item=Item>,
		Items: IntoIterator<Item=EncodeLikeItem>,
		Items::IntoIter: ExactSizeIterator
	{
		let final_key = Self::storage_double_map_final_key(k1, k2);

		let encoded_value = unhashed::get_raw(&final_key)
			.unwrap_or_else(|| {
				match G::from_query_to_optional_value(G::from_optional_value_to_query(None)) {
					Some(value) => value.encode(),
					None => Vec::new(),
				}
			});

		let new_val = V::append_or_new(
			encoded_value,
			items,
		).map_err(|_| "Could not append given item")?;
		unhashed::put_raw(&final_key, &new_val);

		Ok(())
	}

	fn append_or_insert<Items, Item, EncodeLikeItem, KArg1, KArg2>(
		k1: KArg1,
		k2: KArg2,
		items: Items,
	) where
		KArg1: EncodeLike<K1>,
		KArg2: EncodeLike<K2>,
		Item: Encode,
		EncodeLikeItem: EncodeLike<Item>,
		V: EncodeAppend<Item=Item>,
		Items: IntoIterator<Item=EncodeLikeItem> + Clone + EncodeLike<V>,
		Items::IntoIter: ExactSizeIterator
	{
		Self::append(Ref::from(&k1), Ref::from(&k2), items.clone())
			.unwrap_or_else(|_| Self::insert(k1, k2, items));
	}

	fn decode_len<KArg1, KArg2>(key1: KArg1, key2: KArg2) -> Result<usize, &'static str> where
		KArg1: EncodeLike<K1>,
		KArg2: EncodeLike<K2>,
		V: codec::DecodeLength + Len,
	{
		let final_key = Self::storage_double_map_final_key(key1, key2);
		if let Some(v) = unhashed::get_raw(&final_key) {
			<V as codec::DecodeLength>::len(&v).map_err(|e| e.what())
		} else {
			let len = G::from_query_to_optional_value(G::from_optional_value_to_query(None))
				.map(|v| v.len())
				.unwrap_or(0);

			Ok(len)
		}
	}

	fn migrate_keys<
		OldHasher1: StorageHasher,
		OldHasher2: StorageHasher,
		KeyArg1: EncodeLike<K1>,
		KeyArg2: EncodeLike<K2>,
	>(key1: KeyArg1, key2: KeyArg2) -> Option<V> {
		let old_key = {
			let module_prefix_hashed = Twox128::hash(Self::module_prefix());
			let storage_prefix_hashed = Twox128::hash(Self::storage_prefix());
			let key1_hashed = key1.borrow().using_encoded(OldHasher1::hash);
			let key2_hashed = key2.borrow().using_encoded(OldHasher2::hash);

			let mut final_key = Vec::with_capacity(
				module_prefix_hashed.len()
					+ storage_prefix_hashed.len()
					+ key1_hashed.as_ref().len()
					+ key2_hashed.as_ref().len()
			);

			final_key.extend_from_slice(&module_prefix_hashed[..]);
			final_key.extend_from_slice(&storage_prefix_hashed[..]);
			final_key.extend_from_slice(key1_hashed.as_ref());
			final_key.extend_from_slice(key2_hashed.as_ref());

			final_key
		};
		unhashed::take(old_key.as_ref()).map(|value| {
			unhashed::put(Self::storage_double_map_final_key(key1, key2).as_ref(), &value);
			value
		})
	}

	fn iter_prefix_key2_value(k1: impl EncodeLike<K1>) -> storage::PrefixIterator<(K2, V)> where
		Self::Hasher2: StorageHasherInfo<K2, Info=K2>,
	{
		let prefix = G::storage_double_map_final_key1(k1);
		storage::PrefixIterator {
			prefix: prefix.clone(),
			previous_key: prefix,
			drain: false,
			closure: |raw_key, raw_value| {
				from_raw_to_key_info_value::<_, _, _, G>(raw_key, raw_value)
					.map(|(_k1, k2, v)| (k2, v))
			}
		}
	}

	fn drain_prefix_key2_value(k1: impl EncodeLike<K1>) -> storage::PrefixIterator<(K2, V)> where
		Self::Hasher2: StorageHasherInfo<K2, Info=K2>,
	{
		let prefix = G::storage_double_map_final_key1(k1);
		storage::PrefixIterator {
			prefix: prefix.clone(),
			previous_key: prefix,
			drain: true,
			closure: |raw_key, raw_value| {
				from_raw_to_key_info_value::<_, _, _, G>(raw_key, raw_value)
					.map(|(_k1, k2, v)| (k2, v))
			}
		}
	}

	fn iter_key1_value() -> storage::PrefixIterator<(K1, V)> where
		Self::Hasher1: StorageHasherInfo<K1, Info=K1>,
	{
		let prefix = G::prefix_hash();
		storage::PrefixIterator {
			prefix: prefix.clone(),
			previous_key: prefix,
			drain: false,
			closure: |raw_key, raw_value| {
				from_raw_to_key_info_value::<_, _, _, G>(raw_key, raw_value)
					.map(|(k1, _k2, v)| (k1, v))
			}
		}
	}

	fn iter_key2_value() -> storage::PrefixIterator<(K2, V)> where
		Self::Hasher2: StorageHasherInfo<K2, Info=K2>,
	{
		let prefix = G::prefix_hash();
		storage::PrefixIterator {
			prefix: prefix.clone(),
			previous_key: prefix,
			drain: false,
			closure: |raw_key, raw_value| {
				from_raw_to_key_info_value::<_, _, _, G>(raw_key, raw_value)
					.map(|(_k1, k2, v)| (k2, v))
			}
		}
	}

	fn iter_key1_key2_value() -> storage::PrefixIterator<(K1, K2, V)> where
		Self::Hasher1: StorageHasherInfo<K1, Info=K1>,
		Self::Hasher2: StorageHasherInfo<K2, Info=K2>,
	{
		let prefix = G::prefix_hash();
		storage::PrefixIterator {
			prefix: prefix.clone(),
			previous_key: prefix,
			drain: false,
			closure: |raw_key, raw_value| {
				from_raw_to_key_info_value::<_, _, _, G>(raw_key, raw_value)
					.map(|(k1, k2, v)| (k1, k2, v))
			}
		}
	}

	fn iter_value() -> storage::PrefixIterator<V> {
		let prefix = G::prefix_hash();
		storage::PrefixIterator {
			prefix: prefix.clone(),
			previous_key: prefix,
			drain: false,
			closure: |_raw_key, mut raw_value| V::decode(&mut raw_value),
		}
	}

	fn translate<O: Decode, F: Fn(O) -> Option<V>>(f: F) {
		let prefix = G::prefix_hash();
		let mut previous_key = prefix.clone();
		loop {
			match sp_io::storage::next_key(&previous_key).filter(|n| n.starts_with(&prefix)) {
				Some(next) => {
					previous_key = next;
					let maybe_value = unhashed::get::<O>(&previous_key);
					match maybe_value {
						Some(value) => match f(value) {
							Some(new) => unhashed::put::<V>(&previous_key, &new),
							None => unhashed::kill(&previous_key),
						},
						None => {
							crate::debug::error!(
								"next_key returned a key which failed to decode at {:?}",
								previous_key
							);
							continue
						}
					}
				}
				None => return,
			}
		}
	}
}

fn from_raw_to_key_info_value<K1, K2, V, G>(
	raw_key: &[u8],
	mut raw_value: &[u8]
) ->
	Result<
		(
			<G::Hasher1 as StorageHasherInfo<K1>>::Info,
			<G::Hasher2 as StorageHasherInfo<K2>>::Info,
			V,
		),
		codec::Error,
	>
where
	K1: FullCodec,
	K2: FullCodec,
	V: FullCodec,
	G: StorageDoubleMap<K1, K2, V>,
{
	let prefix_hash = G::prefix_hash();
	if raw_key.len() < prefix_hash.len() {
		return Err("Input length is too small".into())
	}

	let mut decode_key_input = &raw_key[prefix_hash.len()..];
	let key1 = G::Hasher1::decode_hash_and_then_info(&mut decode_key_input)?;
	let key2 = G::Hasher2::decode_hash_and_then_info(&mut decode_key_input)?;
	let value = V::decode(&mut raw_value)?;

	Ok((key1, key2, value))
}

#[cfg(test)]
mod test {
	use sp_io::TestExternalities;
	use crate::storage::{self, StorageDoubleMap};
	use crate::hash::Twox128;

	#[test]
	fn iter_prefix_works() {
		TestExternalities::default().execute_with(|| {
			struct MyStorage;
			impl storage::generator::StorageDoubleMap<u64, u64, u64> for MyStorage {
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

			assert_eq!(MyStorage::iter_prefix_value(1).collect::<Vec<_>>(), vec![7, 8]);
			assert_eq!(MyStorage::iter_prefix_value(2).collect::<Vec<_>>(), vec![10, 9]);
		});
	}
}
