// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#[cfg(not(feature = "std"))]
use sp_std::prelude::*;
use sp_std::borrow::Borrow;
use codec::{FullCodec, Decode, Encode, EncodeLike};
use crate::{
	storage::{
		self, unhashed,
		types::{KeyGenerator, KeyHasherGenerator, ReversibleKeyGenerator},
		StorageAppend, PrefixIterator
	},
	Never, hash::{StorageHasher, Twox128},
};

/// Generator for `StorageNMap` used by `decl_storage`.
///
/// By default each key value is stored at:
/// ```nocompile
/// Twox128(module_prefix) ++ Twox128(storage_prefix)
///     ++ Hasher1(encode(key1)) ++ Hasher2(encode(key2)) ++ ... ++ HasherN(encode(keyN))
/// ```
///
/// # Warning
///
/// If the keys are not trusted (e.g. can be set by a user), a cryptographic `hasher` such as
/// `blake2_256` must be used.  Otherwise, other values in storage with the same prefix can
/// be compromised.
pub trait StorageNMap<K: KeyGenerator, V: FullCodec> {
	/// The type that get/take returns.
	type Query;

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
	
	/// Generate a partial key used in top storage.
	fn storage_n_map_partial_key<KG, KArg>(key: (KArg, KG::NextKey)) -> Vec<u8>
	where
		KG: KeyGenerator,
		KArg: EncodeLike<KG::CurrentKey>,
	{
		let module_prefix_hashed = Twox128::hash(Self::module_prefix());
		let storage_prefix_hashed = Twox128::hash(Self::storage_prefix());
		let key_hashed = KG::final_key(&key);

		let mut final_key = Vec::with_capacity(
			module_prefix_hashed.len() + storage_prefix_hashed.len() + key_hashed.len()
		);

		final_key.extend_from_slice(&module_prefix_hashed[..]);
		final_key.extend_from_slice(&storage_prefix_hashed[..]);
		final_key.extend_from_slice(key_hashed.as_ref());

		final_key
	}

	/// Generate the full key used in top storage.
	fn storage_n_map_final_key<KArg: EncodeLike<K::CurrentKey>>(key: &(KArg, K::NextKey)) -> Vec<u8> {
		let module_prefix_hashed = Twox128::hash(Self::module_prefix());
		let storage_prefix_hashed = Twox128::hash(Self::storage_prefix());
		let key_hashed = K::final_key(key);

		let mut final_key = Vec::with_capacity(
			module_prefix_hashed.len() + storage_prefix_hashed.len() + key_hashed.len()
		);

		final_key.extend_from_slice(&module_prefix_hashed[..]);
		final_key.extend_from_slice(&storage_prefix_hashed[..]);
		final_key.extend_from_slice(key_hashed.as_ref());

		final_key
	}
}

impl<K, V, G> storage::StorageNMap<K, V> for G
where
	K: KeyGenerator,
	V: FullCodec,
	G: StorageNMap<K, V>,
{
	type Query = G::Query;

	fn hashed_key_for<KArg: EncodeLike<K::CurrentKey>>(key: (KArg, K::NextKey)) -> Vec<u8> {
		Self::storage_n_map_final_key(&key)
	}

	fn contains_key<KArg: EncodeLike<K::CurrentKey>>(key: (KArg, K::NextKey)) -> bool {
		unhashed::exists(&Self::storage_n_map_final_key(&key))
	}

	fn get<KArg: EncodeLike<K::CurrentKey>>(key: (KArg, K::NextKey)) -> Self::Query {
		G::from_optional_value_to_query(unhashed::get(&Self::storage_n_map_final_key(&key)))
	}

	fn try_get<KArg: EncodeLike<K::CurrentKey>>(key: (KArg, K::NextKey)) -> Result<V, ()> {
		unhashed::get(&Self::storage_n_map_final_key(&key)).ok_or(())
	}

	fn take<KArg: EncodeLike<K::CurrentKey>>(key: (KArg, K::NextKey)) -> Self::Query {
		let final_key = Self::storage_n_map_final_key(&key);

		let value = unhashed::take(&final_key);
		G::from_optional_value_to_query(value)
	}

	fn swap<KArg1, KArg2, KOther>(key1: (KArg1, K::NextKey), key2: (KArg2, KOther::NextKey))
	where
		KOther: KeyGenerator,
		KArg1: EncodeLike<K::CurrentKey>,
		KArg2: EncodeLike<KOther::CurrentKey>,
	{
		let final_x_key = Self::storage_n_map_final_key(&key1);
		// Not really a partial key, but only this function allows us to specify a foreign key generator
		let final_y_key = Self::storage_n_map_partial_key::<KOther, KArg2>(key2);

		let v1 = unhashed::get_raw(&final_x_key);
		if let Some(val) = unhashed::get_raw(&final_y_key) {
			unhashed::put_raw(&final_x_key, &val);
		} else {
			unhashed::kill(&final_x_key);
		}
		if let Some(val) = v1 {
			unhashed::put_raw(&final_y_key, &val);
		} else {
			unhashed::kill(&final_y_key);
		}
	}

	fn insert<KArg, VArg>(key: (KArg, K::NextKey), val: VArg)
	where
		KArg: EncodeLike<K::CurrentKey>,
		VArg: EncodeLike<V>,
	{
		unhashed::put(&Self::storage_n_map_final_key(&key), &val.borrow());
	}

	fn remove<KArg: EncodeLike<K::CurrentKey>>(key: (KArg, K::NextKey)) {
		unhashed::kill(&Self::storage_n_map_final_key(&key));
	}

	fn remove_prefix<KG, KArg>(partial_key: (KArg, KG::NextKey))
	where
		KG: KeyGenerator,
		KArg: ?Sized + EncodeLike<KG::CurrentKey>,
	{
		unhashed::kill_prefix(&Self::storage_n_map_partial_key::<KG, KArg>(partial_key));
	}

	fn iter_prefix_values<KG, KArg>(partial_key: (KArg, KG::NextKey)) -> PrefixIterator<V>
	where
		KG: KeyGenerator,
		KArg: ?Sized + EncodeLike<KG::CurrentKey>,
	{
		let prefix = Self::storage_n_map_partial_key::<KG, KArg>(partial_key);
		PrefixIterator {
			prefix: prefix.clone(),
			previous_key: prefix,
			drain: false,
			closure: |_raw_key, mut raw_value| V::decode(&mut raw_value),
		}
	}

	fn mutate<KArg: EncodeLike<K::CurrentKey>, R, F: FnOnce(&mut Self::Query) -> R>(
		key: (KArg, K::NextKey),
		f: F,
	) -> R {
		Self::try_mutate(key, |v| Ok::<R, Never>(f(v))).expect("`Never` can not be constructed; qed")
	}

	fn try_mutate<KArg: EncodeLike<K::CurrentKey>, R, E, F: FnOnce(&mut Self::Query) -> Result<R, E>>(
		key: (KArg, K::NextKey),
		f: F,
	) -> Result<R, E> {
		let final_key = Self::storage_n_map_final_key(&key);
		let mut val = G::from_optional_value_to_query(unhashed::get(final_key.as_ref()));

		let ret = f(&mut val);
		if ret.is_ok() {
			match G::from_query_to_optional_value(val) {
				Some(ref val) => unhashed::put(final_key.as_ref(), val),
				None => unhashed::kill(final_key.as_ref()),
			}
		}
		ret
	}

	fn mutate_exists<KArg: EncodeLike<K::CurrentKey>, R, F: FnOnce(&mut Option<V>) -> R>(
		key: (KArg, K::NextKey),
		f: F,
	) -> R {
		Self::try_mutate_exists(key, |v| Ok::<R, Never>(f(v))).expect("`Never` can not be constructed; qed")
	}

	fn try_mutate_exists<KArg: EncodeLike<K::CurrentKey>, R, E, F: FnOnce(&mut Option<V>) -> Result<R, E>>(
		key: (KArg, K::NextKey),
		f: F,
	) -> Result<R, E> {
		let final_key = Self::storage_n_map_final_key(&key);
		let mut val = unhashed::get(final_key.as_ref());

		let ret = f(&mut val);
		if ret.is_ok() {
			match val {
				Some(ref val) => unhashed::put(final_key.as_ref(), val),
				None => unhashed::kill(final_key.as_ref()),
			}
		}
		ret
	}

	fn append<Item, EncodeLikeItem, KArg>(key: (KArg, K::NextKey), item: EncodeLikeItem)
	where
		KArg: EncodeLike<K::CurrentKey>,
		Item: Encode,
		EncodeLikeItem: EncodeLike<Item>,
		V: StorageAppend<Item>
	{
		let final_key = Self::storage_n_map_final_key(&key);
		sp_io::storage::append(&final_key, item.encode());
	}

	fn migrate_keys<OldHasher, KArg>(key: (KArg, K::NextKey)) -> Option<V>
	where
		OldHasher: KeyHasherGenerator,
		KArg: EncodeLike<K::CurrentKey>
	{
		let old_key = {
			let module_prefix_hashed = Twox128::hash(Self::module_prefix());
			let storage_prefix_hashed = Twox128::hash(Self::storage_prefix());
			let key_hashed = K::final_hash::<KArg, OldHasher>(&key);

			let mut final_key = Vec::with_capacity(
				module_prefix_hashed.len()
					+ storage_prefix_hashed.len()
					+ key_hashed.len()
			);

			final_key.extend_from_slice(&module_prefix_hashed[..]);
			final_key.extend_from_slice(&storage_prefix_hashed[..]);
			final_key.extend_from_slice(key_hashed.as_ref());

			final_key
		};
		unhashed::take(old_key.as_ref()).map(|value| {
			unhashed::put(Self::storage_n_map_final_key(&key).as_ref(), &value);
			value
		})
	}
}

impl<K: ReversibleKeyGenerator, V: FullCodec, G: StorageNMap<K, V>> storage::IterableStorageNMap<K, V> for G {
	type Iterator = PrefixIterator<((K::CurrentKey, K::NextKey), V)>;

	fn iter() -> Self::Iterator {
		let prefix = G::prefix_hash();
		Self::Iterator {
			prefix: prefix.clone(),
			previous_key: prefix,
			drain: false,
			closure: |raw_key_without_prefix, mut raw_value| {
				let final_key = K::decode_final_key(raw_key_without_prefix)?;
				Ok((final_key, V::decode(&mut raw_value)?))
			}
		}
	}

	fn drain() -> Self::Iterator {
		let mut iterator = Self::iter();
		iterator.drain = true;
		iterator
	}

	fn translate<O: Decode, F: FnMut((K::CurrentKey, K::NextKey), O) -> Option<V>>(mut f: F) {
		let prefix = G::prefix_hash();
		let mut previous_key = prefix.clone();
		while let Some(next) = sp_io::storage::next_key(&previous_key)
			.filter(|n| n.starts_with(&prefix))
		{
			previous_key = next;
			let value = match unhashed::get::<O>(&previous_key) {
				Some(value) => value,
				None => {
					log::error!("Invalid translate: fail to decode old value");
					continue
				},
			};
			
			let final_key = match K::decode_final_key(&previous_key[prefix.len()..]) {
				Ok(final_key) => final_key,
				Err(_) => {
					log::error!("Invalid translate: fail to decode key");
					continue
				}
			};

			match f(final_key, value) {
				Some(new) => unhashed::put::<V>(&previous_key, &new),
				None => unhashed::kill(&previous_key),
			}
		}
	}
}
