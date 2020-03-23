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
use codec::{FullCodec, Decode, Encode, EncodeLike, Ref, EncodeAppend};
use crate::{storage::{self, unhashed}, traits::Len};
use crate::hash::{StorageHasher, Twox128, ReversibleStorageHasher};

/// Generator for `StorageMap` used by `decl_storage`.
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
pub trait StorageMap<K: FullCodec, V: FullCodec> {
	/// The type that get/take returns.
	type Query;

	/// Hasher. Used for generating final key.
	type Hasher: StorageHasher;

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

	/// Generate the full key used in top storage.
	fn storage_map_final_key<KeyArg>(key: KeyArg) -> Vec<u8> where
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
}

impl<K: FullCodec, V: FullCodec, G: StorageMap<K, V>> storage::StorageMap<K, V> for G {
	type Query = G::Query;
	type Hasher = G::Hasher;

	fn hashed_key_for<KeyArg: EncodeLike<K>>(key: KeyArg) -> Vec<u8> {
		Self::storage_map_final_key(key)
	}

	fn swap<KeyArg1: EncodeLike<K>, KeyArg2: EncodeLike<K>>(key1: KeyArg1, key2: KeyArg2) {
		let k1 = Self::storage_map_final_key(key1);
		let k2 = Self::storage_map_final_key(key2);

		let v1 = unhashed::get_raw(k1.as_ref());
		if let Some(val) = unhashed::get_raw(k2.as_ref()) {
			unhashed::put_raw(k1.as_ref(), &val);
		} else {
			unhashed::kill(k1.as_ref())
		}
		if let Some(val) = v1 {
			unhashed::put_raw(k2.as_ref(), &val);
		} else {
			unhashed::kill(k2.as_ref())
		}
	}

	fn contains_key<KeyArg: EncodeLike<K>>(key: KeyArg) -> bool {
		unhashed::exists(Self::storage_map_final_key(key).as_ref())
	}

	fn get<KeyArg: EncodeLike<K>>(key: KeyArg) -> Self::Query {
		G::from_optional_value_to_query(unhashed::get(Self::storage_map_final_key(key).as_ref()))
	}

	fn insert<KeyArg: EncodeLike<K>, ValArg: EncodeLike<V>>(key: KeyArg, val: ValArg) {
		unhashed::put(Self::storage_map_final_key(key).as_ref(), &val)
	}

	fn remove<KeyArg: EncodeLike<K>>(key: KeyArg) {
		unhashed::kill(Self::storage_map_final_key(key).as_ref())
	}

	fn mutate<KeyArg: EncodeLike<K>, R, F: FnOnce(&mut Self::Query) -> R>(key: KeyArg, f: F) -> R {
		let final_key = Self::storage_map_final_key(key);
		let mut val = G::from_optional_value_to_query(unhashed::get(final_key.as_ref()));

		let ret = f(&mut val);
		match G::from_query_to_optional_value(val) {
			Some(ref val) => unhashed::put(final_key.as_ref(), &val),
			None => unhashed::kill(final_key.as_ref()),
		}
		ret
	}

	fn mutate_exists<KeyArg: EncodeLike<K>, R, F: FnOnce(&mut Option<V>) -> R>(key: KeyArg, f: F) -> R {
		let final_key = Self::storage_map_final_key(key);
		let mut val = unhashed::get(final_key.as_ref());

		let ret = f(&mut val);
		match val {
			Some(ref val) => unhashed::put(final_key.as_ref(), &val),
			None => unhashed::kill(final_key.as_ref()),
		}
		ret
	}

	fn try_mutate<KeyArg: EncodeLike<K>, R, E, F: FnOnce(&mut Self::Query) -> Result<R, E>>(
		key: KeyArg,
		f: F
	) -> Result<R, E> {
		let final_key = Self::storage_map_final_key(key);
		let mut val = G::from_optional_value_to_query(unhashed::get(final_key.as_ref()));

		let ret = f(&mut val);
		if ret.is_ok() {
			match G::from_query_to_optional_value(val) {
				Some(ref val) => unhashed::put(final_key.as_ref(), &val.borrow()),
				None => unhashed::kill(final_key.as_ref()),
			}
		}
		ret
	}

	fn try_mutate_exists<KeyArg: EncodeLike<K>, R, E, F: FnOnce(&mut Option<V>) -> Result<R, E>>(
		key: KeyArg,
		f: F
	) -> Result<R, E> {
		let final_key = Self::storage_map_final_key(key);
		let mut val = unhashed::get(final_key.as_ref());

		let ret = f(&mut val);
		if ret.is_ok() {
			match val {
				Some(ref val) => unhashed::put(final_key.as_ref(), &val.borrow()),
				None => unhashed::kill(final_key.as_ref()),
			}
		}
		ret
	}

	fn take<KeyArg: EncodeLike<K>>(key: KeyArg) -> Self::Query {
		let key = Self::storage_map_final_key(key);
		let value = unhashed::take(key.as_ref());
		G::from_optional_value_to_query(value)
	}

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
		let encoded_value = unhashed::get_raw(key.as_ref())
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
		unhashed::put_raw(key.as_ref(), &new_val);
		Ok(())
	}

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

	fn decode_len<KeyArg: EncodeLike<K>>(key: KeyArg) -> Result<usize, &'static str>
		where V: codec::DecodeLength + Len
	{
		let key = Self::storage_map_final_key(key);
		if let Some(v) = unhashed::get_raw(key.as_ref()) {
			<V as codec::DecodeLength>::len(&v).map_err(|e| e.what())
		} else {
			let len = G::from_query_to_optional_value(G::from_optional_value_to_query(None))
				.map(|v| v.len())
				.unwrap_or(0);

			Ok(len)
		}
	}

	fn migrate_key<OldHasher: StorageHasher, KeyArg: EncodeLike<K>>(key: KeyArg) -> Option<V> {
		let old_key = {
			let module_prefix_hashed = Twox128::hash(Self::module_prefix());
			let storage_prefix_hashed = Twox128::hash(Self::storage_prefix());
			let key_hashed = key.borrow().using_encoded(OldHasher::hash);

			let mut final_key = Vec::with_capacity(
				module_prefix_hashed.len() + storage_prefix_hashed.len() + key_hashed.as_ref().len()
			);

			final_key.extend_from_slice(&module_prefix_hashed[..]);
			final_key.extend_from_slice(&storage_prefix_hashed[..]);
			final_key.extend_from_slice(key_hashed.as_ref());

			final_key
		};
		unhashed::take(old_key.as_ref()).map(|value| {
			unhashed::put(Self::storage_map_final_key(key).as_ref(), &value);
			value
		})
	}

	fn iter_key_value() -> storage::PrefixIterator<(K, V)> where
		Self::Hasher: ReversibleStorageHasher
	{
		let prefix = G::prefix_hash();
		storage::PrefixIterator {
			prefix: prefix.clone(),
			previous_key: prefix,
			drain: false,
			closure: from_hashed_key_to_key_value::<_, _, G>,
		}
	}

	fn drain_key_value() -> storage::PrefixIterator<(K, V)> where
		Self::Hasher: ReversibleStorageHasher
	{
		let prefix = G::prefix_hash();
		storage::PrefixIterator {
			prefix: prefix.clone(),
			previous_key: prefix,
			drain: true,
			closure: from_hashed_key_to_key_value::<_, _, G>,
		}
	}

	fn iter_value() -> storage::PrefixIterator<V> {
		let prefix = Self::prefix_hash();
		storage::PrefixIterator {
			prefix: prefix.to_vec(),
			previous_key: prefix.to_vec(),
			drain: false,
			closure: |_raw_key, mut raw_value| V::decode(&mut raw_value),
		}
	}

	fn translate_key_value<O: Decode, F: Fn(K, O) -> Option<V>>(f: F) where
		Self::Hasher: ReversibleStorageHasher
	{
		let prefix = G::prefix_hash();
		let mut previous_key = prefix.clone();
		loop {
			match sp_io::storage::next_key(&previous_key).filter(|n| n.starts_with(&prefix)) {
				Some(next) => {
					previous_key = next;
					let maybe_value = unhashed::get::<O>(&previous_key);
					let value = match maybe_value {
						Some(value) => value,
						None => {
							crate::debug::error!(
								"next_key returned a key with no value at {:?}", previous_key
							);
							continue
						},
					};

					// Slice in bound because already check by `starts_with`
					let mut hashed_key = &previous_key[prefix.len()..];

					let mut key_material = G::Hasher::reverse(&mut hashed_key);
					let key = match K::decode(&mut key_material) {
						Ok(key) => key,
						Err(e) => {
							crate::debug::error!(
								"old key failed to decode at {:?}: {:?}",
								previous_key, e
							);
							continue
						},
					};

					match f(key, value) {
						Some(new) => unhashed::put::<V>(&previous_key, &new),
						None => unhashed::kill(&previous_key),
					}
				}
				None => return,
			}
		}
	}

	fn translate_value<OldV, TranslateV>(translate_val: TranslateV) -> Result<(), u32>
		where OldV: Decode, TranslateV: Fn(OldV) -> V
	{
		let prefix = Self::prefix_hash();
		let mut previous_key = prefix.to_vec();
		let mut errors = 0;
		while let Some(next_key) = sp_io::storage::next_key(&previous_key)
			.filter(|n| n.starts_with(&prefix[..]))
		{
			if let Some(value) = unhashed::get(&next_key) {
				unhashed::put(&next_key[..], &translate_val(value));
			} else {
				// We failed to read the value. Remove the key and increment errors.
				unhashed::kill(&next_key[..]);
				errors += 1;
			}

			previous_key = next_key;
		}

		if errors == 0 {
			Ok(())
		} else {
			Err(errors)
		}
	}

	fn remove_all() {
		sp_io::storage::clear_prefix(&Self::prefix_hash())
	}
}

fn from_hashed_key_to_key_value<K, V, G>(
	hashed_key: &[u8],
	mut raw_value: &[u8]
) -> Result<(K, V), codec::Error> where
	K: FullCodec,
	V: FullCodec,
	G: StorageMap<K, V>,
	G::Hasher: ReversibleStorageHasher,
{
	let mut key_material = G::Hasher::reverse(hashed_key);
	let key = K::decode(&mut key_material)?;
	let value = V::decode(&mut raw_value)?;

	Ok((key, value))
}
