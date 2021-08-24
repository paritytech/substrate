// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

use crate::{
	hash::{ReversibleStorageHasher, StorageHasher},
	storage::{self, storage_prefix, unhashed, KeyPrefixIterator, PrefixIterator, StorageAppend},
	Never,
};
use codec::{Decode, Encode, EncodeLike, FullCodec, FullEncode};
use sp_std::borrow::Borrow;
#[cfg(not(feature = "std"))]
use sp_std::prelude::*;

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
pub trait StorageMap<K: FullEncode, V: FullCodec> {
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
		let result = storage_prefix(Self::module_prefix(), Self::storage_prefix());
		result.to_vec()
	}

	/// Convert an optional value retrieved from storage to the type queried.
	fn from_optional_value_to_query(v: Option<V>) -> Self::Query;

	/// Convert a query to an optional value into storage.
	fn from_query_to_optional_value(v: Self::Query) -> Option<V>;

	/// Generate the full key used in top storage.
	fn storage_map_final_key<KeyArg>(key: KeyArg) -> Vec<u8>
	where
		KeyArg: EncodeLike<K>,
	{
		let storage_prefix = storage_prefix(Self::module_prefix(), Self::storage_prefix());
		let key_hashed = key.borrow().using_encoded(Self::Hasher::hash);

		let mut final_key = Vec::with_capacity(storage_prefix.len() + key_hashed.as_ref().len());

		final_key.extend_from_slice(&storage_prefix);
		final_key.extend_from_slice(key_hashed.as_ref());

		final_key
	}
}

/// Utility to iterate through items in a storage map.
pub struct StorageMapIterator<K, V, Hasher> {
	prefix: Vec<u8>,
	previous_key: Vec<u8>,
	drain: bool,
	_phantom: ::sp_std::marker::PhantomData<(K, V, Hasher)>,
}

impl<K: Decode + Sized, V: Decode + Sized, Hasher: ReversibleStorageHasher> Iterator
	for StorageMapIterator<K, V, Hasher>
{
	type Item = (K, V);

	fn next(&mut self) -> Option<(K, V)> {
		loop {
			let maybe_next = sp_io::storage::next_key(&self.previous_key)
				.filter(|n| n.starts_with(&self.prefix));
			break match maybe_next {
				Some(next) => {
					self.previous_key = next;
					match unhashed::get::<V>(&self.previous_key) {
						Some(value) => {
							if self.drain {
								unhashed::kill(&self.previous_key)
							}
							let mut key_material =
								Hasher::reverse(&self.previous_key[self.prefix.len()..]);
							match K::decode(&mut key_material) {
								Ok(key) => Some((key, value)),
								Err(_) => continue,
							}
						},
						None => continue,
					}
				},
				None => None,
			}
		}
	}
}

impl<K: FullCodec, V: FullCodec, G: StorageMap<K, V>> storage::IterableStorageMap<K, V> for G
where
	G::Hasher: ReversibleStorageHasher,
{
	type Iterator = PrefixIterator<(K, V)>;
	type KeyIterator = KeyPrefixIterator<K>;

	/// Enumerate all elements in the map.
	fn iter() -> Self::Iterator {
		let prefix = G::prefix_hash();
		PrefixIterator {
			prefix: prefix.clone(),
			previous_key: prefix,
			drain: false,
			closure: |raw_key_without_prefix, mut raw_value| {
				let mut key_material = G::Hasher::reverse(raw_key_without_prefix);
				Ok((K::decode(&mut key_material)?, V::decode(&mut raw_value)?))
			},
		}
	}

	/// Enumerate all elements in the map after a given key.
	fn iter_from(starting_raw_key: Vec<u8>) -> Self::Iterator {
		let mut iter = Self::iter();
		iter.set_last_raw_key(starting_raw_key);
		iter
	}

	/// Enumerate all keys in the map.
	fn iter_keys() -> Self::KeyIterator {
		let prefix = G::prefix_hash();
		KeyPrefixIterator {
			prefix: prefix.clone(),
			previous_key: prefix,
			drain: false,
			closure: |raw_key_without_prefix| {
				let mut key_material = G::Hasher::reverse(raw_key_without_prefix);
				K::decode(&mut key_material)
			},
		}
	}

	/// Enumerate all keys in the map after a given key.
	fn iter_keys_from(starting_raw_key: Vec<u8>) -> Self::KeyIterator {
		let mut iter = Self::iter_keys();
		iter.set_last_raw_key(starting_raw_key);
		iter
	}

	/// Enumerate all elements in the map.
	fn drain() -> Self::Iterator {
		let mut iterator = Self::iter();
		iterator.drain = true;
		iterator
	}

	fn translate<O: Decode, F: FnMut(K, O) -> Option<V>>(mut f: F) {
		let prefix = G::prefix_hash();
		let mut previous_key = prefix.clone();
		while let Some(next) =
			sp_io::storage::next_key(&previous_key).filter(|n| n.starts_with(&prefix))
		{
			previous_key = next;
			let value = match unhashed::get::<O>(&previous_key) {
				Some(value) => value,
				None => {
					log::error!("Invalid translate: fail to decode old value");
					continue
				},
			};

			let mut key_material = G::Hasher::reverse(&previous_key[prefix.len()..]);
			let key = match K::decode(&mut key_material) {
				Ok(key) => key,
				Err(_) => {
					log::error!("Invalid translate: fail to decode key");
					continue
				},
			};

			match f(key, value) {
				Some(new) => unhashed::put::<V>(&previous_key, &new),
				None => unhashed::kill(&previous_key),
			}
		}
	}
}

impl<K: FullEncode, V: FullCodec, G: StorageMap<K, V>> storage::StorageMap<K, V> for G {
	type Query = G::Query;

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

	fn try_get<KeyArg: EncodeLike<K>>(key: KeyArg) -> Result<V, ()> {
		unhashed::get(Self::storage_map_final_key(key).as_ref()).ok_or(())
	}

	fn insert<KeyArg: EncodeLike<K>, ValArg: EncodeLike<V>>(key: KeyArg, val: ValArg) {
		unhashed::put(Self::storage_map_final_key(key).as_ref(), &val)
	}

	fn remove<KeyArg: EncodeLike<K>>(key: KeyArg) {
		unhashed::kill(Self::storage_map_final_key(key).as_ref())
	}

	fn mutate<KeyArg: EncodeLike<K>, R, F: FnOnce(&mut Self::Query) -> R>(key: KeyArg, f: F) -> R {
		Self::try_mutate(key, |v| Ok::<R, Never>(f(v)))
			.expect("`Never` can not be constructed; qed")
	}

	fn mutate_exists<KeyArg: EncodeLike<K>, R, F: FnOnce(&mut Option<V>) -> R>(
		key: KeyArg,
		f: F,
	) -> R {
		Self::try_mutate_exists(key, |v| Ok::<R, Never>(f(v)))
			.expect("`Never` can not be constructed; qed")
	}

	fn try_mutate<KeyArg: EncodeLike<K>, R, E, F: FnOnce(&mut Self::Query) -> Result<R, E>>(
		key: KeyArg,
		f: F,
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
		f: F,
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

	fn append<Item, EncodeLikeItem, EncodeLikeKey>(key: EncodeLikeKey, item: EncodeLikeItem)
	where
		EncodeLikeKey: EncodeLike<K>,
		Item: Encode,
		EncodeLikeItem: EncodeLike<Item>,
		V: StorageAppend<Item>,
	{
		let key = Self::storage_map_final_key(key);
		sp_io::storage::append(&key, item.encode());
	}

	fn migrate_key<OldHasher: StorageHasher, KeyArg: EncodeLike<K>>(key: KeyArg) -> Option<V> {
		let old_key = {
			let storage_prefix = storage_prefix(Self::module_prefix(), Self::storage_prefix());
			let key_hashed = key.borrow().using_encoded(OldHasher::hash);

			let mut final_key =
				Vec::with_capacity(storage_prefix.len() + key_hashed.as_ref().len());

			final_key.extend_from_slice(&storage_prefix);
			final_key.extend_from_slice(key_hashed.as_ref());

			final_key
		};
		unhashed::take(old_key.as_ref()).map(|value| {
			unhashed::put(Self::storage_map_final_key(key).as_ref(), &value);
			value
		})
	}
}

/// Test iterators for StorageMap
#[cfg(test)]
mod test_iterators {
	use crate::{
		hash::StorageHasher,
		storage::{generator::StorageMap, unhashed, IterableStorageMap},
	};
	use codec::{Decode, Encode};

	pub trait Config: 'static {
		type Origin;
		type BlockNumber;
		type PalletInfo: crate::traits::PalletInfo;
		type DbWeight: crate::traits::Get<crate::weights::RuntimeDbWeight>;
	}

	crate::decl_module! {
		pub struct Module<T: Config> for enum Call where origin: T::Origin, system=self {}
	}

	#[derive(PartialEq, Eq, Clone, Encode, Decode)]
	struct NoDef(u32);

	crate::decl_storage! {
		trait Store for Module<T: Config> as Test {
			Map: map hasher(blake2_128_concat) u16 => u64;
		}
	}

	fn key_before_prefix(mut prefix: Vec<u8>) -> Vec<u8> {
		let last = prefix.iter_mut().last().unwrap();
		assert!(*last != 0, "mock function not implemented for this prefix");
		*last -= 1;
		prefix
	}

	fn key_after_prefix(mut prefix: Vec<u8>) -> Vec<u8> {
		let last = prefix.iter_mut().last().unwrap();
		assert!(*last != 255, "mock function not implemented for this prefix");
		*last += 1;
		prefix
	}

	#[test]
	fn map_iter_from() {
		sp_io::TestExternalities::default().execute_with(|| {
			use crate::hash::Identity;
			crate::generate_storage_alias!(MyModule, MyMap => Map<(u64, Identity), u64>);

			MyMap::insert(1, 10);
			MyMap::insert(2, 20);
			MyMap::insert(3, 30);
			MyMap::insert(4, 40);
			MyMap::insert(5, 50);

			let starting_raw_key = MyMap::storage_map_final_key(3);
			let iter = MyMap::iter_from(starting_raw_key);
			assert_eq!(iter.collect::<Vec<_>>(), vec![(4, 40), (5, 50)]);

			let starting_raw_key = MyMap::storage_map_final_key(2);
			let iter = MyMap::iter_keys_from(starting_raw_key);
			assert_eq!(iter.collect::<Vec<_>>(), vec![3, 4, 5]);
		});
	}

	#[test]
	fn map_reversible_reversible_iteration() {
		sp_io::TestExternalities::default().execute_with(|| {
			// All map iterator
			let prefix = Map::prefix_hash();

			unhashed::put(&key_before_prefix(prefix.clone()), &1u64);
			unhashed::put(&key_after_prefix(prefix.clone()), &1u64);

			for i in 0..4 {
				Map::insert(i as u16, i as u64);
			}

			assert_eq!(Map::iter().collect::<Vec<_>>(), vec![(3, 3), (0, 0), (2, 2), (1, 1)]);

			assert_eq!(Map::iter_keys().collect::<Vec<_>>(), vec![3, 0, 2, 1]);

			assert_eq!(Map::iter_values().collect::<Vec<_>>(), vec![3, 0, 2, 1]);

			assert_eq!(Map::drain().collect::<Vec<_>>(), vec![(3, 3), (0, 0), (2, 2), (1, 1)]);

			assert_eq!(Map::iter().collect::<Vec<_>>(), vec![]);
			assert_eq!(unhashed::get(&key_before_prefix(prefix.clone())), Some(1u64));
			assert_eq!(unhashed::get(&key_after_prefix(prefix.clone())), Some(1u64));

			// Translate
			let prefix = Map::prefix_hash();

			unhashed::put(&key_before_prefix(prefix.clone()), &1u64);
			unhashed::put(&key_after_prefix(prefix.clone()), &1u64);
			for i in 0..4 {
				Map::insert(i as u16, i as u64);
			}

			// Wrong key
			unhashed::put(&[prefix.clone(), vec![1, 2, 3]].concat(), &3u64.encode());

			// Wrong value
			unhashed::put(
				&[prefix.clone(), crate::Blake2_128Concat::hash(&6u16.encode())].concat(),
				&vec![1],
			);

			Map::translate(|_k1, v: u64| Some(v * 2));
			assert_eq!(Map::iter().collect::<Vec<_>>(), vec![(3, 6), (0, 0), (2, 4), (1, 2)]);
		})
	}
}
