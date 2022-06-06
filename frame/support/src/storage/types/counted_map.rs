// This file is part of Substrate.

// Copyright (C) 2021-2022 Parity Technologies (UK) Ltd.
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

//! Storage counted map type.

use crate::{
	metadata::StorageEntryMetadata,
	storage::{
		generator::StorageMap as _,
		types::{
			OptionQuery, QueryKindTrait, StorageEntryMetadataBuilder, StorageMap, StorageValue,
			ValueQuery,
		},
		StorageAppend, StorageDecodeLength, StorageTryAppend,
	},
	traits::{Get, GetDefault, StorageInfo, StorageInfoTrait, StorageInstance},
	Never,
};
use codec::{Decode, Encode, EncodeLike, FullCodec, MaxEncodedLen, Ref};
use sp_io::MultiRemovalResults;
use sp_runtime::traits::Saturating;
use sp_std::prelude::*;

/// A wrapper around a `StorageMap` and a `StorageValue<Value=u32>` to keep track of how many items
/// are in a map, without needing to iterate all the values.
///
/// This storage item has additional storage read and write overhead when manipulating values
/// compared to a regular storage map.
///
/// For functions where we only add or remove a value, a single storage read is needed to check if
/// that value already exists. For mutate functions, two storage reads are used to check if the
/// value existed before and after the mutation.
///
/// Whenever the counter needs to be updated, an additional read and write occurs to update that
/// counter.
pub struct CountedStorageMap<
	Prefix,
	Hasher,
	Key,
	Value,
	QueryKind = OptionQuery,
	OnEmpty = GetDefault,
	MaxValues = GetDefault,
>(core::marker::PhantomData<(Prefix, Hasher, Key, Value, QueryKind, OnEmpty, MaxValues)>);

/// The requirement for an instance of [`CountedStorageMap`].
pub trait CountedStorageMapInstance: StorageInstance {
	/// The prefix to use for the counter storage value.
	type CounterPrefix: StorageInstance;
}

// Private helper trait to access map from counted storage map.
trait MapWrapper {
	type Map;
}

impl<P: CountedStorageMapInstance, H, K, V, Q, O, M> MapWrapper
	for CountedStorageMap<P, H, K, V, Q, O, M>
{
	type Map = StorageMap<P, H, K, V, Q, O, M>;
}

type CounterFor<P> = StorageValue<<P as CountedStorageMapInstance>::CounterPrefix, u32, ValueQuery>;

/// On removal logic for updating counter while draining upon some prefix with
/// [`crate::storage::PrefixIterator`].
pub struct OnRemovalCounterUpdate<Prefix>(core::marker::PhantomData<Prefix>);

impl<Prefix: CountedStorageMapInstance> crate::storage::PrefixIteratorOnRemoval
	for OnRemovalCounterUpdate<Prefix>
{
	fn on_removal(_key: &[u8], _value: &[u8]) {
		CounterFor::<Prefix>::mutate(|value| value.saturating_dec());
	}
}

impl<Prefix, Hasher, Key, Value, QueryKind, OnEmpty, MaxValues>
	CountedStorageMap<Prefix, Hasher, Key, Value, QueryKind, OnEmpty, MaxValues>
where
	Prefix: CountedStorageMapInstance,
	Hasher: crate::hash::StorageHasher,
	Key: FullCodec,
	Value: FullCodec,
	QueryKind: QueryKindTrait<Value, OnEmpty>,
	OnEmpty: Get<QueryKind::Query> + 'static,
	MaxValues: Get<Option<u32>>,
{
	/// The key used to store the counter of the map.
	pub fn counter_storage_final_key() -> [u8; 32] {
		CounterFor::<Prefix>::hashed_key()
	}

	/// The prefix used to generate the key of the map.
	pub fn map_storage_final_prefix() -> Vec<u8> {
		use crate::storage::generator::StorageMap;
		<Self as MapWrapper>::Map::prefix_hash()
	}

	/// Get the storage key used to fetch a value corresponding to a specific key.
	pub fn hashed_key_for<KeyArg: EncodeLike<Key>>(key: KeyArg) -> Vec<u8> {
		<Self as MapWrapper>::Map::hashed_key_for(key)
	}

	/// Does the value (explicitly) exist in storage?
	pub fn contains_key<KeyArg: EncodeLike<Key>>(key: KeyArg) -> bool {
		<Self as MapWrapper>::Map::contains_key(key)
	}

	/// Load the value associated with the given key from the map.
	pub fn get<KeyArg: EncodeLike<Key>>(key: KeyArg) -> QueryKind::Query {
		<Self as MapWrapper>::Map::get(key)
	}

	/// Try to get the value for the given key from the map.
	///
	/// Returns `Ok` if it exists, `Err` if not.
	pub fn try_get<KeyArg: EncodeLike<Key>>(key: KeyArg) -> Result<Value, ()> {
		<Self as MapWrapper>::Map::try_get(key)
	}

	/// Store or remove the value to be associated with `key` so that `get` returns the `query`.
	pub fn set<KeyArg: EncodeLike<Key>>(key: KeyArg, q: QueryKind::Query) {
		<Self as MapWrapper>::Map::set(key, q)
	}

	/// Swap the values of two keys.
	pub fn swap<KeyArg1: EncodeLike<Key>, KeyArg2: EncodeLike<Key>>(key1: KeyArg1, key2: KeyArg2) {
		<Self as MapWrapper>::Map::swap(key1, key2)
	}

	/// Store a value to be associated with the given key from the map.
	pub fn insert<KeyArg: EncodeLike<Key> + Clone, ValArg: EncodeLike<Value>>(
		key: KeyArg,
		val: ValArg,
	) {
		if !<Self as MapWrapper>::Map::contains_key(Ref::from(&key)) {
			CounterFor::<Prefix>::mutate(|value| value.saturating_inc());
		}
		<Self as MapWrapper>::Map::insert(key, val)
	}

	/// Remove the value under a key.
	pub fn remove<KeyArg: EncodeLike<Key> + Clone>(key: KeyArg) {
		if <Self as MapWrapper>::Map::contains_key(Ref::from(&key)) {
			CounterFor::<Prefix>::mutate(|value| value.saturating_dec());
		}
		<Self as MapWrapper>::Map::remove(key)
	}

	/// Mutate the value under a key.
	pub fn mutate<KeyArg: EncodeLike<Key> + Clone, R, F: FnOnce(&mut QueryKind::Query) -> R>(
		key: KeyArg,
		f: F,
	) -> R {
		Self::try_mutate(key, |v| Ok::<R, Never>(f(v)))
			.expect("`Never` can not be constructed; qed")
	}

	/// Mutate the item, only if an `Ok` value is returned.
	pub fn try_mutate<KeyArg, R, E, F>(key: KeyArg, f: F) -> Result<R, E>
	where
		KeyArg: EncodeLike<Key> + Clone,
		F: FnOnce(&mut QueryKind::Query) -> Result<R, E>,
	{
		Self::try_mutate_exists(key, |option_value_ref| {
			let option_value = core::mem::replace(option_value_ref, None);
			let mut query = <Self as MapWrapper>::Map::from_optional_value_to_query(option_value);
			let res = f(&mut query);
			let option_value = <Self as MapWrapper>::Map::from_query_to_optional_value(query);
			let _ = core::mem::replace(option_value_ref, option_value);
			res
		})
	}

	/// Mutate the value under a key. Deletes the item if mutated to a `None`.
	pub fn mutate_exists<KeyArg: EncodeLike<Key> + Clone, R, F: FnOnce(&mut Option<Value>) -> R>(
		key: KeyArg,
		f: F,
	) -> R {
		Self::try_mutate_exists(key, |v| Ok::<R, Never>(f(v)))
			.expect("`Never` can not be constructed; qed")
	}

	/// Mutate the item, only if an `Ok` value is returned. Deletes the item if mutated to a `None`.
	/// `f` will always be called with an option representing if the storage item exists (`Some<V>`)
	/// or if the storage item does not exist (`None`), independent of the `QueryType`.
	pub fn try_mutate_exists<KeyArg, R, E, F>(key: KeyArg, f: F) -> Result<R, E>
	where
		KeyArg: EncodeLike<Key> + Clone,
		F: FnOnce(&mut Option<Value>) -> Result<R, E>,
	{
		<Self as MapWrapper>::Map::try_mutate_exists(key, |option_value| {
			let existed = option_value.is_some();
			let res = f(option_value);
			let exist = option_value.is_some();

			if res.is_ok() {
				if existed && !exist {
					// Value was deleted
					CounterFor::<Prefix>::mutate(|value| value.saturating_dec());
				} else if !existed && exist {
					// Value was added
					CounterFor::<Prefix>::mutate(|value| value.saturating_inc());
				}
			}
			res
		})
	}

	/// Take the value under a key.
	pub fn take<KeyArg: EncodeLike<Key> + Clone>(key: KeyArg) -> QueryKind::Query {
		let removed_value = <Self as MapWrapper>::Map::mutate_exists(key, |value| value.take());
		if removed_value.is_some() {
			CounterFor::<Prefix>::mutate(|value| value.saturating_dec());
		}
		<Self as MapWrapper>::Map::from_optional_value_to_query(removed_value)
	}

	/// Append the given items to the value in the storage.
	///
	/// `Value` is required to implement `codec::EncodeAppend`.
	///
	/// # Warning
	///
	/// If the storage item is not encoded properly, the storage will be overwritten and set to
	/// `[item]`. Any default value set for the storage item will be ignored on overwrite.
	pub fn append<Item, EncodeLikeItem, EncodeLikeKey>(key: EncodeLikeKey, item: EncodeLikeItem)
	where
		EncodeLikeKey: EncodeLike<Key> + Clone,
		Item: Encode,
		EncodeLikeItem: EncodeLike<Item>,
		Value: StorageAppend<Item>,
	{
		if !<Self as MapWrapper>::Map::contains_key(Ref::from(&key)) {
			CounterFor::<Prefix>::mutate(|value| value.saturating_inc());
		}
		<Self as MapWrapper>::Map::append(key, item)
	}

	/// Read the length of the storage value without decoding the entire value under the given
	/// `key`.
	///
	/// `Value` is required to implement [`StorageDecodeLength`].
	///
	/// If the value does not exists or it fails to decode the length, `None` is returned. Otherwise
	/// `Some(len)` is returned.
	///
	/// # Warning
	///
	/// `None` does not mean that `get()` does not return a value. The default value is completly
	/// ignored by this function.
	pub fn decode_len<KeyArg: EncodeLike<Key>>(key: KeyArg) -> Option<usize>
	where
		Value: StorageDecodeLength,
	{
		<Self as MapWrapper>::Map::decode_len(key)
	}

	/// Migrate an item with the given `key` from a defunct `OldHasher` to the current hasher.
	///
	/// If the key doesn't exist, then it's a no-op. If it does, then it returns its value.
	pub fn migrate_key<OldHasher: crate::hash::StorageHasher, KeyArg: EncodeLike<Key>>(
		key: KeyArg,
	) -> Option<Value> {
		<Self as MapWrapper>::Map::migrate_key::<OldHasher, _>(key)
	}

	/// Remove all values in the map.
	#[deprecated = "Use `clear` instead"]
	pub fn remove_all() {
		#[allow(deprecated)]
		<Self as MapWrapper>::Map::remove_all(None);
		CounterFor::<Prefix>::kill();
	}

	/// Attempt to remove all items from the map.
	///
	/// Returns [`MultiRemovalResults`](sp_io::MultiRemovalResults) to inform about the result. Once
	/// the resultant `maybe_cursor` field is `None`, then no further items remain to be deleted.
	///
	/// NOTE: After the initial call for any given map, it is important that no further items
	/// are inserted into the map. If so, then the map may not be empty when the resultant
	/// `maybe_cursor` is `None`.
	///
	/// # Limit
	///
	/// A `limit` must always be provided through in order to cap the maximum
	/// amount of deletions done in a single call. This is one fewer than the
	/// maximum number of backend iterations which may be done by this operation and as such
	/// represents the maximum number of backend deletions which may happen. A `limit` of zero
	/// implies that no keys will be deleted, though there may be a single iteration done.
	///
	/// # Cursor
	///
	/// A *cursor* may be passed in to this operation with `maybe_cursor`. `None` should only be
	/// passed once (in the initial call) for any given storage map. Subsequent calls
	/// operating on the same map should always pass `Some`, and this should be equal to the
	/// previous call result's `maybe_cursor` field.
	pub fn clear(limit: u32, maybe_cursor: Option<&[u8]>) -> MultiRemovalResults {
		let result = <Self as MapWrapper>::Map::clear(limit, maybe_cursor);
		match result.maybe_cursor {
			None => CounterFor::<Prefix>::kill(),
			Some(_) => CounterFor::<Prefix>::mutate(|x| x.saturating_reduce(result.unique)),
		}
		result
	}

	/// Iter over all value of the storage.
	///
	/// NOTE: If a value failed to decode because storage is corrupted then it is skipped.
	pub fn iter_values() -> crate::storage::PrefixIterator<Value, OnRemovalCounterUpdate<Prefix>> {
		<Self as MapWrapper>::Map::iter_values().convert_on_removal()
	}

	/// Translate the values of all elements by a function `f`, in the map in no particular order.
	///
	/// By returning `None` from `f` for an element, you'll remove it from the map.
	///
	/// NOTE: If a value fail to decode because storage is corrupted then it is skipped.
	///
	/// # Warning
	///
	/// This function must be used with care, before being updated the storage still contains the
	/// old type, thus other calls (such as `get`) will fail at decoding it.
	///
	/// # Usage
	///
	/// This would typically be called inside the module implementation of on_runtime_upgrade.
	pub fn translate_values<OldValue: Decode, F: FnMut(OldValue) -> Option<Value>>(mut f: F) {
		<Self as MapWrapper>::Map::translate_values(|old_value| {
			let res = f(old_value);
			if res.is_none() {
				CounterFor::<Prefix>::mutate(|value| value.saturating_dec());
			}
			res
		})
	}

	/// Try and append the given item to the value in the storage.
	///
	/// Is only available if `Value` of the storage implements [`StorageTryAppend`].
	pub fn try_append<KArg, Item, EncodeLikeItem>(key: KArg, item: EncodeLikeItem) -> Result<(), ()>
	where
		KArg: EncodeLike<Key> + Clone,
		Item: Encode,
		EncodeLikeItem: EncodeLike<Item>,
		Value: StorageTryAppend<Item>,
	{
		let bound = Value::bound();
		let current = <Self as MapWrapper>::Map::decode_len(Ref::from(&key)).unwrap_or_default();
		if current < bound {
			CounterFor::<Prefix>::mutate(|value| value.saturating_inc());
			let key = <Self as MapWrapper>::Map::hashed_key_for(key);
			sp_io::storage::append(&key, item.encode());
			Ok(())
		} else {
			Err(())
		}
	}

	/// Initialize the counter with the actual number of items in the map.
	///
	/// This function iterates through all the items in the map and sets the counter. This operation
	/// can be very heavy, so use with caution.
	///
	/// Returns the number of items in the map which is used to set the counter.
	pub fn initialize_counter() -> u32 {
		let count = Self::iter_values().count() as u32;
		CounterFor::<Prefix>::set(count);
		count
	}

	/// Return the count.
	pub fn count() -> u32 {
		CounterFor::<Prefix>::get()
	}
}

impl<Prefix, Hasher, Key, Value, QueryKind, OnEmpty, MaxValues>
	CountedStorageMap<Prefix, Hasher, Key, Value, QueryKind, OnEmpty, MaxValues>
where
	Prefix: CountedStorageMapInstance,
	Hasher: crate::hash::StorageHasher + crate::ReversibleStorageHasher,
	Key: FullCodec,
	Value: FullCodec,
	QueryKind: QueryKindTrait<Value, OnEmpty>,
	OnEmpty: Get<QueryKind::Query> + 'static,
	MaxValues: Get<Option<u32>>,
{
	/// Enumerate all elements in the map in no particular order.
	///
	/// If you alter the map while doing this, you'll get undefined results.
	pub fn iter() -> crate::storage::PrefixIterator<(Key, Value), OnRemovalCounterUpdate<Prefix>> {
		<Self as MapWrapper>::Map::iter().convert_on_removal()
	}

	/// Remove all elements from the map and iterate through them in no particular order.
	///
	/// If you add elements to the map while doing this, you'll get undefined results.
	pub fn drain() -> crate::storage::PrefixIterator<(Key, Value), OnRemovalCounterUpdate<Prefix>> {
		<Self as MapWrapper>::Map::drain().convert_on_removal()
	}

	/// Translate the values of all elements by a function `f`, in the map in no particular order.
	///
	/// By returning `None` from `f` for an element, you'll remove it from the map.
	///
	/// NOTE: If a value fail to decode because storage is corrupted then it is skipped.
	pub fn translate<O: Decode, F: FnMut(Key, O) -> Option<Value>>(mut f: F) {
		<Self as MapWrapper>::Map::translate(|key, old_value| {
			let res = f(key, old_value);
			if res.is_none() {
				CounterFor::<Prefix>::mutate(|value| value.saturating_dec());
			}
			res
		})
	}

	/// Enumerate all elements in the counted map after a specified `starting_raw_key` in no
	/// particular order.
	///
	/// If you alter the map while doing this, you'll get undefined results.
	pub fn iter_from(
		starting_raw_key: Vec<u8>,
	) -> crate::storage::PrefixIterator<(Key, Value), OnRemovalCounterUpdate<Prefix>> {
		<Self as MapWrapper>::Map::iter_from(starting_raw_key).convert_on_removal()
	}

	/// Enumerate all keys in the counted map.
	///
	/// If you alter the map while doing this, you'll get undefined results.
	pub fn iter_keys() -> crate::storage::KeyPrefixIterator<Key> {
		<Self as MapWrapper>::Map::iter_keys()
	}
}

impl<Prefix, Hasher, Key, Value, QueryKind, OnEmpty, MaxValues> StorageEntryMetadataBuilder
	for CountedStorageMap<Prefix, Hasher, Key, Value, QueryKind, OnEmpty, MaxValues>
where
	Prefix: CountedStorageMapInstance,
	Hasher: crate::hash::StorageHasher,
	Key: FullCodec + scale_info::StaticTypeInfo,
	Value: FullCodec + scale_info::StaticTypeInfo,
	QueryKind: QueryKindTrait<Value, OnEmpty>,
	OnEmpty: Get<QueryKind::Query> + 'static,
	MaxValues: Get<Option<u32>>,
{
	fn build_metadata(docs: Vec<&'static str>, entries: &mut Vec<StorageEntryMetadata>) {
		<Self as MapWrapper>::Map::build_metadata(docs, entries);
		CounterFor::<Prefix>::build_metadata(
			if cfg!(feature = "no-metadata-docs") {
				vec![]
			} else {
				vec!["Counter for the related counted storage map"]
			},
			entries,
		);
	}
}

impl<Prefix, Hasher, Key, Value, QueryKind, OnEmpty, MaxValues> crate::traits::StorageInfoTrait
	for CountedStorageMap<Prefix, Hasher, Key, Value, QueryKind, OnEmpty, MaxValues>
where
	Prefix: CountedStorageMapInstance,
	Hasher: crate::hash::StorageHasher,
	Key: FullCodec + MaxEncodedLen,
	Value: FullCodec + MaxEncodedLen,
	QueryKind: QueryKindTrait<Value, OnEmpty>,
	OnEmpty: Get<QueryKind::Query> + 'static,
	MaxValues: Get<Option<u32>>,
{
	fn storage_info() -> Vec<StorageInfo> {
		[<Self as MapWrapper>::Map::storage_info(), CounterFor::<Prefix>::storage_info()].concat()
	}
}

/// It doesn't require to implement `MaxEncodedLen` and give no information for `max_size`.
impl<Prefix, Hasher, Key, Value, QueryKind, OnEmpty, MaxValues>
	crate::traits::PartialStorageInfoTrait
	for CountedStorageMap<Prefix, Hasher, Key, Value, QueryKind, OnEmpty, MaxValues>
where
	Prefix: CountedStorageMapInstance,
	Hasher: crate::hash::StorageHasher,
	Key: FullCodec,
	Value: FullCodec,
	QueryKind: QueryKindTrait<Value, OnEmpty>,
	OnEmpty: Get<QueryKind::Query> + 'static,
	MaxValues: Get<Option<u32>>,
{
	fn partial_storage_info() -> Vec<StorageInfo> {
		[<Self as MapWrapper>::Map::partial_storage_info(), CounterFor::<Prefix>::storage_info()]
			.concat()
	}
}

#[cfg(test)]
mod test {
	use super::*;
	use crate::{
		hash::*,
		metadata::{StorageEntryModifier, StorageEntryType, StorageHasher},
		storage::{bounded_vec::BoundedVec, types::ValueQuery},
		traits::ConstU32,
	};
	use sp_io::{hashing::twox_128, TestExternalities};

	struct Prefix;
	impl StorageInstance for Prefix {
		fn pallet_prefix() -> &'static str {
			"test"
		}
		const STORAGE_PREFIX: &'static str = "foo";
	}

	struct CounterPrefix;
	impl StorageInstance for CounterPrefix {
		fn pallet_prefix() -> &'static str {
			"test"
		}
		const STORAGE_PREFIX: &'static str = "counter_for_foo";
	}
	impl CountedStorageMapInstance for Prefix {
		type CounterPrefix = CounterPrefix;
	}

	struct ADefault;
	impl crate::traits::Get<u32> for ADefault {
		fn get() -> u32 {
			97
		}
	}

	#[test]
	fn test_value_query() {
		type A = CountedStorageMap<Prefix, Twox64Concat, u16, u32, ValueQuery, ADefault>;

		TestExternalities::default().execute_with(|| {
			let mut k: Vec<u8> = vec![];
			k.extend(&twox_128(b"test"));
			k.extend(&twox_128(b"foo"));
			k.extend(&3u16.twox_64_concat());
			assert_eq!(A::hashed_key_for(3).to_vec(), k);

			assert_eq!(A::contains_key(3), false);
			assert_eq!(A::get(3), ADefault::get());
			assert_eq!(A::try_get(3), Err(()));
			assert_eq!(A::count(), 0);

			// Insert non-existing.
			A::insert(3, 10);

			assert_eq!(A::contains_key(3), true);
			assert_eq!(A::get(3), 10);
			assert_eq!(A::try_get(3), Ok(10));
			assert_eq!(A::count(), 1);

			// Swap non-existing with existing.
			A::swap(4, 3);

			assert_eq!(A::contains_key(3), false);
			assert_eq!(A::get(3), ADefault::get());
			assert_eq!(A::try_get(3), Err(()));
			assert_eq!(A::contains_key(4), true);
			assert_eq!(A::get(4), 10);
			assert_eq!(A::try_get(4), Ok(10));
			assert_eq!(A::count(), 1);

			// Swap existing with non-existing.
			A::swap(4, 3);

			assert_eq!(A::try_get(3), Ok(10));
			assert_eq!(A::contains_key(4), false);
			assert_eq!(A::get(4), ADefault::get());
			assert_eq!(A::try_get(4), Err(()));
			assert_eq!(A::count(), 1);

			A::insert(4, 11);

			assert_eq!(A::try_get(3), Ok(10));
			assert_eq!(A::try_get(4), Ok(11));
			assert_eq!(A::count(), 2);

			// Swap 2 existing.
			A::swap(3, 4);

			assert_eq!(A::try_get(3), Ok(11));
			assert_eq!(A::try_get(4), Ok(10));
			assert_eq!(A::count(), 2);

			// Insert an existing key, shouldn't increment counted values.
			A::insert(3, 11);

			assert_eq!(A::count(), 2);

			// Remove non-existing.
			A::remove(2);

			assert_eq!(A::contains_key(2), false);
			assert_eq!(A::count(), 2);

			// Remove existing.
			A::remove(3);

			assert_eq!(A::try_get(3), Err(()));
			assert_eq!(A::count(), 1);

			// Mutate non-existing to existing.
			A::mutate(3, |query| {
				assert_eq!(*query, ADefault::get());
				*query = 40;
			});

			assert_eq!(A::try_get(3), Ok(40));
			assert_eq!(A::count(), 2);

			// Mutate existing to existing.
			A::mutate(3, |query| {
				assert_eq!(*query, 40);
				*query = 40;
			});

			assert_eq!(A::try_get(3), Ok(40));
			assert_eq!(A::count(), 2);

			// Try fail mutate non-existing to existing.
			A::try_mutate(2, |query| {
				assert_eq!(*query, ADefault::get());
				*query = 4;
				Result::<(), ()>::Err(())
			})
			.err()
			.unwrap();

			assert_eq!(A::try_get(2), Err(()));
			assert_eq!(A::count(), 2);

			// Try succeed mutate non-existing to existing.
			A::try_mutate(2, |query| {
				assert_eq!(*query, ADefault::get());
				*query = 41;
				Result::<(), ()>::Ok(())
			})
			.unwrap();

			assert_eq!(A::try_get(2), Ok(41));
			assert_eq!(A::count(), 3);

			// Try succeed mutate existing to existing.
			A::try_mutate(2, |query| {
				assert_eq!(*query, 41);
				*query = 41;
				Result::<(), ()>::Ok(())
			})
			.unwrap();

			assert_eq!(A::try_get(2), Ok(41));
			assert_eq!(A::count(), 3);

			// Try fail mutate non-existing to existing.
			A::try_mutate_exists(1, |query| {
				assert_eq!(*query, None);
				*query = Some(4);
				Result::<(), ()>::Err(())
			})
			.err()
			.unwrap();

			assert_eq!(A::try_get(1), Err(()));
			assert_eq!(A::count(), 3);

			// Try succeed mutate non-existing to existing.
			A::try_mutate_exists(1, |query| {
				assert_eq!(*query, None);
				*query = Some(43);
				Result::<(), ()>::Ok(())
			})
			.unwrap();

			assert_eq!(A::try_get(1), Ok(43));
			assert_eq!(A::count(), 4);

			// Try succeed mutate existing to existing.
			A::try_mutate_exists(1, |query| {
				assert_eq!(*query, Some(43));
				*query = Some(43);
				Result::<(), ()>::Ok(())
			})
			.unwrap();

			assert_eq!(A::try_get(1), Ok(43));
			assert_eq!(A::count(), 4);

			// Try succeed mutate existing to non-existing.
			A::try_mutate_exists(1, |query| {
				assert_eq!(*query, Some(43));
				*query = None;
				Result::<(), ()>::Ok(())
			})
			.unwrap();

			assert_eq!(A::try_get(1), Err(()));
			assert_eq!(A::count(), 3);

			// Take exsisting.
			assert_eq!(A::take(4), 10);

			assert_eq!(A::try_get(4), Err(()));
			assert_eq!(A::count(), 2);

			// Take non-exsisting.
			assert_eq!(A::take(4), ADefault::get());

			assert_eq!(A::try_get(4), Err(()));
			assert_eq!(A::count(), 2);

			// Remove all.
			let _ = A::clear(u32::max_value(), None);

			assert_eq!(A::count(), 0);
			assert_eq!(A::initialize_counter(), 0);

			A::insert(1, 1);
			A::insert(2, 2);

			// Iter values.
			assert_eq!(A::iter_values().collect::<Vec<_>>(), vec![2, 1]);

			// Iter drain values.
			assert_eq!(A::iter_values().drain().collect::<Vec<_>>(), vec![2, 1]);
			assert_eq!(A::count(), 0);

			A::insert(1, 1);
			A::insert(2, 2);

			// Test initialize_counter.
			assert_eq!(A::initialize_counter(), 2);
		})
	}

	#[test]
	fn test_option_query() {
		type B = CountedStorageMap<Prefix, Twox64Concat, u16, u32>;

		TestExternalities::default().execute_with(|| {
			let mut k: Vec<u8> = vec![];
			k.extend(&twox_128(b"test"));
			k.extend(&twox_128(b"foo"));
			k.extend(&3u16.twox_64_concat());
			assert_eq!(B::hashed_key_for(3).to_vec(), k);

			assert_eq!(B::contains_key(3), false);
			assert_eq!(B::get(3), None);
			assert_eq!(B::try_get(3), Err(()));
			assert_eq!(B::count(), 0);

			// Insert non-existing.
			B::insert(3, 10);

			assert_eq!(B::contains_key(3), true);
			assert_eq!(B::get(3), Some(10));
			assert_eq!(B::try_get(3), Ok(10));
			assert_eq!(B::count(), 1);

			// Swap non-existing with existing.
			B::swap(4, 3);

			assert_eq!(B::contains_key(3), false);
			assert_eq!(B::get(3), None);
			assert_eq!(B::try_get(3), Err(()));
			assert_eq!(B::contains_key(4), true);
			assert_eq!(B::get(4), Some(10));
			assert_eq!(B::try_get(4), Ok(10));
			assert_eq!(B::count(), 1);

			// Swap existing with non-existing.
			B::swap(4, 3);

			assert_eq!(B::try_get(3), Ok(10));
			assert_eq!(B::contains_key(4), false);
			assert_eq!(B::get(4), None);
			assert_eq!(B::try_get(4), Err(()));
			assert_eq!(B::count(), 1);

			B::insert(4, 11);

			assert_eq!(B::try_get(3), Ok(10));
			assert_eq!(B::try_get(4), Ok(11));
			assert_eq!(B::count(), 2);

			// Swap 2 existing.
			B::swap(3, 4);

			assert_eq!(B::try_get(3), Ok(11));
			assert_eq!(B::try_get(4), Ok(10));
			assert_eq!(B::count(), 2);

			// Insert an existing key, shouldn't increment counted values.
			B::insert(3, 11);

			assert_eq!(B::count(), 2);

			// Remove non-existing.
			B::remove(2);

			assert_eq!(B::contains_key(2), false);
			assert_eq!(B::count(), 2);

			// Remove existing.
			B::remove(3);

			assert_eq!(B::try_get(3), Err(()));
			assert_eq!(B::count(), 1);

			// Mutate non-existing to existing.
			B::mutate(3, |query| {
				assert_eq!(*query, None);
				*query = Some(40)
			});

			assert_eq!(B::try_get(3), Ok(40));
			assert_eq!(B::count(), 2);

			// Mutate existing to existing.
			B::mutate(3, |query| {
				assert_eq!(*query, Some(40));
				*query = Some(40)
			});

			assert_eq!(B::try_get(3), Ok(40));
			assert_eq!(B::count(), 2);

			// Mutate existing to non-existing.
			B::mutate(3, |query| {
				assert_eq!(*query, Some(40));
				*query = None
			});

			assert_eq!(B::try_get(3), Err(()));
			assert_eq!(B::count(), 1);

			B::insert(3, 40);

			// Try fail mutate non-existing to existing.
			B::try_mutate(2, |query| {
				assert_eq!(*query, None);
				*query = Some(4);
				Result::<(), ()>::Err(())
			})
			.err()
			.unwrap();

			assert_eq!(B::try_get(2), Err(()));
			assert_eq!(B::count(), 2);

			// Try succeed mutate non-existing to existing.
			B::try_mutate(2, |query| {
				assert_eq!(*query, None);
				*query = Some(41);
				Result::<(), ()>::Ok(())
			})
			.unwrap();

			assert_eq!(B::try_get(2), Ok(41));
			assert_eq!(B::count(), 3);

			// Try succeed mutate existing to existing.
			B::try_mutate(2, |query| {
				assert_eq!(*query, Some(41));
				*query = Some(41);
				Result::<(), ()>::Ok(())
			})
			.unwrap();

			assert_eq!(B::try_get(2), Ok(41));
			assert_eq!(B::count(), 3);

			// Try succeed mutate existing to non-existing.
			B::try_mutate(2, |query| {
				assert_eq!(*query, Some(41));
				*query = None;
				Result::<(), ()>::Ok(())
			})
			.unwrap();

			assert_eq!(B::try_get(2), Err(()));
			assert_eq!(B::count(), 2);

			B::insert(2, 41);

			// Try fail mutate non-existing to existing.
			B::try_mutate_exists(1, |query| {
				assert_eq!(*query, None);
				*query = Some(4);
				Result::<(), ()>::Err(())
			})
			.err()
			.unwrap();

			assert_eq!(B::try_get(1), Err(()));
			assert_eq!(B::count(), 3);

			// Try succeed mutate non-existing to existing.
			B::try_mutate_exists(1, |query| {
				assert_eq!(*query, None);
				*query = Some(43);
				Result::<(), ()>::Ok(())
			})
			.unwrap();

			assert_eq!(B::try_get(1), Ok(43));
			assert_eq!(B::count(), 4);

			// Try succeed mutate existing to existing.
			B::try_mutate_exists(1, |query| {
				assert_eq!(*query, Some(43));
				*query = Some(43);
				Result::<(), ()>::Ok(())
			})
			.unwrap();

			assert_eq!(B::try_get(1), Ok(43));
			assert_eq!(B::count(), 4);

			// Try succeed mutate existing to non-existing.
			B::try_mutate_exists(1, |query| {
				assert_eq!(*query, Some(43));
				*query = None;
				Result::<(), ()>::Ok(())
			})
			.unwrap();

			assert_eq!(B::try_get(1), Err(()));
			assert_eq!(B::count(), 3);

			// Take exsisting.
			assert_eq!(B::take(4), Some(10));

			assert_eq!(B::try_get(4), Err(()));
			assert_eq!(B::count(), 2);

			// Take non-exsisting.
			assert_eq!(B::take(4), None);

			assert_eq!(B::try_get(4), Err(()));
			assert_eq!(B::count(), 2);

			// Remove all.
			let _ = B::clear(u32::max_value(), None);

			assert_eq!(B::count(), 0);
			assert_eq!(B::initialize_counter(), 0);

			B::insert(1, 1);
			B::insert(2, 2);

			// Iter values.
			assert_eq!(B::iter_values().collect::<Vec<_>>(), vec![2, 1]);

			// Iter drain values.
			assert_eq!(B::iter_values().drain().collect::<Vec<_>>(), vec![2, 1]);
			assert_eq!(B::count(), 0);

			B::insert(1, 1);
			B::insert(2, 2);

			// Test initialize_counter.
			assert_eq!(B::initialize_counter(), 2);
		})
	}

	#[test]
	fn append_decode_len_works() {
		type B = CountedStorageMap<Prefix, Twox64Concat, u16, Vec<u32>>;

		TestExternalities::default().execute_with(|| {
			assert_eq!(B::decode_len(0), None);
			B::append(0, 3);
			assert_eq!(B::decode_len(0), Some(1));
			B::append(0, 3);
			assert_eq!(B::decode_len(0), Some(2));
			B::append(0, 3);
			assert_eq!(B::decode_len(0), Some(3));
		})
	}

	#[test]
	fn try_append_decode_len_works() {
		type B = CountedStorageMap<Prefix, Twox64Concat, u16, BoundedVec<u32, ConstU32<3u32>>>;

		TestExternalities::default().execute_with(|| {
			assert_eq!(B::decode_len(0), None);
			B::try_append(0, 3).unwrap();
			assert_eq!(B::decode_len(0), Some(1));
			B::try_append(0, 3).unwrap();
			assert_eq!(B::decode_len(0), Some(2));
			B::try_append(0, 3).unwrap();
			assert_eq!(B::decode_len(0), Some(3));
			B::try_append(0, 3).err().unwrap();
			assert_eq!(B::decode_len(0), Some(3));
		})
	}

	#[test]
	fn migrate_keys_works() {
		type A = CountedStorageMap<Prefix, Twox64Concat, u16, u32>;
		type B = CountedStorageMap<Prefix, Blake2_128Concat, u16, u32>;
		TestExternalities::default().execute_with(|| {
			A::insert(1, 1);
			assert_eq!(B::migrate_key::<Twox64Concat, _>(1), Some(1));
			assert_eq!(B::get(1), Some(1));
		})
	}

	#[test]
	fn translate_values() {
		type A = CountedStorageMap<Prefix, Twox64Concat, u16, u32>;
		TestExternalities::default().execute_with(|| {
			A::insert(1, 1);
			A::insert(2, 2);
			A::translate_values::<u32, _>(|old_value| if old_value == 1 { None } else { Some(1) });
			assert_eq!(A::count(), 1);
			assert_eq!(A::get(2), Some(1));
		})
	}

	#[test]
	fn test_iter_drain_translate() {
		type A = CountedStorageMap<Prefix, Twox64Concat, u16, u32>;
		TestExternalities::default().execute_with(|| {
			A::insert(1, 1);
			A::insert(2, 2);

			assert_eq!(A::iter().collect::<Vec<_>>(), vec![(2, 2), (1, 1)]);

			assert_eq!(A::count(), 2);

			A::translate::<u32, _>(
				|key, value| if key == 1 { None } else { Some(key as u32 * value) },
			);

			assert_eq!(A::count(), 1);

			assert_eq!(A::drain().collect::<Vec<_>>(), vec![(2, 4)]);

			assert_eq!(A::count(), 0);
		})
	}

	#[test]
	fn test_iter_from() {
		type A = CountedStorageMap<Prefix, Twox64Concat, u16, u32>;
		TestExternalities::default().execute_with(|| {
			A::insert(1, 1);
			A::insert(2, 2);
			A::insert(3, 3);
			A::insert(4, 4);

			// no prefix is same as normal iter.
			assert_eq!(A::iter_from(vec![]).collect::<Vec<_>>(), A::iter().collect::<Vec<_>>());

			let iter_all = A::iter().collect::<Vec<_>>();
			let (before, after) = iter_all.split_at(2);
			let last_key = before.last().map(|(k, _)| k).unwrap();
			assert_eq!(A::iter_from(A::hashed_key_for(last_key)).collect::<Vec<_>>(), after);
		})
	}

	#[test]
	fn test_metadata() {
		type A = CountedStorageMap<Prefix, Twox64Concat, u16, u32, ValueQuery, ADefault>;
		let mut entries = vec![];
		A::build_metadata(vec![], &mut entries);
		assert_eq!(
			entries,
			vec![
				StorageEntryMetadata {
					name: "foo",
					modifier: StorageEntryModifier::Default,
					ty: StorageEntryType::Map {
						hashers: vec![StorageHasher::Twox64Concat],
						key: scale_info::meta_type::<u16>(),
						value: scale_info::meta_type::<u32>(),
					},
					default: 97u32.encode(),
					docs: vec![],
				},
				StorageEntryMetadata {
					name: "counter_for_foo",
					modifier: StorageEntryModifier::Default,
					ty: StorageEntryType::Plain(scale_info::meta_type::<u32>()),
					default: vec![0, 0, 0, 0],
					docs: if cfg!(feature = "no-metadata-docs") {
						vec![]
					} else {
						vec!["Counter for the related counted storage map"]
					},
				},
			]
		);
	}
}
