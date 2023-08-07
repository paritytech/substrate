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

//! Counted storage n-map type.

use crate::{
	storage::{
		types::{
			EncodeLikeTuple, HasKeyPrefix, HasReversibleKeyPrefix, OptionQuery, QueryKindTrait,
			StorageEntryMetadataBuilder, StorageNMap, StorageValue, TupleToEncodedIter, ValueQuery,
		},
		KeyGenerator, PrefixIterator, StorageAppend, StorageDecodeLength,
	},
	traits::{Get, GetDefault, StorageInfo, StorageInstance},
	Never,
};
use codec::{Decode, Encode, EncodeLike, FullCodec, MaxEncodedLen, Ref};
use sp_api::metadata_ir::StorageEntryMetadataIR;
use sp_runtime::traits::Saturating;
use sp_std::prelude::*;

/// A wrapper around a `StorageNMap` and a `StorageValue<Value=u32>` to keep track of how many items
/// are in a map, without needing to iterate over all of the values.
///
/// This storage item has some additional storage read and write overhead when manipulating values
/// compared to a regular storage map.
///
/// For functions where we only add or remove a value, a single storage read is needed to check if
/// that value already exists. For mutate functions, two storage reads are used to check if the
/// value existed before and after the mutation.
///
/// Whenever the counter needs to be updated, an additional read and write occurs to update that
/// counter.
pub struct CountedStorageNMap<
	Prefix,
	Key,
	Value,
	QueryKind = OptionQuery,
	OnEmpty = GetDefault,
	MaxValues = GetDefault,
>(core::marker::PhantomData<(Prefix, Key, Value, QueryKind, OnEmpty, MaxValues)>);

/// The requirement for an instance of [`CountedStorageNMap`].
pub trait CountedStorageNMapInstance: StorageInstance {
	/// The prefix to use for the counter storage value.
	type CounterPrefix: StorageInstance;
}

// Private helper trait to access map from counted storage n-map
trait MapWrapper {
	type Map;
}

impl<P: CountedStorageNMapInstance, K, V, Q, O, M> MapWrapper
	for CountedStorageNMap<P, K, V, Q, O, M>
{
	type Map = StorageNMap<P, K, V, Q, O, M>;
}

type CounterFor<P> =
	StorageValue<<P as CountedStorageNMapInstance>::CounterPrefix, u32, ValueQuery>;

/// On removal logic for updating counter while draining upon some prefix with
/// [`crate::storage::PrefixIterator`].
pub struct OnRemovalCounterUpdate<Prefix>(core::marker::PhantomData<Prefix>);

impl<Prefix: CountedStorageNMapInstance> crate::storage::PrefixIteratorOnRemoval
	for OnRemovalCounterUpdate<Prefix>
{
	fn on_removal(_key: &[u8], _value: &[u8]) {
		CounterFor::<Prefix>::mutate(|value| value.saturating_dec());
	}
}

impl<Prefix, Key, Value, QueryKind, OnEmpty, MaxValues>
	CountedStorageNMap<Prefix, Key, Value, QueryKind, OnEmpty, MaxValues>
where
	Prefix: CountedStorageNMapInstance,
	Key: super::key::KeyGenerator,
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
		use crate::storage::generator::StorageNMap;
		<Self as MapWrapper>::Map::prefix_hash()
	}

	/// Get the storage key used to fetch a value corresponding to a specific key.
	pub fn hashed_key_for<KArg: EncodeLikeTuple<Key::KArg> + TupleToEncodedIter>(
		key: KArg,
	) -> Vec<u8> {
		<Self as MapWrapper>::Map::hashed_key_for(key)
	}

	/// Does the value (explicitly) exist in storage?
	pub fn contains_key<KArg: EncodeLikeTuple<Key::KArg> + TupleToEncodedIter>(key: KArg) -> bool {
		<Self as MapWrapper>::Map::contains_key(key)
	}

	/// Load the value associated with the given key from the map.
	pub fn get<KArg: EncodeLikeTuple<Key::KArg> + TupleToEncodedIter>(
		key: KArg,
	) -> QueryKind::Query {
		<Self as MapWrapper>::Map::get(key)
	}

	/// Try to get the value for the given key from the map.
	///
	/// Returns `Ok` if it exists, `Err` if not.
	pub fn try_get<KArg: EncodeLikeTuple<Key::KArg> + TupleToEncodedIter>(
		key: KArg,
	) -> Result<Value, ()> {
		<Self as MapWrapper>::Map::try_get(key)
	}

	/// Store or remove the value to be associated with `key` so that `get` returns the `query`.
	/// It decrements the counter when the value is removed.
	pub fn set<KArg: EncodeLikeTuple<Key::KArg> + TupleToEncodedIter>(
		key: KArg,
		query: QueryKind::Query,
	) {
		let option = QueryKind::from_query_to_optional_value(query);
		if option.is_none() {
			CounterFor::<Prefix>::mutate(|value| value.saturating_dec());
		}
		<Self as MapWrapper>::Map::set(key, QueryKind::from_optional_value_to_query(option))
	}

	/// Take a value from storage, removing it afterwards.
	pub fn take<KArg: EncodeLikeTuple<Key::KArg> + TupleToEncodedIter>(
		key: KArg,
	) -> QueryKind::Query {
		let removed_value =
			<Self as MapWrapper>::Map::mutate_exists(key, |value| core::mem::replace(value, None));
		if removed_value.is_some() {
			CounterFor::<Prefix>::mutate(|value| value.saturating_dec());
		}
		QueryKind::from_optional_value_to_query(removed_value)
	}

	/// Swap the values of two key-pairs.
	pub fn swap<KOther, KArg1, KArg2>(key1: KArg1, key2: KArg2)
	where
		KOther: KeyGenerator,
		KArg1: EncodeLikeTuple<Key::KArg> + TupleToEncodedIter,
		KArg2: EncodeLikeTuple<KOther::KArg> + TupleToEncodedIter,
	{
		<Self as MapWrapper>::Map::swap::<KOther, _, _>(key1, key2)
	}

	/// Store a value to be associated with the given keys from the map.
	pub fn insert<KArg, VArg>(key: KArg, val: VArg)
	where
		KArg: EncodeLikeTuple<Key::KArg> + EncodeLike<Key::KArg> + TupleToEncodedIter,
		VArg: EncodeLike<Value>,
	{
		if !<Self as MapWrapper>::Map::contains_key(Ref::from(&key)) {
			CounterFor::<Prefix>::mutate(|value| value.saturating_inc());
		}
		<Self as MapWrapper>::Map::insert(key, val)
	}

	/// Remove the value under the given keys.
	pub fn remove<KArg: EncodeLikeTuple<Key::KArg> + EncodeLike<Key::KArg> + TupleToEncodedIter>(
		key: KArg,
	) {
		if <Self as MapWrapper>::Map::contains_key(Ref::from(&key)) {
			CounterFor::<Prefix>::mutate(|value| value.saturating_dec());
		}
		<Self as MapWrapper>::Map::remove(key)
	}

	/// Attempt to remove items from the map matching a `partial_key` prefix.
	///
	/// Returns [`MultiRemovalResults`](sp_io::MultiRemovalResults) to inform about the result. Once
	/// the resultant `maybe_cursor` field is `None`, then no further items remain to be deleted.
	///
	/// NOTE: After the initial call for any given map, it is important that no further items
	/// are inserted into the map which match the `partial key`. If so, then the map may not be
	/// empty when the resultant `maybe_cursor` is `None`.
	///
	/// # Limit
	///
	/// A `limit` must be provided in order to cap the maximum
	/// amount of deletions done in a single call. This is one fewer than the
	/// maximum number of backend iterations which may be done by this operation and as such
	/// represents the maximum number of backend deletions which may happen. A `limit` of zero
	/// implies that no keys will be deleted, though there may be a single iteration done.
	///
	/// # Cursor
	///
	/// A *cursor* may be passed in to this operation with `maybe_cursor`. `None` should only be
	/// passed once (in the initial call) for any given storage map and `partial_key`. Subsequent
	/// calls operating on the same map/`partial_key` should always pass `Some`, and this should be
	/// equal to the previous call result's `maybe_cursor` field.
	pub fn clear_prefix<KP>(
		partial_key: KP,
		limit: u32,
		maybe_cursor: Option<&[u8]>,
	) -> sp_io::MultiRemovalResults
	where
		Key: HasKeyPrefix<KP>,
	{
		let result = <Self as MapWrapper>::Map::clear_prefix(partial_key, limit, maybe_cursor);
		match result.maybe_cursor {
			None => CounterFor::<Prefix>::kill(),
			Some(_) => CounterFor::<Prefix>::mutate(|x| x.saturating_reduce(result.unique)),
		}
		result
	}

	/// Iterate over values that share the first key.
	pub fn iter_prefix_values<KP>(partial_key: KP) -> PrefixIterator<Value>
	where
		Key: HasKeyPrefix<KP>,
	{
		<Self as MapWrapper>::Map::iter_prefix_values(partial_key)
	}

	/// Mutate the value under the given keys.
	pub fn mutate<KArg, R, F>(key: KArg, f: F) -> R
	where
		KArg: EncodeLikeTuple<Key::KArg> + TupleToEncodedIter,
		F: FnOnce(&mut QueryKind::Query) -> R,
	{
		Self::try_mutate(key, |v| Ok::<R, Never>(f(v)))
			.expect("`Never` can not be constructed; qed")
	}

	/// Mutate the value under the given keys when the closure returns `Ok`.
	pub fn try_mutate<KArg, R, E, F>(key: KArg, f: F) -> Result<R, E>
	where
		KArg: EncodeLikeTuple<Key::KArg> + TupleToEncodedIter,
		F: FnOnce(&mut QueryKind::Query) -> Result<R, E>,
	{
		Self::try_mutate_exists(key, |option_value_ref| {
			let option_value = core::mem::replace(option_value_ref, None);
			let mut query = QueryKind::from_optional_value_to_query(option_value);
			let res = f(&mut query);
			let option_value = QueryKind::from_query_to_optional_value(query);
			let _ = core::mem::replace(option_value_ref, option_value);
			res
		})
	}

	/// Mutate the value under the given keys. Deletes the item if mutated to a `None`.
	pub fn mutate_exists<KArg, R, F>(key: KArg, f: F) -> R
	where
		KArg: EncodeLikeTuple<Key::KArg> + TupleToEncodedIter,
		F: FnOnce(&mut Option<Value>) -> R,
	{
		Self::try_mutate_exists(key, |v| Ok::<R, Never>(f(v)))
			.expect("`Never` can not be constructed; qed")
	}

	/// Mutate the item, only if an `Ok` value is returned. Deletes the item if mutated to a `None`.
	/// `f` will always be called with an option representing if the storage item exists (`Some<V>`)
	/// or if the storage item does not exist (`None`), independent of the `QueryType`.
	pub fn try_mutate_exists<KArg, R, E, F>(key: KArg, f: F) -> Result<R, E>
	where
		KArg: EncodeLikeTuple<Key::KArg> + TupleToEncodedIter,
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

	/// Append the given item to the value in the storage.
	///
	/// `Value` is required to implement [`StorageAppend`].
	///
	/// # Warning
	///
	/// If the storage item is not encoded properly, the storage will be overwritten
	/// and set to `[item]`. Any default value set for the storage item will be ignored
	/// on overwrite.
	pub fn append<Item, EncodeLikeItem, KArg>(key: KArg, item: EncodeLikeItem)
	where
		KArg: EncodeLikeTuple<Key::KArg> + EncodeLike<Key::KArg> + TupleToEncodedIter,
		Item: Encode,
		EncodeLikeItem: EncodeLike<Item>,
		Value: StorageAppend<Item>,
	{
		if !<Self as MapWrapper>::Map::contains_key(Ref::from(&key)) {
			CounterFor::<Prefix>::mutate(|value| value.saturating_inc());
		}
		<Self as MapWrapper>::Map::append(key, item)
	}

	/// Read the length of the storage value without decoding the entire value under the
	/// given `key1` and `key2`.
	///
	/// `Value` is required to implement [`StorageDecodeLength`].
	///
	/// If the value does not exists or it fails to decode the length, `None` is returned.
	/// Otherwise `Some(len)` is returned.
	///
	/// # Warning
	///
	/// `None` does not mean that `get()` does not return a value. The default value is completly
	/// ignored by this function.
	pub fn decode_len<KArg: EncodeLikeTuple<Key::KArg> + TupleToEncodedIter>(
		key: KArg,
	) -> Option<usize>
	where
		Value: StorageDecodeLength,
	{
		<Self as MapWrapper>::Map::decode_len(key)
	}

	/// Migrate an item with the given `key` from defunct `hash_fns` to the current hashers.
	///
	/// If the key doesn't exist, then it's a no-op. If it does, then it returns its value.
	pub fn migrate_keys<KArg>(key: KArg, hash_fns: Key::HArg) -> Option<Value>
	where
		KArg: EncodeLikeTuple<Key::KArg> + TupleToEncodedIter,
	{
		<Self as MapWrapper>::Map::migrate_keys::<_>(key, hash_fns)
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
	pub fn clear(limit: u32, maybe_cursor: Option<&[u8]>) -> sp_io::MultiRemovalResults {
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
	pub fn iter_values() -> crate::storage::PrefixIterator<Value> {
		<Self as MapWrapper>::Map::iter_values()
	}

	/// Translate the values of all elements by a function `f`, in the map in no particular order.
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

impl<Prefix, Key, Value, QueryKind, OnEmpty, MaxValues>
	CountedStorageNMap<Prefix, Key, Value, QueryKind, OnEmpty, MaxValues>
where
	Prefix: CountedStorageNMapInstance,
	Key: super::key::ReversibleKeyGenerator,
	Value: FullCodec,
	QueryKind: QueryKindTrait<Value, OnEmpty>,
	OnEmpty: Get<QueryKind::Query> + 'static,
	MaxValues: Get<Option<u32>>,
{
	/// Enumerate all elements in the map with prefix key `kp` in no particular order.
	///
	/// If you add or remove values whose prefix key is `kp` to the map while doing this, you'll get
	/// undefined results.
	pub fn iter_prefix<KP>(
		kp: KP,
	) -> crate::storage::PrefixIterator<(<Key as HasKeyPrefix<KP>>::Suffix, Value)>
	where
		Key: HasReversibleKeyPrefix<KP>,
	{
		<Self as MapWrapper>::Map::iter_prefix(kp)
	}

	/// Enumerate all elements in the map with prefix key `kp` after a specified `starting_raw_key`
	/// in no particular order.
	///
	/// If you add or remove values whose prefix key is `kp` to the map while doing this, you'll get
	/// undefined results.
	pub fn iter_prefix_from<KP>(
		kp: KP,
		starting_raw_key: Vec<u8>,
	) -> crate::storage::PrefixIterator<
		(<Key as HasKeyPrefix<KP>>::Suffix, Value),
		OnRemovalCounterUpdate<Prefix>,
	>
	where
		Key: HasReversibleKeyPrefix<KP>,
	{
		<Self as MapWrapper>::Map::iter_prefix_from(kp, starting_raw_key).convert_on_removal()
	}

	/// Enumerate all suffix keys in the map with prefix key `kp` in no particular order.
	///
	/// If you add or remove values whose prefix key is `kp` to the map while doing this, you'll get
	/// undefined results.
	pub fn iter_key_prefix<KP>(
		kp: KP,
	) -> crate::storage::KeyPrefixIterator<<Key as HasKeyPrefix<KP>>::Suffix>
	where
		Key: HasReversibleKeyPrefix<KP>,
	{
		<Self as MapWrapper>::Map::iter_key_prefix(kp)
	}

	/// Enumerate all suffix keys in the map with prefix key `kp` after a specified
	/// `starting_raw_key` in no particular order.
	///
	/// If you add or remove values whose prefix key is `kp` to the map while doing this, you'll get
	/// undefined results.
	pub fn iter_key_prefix_from<KP>(
		kp: KP,
		starting_raw_key: Vec<u8>,
	) -> crate::storage::KeyPrefixIterator<<Key as HasKeyPrefix<KP>>::Suffix>
	where
		Key: HasReversibleKeyPrefix<KP>,
	{
		<Self as MapWrapper>::Map::iter_key_prefix_from(kp, starting_raw_key)
	}

	/// Remove all elements from the map with prefix key `kp` and iterate through them in no
	/// particular order.
	///
	/// If you add elements with prefix key `k1` to the map while doing this, you'll get undefined
	/// results.
	pub fn drain_prefix<KP>(
		kp: KP,
	) -> crate::storage::PrefixIterator<
		(<Key as HasKeyPrefix<KP>>::Suffix, Value),
		OnRemovalCounterUpdate<Prefix>,
	>
	where
		Key: HasReversibleKeyPrefix<KP>,
	{
		<Self as MapWrapper>::Map::drain_prefix(kp).convert_on_removal()
	}

	/// Enumerate all elements in the map in no particular order.
	///
	/// If you add or remove values to the map while doing this, you'll get undefined results.
	pub fn iter(
	) -> crate::storage::PrefixIterator<(Key::Key, Value), OnRemovalCounterUpdate<Prefix>> {
		<Self as MapWrapper>::Map::iter().convert_on_removal()
	}

	/// Enumerate all elements in the map after a specified `starting_key` in no particular order.
	///
	/// If you add or remove values to the map while doing this, you'll get undefined results.
	pub fn iter_from(
		starting_raw_key: Vec<u8>,
	) -> crate::storage::PrefixIterator<(Key::Key, Value), OnRemovalCounterUpdate<Prefix>> {
		<Self as MapWrapper>::Map::iter_from(starting_raw_key).convert_on_removal()
	}

	/// Enumerate all keys in the map in no particular order.
	///
	/// If you add or remove values to the map while doing this, you'll get undefined results.
	pub fn iter_keys() -> crate::storage::KeyPrefixIterator<Key::Key> {
		<Self as MapWrapper>::Map::iter_keys()
	}

	/// Enumerate all keys in the map after a specified `starting_raw_key` in no particular order.
	///
	/// If you add or remove values to the map while doing this, you'll get undefined results.
	pub fn iter_keys_from(
		starting_raw_key: Vec<u8>,
	) -> crate::storage::KeyPrefixIterator<Key::Key> {
		<Self as MapWrapper>::Map::iter_keys_from(starting_raw_key)
	}

	/// Remove all elements from the map and iterate through them in no particular order.
	///
	/// If you add elements to the map while doing this, you'll get undefined results.
	pub fn drain(
	) -> crate::storage::PrefixIterator<(Key::Key, Value), OnRemovalCounterUpdate<Prefix>> {
		<Self as MapWrapper>::Map::drain().convert_on_removal()
	}

	/// Translate the values of all elements by a function `f`, in the map in no particular order.
	///
	/// By returning `None` from `f` for an element, you'll remove it from the map.
	///
	/// NOTE: If a value can't be decoded because the storage is corrupted, then it is skipped.
	pub fn translate<O: Decode, F: FnMut(Key::Key, O) -> Option<Value>>(mut f: F) {
		<Self as MapWrapper>::Map::translate(|key, old_value| {
			let res = f(key, old_value);
			if res.is_none() {
				CounterFor::<Prefix>::mutate(|value| value.saturating_dec());
			}
			res
		})
	}
}

impl<Prefix, Key, Value, QueryKind, OnEmpty, MaxValues> StorageEntryMetadataBuilder
	for CountedStorageNMap<Prefix, Key, Value, QueryKind, OnEmpty, MaxValues>
where
	Prefix: CountedStorageNMapInstance,
	Key: super::key::KeyGenerator,
	Value: FullCodec + scale_info::StaticTypeInfo,
	QueryKind: QueryKindTrait<Value, OnEmpty>,
	OnEmpty: Get<QueryKind::Query> + 'static,
	MaxValues: Get<Option<u32>>,
{
	fn build_metadata(docs: Vec<&'static str>, entries: &mut Vec<StorageEntryMetadataIR>) {
		<Self as MapWrapper>::Map::build_metadata(docs, entries);
		CounterFor::<Prefix>::build_metadata(
			vec![&"Counter for the related counted storage map"],
			entries,
		);
	}
}

impl<Prefix, Key, Value, QueryKind, OnEmpty, MaxValues> crate::traits::StorageInfoTrait
	for CountedStorageNMap<Prefix, Key, Value, QueryKind, OnEmpty, MaxValues>
where
	Prefix: CountedStorageNMapInstance,
	Key: super::key::KeyGenerator + super::key::KeyGeneratorMaxEncodedLen,
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
impl<Prefix, Key, Value, QueryKind, OnEmpty, MaxValues> crate::traits::PartialStorageInfoTrait
	for CountedStorageNMap<Prefix, Key, Value, QueryKind, OnEmpty, MaxValues>
where
	Prefix: CountedStorageNMapInstance,
	Key: super::key::KeyGenerator,
	Value: FullCodec,
	QueryKind: QueryKindTrait<Value, OnEmpty>,
	OnEmpty: Get<QueryKind::Query> + 'static,
	MaxValues: Get<Option<u32>>,
{
	fn partial_storage_info() -> Vec<StorageInfo> {
		[
			<Self as MapWrapper>::Map::partial_storage_info(),
			CounterFor::<Prefix>::partial_storage_info(),
		]
		.concat()
	}
}

#[cfg(test)]
mod test {
	use super::*;
	use crate::{
		hash::{StorageHasher as _, *},
		storage::types::{Key as NMapKey, ValueQuery},
	};
	use sp_api::metadata_ir::{StorageEntryModifierIR, StorageEntryTypeIR, StorageHasherIR};
	use sp_io::{hashing::twox_128, TestExternalities};

	struct Prefix;
	impl StorageInstance for Prefix {
		fn pallet_prefix() -> &'static str {
			"test"
		}
		const STORAGE_PREFIX: &'static str = "Foo";
	}
	impl CountedStorageNMapInstance for Prefix {
		type CounterPrefix = Prefix;
	}

	struct ADefault;
	impl crate::traits::Get<u32> for ADefault {
		fn get() -> u32 {
			98
		}
	}

	#[test]
	fn test_1_key() {
		type A = CountedStorageNMap<Prefix, NMapKey<Blake2_128Concat, u16>, u32, OptionQuery>;
		type AValueQueryWithAnOnEmpty =
			CountedStorageNMap<Prefix, NMapKey<Blake2_128Concat, u16>, u32, ValueQuery, ADefault>;
		type B = CountedStorageNMap<Prefix, NMapKey<Blake2_256, u16>, u32, ValueQuery>;
		type C = CountedStorageNMap<Prefix, NMapKey<Blake2_128Concat, u16>, u8, ValueQuery>;
		type WithLen = CountedStorageNMap<Prefix, NMapKey<Blake2_128Concat, u16>, Vec<u32>>;

		TestExternalities::default().execute_with(|| {
			let mut k: Vec<u8> = vec![];
			k.extend(&twox_128(b"test"));
			k.extend(&twox_128(b"Foo"));
			k.extend(&3u16.blake2_128_concat());
			assert_eq!(A::hashed_key_for((&3,)).to_vec(), k);

			assert_eq!(A::contains_key((3,)), false);
			assert_eq!(A::get((3,)), None);
			assert_eq!(AValueQueryWithAnOnEmpty::get((3,)), 98);
			assert_eq!(A::count(), 0);

			A::insert((3,), 10);
			assert_eq!(A::contains_key((3,)), true);
			assert_eq!(A::get((3,)), Some(10));
			assert_eq!(AValueQueryWithAnOnEmpty::get((3,)), 10);
			assert_eq!(A::count(), 1);

			A::swap::<NMapKey<Blake2_128Concat, u16>, _, _>((3,), (2,));
			assert_eq!(A::contains_key((3,)), false);
			assert_eq!(A::contains_key((2,)), true);
			assert_eq!(A::get((3,)), None);
			assert_eq!(AValueQueryWithAnOnEmpty::get((3,)), 98);
			assert_eq!(A::get((2,)), Some(10));
			assert_eq!(AValueQueryWithAnOnEmpty::get((2,)), 10);
			assert_eq!(A::count(), 1);

			A::remove((2,));
			assert_eq!(A::contains_key((2,)), false);
			assert_eq!(A::get((2,)), None);
			assert_eq!(A::count(), 0);

			AValueQueryWithAnOnEmpty::mutate((2,), |v| *v = *v * 2);
			AValueQueryWithAnOnEmpty::mutate((2,), |v| *v = *v * 2);
			assert_eq!(A::contains_key((2,)), true);
			assert_eq!(A::get((2,)), Some(98 * 4));
			assert_eq!(A::count(), 1);

			A::remove((2,));
			let _: Result<(), ()> = AValueQueryWithAnOnEmpty::try_mutate((2,), |v| {
				*v = *v * 2;
				Ok(())
			});
			let _: Result<(), ()> = AValueQueryWithAnOnEmpty::try_mutate((2,), |v| {
				*v = *v * 2;
				Ok(())
			});
			assert_eq!(A::contains_key((2,)), true);
			assert_eq!(A::get((2,)), Some(98 * 4));
			assert_eq!(A::count(), 1);

			A::remove((2,));
			let _: Result<(), ()> = AValueQueryWithAnOnEmpty::try_mutate((2,), |v| {
				*v = *v * 2;
				Err(())
			});
			assert_eq!(A::contains_key((2,)), false);
			assert_eq!(A::count(), 0);

			A::remove((2,));
			AValueQueryWithAnOnEmpty::mutate_exists((2,), |v| {
				assert!(v.is_none());
				*v = Some(10);
			});
			assert_eq!(A::contains_key((2,)), true);
			assert_eq!(A::get((2,)), Some(10));
			AValueQueryWithAnOnEmpty::mutate_exists((2,), |v| {
				*v = Some(v.unwrap() * 10);
			});
			assert_eq!(A::contains_key((2,)), true);
			assert_eq!(A::get((2,)), Some(100));
			assert_eq!(A::count(), 1);

			A::remove((2,));
			let _: Result<(), ()> = AValueQueryWithAnOnEmpty::try_mutate_exists((2,), |v| {
				assert!(v.is_none());
				*v = Some(10);
				Ok(())
			});
			assert_eq!(A::contains_key((2,)), true);
			assert_eq!(A::get((2,)), Some(10));
			let _: Result<(), ()> = AValueQueryWithAnOnEmpty::try_mutate_exists((2,), |v| {
				*v = Some(v.unwrap() * 10);
				Ok(())
			});
			assert_eq!(A::contains_key((2,)), true);
			assert_eq!(A::get((2,)), Some(100));
			assert_eq!(A::try_get((2,)), Ok(100));
			let _: Result<(), ()> = AValueQueryWithAnOnEmpty::try_mutate_exists((2,), |v| {
				*v = Some(v.unwrap() * 10);
				Err(())
			});
			assert_eq!(A::contains_key((2,)), true);
			assert_eq!(A::get((2,)), Some(100));
			assert_eq!(A::count(), 1);

			A::insert((2,), 10);
			assert_eq!(A::take((2,)), Some(10));
			assert_eq!(A::contains_key((2,)), false);
			assert_eq!(AValueQueryWithAnOnEmpty::take((2,)), 98);
			assert_eq!(A::contains_key((2,)), false);
			assert_eq!(A::try_get((2,)), Err(()));
			assert_eq!(A::count(), 0);

			B::insert((2,), 10);
			assert_eq!(
				A::migrate_keys((2,), (Box::new(|key| Blake2_256::hash(key).to_vec()),),),
				Some(10)
			);
			assert_eq!(A::contains_key((2,)), true);
			assert_eq!(A::get((2,)), Some(10));
			assert_eq!(A::count(), 1);

			A::insert((3,), 10);
			A::insert((4,), 10);
			assert_eq!(A::count(), 3);
			let _ = A::clear(u32::max_value(), None);
			assert!(!A::contains_key((2,)) && !A::contains_key((3,)) && !A::contains_key((4,)));
			assert_eq!(A::count(), 0);

			A::insert((3,), 10);
			A::insert((4,), 10);
			assert_eq!(A::iter_values().collect::<Vec<_>>(), vec![10, 10]);
			assert_eq!(A::count(), 2);

			C::insert((3,), 10);
			C::insert((4,), 10);
			A::translate_values::<u8, _>(|v| Some((v * 2).into()));
			assert_eq!(A::iter().collect::<Vec<_>>(), vec![(4, 20), (3, 20)]);
			assert_eq!(A::count(), 2);

			A::insert((3,), 10);
			A::insert((4,), 10);
			assert_eq!(A::iter().collect::<Vec<_>>(), vec![(4, 10), (3, 10)]);
			assert_eq!(A::drain().collect::<Vec<_>>(), vec![(4, 10), (3, 10)]);
			assert_eq!(A::iter().collect::<Vec<_>>(), vec![]);
			assert_eq!(A::count(), 0);

			C::insert((3,), 10);
			C::insert((4,), 10);
			A::translate::<u8, _>(|k1, v| Some((k1 as u16 * v as u16).into()));
			assert_eq!(A::iter().collect::<Vec<_>>(), vec![(4, 40), (3, 30)]);
			assert_eq!(A::count(), 2);

			let mut entries = vec![];
			A::build_metadata(vec![], &mut entries);
			AValueQueryWithAnOnEmpty::build_metadata(vec![], &mut entries);
			assert_eq!(
				entries,
				vec![
					StorageEntryMetadataIR {
						name: "Foo",
						modifier: StorageEntryModifierIR::Optional,
						ty: StorageEntryTypeIR::Map {
							hashers: vec![StorageHasherIR::Blake2_128Concat],
							key: scale_info::meta_type::<u16>(),
							value: scale_info::meta_type::<u32>(),
						},
						default: Option::<u32>::None.encode(),
						docs: vec![],
					},
					StorageEntryMetadataIR {
						name: "Foo",
						modifier: StorageEntryModifierIR::Default,
						ty: StorageEntryTypeIR::Plain(scale_info::meta_type::<u32>()),
						default: vec![0, 0, 0, 0],
						docs: if cfg!(feature = "no-metadata-docs") {
							vec![]
						} else {
							vec!["Counter for the related counted storage map"]
						},
					},
					StorageEntryMetadataIR {
						name: "Foo",
						modifier: StorageEntryModifierIR::Default,
						ty: StorageEntryTypeIR::Map {
							hashers: vec![StorageHasherIR::Blake2_128Concat],
							key: scale_info::meta_type::<u16>(),
							value: scale_info::meta_type::<u32>(),
						},
						default: 98u32.encode(),
						docs: vec![],
					},
					StorageEntryMetadataIR {
						name: "Foo",
						modifier: StorageEntryModifierIR::Default,
						ty: StorageEntryTypeIR::Plain(scale_info::meta_type::<u32>()),
						default: vec![0, 0, 0, 0],
						docs: if cfg!(feature = "no-metadata-docs") {
							vec![]
						} else {
							vec!["Counter for the related counted storage map"]
						},
					},
				]
			);

			let _ = WithLen::clear(u32::max_value(), None);
			assert_eq!(WithLen::decode_len((3,)), None);
			WithLen::append((0,), 10);
			assert_eq!(WithLen::decode_len((0,)), Some(1));
		});
	}

	#[test]
	fn test_2_keys() {
		type A = CountedStorageNMap<
			Prefix,
			(NMapKey<Blake2_128Concat, u16>, NMapKey<Twox64Concat, u8>),
			u32,
			OptionQuery,
		>;
		type AValueQueryWithAnOnEmpty = CountedStorageNMap<
			Prefix,
			(NMapKey<Blake2_128Concat, u16>, NMapKey<Twox64Concat, u8>),
			u32,
			ValueQuery,
			ADefault,
		>;
		type B = CountedStorageNMap<
			Prefix,
			(NMapKey<Blake2_256, u16>, NMapKey<Twox128, u8>),
			u32,
			ValueQuery,
		>;
		type C = CountedStorageNMap<
			Prefix,
			(NMapKey<Blake2_128Concat, u16>, NMapKey<Twox64Concat, u8>),
			u8,
			ValueQuery,
		>;
		type WithLen = CountedStorageNMap<
			Prefix,
			(NMapKey<Blake2_128Concat, u16>, NMapKey<Twox64Concat, u8>),
			Vec<u32>,
		>;

		TestExternalities::default().execute_with(|| {
			let mut k: Vec<u8> = vec![];
			k.extend(&twox_128(b"test"));
			k.extend(&twox_128(b"Foo"));
			k.extend(&3u16.blake2_128_concat());
			k.extend(&30u8.twox_64_concat());
			assert_eq!(A::hashed_key_for((3, 30)).to_vec(), k);

			assert_eq!(A::contains_key((3, 30)), false);
			assert_eq!(A::get((3, 30)), None);
			assert_eq!(AValueQueryWithAnOnEmpty::get((3, 30)), 98);
			assert_eq!(A::count(), 0);

			A::insert((3, 30), 10);
			assert_eq!(A::contains_key((3, 30)), true);
			assert_eq!(A::get((3, 30)), Some(10));
			assert_eq!(AValueQueryWithAnOnEmpty::get((3, 30)), 10);
			assert_eq!(A::count(), 1);

			A::swap::<(NMapKey<Blake2_128Concat, u16>, NMapKey<Twox64Concat, u8>), _, _>(
				(3, 30),
				(2, 20),
			);
			assert_eq!(A::contains_key((3, 30)), false);
			assert_eq!(A::contains_key((2, 20)), true);
			assert_eq!(A::get((3, 30)), None);
			assert_eq!(AValueQueryWithAnOnEmpty::get((3, 30)), 98);
			assert_eq!(A::get((2, 20)), Some(10));
			assert_eq!(AValueQueryWithAnOnEmpty::get((2, 20)), 10);
			assert_eq!(A::count(), 1);

			A::remove((2, 20));
			assert_eq!(A::contains_key((2, 20)), false);
			assert_eq!(A::get((2, 20)), None);
			assert_eq!(A::count(), 0);

			AValueQueryWithAnOnEmpty::mutate((2, 20), |v| *v = *v * 2);
			AValueQueryWithAnOnEmpty::mutate((2, 20), |v| *v = *v * 2);
			assert_eq!(A::contains_key((2, 20)), true);
			assert_eq!(A::get((2, 20)), Some(98 * 4));
			assert_eq!(A::count(), 1);

			A::remove((2, 20));
			let _: Result<(), ()> = AValueQueryWithAnOnEmpty::try_mutate((2, 20), |v| {
				*v = *v * 2;
				Err(())
			});
			assert_eq!(A::contains_key((2, 20)), false);
			assert_eq!(A::count(), 0);

			A::remove((2, 20));
			let _: Result<(), ()> = AValueQueryWithAnOnEmpty::try_mutate((2, 20), |v| {
				*v = *v * 2;
				Err(())
			});
			assert_eq!(A::contains_key((2, 20)), false);
			assert_eq!(A::count(), 0);

			A::remove((2, 20));
			AValueQueryWithAnOnEmpty::mutate_exists((2, 20), |v| {
				assert!(v.is_none());
				*v = Some(10);
			});
			assert_eq!(A::contains_key((2, 20)), true);
			assert_eq!(A::get((2, 20)), Some(10));
			assert_eq!(A::count(), 1);
			AValueQueryWithAnOnEmpty::mutate_exists((2, 20), |v| {
				*v = Some(v.unwrap() * 10);
			});
			assert_eq!(A::contains_key((2, 20)), true);
			assert_eq!(A::get((2, 20)), Some(100));
			assert_eq!(A::count(), 1);

			A::remove((2, 20));
			let _: Result<(), ()> = AValueQueryWithAnOnEmpty::try_mutate_exists((2, 20), |v| {
				assert!(v.is_none());
				*v = Some(10);
				Ok(())
			});
			assert_eq!(A::contains_key((2, 20)), true);
			assert_eq!(A::get((2, 20)), Some(10));
			let _: Result<(), ()> = AValueQueryWithAnOnEmpty::try_mutate_exists((2, 20), |v| {
				*v = Some(v.unwrap() * 10);
				Ok(())
			});
			assert_eq!(A::contains_key((2, 20)), true);
			assert_eq!(A::get((2, 20)), Some(100));
			assert_eq!(A::try_get((2, 20)), Ok(100));
			assert_eq!(A::count(), 1);
			let _: Result<(), ()> = AValueQueryWithAnOnEmpty::try_mutate_exists((2, 20), |v| {
				*v = Some(v.unwrap() * 10);
				Err(())
			});
			assert_eq!(A::contains_key((2, 20)), true);
			assert_eq!(A::get((2, 20)), Some(100));
			assert_eq!(A::count(), 1);

			A::insert((2, 20), 10);
			assert_eq!(A::take((2, 20)), Some(10));
			assert_eq!(A::contains_key((2, 20)), false);
			assert_eq!(AValueQueryWithAnOnEmpty::take((2, 20)), 98);
			assert_eq!(A::contains_key((2, 20)), false);
			assert_eq!(A::try_get((2, 20)), Err(()));
			assert_eq!(A::count(), 0);

			B::insert((2, 20), 10);
			assert_eq!(
				A::migrate_keys(
					(2, 20),
					(
						Box::new(|key| Blake2_256::hash(key).to_vec()),
						Box::new(|key| Twox128::hash(key).to_vec()),
					),
				),
				Some(10)
			);
			assert_eq!(A::contains_key((2, 20)), true);
			assert_eq!(A::get((2, 20)), Some(10));
			assert_eq!(A::count(), 1);

			A::insert((3, 30), 10);
			A::insert((4, 40), 10);
			assert_eq!(A::count(), 3);
			let _ = A::clear(u32::max_value(), None);
			// one of the item has been removed
			assert!(
				!A::contains_key((2, 20)) && !A::contains_key((3, 30)) && !A::contains_key((4, 40))
			);
			assert_eq!(A::count(), 0);

			assert_eq!(A::count(), 0);

			A::insert((3, 30), 10);
			A::insert((4, 40), 10);
			assert_eq!(A::iter_values().collect::<Vec<_>>(), vec![10, 10]);
			assert_eq!(A::count(), 2);

			C::insert((3, 30), 10);
			C::insert((4, 40), 10);
			A::translate_values::<u8, _>(|v| Some((v * 2).into()));
			assert_eq!(A::iter().collect::<Vec<_>>(), vec![((4, 40), 20), ((3, 30), 20)]);
			assert_eq!(A::count(), 2);

			A::insert((3, 30), 10);
			A::insert((4, 40), 10);
			assert_eq!(A::iter().collect::<Vec<_>>(), vec![((4, 40), 10), ((3, 30), 10)]);
			assert_eq!(A::drain().collect::<Vec<_>>(), vec![((4, 40), 10), ((3, 30), 10)]);
			assert_eq!(A::iter().collect::<Vec<_>>(), vec![]);
			assert_eq!(A::count(), 0);

			C::insert((3, 30), 10);
			C::insert((4, 40), 10);
			A::translate::<u8, _>(|(k1, k2), v| Some((k1 * k2 as u16 * v as u16).into()));
			assert_eq!(A::iter().collect::<Vec<_>>(), vec![((4, 40), 1600), ((3, 30), 900)]);
			assert_eq!(A::count(), 2);

			let mut entries = vec![];
			A::build_metadata(vec![], &mut entries);
			AValueQueryWithAnOnEmpty::build_metadata(vec![], &mut entries);
			assert_eq!(
				entries,
				vec![
					StorageEntryMetadataIR {
						name: "Foo",
						modifier: StorageEntryModifierIR::Optional,
						ty: StorageEntryTypeIR::Map {
							hashers: vec![
								StorageHasherIR::Blake2_128Concat,
								StorageHasherIR::Twox64Concat
							],
							key: scale_info::meta_type::<(u16, u8)>(),
							value: scale_info::meta_type::<u32>(),
						},
						default: Option::<u32>::None.encode(),
						docs: vec![],
					},
					StorageEntryMetadataIR {
						name: "Foo",
						modifier: StorageEntryModifierIR::Default,
						ty: StorageEntryTypeIR::Plain(scale_info::meta_type::<u32>()),
						default: vec![0, 0, 0, 0],
						docs: if cfg!(feature = "no-metadata-docs") {
							vec![]
						} else {
							vec!["Counter for the related counted storage map"]
						},
					},
					StorageEntryMetadataIR {
						name: "Foo",
						modifier: StorageEntryModifierIR::Default,
						ty: StorageEntryTypeIR::Map {
							hashers: vec![
								StorageHasherIR::Blake2_128Concat,
								StorageHasherIR::Twox64Concat
							],
							key: scale_info::meta_type::<(u16, u8)>(),
							value: scale_info::meta_type::<u32>(),
						},
						default: 98u32.encode(),
						docs: vec![],
					},
					StorageEntryMetadataIR {
						name: "Foo",
						modifier: StorageEntryModifierIR::Default,
						ty: StorageEntryTypeIR::Plain(scale_info::meta_type::<u32>()),
						default: vec![0, 0, 0, 0],
						docs: if cfg!(feature = "no-metadata-docs") {
							vec![]
						} else {
							vec!["Counter for the related counted storage map"]
						},
					},
				]
			);

			let _ = WithLen::clear(u32::max_value(), None);
			assert_eq!(WithLen::decode_len((3, 30)), None);
			WithLen::append((0, 100), 10);
			assert_eq!(WithLen::decode_len((0, 100)), Some(1));

			A::insert((3, 30), 11);
			A::insert((3, 31), 12);
			A::insert((4, 40), 13);
			A::insert((4, 41), 14);
			assert_eq!(A::iter_prefix_values((3,)).collect::<Vec<_>>(), vec![12, 11]);
			assert_eq!(A::iter_prefix_values((4,)).collect::<Vec<_>>(), vec![13, 14]);
			assert_eq!(A::count(), 5);
		});
	}

	#[test]
	fn test_3_keys() {
		type A = CountedStorageNMap<
			Prefix,
			(
				NMapKey<Blake2_128Concat, u16>,
				NMapKey<Blake2_128Concat, u16>,
				NMapKey<Twox64Concat, u16>,
			),
			u32,
			OptionQuery,
		>;
		type AValueQueryWithAnOnEmpty = CountedStorageNMap<
			Prefix,
			(
				NMapKey<Blake2_128Concat, u16>,
				NMapKey<Blake2_128Concat, u16>,
				NMapKey<Twox64Concat, u16>,
			),
			u32,
			ValueQuery,
			ADefault,
		>;
		type B = CountedStorageNMap<
			Prefix,
			(NMapKey<Blake2_256, u16>, NMapKey<Blake2_256, u16>, NMapKey<Twox128, u16>),
			u32,
			ValueQuery,
		>;
		type C = CountedStorageNMap<
			Prefix,
			(
				NMapKey<Blake2_128Concat, u16>,
				NMapKey<Blake2_128Concat, u16>,
				NMapKey<Twox64Concat, u16>,
			),
			u8,
			ValueQuery,
		>;
		type WithLen = CountedStorageNMap<
			Prefix,
			(
				NMapKey<Blake2_128Concat, u16>,
				NMapKey<Blake2_128Concat, u16>,
				NMapKey<Twox64Concat, u16>,
			),
			Vec<u32>,
		>;

		TestExternalities::default().execute_with(|| {
			let mut k: Vec<u8> = vec![];
			k.extend(&twox_128(b"test"));
			k.extend(&twox_128(b"Foo"));
			k.extend(&1u16.blake2_128_concat());
			k.extend(&10u16.blake2_128_concat());
			k.extend(&100u16.twox_64_concat());
			assert_eq!(A::hashed_key_for((1, 10, 100)).to_vec(), k);

			assert_eq!(A::contains_key((1, 10, 100)), false);
			assert_eq!(A::get((1, 10, 100)), None);
			assert_eq!(AValueQueryWithAnOnEmpty::get((1, 10, 100)), 98);
			assert_eq!(A::count(), 0);

			A::insert((1, 10, 100), 30);
			assert_eq!(A::contains_key((1, 10, 100)), true);
			assert_eq!(A::get((1, 10, 100)), Some(30));
			assert_eq!(AValueQueryWithAnOnEmpty::get((1, 10, 100)), 30);
			assert_eq!(A::count(), 1);

			A::swap::<
				(
					NMapKey<Blake2_128Concat, u16>,
					NMapKey<Blake2_128Concat, u16>,
					NMapKey<Twox64Concat, u16>,
				),
				_,
				_,
			>((1, 10, 100), (2, 20, 200));
			assert_eq!(A::contains_key((1, 10, 100)), false);
			assert_eq!(A::contains_key((2, 20, 200)), true);
			assert_eq!(A::get((1, 10, 100)), None);
			assert_eq!(AValueQueryWithAnOnEmpty::get((1, 10, 100)), 98);
			assert_eq!(A::get((2, 20, 200)), Some(30));
			assert_eq!(AValueQueryWithAnOnEmpty::get((2, 20, 200)), 30);
			assert_eq!(A::count(), 1);

			A::remove((2, 20, 200));
			assert_eq!(A::contains_key((2, 20, 200)), false);
			assert_eq!(A::get((2, 20, 200)), None);
			assert_eq!(A::count(), 0);

			AValueQueryWithAnOnEmpty::mutate((2, 20, 200), |v| *v = *v * 2);
			AValueQueryWithAnOnEmpty::mutate((2, 20, 200), |v| *v = *v * 2);
			assert_eq!(A::contains_key((2, 20, 200)), true);
			assert_eq!(A::get((2, 20, 200)), Some(98 * 4));
			assert_eq!(A::count(), 1);

			A::remove((2, 20, 200));
			let _: Result<(), ()> = AValueQueryWithAnOnEmpty::try_mutate((2, 20, 200), |v| {
				*v = *v * 2;
				Err(())
			});
			assert_eq!(A::contains_key((2, 20, 200)), false);
			assert_eq!(A::count(), 0);

			A::remove((2, 20, 200));
			AValueQueryWithAnOnEmpty::mutate_exists((2, 20, 200), |v| {
				assert!(v.is_none());
				*v = Some(10);
			});
			assert_eq!(A::contains_key((2, 20, 200)), true);
			assert_eq!(A::get((2, 20, 200)), Some(10));
			assert_eq!(A::count(), 1);
			AValueQueryWithAnOnEmpty::mutate_exists((2, 20, 200), |v| {
				*v = Some(v.unwrap() * 10);
			});
			assert_eq!(A::contains_key((2, 20, 200)), true);
			assert_eq!(A::get((2, 20, 200)), Some(100));
			assert_eq!(A::count(), 1);

			A::remove((2, 20, 200));
			let _: Result<(), ()> =
				AValueQueryWithAnOnEmpty::try_mutate_exists((2, 20, 200), |v| {
					assert!(v.is_none());
					*v = Some(10);
					Ok(())
				});
			assert_eq!(A::contains_key((2, 20, 200)), true);
			assert_eq!(A::get((2, 20, 200)), Some(10));
			let _: Result<(), ()> =
				AValueQueryWithAnOnEmpty::try_mutate_exists((2, 20, 200), |v| {
					*v = Some(v.unwrap() * 10);
					Ok(())
				});
			assert_eq!(A::contains_key((2, 20, 200)), true);
			assert_eq!(A::get((2, 20, 200)), Some(100));
			assert_eq!(A::try_get((2, 20, 200)), Ok(100));
			assert_eq!(A::count(), 1);
			let _: Result<(), ()> =
				AValueQueryWithAnOnEmpty::try_mutate_exists((2, 20, 200), |v| {
					*v = Some(v.unwrap() * 10);
					Err(())
				});
			assert_eq!(A::contains_key((2, 20, 200)), true);
			assert_eq!(A::get((2, 20, 200)), Some(100));
			assert_eq!(A::count(), 1);

			A::insert((2, 20, 200), 10);
			assert_eq!(A::take((2, 20, 200)), Some(10));
			assert_eq!(A::contains_key((2, 20, 200)), false);
			assert_eq!(AValueQueryWithAnOnEmpty::take((2, 20, 200)), 98);
			assert_eq!(A::contains_key((2, 20, 200)), false);
			assert_eq!(A::try_get((2, 20, 200)), Err(()));
			assert_eq!(A::count(), 0);

			B::insert((2, 20, 200), 10);
			assert_eq!(
				A::migrate_keys(
					(2, 20, 200),
					(
						Box::new(|key| Blake2_256::hash(key).to_vec()),
						Box::new(|key| Blake2_256::hash(key).to_vec()),
						Box::new(|key| Twox128::hash(key).to_vec()),
					),
				),
				Some(10)
			);
			assert_eq!(A::contains_key((2, 20, 200)), true);
			assert_eq!(A::get((2, 20, 200)), Some(10));
			assert_eq!(A::count(), 1);

			A::insert((3, 30, 300), 10);
			A::insert((4, 40, 400), 10);
			assert_eq!(A::count(), 3);
			let _ = A::clear(u32::max_value(), None);
			// one of the item has been removed
			assert!(
				!A::contains_key((2, 20, 200)) &&
					!A::contains_key((3, 30, 300)) &&
					!A::contains_key((4, 40, 400))
			);
			assert_eq!(A::count(), 0);

			A::insert((3, 30, 300), 10);
			A::insert((4, 40, 400), 10);
			assert_eq!(A::iter_values().collect::<Vec<_>>(), vec![10, 10]);
			assert_eq!(A::count(), 2);

			C::insert((3, 30, 300), 10);
			C::insert((4, 40, 400), 10);
			A::translate_values::<u8, _>(|v| Some((v * 2).into()));
			assert_eq!(A::iter().collect::<Vec<_>>(), vec![((4, 40, 400), 20), ((3, 30, 300), 20)]);
			assert_eq!(A::count(), 2);

			A::insert((3, 30, 300), 10);
			A::insert((4, 40, 400), 10);
			assert_eq!(A::iter().collect::<Vec<_>>(), vec![((4, 40, 400), 10), ((3, 30, 300), 10)]);
			assert_eq!(
				A::drain().collect::<Vec<_>>(),
				vec![((4, 40, 400), 10), ((3, 30, 300), 10)]
			);
			assert_eq!(A::iter().collect::<Vec<_>>(), vec![]);
			assert_eq!(A::count(), 0);

			C::insert((3, 30, 300), 10);
			C::insert((4, 40, 400), 10);
			A::translate::<u8, _>(|(k1, k2, k3), v| {
				Some((k1 * k2 as u16 * v as u16 / k3 as u16).into())
			});
			assert_eq!(A::iter().collect::<Vec<_>>(), vec![((4, 40, 400), 4), ((3, 30, 300), 3)]);
			assert_eq!(A::count(), 2);

			let mut entries = vec![];
			A::build_metadata(vec![], &mut entries);
			AValueQueryWithAnOnEmpty::build_metadata(vec![], &mut entries);
			assert_eq!(
				entries,
				vec![
					StorageEntryMetadataIR {
						name: "Foo",
						modifier: StorageEntryModifierIR::Optional,
						ty: StorageEntryTypeIR::Map {
							hashers: vec![
								StorageHasherIR::Blake2_128Concat,
								StorageHasherIR::Blake2_128Concat,
								StorageHasherIR::Twox64Concat
							],
							key: scale_info::meta_type::<(u16, u16, u16)>(),
							value: scale_info::meta_type::<u32>(),
						},
						default: Option::<u32>::None.encode(),
						docs: vec![],
					},
					StorageEntryMetadataIR {
						name: "Foo",
						modifier: StorageEntryModifierIR::Default,
						ty: StorageEntryTypeIR::Plain(scale_info::meta_type::<u32>()),
						default: vec![0, 0, 0, 0],
						docs: if cfg!(feature = "no-metadata-docs") {
							vec![]
						} else {
							vec!["Counter for the related counted storage map"]
						},
					},
					StorageEntryMetadataIR {
						name: "Foo",
						modifier: StorageEntryModifierIR::Default,
						ty: StorageEntryTypeIR::Map {
							hashers: vec![
								StorageHasherIR::Blake2_128Concat,
								StorageHasherIR::Blake2_128Concat,
								StorageHasherIR::Twox64Concat
							],
							key: scale_info::meta_type::<(u16, u16, u16)>(),
							value: scale_info::meta_type::<u32>(),
						},
						default: 98u32.encode(),
						docs: vec![],
					},
					StorageEntryMetadataIR {
						name: "Foo",
						modifier: StorageEntryModifierIR::Default,
						ty: StorageEntryTypeIR::Plain(scale_info::meta_type::<u32>()),
						default: vec![0, 0, 0, 0],
						docs: if cfg!(feature = "no-metadata-docs") {
							vec![]
						} else {
							vec!["Counter for the related counted storage map"]
						},
					},
				]
			);

			let _ = WithLen::clear(u32::max_value(), None);
			assert_eq!(WithLen::decode_len((3, 30, 300)), None);
			WithLen::append((0, 100, 1000), 10);
			assert_eq!(WithLen::decode_len((0, 100, 1000)), Some(1));

			A::insert((3, 30, 300), 11);
			A::insert((3, 30, 301), 12);
			A::insert((4, 40, 400), 13);
			A::insert((4, 40, 401), 14);
			assert_eq!(A::iter_prefix_values((3,)).collect::<Vec<_>>(), vec![11, 12]);
			assert_eq!(A::iter_prefix_values((4,)).collect::<Vec<_>>(), vec![14, 13]);
			assert_eq!(A::iter_prefix_values((3, 30)).collect::<Vec<_>>(), vec![11, 12]);
			assert_eq!(A::iter_prefix_values((4, 40)).collect::<Vec<_>>(), vec![14, 13]);
			assert_eq!(A::count(), 5);
		});
	}
}
