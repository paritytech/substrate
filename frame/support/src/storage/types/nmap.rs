// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! Storage n-map type. Particularly implements `StorageNMap` and `StoragePrefixedMap`
//! traits and their methods directly.

use crate::{
	storage::{
		types::{
			EncodeLikeTuple, HasKeyPrefix, HasReversibleKeyPrefix, OptionQuery, QueryKindTrait,
			StorageEntryMetadataBuilder, TupleToEncodedIter,
		},
		KeyGenerator, PrefixIterator, StorageAppend, StorageDecodeLength, StoragePrefixedMap,
	},
	traits::{Get, GetDefault, StorageInfo, StorageInstance},
};
use codec::{Decode, Encode, EncodeLike, FullCodec, MaxEncodedLen};
use sp_metadata_ir::{StorageEntryMetadataIR, StorageEntryTypeIR};
use sp_runtime::SaturatedConversion;
use sp_std::prelude::*;

/// A type that allow to store values for an arbitrary number of keys in the form of
/// `(Key<Hasher1, key1>, Key<Hasher2, key2>, ..., Key<HasherN, keyN>)`.
///
/// Each value is stored at:
/// ```nocompile
/// Twox128(Prefix::pallet_prefix())
/// 		++ Twox128(Prefix::STORAGE_PREFIX)
/// 		++ Hasher1(encode(key1))
/// 		++ Hasher2(encode(key2))
/// 	++ ...
/// 	++ HasherN(encode(keyN))
/// ```
///
/// # Warning
///
/// If the keys are not trusted (e.g. can be set by a user), a cryptographic `hasher`
/// such as `blake2_128_concat` must be used for the key hashers. Otherwise, other values
/// in storage can be compromised.
pub struct StorageNMap<
	Prefix,
	Key,
	Value,
	QueryKind = OptionQuery,
	OnEmpty = GetDefault,
	MaxValues = GetDefault,
>(core::marker::PhantomData<(Prefix, Key, Value, QueryKind, OnEmpty, MaxValues)>);

impl<Prefix, Key, Value, QueryKind, OnEmpty, MaxValues>
	crate::storage::generator::StorageNMap<Key, Value>
	for StorageNMap<Prefix, Key, Value, QueryKind, OnEmpty, MaxValues>
where
	Prefix: StorageInstance,
	Key: super::key::KeyGenerator,
	Value: FullCodec,
	QueryKind: QueryKindTrait<Value, OnEmpty>,
	OnEmpty: Get<QueryKind::Query> + 'static,
	MaxValues: Get<Option<u32>>,
{
	type Query = QueryKind::Query;
	fn module_prefix() -> &'static [u8] {
		Prefix::pallet_prefix().as_bytes()
	}
	fn storage_prefix() -> &'static [u8] {
		Prefix::STORAGE_PREFIX.as_bytes()
	}
	fn from_optional_value_to_query(v: Option<Value>) -> Self::Query {
		QueryKind::from_optional_value_to_query(v)
	}
	fn from_query_to_optional_value(v: Self::Query) -> Option<Value> {
		QueryKind::from_query_to_optional_value(v)
	}
}

impl<Prefix, Key, Value, QueryKind, OnEmpty, MaxValues> crate::storage::StoragePrefixedMap<Value>
	for StorageNMap<Prefix, Key, Value, QueryKind, OnEmpty, MaxValues>
where
	Prefix: StorageInstance,
	Key: super::key::KeyGenerator,
	Value: FullCodec,
	QueryKind: QueryKindTrait<Value, OnEmpty>,
	OnEmpty: Get<QueryKind::Query> + 'static,
	MaxValues: Get<Option<u32>>,
{
	fn module_prefix() -> &'static [u8] {
		<Self as crate::storage::generator::StorageNMap<Key, Value>>::module_prefix()
	}
	fn storage_prefix() -> &'static [u8] {
		<Self as crate::storage::generator::StorageNMap<Key, Value>>::storage_prefix()
	}
}

impl<Prefix, Key, Value, QueryKind, OnEmpty, MaxValues>
	StorageNMap<Prefix, Key, Value, QueryKind, OnEmpty, MaxValues>
where
	Prefix: StorageInstance,
	Key: super::key::KeyGenerator,
	Value: FullCodec,
	QueryKind: QueryKindTrait<Value, OnEmpty>,
	OnEmpty: Get<QueryKind::Query> + 'static,
	MaxValues: Get<Option<u32>>,
{
	/// Get the storage key used to fetch a value corresponding to a specific key.
	pub fn hashed_key_for<KArg: EncodeLikeTuple<Key::KArg> + TupleToEncodedIter>(
		key: KArg,
	) -> Vec<u8> {
		<Self as crate::storage::StorageNMap<Key, Value>>::hashed_key_for(key)
	}

	/// Does the value (explicitly) exist in storage?
	pub fn contains_key<KArg: EncodeLikeTuple<Key::KArg> + TupleToEncodedIter>(key: KArg) -> bool {
		<Self as crate::storage::StorageNMap<Key, Value>>::contains_key(key)
	}

	/// Load the value associated with the given key from the map.
	pub fn get<KArg: EncodeLikeTuple<Key::KArg> + TupleToEncodedIter>(
		key: KArg,
	) -> QueryKind::Query {
		<Self as crate::storage::StorageNMap<Key, Value>>::get(key)
	}

	/// Try to get the value for the given key from the map.
	///
	/// Returns `Ok` if it exists, `Err` if not.
	pub fn try_get<KArg: EncodeLikeTuple<Key::KArg> + TupleToEncodedIter>(
		key: KArg,
	) -> Result<Value, ()> {
		<Self as crate::storage::StorageNMap<Key, Value>>::try_get(key)
	}

	/// Store or remove the value to be associated with `key` so that `get` returns the `query`.
	pub fn set<KArg: EncodeLikeTuple<Key::KArg> + TupleToEncodedIter>(
		key: KArg,
		query: QueryKind::Query,
	) {
		<Self as crate::storage::StorageNMap<Key, Value>>::set(key, query)
	}

	/// Take a value from storage, removing it afterwards.
	pub fn take<KArg: EncodeLikeTuple<Key::KArg> + TupleToEncodedIter>(
		key: KArg,
	) -> QueryKind::Query {
		<Self as crate::storage::StorageNMap<Key, Value>>::take(key)
	}

	/// Swap the values of two key-pairs.
	pub fn swap<KOther, KArg1, KArg2>(key1: KArg1, key2: KArg2)
	where
		KOther: KeyGenerator,
		KArg1: EncodeLikeTuple<Key::KArg> + TupleToEncodedIter,
		KArg2: EncodeLikeTuple<KOther::KArg> + TupleToEncodedIter,
	{
		<Self as crate::storage::StorageNMap<Key, Value>>::swap::<KOther, _, _>(key1, key2)
	}

	/// Store a value to be associated with the given keys from the map.
	pub fn insert<KArg, VArg>(key: KArg, val: VArg)
	where
		KArg: EncodeLikeTuple<Key::KArg> + TupleToEncodedIter,
		VArg: EncodeLike<Value>,
	{
		<Self as crate::storage::StorageNMap<Key, Value>>::insert(key, val)
	}

	/// Remove the value under the given keys.
	pub fn remove<KArg: EncodeLikeTuple<Key::KArg> + TupleToEncodedIter>(key: KArg) {
		<Self as crate::storage::StorageNMap<Key, Value>>::remove(key)
	}

	/// Remove all values starting with `partial_key` in the overlay and up to `limit` in the
	/// backend.
	///
	/// All values in the client overlay will be deleted, if there is some `limit` then up to
	/// `limit` values are deleted from the client backend, if `limit` is none then all values in
	/// the client backend are deleted.
	///
	/// # Note
	///
	/// Calling this multiple times per block with a `limit` set leads always to the same keys being
	/// removed and the same result being returned. This happens because the keys to delete in the
	/// overlay are not taken into account when deleting keys in the backend.
	#[deprecated = "Use `clear_prefix` instead"]
	pub fn remove_prefix<KP>(partial_key: KP, limit: Option<u32>) -> sp_io::KillStorageResult
	where
		Key: HasKeyPrefix<KP>,
	{
		#[allow(deprecated)]
		<Self as crate::storage::StorageNMap<Key, Value>>::remove_prefix(partial_key, limit)
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
		<Self as crate::storage::StorageNMap<Key, Value>>::clear_prefix(
			partial_key,
			limit,
			maybe_cursor,
		)
	}

	/// Iterate over values that share the first key.
	pub fn iter_prefix_values<KP>(partial_key: KP) -> PrefixIterator<Value>
	where
		Key: HasKeyPrefix<KP>,
	{
		<Self as crate::storage::StorageNMap<Key, Value>>::iter_prefix_values(partial_key)
	}

	/// Mutate the value under the given keys.
	pub fn mutate<KArg, R, F>(key: KArg, f: F) -> R
	where
		KArg: EncodeLikeTuple<Key::KArg> + TupleToEncodedIter,
		F: FnOnce(&mut QueryKind::Query) -> R,
	{
		<Self as crate::storage::StorageNMap<Key, Value>>::mutate(key, f)
	}

	/// Mutate the value under the given keys when the closure returns `Ok`.
	pub fn try_mutate<KArg, R, E, F>(key: KArg, f: F) -> Result<R, E>
	where
		KArg: EncodeLikeTuple<Key::KArg> + TupleToEncodedIter,
		F: FnOnce(&mut QueryKind::Query) -> Result<R, E>,
	{
		<Self as crate::storage::StorageNMap<Key, Value>>::try_mutate(key, f)
	}

	/// Mutate the value under the given keys. Deletes the item if mutated to a `None`.
	pub fn mutate_exists<KArg, R, F>(key: KArg, f: F) -> R
	where
		KArg: EncodeLikeTuple<Key::KArg> + TupleToEncodedIter,
		F: FnOnce(&mut Option<Value>) -> R,
	{
		<Self as crate::storage::StorageNMap<Key, Value>>::mutate_exists(key, f)
	}

	/// Mutate the item, only if an `Ok` value is returned. Deletes the item if mutated to a `None`.
	/// `f` will always be called with an option representing if the storage item exists (`Some<V>`)
	/// or if the storage item does not exist (`None`), independent of the `QueryType`.
	pub fn try_mutate_exists<KArg, R, E, F>(key: KArg, f: F) -> Result<R, E>
	where
		KArg: EncodeLikeTuple<Key::KArg> + TupleToEncodedIter,
		F: FnOnce(&mut Option<Value>) -> Result<R, E>,
	{
		<Self as crate::storage::StorageNMap<Key, Value>>::try_mutate_exists(key, f)
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
		KArg: EncodeLikeTuple<Key::KArg> + TupleToEncodedIter,
		Item: Encode,
		EncodeLikeItem: EncodeLike<Item>,
		Value: StorageAppend<Item>,
	{
		<Self as crate::storage::StorageNMap<Key, Value>>::append(key, item)
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
		<Self as crate::storage::StorageNMap<Key, Value>>::decode_len(key)
	}

	/// Migrate an item with the given `key` from defunct `hash_fns` to the current hashers.
	///
	/// If the key doesn't exist, then it's a no-op. If it does, then it returns its value.
	pub fn migrate_keys<KArg>(key: KArg, hash_fns: Key::HArg) -> Option<Value>
	where
		KArg: EncodeLikeTuple<Key::KArg> + TupleToEncodedIter,
	{
		<Self as crate::storage::StorageNMap<Key, Value>>::migrate_keys::<_>(key, hash_fns)
	}

	/// Remove all values in the overlay and up to `limit` in the backend.
	///
	/// All values in the client overlay will be deleted, if there is some `limit` then up to
	/// `limit` values are deleted from the client backend, if `limit` is none then all values in
	/// the client backend are deleted.
	///
	/// # Note
	///
	/// Calling this multiple times per block with a `limit` set leads always to the same keys being
	/// removed and the same result being returned. This happens because the keys to delete in the
	/// overlay are not taken into account when deleting keys in the backend.
	#[deprecated = "Use `clear` instead"]
	pub fn remove_all(limit: Option<u32>) -> sp_io::KillStorageResult {
		#[allow(deprecated)]
		<Self as crate::storage::StoragePrefixedMap<Value>>::remove_all(limit).into()
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
		<Self as crate::storage::StoragePrefixedMap<Value>>::clear(limit, maybe_cursor)
	}

	/// Iter over all value of the storage.
	///
	/// NOTE: If a value failed to decode because storage is corrupted then it is skipped.
	pub fn iter_values() -> crate::storage::PrefixIterator<Value> {
		<Self as crate::storage::StoragePrefixedMap<Value>>::iter_values()
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
	pub fn translate_values<OldValue: Decode, F: FnMut(OldValue) -> Option<Value>>(f: F) {
		<Self as crate::storage::StoragePrefixedMap<Value>>::translate_values(f)
	}
}

impl<Prefix, Key, Value, QueryKind, OnEmpty, MaxValues>
	StorageNMap<Prefix, Key, Value, QueryKind, OnEmpty, MaxValues>
where
	Prefix: StorageInstance,
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
		<Self as crate::storage::IterableStorageNMap<Key, Value>>::iter_prefix(kp)
	}

	/// Enumerate all elements in the map with prefix key `kp` after a specified `starting_raw_key`
	/// in no particular order.
	///
	/// If you add or remove values whose prefix key is `kp` to the map while doing this, you'll get
	/// undefined results.
	pub fn iter_prefix_from<KP>(
		kp: KP,
		starting_raw_key: Vec<u8>,
	) -> crate::storage::PrefixIterator<(<Key as HasKeyPrefix<KP>>::Suffix, Value)>
	where
		Key: HasReversibleKeyPrefix<KP>,
	{
		<Self as crate::storage::IterableStorageNMap<Key, Value>>::iter_prefix_from(
			kp,
			starting_raw_key,
		)
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
		<Self as crate::storage::IterableStorageNMap<Key, Value>>::iter_key_prefix(kp)
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
		<Self as crate::storage::IterableStorageNMap<Key, Value>>::iter_key_prefix_from(
			kp,
			starting_raw_key,
		)
	}

	/// Remove all elements from the map with prefix key `kp` and iterate through them in no
	/// particular order.
	///
	/// If you add elements with prefix key `k1` to the map while doing this, you'll get undefined
	/// results.
	pub fn drain_prefix<KP>(
		kp: KP,
	) -> crate::storage::PrefixIterator<(<Key as HasKeyPrefix<KP>>::Suffix, Value)>
	where
		Key: HasReversibleKeyPrefix<KP>,
	{
		<Self as crate::storage::IterableStorageNMap<Key, Value>>::drain_prefix(kp)
	}

	/// Enumerate all elements in the map in no particular order.
	///
	/// If you add or remove values to the map while doing this, you'll get undefined results.
	pub fn iter() -> crate::storage::PrefixIterator<(Key::Key, Value)> {
		<Self as crate::storage::IterableStorageNMap<Key, Value>>::iter()
	}

	/// Enumerate all elements in the map after a specified `starting_key` in no particular order.
	///
	/// If you add or remove values to the map while doing this, you'll get undefined results.
	pub fn iter_from(
		starting_raw_key: Vec<u8>,
	) -> crate::storage::PrefixIterator<(Key::Key, Value)> {
		<Self as crate::storage::IterableStorageNMap<Key, Value>>::iter_from(starting_raw_key)
	}

	/// Enumerate all keys in the map in no particular order.
	///
	/// If you add or remove values to the map while doing this, you'll get undefined results.
	pub fn iter_keys() -> crate::storage::KeyPrefixIterator<Key::Key> {
		<Self as crate::storage::IterableStorageNMap<Key, Value>>::iter_keys()
	}

	/// Enumerate all keys in the map after a specified `starting_raw_key` in no particular order.
	///
	/// If you add or remove values to the map while doing this, you'll get undefined results.
	pub fn iter_keys_from(
		starting_raw_key: Vec<u8>,
	) -> crate::storage::KeyPrefixIterator<Key::Key> {
		<Self as crate::storage::IterableStorageNMap<Key, Value>>::iter_keys_from(starting_raw_key)
	}

	/// Remove all elements from the map and iterate through them in no particular order.
	///
	/// If you add elements to the map while doing this, you'll get undefined results.
	pub fn drain() -> crate::storage::PrefixIterator<(Key::Key, Value)> {
		<Self as crate::storage::IterableStorageNMap<Key, Value>>::drain()
	}

	/// Translate the values of all elements by a function `f`, in the map in no particular order.
	///
	/// By returning `None` from `f` for an element, you'll remove it from the map.
	///
	/// NOTE: If a value fail to decode because storage is corrupted then it is skipped.
	pub fn translate<O: Decode, F: FnMut(Key::Key, O) -> Option<Value>>(f: F) {
		<Self as crate::storage::IterableStorageNMap<Key, Value>>::translate(f)
	}
}

impl<Prefix, Key, Value, QueryKind, OnEmpty, MaxValues> StorageEntryMetadataBuilder
	for StorageNMap<Prefix, Key, Value, QueryKind, OnEmpty, MaxValues>
where
	Prefix: StorageInstance,
	Key: super::key::KeyGenerator,
	Value: FullCodec + scale_info::StaticTypeInfo,
	QueryKind: QueryKindTrait<Value, OnEmpty>,
	OnEmpty: Get<QueryKind::Query> + 'static,
	MaxValues: Get<Option<u32>>,
{
	fn build_metadata(docs: Vec<&'static str>, entries: &mut Vec<StorageEntryMetadataIR>) {
		let docs = if cfg!(feature = "no-metadata-docs") { vec![] } else { docs };

		let entry = StorageEntryMetadataIR {
			name: Prefix::STORAGE_PREFIX,
			modifier: QueryKind::METADATA,
			ty: StorageEntryTypeIR::Map {
				key: scale_info::meta_type::<Key::Key>(),
				hashers: Key::HASHER_METADATA.to_vec(),
				value: scale_info::meta_type::<Value>(),
			},
			default: OnEmpty::get().encode(),
			docs,
		};

		entries.push(entry);
	}
}

impl<Prefix, Key, Value, QueryKind, OnEmpty, MaxValues> crate::traits::StorageInfoTrait
	for StorageNMap<Prefix, Key, Value, QueryKind, OnEmpty, MaxValues>
where
	Prefix: StorageInstance,
	Key: super::key::KeyGenerator + super::key::KeyGeneratorMaxEncodedLen,
	Value: FullCodec + MaxEncodedLen,
	QueryKind: QueryKindTrait<Value, OnEmpty>,
	OnEmpty: Get<QueryKind::Query> + 'static,
	MaxValues: Get<Option<u32>>,
{
	fn storage_info() -> Vec<StorageInfo> {
		vec![StorageInfo {
			pallet_name: Self::module_prefix().to_vec(),
			storage_name: Self::storage_prefix().to_vec(),
			prefix: Self::final_prefix().to_vec(),
			max_values: MaxValues::get(),
			max_size: Some(
				Key::key_max_encoded_len()
					.saturating_add(Value::max_encoded_len())
					.saturated_into(),
			),
		}]
	}
}

/// It doesn't require to implement `MaxEncodedLen` and give no information for `max_size`.
impl<Prefix, Key, Value, QueryKind, OnEmpty, MaxValues> crate::traits::PartialStorageInfoTrait
	for StorageNMap<Prefix, Key, Value, QueryKind, OnEmpty, MaxValues>
where
	Prefix: StorageInstance,
	Key: super::key::KeyGenerator,
	Value: FullCodec,
	QueryKind: QueryKindTrait<Value, OnEmpty>,
	OnEmpty: Get<QueryKind::Query> + 'static,
	MaxValues: Get<Option<u32>>,
{
	fn partial_storage_info() -> Vec<StorageInfo> {
		vec![StorageInfo {
			pallet_name: Self::module_prefix().to_vec(),
			storage_name: Self::storage_prefix().to_vec(),
			prefix: Self::final_prefix().to_vec(),
			max_values: MaxValues::get(),
			max_size: None,
		}]
	}
}
#[cfg(test)]
mod test {
	use super::*;
	use crate::{
		hash::{StorageHasher as _, *},
		storage::types::{Key as NMapKey, ValueQuery},
	};
	use sp_io::{hashing::twox_128, TestExternalities};
	use sp_metadata_ir::{StorageEntryModifierIR, StorageHasherIR};

	struct Prefix;
	impl StorageInstance for Prefix {
		fn pallet_prefix() -> &'static str {
			"test"
		}
		const STORAGE_PREFIX: &'static str = "Foo";
	}

	struct ADefault;
	impl crate::traits::Get<u32> for ADefault {
		fn get() -> u32 {
			98
		}
	}

	#[test]
	fn test_1_key() {
		type A = StorageNMap<Prefix, NMapKey<Blake2_128Concat, u16>, u32, OptionQuery>;
		type AValueQueryWithAnOnEmpty =
			StorageNMap<Prefix, NMapKey<Blake2_128Concat, u16>, u32, ValueQuery, ADefault>;
		type B = StorageNMap<Prefix, NMapKey<Blake2_256, u16>, u32, ValueQuery>;
		type C = StorageNMap<Prefix, NMapKey<Blake2_128Concat, u16>, u8, ValueQuery>;
		type WithLen = StorageNMap<Prefix, NMapKey<Blake2_128Concat, u16>, Vec<u32>>;

		TestExternalities::default().execute_with(|| {
			let mut k: Vec<u8> = vec![];
			k.extend(&twox_128(b"test"));
			k.extend(&twox_128(b"Foo"));
			k.extend(&3u16.blake2_128_concat());
			assert_eq!(A::hashed_key_for((&3,)).to_vec(), k);

			assert_eq!(A::contains_key((3,)), false);
			assert_eq!(A::get((3,)), None);
			assert_eq!(AValueQueryWithAnOnEmpty::get((3,)), 98);

			A::insert((3,), 10);
			assert_eq!(A::contains_key((3,)), true);
			assert_eq!(A::get((3,)), Some(10));
			assert_eq!(AValueQueryWithAnOnEmpty::get((3,)), 10);

			{
				#[crate::storage_alias]
				type Foo = StorageNMap<test, (NMapKey<Blake2_128Concat, u16>), u32>;

				assert_eq!(Foo::contains_key((3,)), true);
				assert_eq!(Foo::get((3,)), Some(10));
			}

			A::swap::<NMapKey<Blake2_128Concat, u16>, _, _>((3,), (2,));
			assert_eq!(A::contains_key((3,)), false);
			assert_eq!(A::contains_key((2,)), true);
			assert_eq!(A::get((3,)), None);
			assert_eq!(AValueQueryWithAnOnEmpty::get((3,)), 98);
			assert_eq!(A::get((2,)), Some(10));
			assert_eq!(AValueQueryWithAnOnEmpty::get((2,)), 10);

			A::remove((2,));
			assert_eq!(A::contains_key((2,)), false);
			assert_eq!(A::get((2,)), None);

			AValueQueryWithAnOnEmpty::mutate((2,), |v| *v = *v * 2);
			AValueQueryWithAnOnEmpty::mutate((2,), |v| *v = *v * 2);
			assert_eq!(A::contains_key((2,)), true);
			assert_eq!(A::get((2,)), Some(98 * 4));

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

			A::remove((2,));
			let _: Result<(), ()> = AValueQueryWithAnOnEmpty::try_mutate((2,), |v| {
				*v = *v * 2;
				Err(())
			});
			assert_eq!(A::contains_key((2,)), false);

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

			A::insert((2,), 10);
			assert_eq!(A::take((2,)), Some(10));
			assert_eq!(A::contains_key((2,)), false);
			assert_eq!(AValueQueryWithAnOnEmpty::take((2,)), 98);
			assert_eq!(A::contains_key((2,)), false);
			assert_eq!(A::try_get((2,)), Err(()));

			B::insert((2,), 10);
			assert_eq!(
				A::migrate_keys((2,), (Box::new(|key| Blake2_256::hash(key).to_vec()),),),
				Some(10)
			);
			assert_eq!(A::contains_key((2,)), true);
			assert_eq!(A::get((2,)), Some(10));

			A::insert((3,), 10);
			A::insert((4,), 10);
			let _ = A::clear(u32::max_value(), None);
			assert_eq!(A::contains_key((3,)), false);
			assert_eq!(A::contains_key((4,)), false);

			A::insert((3,), 10);
			A::insert((4,), 10);
			assert_eq!(A::iter_values().collect::<Vec<_>>(), vec![10, 10]);

			C::insert((3,), 10);
			C::insert((4,), 10);
			A::translate_values::<u8, _>(|v| Some((v * 2).into()));
			assert_eq!(A::iter().collect::<Vec<_>>(), vec![(4, 20), (3, 20)]);

			A::insert((3,), 10);
			A::insert((4,), 10);
			assert_eq!(A::iter().collect::<Vec<_>>(), vec![(4, 10), (3, 10)]);
			assert_eq!(A::drain().collect::<Vec<_>>(), vec![(4, 10), (3, 10)]);
			assert_eq!(A::iter().collect::<Vec<_>>(), vec![]);

			C::insert((3,), 10);
			C::insert((4,), 10);
			A::translate::<u8, _>(|k1, v| Some((k1 as u16 * v as u16).into()));
			assert_eq!(A::iter().collect::<Vec<_>>(), vec![(4, 40), (3, 30)]);

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
						ty: StorageEntryTypeIR::Map {
							hashers: vec![StorageHasherIR::Blake2_128Concat],
							key: scale_info::meta_type::<u16>(),
							value: scale_info::meta_type::<u32>(),
						},
						default: 98u32.encode(),
						docs: vec![],
					}
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
		type A = StorageNMap<
			Prefix,
			(NMapKey<Blake2_128Concat, u16>, NMapKey<Twox64Concat, u8>),
			u32,
			OptionQuery,
		>;
		type AValueQueryWithAnOnEmpty = StorageNMap<
			Prefix,
			(NMapKey<Blake2_128Concat, u16>, NMapKey<Twox64Concat, u8>),
			u32,
			ValueQuery,
			ADefault,
		>;
		type B =
			StorageNMap<Prefix, (NMapKey<Blake2_256, u16>, NMapKey<Twox128, u8>), u32, ValueQuery>;
		type C = StorageNMap<
			Prefix,
			(NMapKey<Blake2_128Concat, u16>, NMapKey<Twox64Concat, u8>),
			u8,
			ValueQuery,
		>;
		type WithLen = StorageNMap<
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

			A::insert((3, 30), 10);
			assert_eq!(A::contains_key((3, 30)), true);
			assert_eq!(A::get((3, 30)), Some(10));
			assert_eq!(AValueQueryWithAnOnEmpty::get((3, 30)), 10);

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

			A::remove((2, 20));
			assert_eq!(A::contains_key((2, 20)), false);
			assert_eq!(A::get((2, 20)), None);

			AValueQueryWithAnOnEmpty::mutate((2, 20), |v| *v = *v * 2);
			AValueQueryWithAnOnEmpty::mutate((2, 20), |v| *v = *v * 2);
			assert_eq!(A::contains_key((2, 20)), true);
			assert_eq!(A::get((2, 20)), Some(98 * 4));

			A::remove((2, 20));
			let _: Result<(), ()> = AValueQueryWithAnOnEmpty::try_mutate((2, 20), |v| {
				*v = *v * 2;
				Err(())
			});
			assert_eq!(A::contains_key((2, 20)), false);

			A::remove((2, 20));
			let _: Result<(), ()> = AValueQueryWithAnOnEmpty::try_mutate((2, 20), |v| {
				*v = *v * 2;
				Err(())
			});
			assert_eq!(A::contains_key((2, 20)), false);

			A::remove((2, 20));
			AValueQueryWithAnOnEmpty::mutate_exists((2, 20), |v| {
				assert!(v.is_none());
				*v = Some(10);
			});
			assert_eq!(A::contains_key((2, 20)), true);
			assert_eq!(A::get((2, 20)), Some(10));
			AValueQueryWithAnOnEmpty::mutate_exists((2, 20), |v| {
				*v = Some(v.unwrap() * 10);
			});
			assert_eq!(A::contains_key((2, 20)), true);
			assert_eq!(A::get((2, 20)), Some(100));

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
			let _: Result<(), ()> = AValueQueryWithAnOnEmpty::try_mutate_exists((2, 20), |v| {
				*v = Some(v.unwrap() * 10);
				Err(())
			});
			assert_eq!(A::contains_key((2, 20)), true);
			assert_eq!(A::get((2, 20)), Some(100));

			A::insert((2, 20), 10);
			assert_eq!(A::take((2, 20)), Some(10));
			assert_eq!(A::contains_key((2, 20)), false);
			assert_eq!(AValueQueryWithAnOnEmpty::take((2, 20)), 98);
			assert_eq!(A::contains_key((2, 20)), false);
			assert_eq!(A::try_get((2, 20)), Err(()));

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

			A::insert((3, 30), 10);
			A::insert((4, 40), 10);
			let _ = A::clear(u32::max_value(), None);
			assert_eq!(A::contains_key((3, 30)), false);
			assert_eq!(A::contains_key((4, 40)), false);

			A::insert((3, 30), 10);
			A::insert((4, 40), 10);
			assert_eq!(A::iter_values().collect::<Vec<_>>(), vec![10, 10]);

			C::insert((3, 30), 10);
			C::insert((4, 40), 10);
			A::translate_values::<u8, _>(|v| Some((v * 2).into()));
			assert_eq!(A::iter().collect::<Vec<_>>(), vec![((4, 40), 20), ((3, 30), 20)]);

			A::insert((3, 30), 10);
			A::insert((4, 40), 10);
			assert_eq!(A::iter().collect::<Vec<_>>(), vec![((4, 40), 10), ((3, 30), 10)]);
			assert_eq!(A::drain().collect::<Vec<_>>(), vec![((4, 40), 10), ((3, 30), 10)]);
			assert_eq!(A::iter().collect::<Vec<_>>(), vec![]);

			C::insert((3, 30), 10);
			C::insert((4, 40), 10);
			A::translate::<u8, _>(|(k1, k2), v| Some((k1 * k2 as u16 * v as u16).into()));
			assert_eq!(A::iter().collect::<Vec<_>>(), vec![((4, 40), 1600), ((3, 30), 900)]);

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
					}
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
		});
	}

	#[test]
	fn test_3_keys() {
		type A = StorageNMap<
			Prefix,
			(
				NMapKey<Blake2_128Concat, u16>,
				NMapKey<Blake2_128Concat, u16>,
				NMapKey<Twox64Concat, u16>,
			),
			u32,
			OptionQuery,
		>;
		type AValueQueryWithAnOnEmpty = StorageNMap<
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
		type B = StorageNMap<
			Prefix,
			(NMapKey<Blake2_256, u16>, NMapKey<Blake2_256, u16>, NMapKey<Twox128, u16>),
			u32,
			ValueQuery,
		>;
		type C = StorageNMap<
			Prefix,
			(
				NMapKey<Blake2_128Concat, u16>,
				NMapKey<Blake2_128Concat, u16>,
				NMapKey<Twox64Concat, u16>,
			),
			u8,
			ValueQuery,
		>;
		type WithLen = StorageNMap<
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

			A::insert((1, 10, 100), 30);
			assert_eq!(A::contains_key((1, 10, 100)), true);
			assert_eq!(A::get((1, 10, 100)), Some(30));
			assert_eq!(AValueQueryWithAnOnEmpty::get((1, 10, 100)), 30);

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

			A::remove((2, 20, 200));
			assert_eq!(A::contains_key((2, 20, 200)), false);
			assert_eq!(A::get((2, 20, 200)), None);

			AValueQueryWithAnOnEmpty::mutate((2, 20, 200), |v| *v = *v * 2);
			AValueQueryWithAnOnEmpty::mutate((2, 20, 200), |v| *v = *v * 2);
			assert_eq!(A::contains_key((2, 20, 200)), true);
			assert_eq!(A::get((2, 20, 200)), Some(98 * 4));

			A::remove((2, 20, 200));
			let _: Result<(), ()> = AValueQueryWithAnOnEmpty::try_mutate((2, 20, 200), |v| {
				*v = *v * 2;
				Err(())
			});
			assert_eq!(A::contains_key((2, 20, 200)), false);

			A::remove((2, 20, 200));
			AValueQueryWithAnOnEmpty::mutate_exists((2, 20, 200), |v| {
				assert!(v.is_none());
				*v = Some(10);
			});
			assert_eq!(A::contains_key((2, 20, 200)), true);
			assert_eq!(A::get((2, 20, 200)), Some(10));
			AValueQueryWithAnOnEmpty::mutate_exists((2, 20, 200), |v| {
				*v = Some(v.unwrap() * 10);
			});
			assert_eq!(A::contains_key((2, 20, 200)), true);
			assert_eq!(A::get((2, 20, 200)), Some(100));

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
			let _: Result<(), ()> =
				AValueQueryWithAnOnEmpty::try_mutate_exists((2, 20, 200), |v| {
					*v = Some(v.unwrap() * 10);
					Err(())
				});
			assert_eq!(A::contains_key((2, 20, 200)), true);
			assert_eq!(A::get((2, 20, 200)), Some(100));

			A::insert((2, 20, 200), 10);
			assert_eq!(A::take((2, 20, 200)), Some(10));
			assert_eq!(A::contains_key((2, 20, 200)), false);
			assert_eq!(AValueQueryWithAnOnEmpty::take((2, 20, 200)), 98);
			assert_eq!(A::contains_key((2, 20, 200)), false);
			assert_eq!(A::try_get((2, 20, 200)), Err(()));

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

			A::insert((3, 30, 300), 10);
			A::insert((4, 40, 400), 10);
			let _ = A::clear(u32::max_value(), None);
			assert_eq!(A::contains_key((3, 30, 300)), false);
			assert_eq!(A::contains_key((4, 40, 400)), false);

			A::insert((3, 30, 300), 10);
			A::insert((4, 40, 400), 10);
			assert_eq!(A::iter_values().collect::<Vec<_>>(), vec![10, 10]);

			C::insert((3, 30, 300), 10);
			C::insert((4, 40, 400), 10);
			A::translate_values::<u8, _>(|v| Some((v * 2).into()));
			assert_eq!(A::iter().collect::<Vec<_>>(), vec![((4, 40, 400), 20), ((3, 30, 300), 20)]);

			A::insert((3, 30, 300), 10);
			A::insert((4, 40, 400), 10);
			assert_eq!(A::iter().collect::<Vec<_>>(), vec![((4, 40, 400), 10), ((3, 30, 300), 10)]);
			assert_eq!(
				A::drain().collect::<Vec<_>>(),
				vec![((4, 40, 400), 10), ((3, 30, 300), 10)]
			);
			assert_eq!(A::iter().collect::<Vec<_>>(), vec![]);

			C::insert((3, 30, 300), 10);
			C::insert((4, 40, 400), 10);
			A::translate::<u8, _>(|(k1, k2, k3), v| {
				Some((k1 * k2 as u16 * v as u16 / k3 as u16).into())
			});
			assert_eq!(A::iter().collect::<Vec<_>>(), vec![((4, 40, 400), 4), ((3, 30, 300), 3)]);

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
					}
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
		});
	}
}
