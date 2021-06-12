use codec::{FullCodec, Decode, EncodeLike, Encode};
use crate::{
	storage::{
		StorageMap, StorageValue,
		StorageAppend, StorageTryAppend, StorageDecodeLength, StoragePrefixedMap,
		generator::{StorageMap as StorageMapT, StorageValue as StorageValueT},
	},
};
use sp_std::prelude::*;
use sp_runtime::traits::Saturating;

/// A wrapper around a `StorageMap` and a `StorageValue<u32>` to keep track of how many items are in
/// a map, without needing to iterate all the values.
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
pub struct CountedStorageMap<Key, Value, Map, Counter>(
	core::marker::PhantomData<(Key, Value, Map, Counter)>
);

impl<Key, Value, Map, Counter>
	StorageMapT<Key, Value>
	for CountedStorageMap<Key, Value, Map, Counter>
where
	Key: FullCodec,
	Value: FullCodec,
	Map: StorageMapT<Key, Value>,
	Counter: StorageValueT<u32>
{
	type Query = Map::Query;
	type Hasher = Map::Hasher;
	fn module_prefix() -> &'static [u8] {
		Map::module_prefix()
	}
	fn storage_prefix() -> &'static [u8] {
		Map::storage_prefix()
	}
	fn from_optional_value_to_query(v: Option<Value>) -> Self::Query {
		Map::from_optional_value_to_query(v)
	}
	fn from_query_to_optional_value(v: Self::Query) -> Option<Value> {
		Map::from_query_to_optional_value(v)
	}
}

impl<Key, Value, Map, Counter>
	StoragePrefixedMap<Value> for
	CountedStorageMap<Key, Value, Map, Counter>
where
	Value: FullCodec,
	Map: crate::StoragePrefixedMap<Value>,
	Counter: StorageValueT<u32>
{
	fn module_prefix() -> &'static [u8] {
		Map::module_prefix()
	}
	fn storage_prefix() -> &'static [u8] {
		Map::storage_prefix()
	}
}

impl<Key, Value, Map, Counter>
	CountedStorageMap<Key, Value, Map, Counter>
where
	Key: FullCodec,
	Value: FullCodec,
	Map: StorageMapT<Key, Value> + crate::StoragePrefixedMap<Value>,
	Counter: StorageValueT<u32, Query=u32>,
{
	// Internal helper function to track the counter as a value is mutated.
	fn mutate_counter<
		KeyArg: EncodeLike<Key> + Clone,
		M: FnOnce(KeyArg, F) -> R,
		F: FnOnce(I) -> R,
		I,
		R,
	>(m: M, key: KeyArg, f: F) -> R {
		let val_existed = Map::contains_key(key.clone());
		let res = m(key.clone(), f);
		let val_exists = Map::contains_key(key);

		if val_existed && !val_exists {
			// Value was deleted
			Counter::mutate(|value| value.saturating_dec());
		} else if !val_existed && val_exists {
			// Value was added
			Counter::mutate(|value| value.saturating_inc());
		}

		res
	}

	/// Get the storage key used to fetch a value corresponding to a specific key.
	pub fn hashed_key_for<KeyArg: EncodeLike<Key>>(key: KeyArg) -> Vec<u8> {
		Map::hashed_key_for(key)
	}

	/// Does the value (explicitly) exist in storage?
	pub fn contains_key<KeyArg: EncodeLike<Key>>(key: KeyArg) -> bool {
		Map::contains_key(key)
	}

	/// Load the value associated with the given key from the map.
	pub fn get<KeyArg: EncodeLike<Key>>(key: KeyArg) -> Map::Query {
		Map::get(key)
	}

	/// Try to get the value for the given key from the map.
	///
	/// Returns `Ok` if it exists, `Err` if not.
	pub fn try_get<KeyArg: EncodeLike<Key>>(key: KeyArg) -> Result<Value, ()> {
		Map::try_get(key)
	}

	/// Swap the values of two keys.
	pub fn swap<KeyArg1: EncodeLike<Key>, KeyArg2: EncodeLike<Key>>(key1: KeyArg1, key2: KeyArg2) {
		Map::swap(key1, key2)
	}

	/// Store a value to be associated with the given key from the map.
	pub fn insert<KeyArg: EncodeLike<Key> + Clone, ValArg: EncodeLike<Value>>(key: KeyArg, val: ValArg) {
		if !Map::contains_key(key.clone()) {
			Counter::mutate(|value| value.saturating_inc());
		}
		Map::insert(key, val)
	}

	/// Remove the value under a key.
	pub fn remove<KeyArg: EncodeLike<Key> + Clone>(key: KeyArg) {
		if Map::contains_key(key.clone()) {
			Counter::mutate(|value| value.saturating_dec());
		}
		Map::remove(key)
	}

	/// Mutate the value under a key.
	pub fn mutate<KeyArg: EncodeLike<Key> + Clone, R, F: FnOnce(&mut Map::Query) -> R>(
		key: KeyArg,
		f: F
	) -> R {
		Self::mutate_counter(
			Map::mutate,
			key,
			f,
		)
	}

	/// Mutate the item, only if an `Ok` value is returned.
	pub fn try_mutate<KeyArg, R, E, F>(key: KeyArg, f: F) -> Result<R, E>
	where
		KeyArg: EncodeLike<Key> + Clone,
		F: FnOnce(&mut Map::Query) -> Result<R, E>,
	{
		Self::mutate_counter(
			Map::try_mutate,
			key,
			f,
		)
	}

	/// Mutate the value under a key. Deletes the item if mutated to a `None`.
	pub fn mutate_exists<KeyArg: EncodeLike<Key> + Clone, R, F: FnOnce(&mut Option<Value>) -> R>(
		key: KeyArg,
		f: F
	) -> R {
		Self::mutate_counter(
			Map::mutate_exists,
			key,
			f,
		)
	}

	/// Mutate the item, only if an `Ok` value is returned. Deletes the item if mutated to a `None`.
	pub fn try_mutate_exists<KeyArg, R, E, F>(key: KeyArg, f: F) -> Result<R, E>
	where
		KeyArg: EncodeLike<Key> + Clone,
		F: FnOnce(&mut Option<Value>) -> Result<R, E>,
	{
		Self::mutate_counter(
			Map::try_mutate_exists,
			key,
			f,
		)
	}

	/// Take the value under a key.
	pub fn take<KeyArg: EncodeLike<Key> + Clone>(key: KeyArg) -> Map::Query {
		if Map::contains_key(key.clone()) {
			Counter::mutate(|value| value.saturating_dec());
		}
		Map::take(key)
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
		Value: StorageAppend<Item>
	{
		if !Map::contains_key(key.clone()) {
			Counter::mutate(|value| value.saturating_inc());
		}
		Map::append(key, item)
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
		where Value: StorageDecodeLength,
	{
		Map::decode_len(key)
	}

	/// Migrate an item with the given `key` from a defunct `OldHasher` to the current hasher.
	///
	/// If the key doesn't exist, then it's a no-op. If it does, then it returns its value.
	pub fn migrate_key<OldHasher: crate::hash::StorageHasher, KeyArg: EncodeLike<Key>>(
		key: KeyArg
	) -> Option<Value> {
		Map::migrate_key::<OldHasher, _>(key)
	}

	/// Remove all value of the storage.
	pub fn remove_all() {
		Counter::set(0u32);
		Map::remove_all()
	}

	/// Iter over all value of the storage.
	///
	/// NOTE: If a value failed to decode becaues storage is corrupted then it is skipped.
	pub fn iter_values() -> crate::storage::PrefixIterator<Value> {
		Map::iter_values()
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
	pub fn translate_values<OldValue: Decode, F: FnMut(OldValue) -> Option<Value>>(f: F) {
		Map::translate_values(f)
	}

	/// Try and append the given item to the value in the storage.
	///
	/// Is only available if `Value` of the storage implements [`StorageTryAppend`].
	pub fn try_append<KArg, Item, EncodeLikeItem>(
		key: KArg,
		item: EncodeLikeItem,
	) -> Result<(), ()>
	where
		KArg: EncodeLike<Key> + Clone,
		Item: Encode,
		EncodeLikeItem: EncodeLike<Item>,
		Value: StorageTryAppend<Item>,
	{
		<
			Self as crate::storage::TryAppendMap<Key, Value, Item>
		>::try_append(key, item)
	}

	/// Initialize the counter with the actual number of items in the map.
	///
	/// This function iterates through all the items in the map and sets the counter. This operation
	/// can be very heavy, so use with caution.
	///
	/// Returns the number of items in the map which is used to set the counter.
	pub fn initialize_counter() -> u32 {
		let count = Self::iter_values().count() as u32;
		Counter::set(count);
		count
	}

	/// Return the count.
	pub fn count() -> u32 {
		Counter::get()
	}
}
