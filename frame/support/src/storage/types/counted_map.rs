use codec::{FullCodec, Decode, EncodeLike, Encode};
use crate::{
	traits::{StorageInstance, GetDefault, Get, StorageInfo},
	storage::{
		StorageAppend, StorageTryAppend, StorageDecodeLength,
		types::{
			OptionQuery, ValueQuery, StorageMap, StorageValue, QueryKindTrait,
			StorageMapMetadata, StorageValueMetadata
		},
	},
};
use sp_std::prelude::*;
use sp_runtime::traits::Saturating;
use frame_metadata::{
	DefaultByteGetter, StorageEntryModifier,
};
use max_encoded_len::MaxEncodedLen;

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
///
/// The storage prefix for the storage value is the given prefix concatenated with `"Counter"`.
pub struct CountedStorageMap<
	Prefix, Hasher, Key, Value, QueryKind=OptionQuery, OnEmpty=GetDefault, MaxValues=GetDefault,
>(
	core::marker::PhantomData<(Prefix, Hasher, Key, Value, QueryKind, OnEmpty, MaxValues)>
);

/// The requirement for an instance of [`CountedStorageMap`].
pub trait CountedStorageMapInstance: StorageInstance {
	/// The prefix to use for the counter storage value.
	type CounterPrefix: StorageInstance;
}

// Internal helper trait to access map from counted storage map.
trait Helper {
	type Map;
	type Counter;
}

impl<P: CountedStorageMapInstance, H, K, V, Q, O, M>
	Helper
	for CountedStorageMap<P, H, K, V, Q, O, M>
{
	type Map = StorageMap<P, H, K, V, Q, O, M>;
	type Counter = StorageValue<P::CounterPrefix, u32, ValueQuery>;
}

// Do not use storage value, simply implement some get/set/inc/dec

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
	// Internal helper function to track the counter as a value is mutated.
	fn mutate_counter<
		KeyArg: EncodeLike<Key> + Clone,
		M: FnOnce(KeyArg, F) -> R,
		F: FnOnce(I) -> R,
		I,
		R,
	>(m: M, key: KeyArg, f: F) -> R {
		let val_existed = <Self as Helper>::Map::contains_key(key.clone());
		let res = m(key.clone(), f);
		let val_exists = <Self as Helper>::Map::contains_key(key);

		if val_existed && !val_exists {
			// Value was deleted
			<Self as Helper>::Counter::mutate(|value| value.saturating_dec());
		} else if !val_existed && val_exists {
			// Value was added
			<Self as Helper>::Counter::mutate(|value| value.saturating_inc());
		}

		res
	}

	/// Get the storage key used to fetch a value corresponding to a specific key.
	pub fn hashed_key_for<KeyArg: EncodeLike<Key>>(key: KeyArg) -> Vec<u8> {
		<Self as Helper>::Map::hashed_key_for(key)
	}

	/// Does the value (explicitly) exist in storage?
	pub fn contains_key<KeyArg: EncodeLike<Key>>(key: KeyArg) -> bool {
		<Self as Helper>::Map::contains_key(key)
	}

	/// Load the value associated with the given key from the map.
	pub fn get<KeyArg: EncodeLike<Key>>(key: KeyArg) -> QueryKind::Query {
		<Self as Helper>::Map::get(key)
	}

	/// Try to get the value for the given key from the map.
	///
	/// Returns `Ok` if it exists, `Err` if not.
	pub fn try_get<KeyArg: EncodeLike<Key>>(key: KeyArg) -> Result<Value, ()> {
		<Self as Helper>::Map::try_get(key)
	}

	/// Swap the values of two keys.
	pub fn swap<KeyArg1: EncodeLike<Key>, KeyArg2: EncodeLike<Key>>(key1: KeyArg1, key2: KeyArg2) {
		<Self as Helper>::Map::swap(key1, key2)
	}

	/// Store a value to be associated with the given key from the map.
	pub fn insert<KeyArg: EncodeLike<Key> + Clone, ValArg: EncodeLike<Value>>(key: KeyArg, val: ValArg) {
		if !<Self as Helper>::Map::contains_key(key.clone()) {
			<Self as Helper>::Counter::mutate(|value| value.saturating_inc());
		}
		<Self as Helper>::Map::insert(key, val)
	}

	/// Remove the value under a key.
	pub fn remove<KeyArg: EncodeLike<Key> + Clone>(key: KeyArg) {
		if <Self as Helper>::Map::contains_key(key.clone()) {
			<Self as Helper>::Counter::mutate(|value| value.saturating_dec());
		}
		<Self as Helper>::Map::remove(key)
	}

	/// Mutate the value under a key.
	pub fn mutate<KeyArg: EncodeLike<Key> + Clone, R, F: FnOnce(&mut QueryKind::Query) -> R>(
		key: KeyArg,
		f: F
	) -> R {
		Self::mutate_counter(
			<Self as Helper>::Map::mutate,
			key,
			f,
		)
	}

	/// Mutate the item, only if an `Ok` value is returned.
	pub fn try_mutate<KeyArg, R, E, F>(key: KeyArg, f: F) -> Result<R, E>
	where
		KeyArg: EncodeLike<Key> + Clone,
		F: FnOnce(&mut QueryKind::Query) -> Result<R, E>,
	{
		Self::mutate_counter(
			<Self as Helper>::Map::try_mutate,
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
			<Self as Helper>::Map::mutate_exists,
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
			<Self as Helper>::Map::try_mutate_exists,
			key,
			f,
		)
	}

	/// Take the value under a key.
	pub fn take<KeyArg: EncodeLike<Key> + Clone>(key: KeyArg) -> QueryKind::Query {
		if <Self as Helper>::Map::contains_key(key.clone()) {
			<Self as Helper>::Counter::mutate(|value| value.saturating_dec());
		}
		<Self as Helper>::Map::take(key)
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
		if !<Self as Helper>::Map::contains_key(key.clone()) {
			<Self as Helper>::Counter::mutate(|value| value.saturating_inc());
		}
		<Self as Helper>::Map::append(key, item)
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
		<Self as Helper>::Map::decode_len(key)
	}

	/// Migrate an item with the given `key` from a defunct `OldHasher` to the current hasher.
	///
	/// If the key doesn't exist, then it's a no-op. If it does, then it returns its value.
	pub fn migrate_key<OldHasher: crate::hash::StorageHasher, KeyArg: EncodeLike<Key>>(
		key: KeyArg
	) -> Option<Value> {
		<Self as Helper>::Map::migrate_key::<OldHasher, _>(key)
	}

	/// Remove all value of the storage.
	pub fn remove_all() {
		<Self as Helper>::Counter::set(0u32);
		<Self as Helper>::Map::remove_all()
	}

	/// Iter over all value of the storage.
	///
	/// NOTE: If a value failed to decode becaues storage is corrupted then it is skipped.
	pub fn iter_values() -> crate::storage::PrefixIterator<Value> {
		<Self as Helper>::Map::iter_values()
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
		<Self as Helper>::Map::translate_values(f)
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
		let bound = Value::bound();
		let current = <Self as Helper>::Map::decode_len(key.clone()).unwrap_or_default();
		if current < bound {
			<Self as Helper>::Counter::mutate(|value| value.saturating_inc());
			let key = <Self as Helper>::Map::hashed_key_for(key);
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
		<Self as Helper>::Counter::set(count);
		count
	}

	/// Return the count.
	pub fn count() -> u32 {
		<Self as Helper>::Counter::get()
	}
}

/// Part of storage metadata for a counted storage map.
pub trait CountedStorageMapMetadata {
	const MODIFIER: StorageEntryModifier;
	const NAME: &'static str;
	const DEFAULT: DefaultByteGetter;
	const HASHER: frame_metadata::StorageHasher;
	const COUNTER_NAME: &'static str;
	const COUNTER_MODIFIER: StorageEntryModifier;
	const COUNTER_TY: &'static str;
	const COUNTER_DEFAULT: DefaultByteGetter;
	const COUNTER_DOC: &'static str;
}

impl<Prefix, Hasher, Key, Value, QueryKind, OnEmpty, MaxValues> CountedStorageMapMetadata
	for CountedStorageMap<Prefix, Hasher, Key, Value, QueryKind, OnEmpty, MaxValues> where
	Prefix: CountedStorageMapInstance,
	Hasher: crate::hash::StorageHasher,
	Key: FullCodec,
	Value: FullCodec,
	QueryKind: QueryKindTrait<Value, OnEmpty>,
	OnEmpty: Get<QueryKind::Query> + 'static,
	MaxValues: Get<Option<u32>>,
{
	const MODIFIER: StorageEntryModifier = <Self as Helper>::Map::MODIFIER;
	const HASHER: frame_metadata::StorageHasher = <Self as Helper>::Map::HASHER;
	const NAME: &'static str = <Self as Helper>::Map::NAME;
	const DEFAULT: DefaultByteGetter = <Self as Helper>::Map::DEFAULT;
	const COUNTER_NAME: &'static str = <Self as Helper>::Counter::NAME;
	const COUNTER_MODIFIER: StorageEntryModifier = <Self as Helper>::Counter::MODIFIER;
	const COUNTER_TY: &'static str = "u32";
	const COUNTER_DEFAULT: DefaultByteGetter = <Self as Helper>::Counter::DEFAULT;
	const COUNTER_DOC: &'static str = &"Counter for the related counted storage map";
}

impl<Prefix, Hasher, Key, Value, QueryKind, OnEmpty, MaxValues>
	crate::traits::StorageInfoTrait for
	CountedStorageMap<Prefix, Hasher, Key, Value, QueryKind, OnEmpty, MaxValues>
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
		[<Self as Helper>::Map::storage_info(), <Self as Helper>::Counter::storage_info()].concat()
	}
}

// TODO TODO: test that
