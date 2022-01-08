use crate::{
	storage::{
		types::{OptionQuery, QueryKindTrait, StorageDoubleMap, StorageValue, ValueQuery},
		StorageAppend, StorageDecodeLength, StorageTryAppend,
	},
	traits::{Get, GetDefault, StorageInstance},
	Never,
};
use codec::{Decode, Encode, EncodeLike, FullCodec, Ref};
use sp_runtime::traits::Saturating;

pub struct CountedStorageDoubleMap<
	Prefix,
	Hasher1,
	Key1,
	Hasher2,
	Key2,
	Value,
	QueryKind = OptionQuery,
	OnEmpty = GetDefault,
	MaxValues = GetDefault,
>(
	core::marker::PhantomData<(
		Prefix,
		Hasher1,
		Key1,
		Hasher2,
		Key2,
		Value,
		QueryKind,
		OnEmpty,
		MaxValues,
	)>,
);

/// The requirement for an instance of [`CountedStorageDoubleMap`].
pub trait CountedStorageDoubleMapInstance: StorageInstance {
	/// The prefix to use for the counter storage value.
	type CounterPrefix: StorageInstance;
}

// Private helper trait to access map from counted storage double map
trait MapWrapper {
	type Map;
}

impl<P: CountedStorageDoubleMapInstance, H1, K1, H2, K2, V, Q, O, M> MapWrapper
	for CountedStorageDoubleMap<P, H1, K1, H2, K2, V, Q, O, M>
{
	type Map = StorageDoubleMap<P, H1, K1, H2, K2, V, Q, O, M>;
}

type CounterFor<P> =
	StorageValue<<P as CountedStorageDoubleMapInstance>::CounterPrefix, u32, ValueQuery>;

/// On removal logic for updating counter while draining upon some prefix with
/// [`crate::storage::PrefixIterator`].
pub struct OnRemovalCounterUpdate<Prefix>(core::marker::PhantomData<Prefix>);

impl<Prefix: CountedStorageDoubleMapInstance> crate::storage::PrefixIteratorOnRemoval
	for OnRemovalCounterUpdate<Prefix>
{
	fn on_removal(_key: &[u8], _value: &[u8]) {
		CounterFor::<Prefix>::mutate(|value| value.saturating_dec());
	}
}

impl<Prefix, Hasher1, Key1, Hasher2, Key2, Value, QueryKind, OnEmpty, MaxValues>
	CountedStorageDoubleMap<Prefix, Hasher1, Key1, Hasher2, Key2, Value, QueryKind, OnEmpty, MaxValues>
where
	Prefix: CountedStorageDoubleMapInstance,
	Hasher1: crate::hash::StorageHasher,
	Key1: FullCodec,
	Hasher2: crate::hash::StorageHasher,
	Key2: FullCodec,
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
		use crate::storage::generator::StorageDoubleMap;
		<Self as MapWrapper>::Map::prefix_hash()
	}

	/// Get the storage key used to fetch a value corresponding to a specific key.
	pub fn hashed_key_for<KArg1, KArg2>(k1: KArg1, k2: KArg2) -> Vec<u8>
	where
		KArg1: EncodeLike<Key1>,
		KArg2: EncodeLike<Key2>,
	{
		<Self as MapWrapper>::Map::hashed_key_for(k1, k2)
	}

	/// Does the value (explicitly) exist in storage?
	pub fn contains_key<KArg1, KArg2>(k1: KArg1, k2: KArg2) -> bool
	where
		KArg1: EncodeLike<Key1>,
		KArg2: EncodeLike<Key2>,
	{
		<Self as MapWrapper>::Map::contains_key(k1, k2)
	}

	/// Load the value associated with the given key from the double map.
	pub fn get<KArg1, KArg2>(k1: KArg1, k2: KArg2) -> QueryKind::Query
	where
		KArg1: EncodeLike<Key1>,
		KArg2: EncodeLike<Key2>,
	{
		<Self as MapWrapper>::Map::get(k1, k2)
	}

	/// Try to get the value for the given key from the double map.
	///
	/// Returns `Ok` if it exists, `Err` if not.
	pub fn try_get<KArg1, KArg2>(k1: KArg1, k2: KArg2) -> Result<Value, ()>
	where
		KArg1: EncodeLike<Key1>,
		KArg2: EncodeLike<Key2>,
	{
		<Self as MapWrapper>::Map::try_get(k1, k2)
	}

	/// Take a value from storage, removing it afterwards.
	pub fn take<KArg1, KArg2>(k1: KArg1, k2: KArg2) -> QueryKind::Query
	where
		KArg1: EncodeLike<Key1>,
		KArg2: EncodeLike<Key2>,
	{
		<Self as MapWrapper>::Map::take(k1, k2)
	}

	/// Swap the values of two key-pairs.
	pub fn swap<XKArg1, XKArg2, YKArg1, YKArg2>(
		x_k1: XKArg1,
		x_k2: XKArg2,
		y_k1: YKArg1,
		y_k2: YKArg2,
	) where
		XKArg1: EncodeLike<Key1>,
		XKArg2: EncodeLike<Key2>,
		YKArg1: EncodeLike<Key1>,
		YKArg2: EncodeLike<Key2>,
	{
		<Self as MapWrapper>::Map::swap(x_k1, x_k2, y_k1, y_k2)
	}

	/// Store a value to be associated with the given keys from the double map.
	pub fn insert<KArg1, KArg2, VArg>(k1: KArg1, k2: KArg2, val: VArg)
	where
		KArg1: EncodeLike<Key1>,
		KArg2: EncodeLike<Key2>,
		VArg: EncodeLike<Value>,
	{
		if !<Self as MapWrapper>::Map::contains_key(Ref::from(&k1), Ref::from(&k2)) {
			CounterFor::<Prefix>::mutate(|value| value.saturating_inc());
		}
		<Self as MapWrapper>::Map::insert(k1, k2, val)
	}

	/// Remove the value under the given keys.
	pub fn remove<KArg1, KArg2>(k1: KArg1, k2: KArg2)
	where
		KArg1: EncodeLike<Key1>,
		KArg2: EncodeLike<Key2>,
	{
		if !<Self as MapWrapper>::Map::contains_key(Ref::from(&k1), Ref::from(&k2)) {
			CounterFor::<Prefix>::mutate(|value| value.saturating_dec());
		}
		<Self as MapWrapper>::Map::remove(k1, k2)
	}

	// TODO: implement
	/// Remove all values under the first key.
	// pub fn remove_prefix<KArg1>(k1: KArg1)
	// where
	// 	KArg1: ?Sized + EncodeLike<Key1>,
	// {
	// 	<Self as MapWrapper>::Map::remove_prefix(k1, limit)
	// }

	/// Iterate over values that share the first key.
	pub fn iter_prefix_values<KArg1>(
		k1: KArg1,
	) -> crate::storage::PrefixIterator<Value, OnRemovalCounterUpdate<Prefix>>
	where
		KArg1: ?Sized + EncodeLike<Key1>,
	{
		let map_iterator = <Self as MapWrapper>::Map::iter_prefix_values(k1);
		crate::storage::PrefixIterator {
			prefix: map_iterator.prefix,
			previous_key: map_iterator.previous_key,
			drain: map_iterator.drain,
			closure: map_iterator.closure,
			phantom: Default::default(),
		}
	}

	// TODO: implement
	/// Mutate the value under the given keys.
	// pub fn mutate<KArg1, KArg2, R, F>(k1: KArg1, k2: KArg2, f: F) -> R
	// where
	// 	KArg1: EncodeLike<Key1>,
	// 	KArg2: EncodeLike<Key2>,
	// 	F: FnOnce(&mut QueryKind::Query) -> R,
	// {
	// 	Self::try_mutate(k1, k2, |v| Ok::<R, Never>(f(v)))
	// 		.expect("`Never` can not be constructed; qed")
	// }

	// TODO: implement
	/// Mutate the value under the given keys when the closure returns `Ok`.
	// pub fn try_mutate<KArg1, KArg2, R, E, F>(k1: KArg1, k2: KArg2, f: F) -> Result<R, E>
	// where
	// 	KArg1: EncodeLike<Key1>,
	// 	KArg2: EncodeLike<Key2>,
	// 	F: FnOnce(&mut QueryKind::Query) -> Result<R, E>,
	// {
	// 	Self::try_mutate_exists(k1, k2, |option_value_ref| {
	// 		let option_value = core::mem::replace(option_value_ref, None);
	// 		let mut query = <Self as MapWrapper>::Map::from_optional_value_to_query(option_value);
	// 		let res = f(&mut query);
	// 		let option_value = <Self as MapWrapper>::Map::from_query_to_optional_value(query);
	// 		let _ = core::mem::replace(option_value_ref, option_value);
	// 		res
	// 	})
	// }

	// TODO: implement
	/// Mutate the value under the given keys. Deletes the item if mutated to a `None`.
	// pub fn mutate_exists<KArg1, KArg2, R, F>(k1: KArg1, k2: KArg2, f: F) -> R
	// where
	// 	KArg1: EncodeLike<Key1>,
	// 	KArg2: EncodeLike<Key2>,
	// 	F: FnOnce(&mut Option<Value>) -> R,
	// {
	// 	Self::try_mutate_exists(k1, k2, |v| Ok::<R, Never>(f(v)))
	// 		.expect("`Never` can not be constructed; qed")
	// }

	// TODO: implement
	/// Mutate the item, only if an `Ok` value is returned. Deletes the item if mutated to a `None`.
	// pub fn try_mutate_exists<KArg1, KArg2, R, E, F>(k1: KArg1, k2: KArg2, f: F) -> Result<R, E>
	// where
	// 	KArg1: EncodeLike<Key1>,
	// 	KArg2: EncodeLike<Key2>,
	// 	F: FnOnce(&mut Option<Value>) -> Result<R, E>,
	// {
	// 	<Self as MapWrapper>::Map::try_mutate_exists(k1, k2, |option_value| {
	// 		let existed = option_value.is_some();
	// 		let res = f(option_value);
	// 		let exist = option_value.is_some();

	// 		if res.is_ok() {
	// 			if existed && !exist {
	// 				// Value was deleted
	// 				CounterFor::<Prefix>::mutate(|value| value.saturating_dec());
	// 			} else if !existed && exist {
	// 				// Value was added
	// 				CounterFor::<Prefix>::mutate(|value| value.saturating_inc());
	// 			}
	// 		}
	// 		res
	// 	})
	// }

	/// Append the given item to the value in the storage.
	///
	/// `Value` is required to implement [`StorageAppend`].
	///
	/// # Warning
	///
	/// If the storage item is not encoded properly, the storage will be overwritten
	/// and set to `[item]`. Any default value set for the storage item will be ignored
	/// on overwrite.
	pub fn append<Item, EncodeLikeItem, KArg1, KArg2>(k1: KArg1, k2: KArg2, item: EncodeLikeItem)
	where
		KArg1: EncodeLike<Key1>,
		KArg2: EncodeLike<Key2>,
		Item: Encode,
		EncodeLikeItem: EncodeLike<Item>,
		Value: StorageAppend<Item>,
	{
		if !<Self as MapWrapper>::Map::contains_key(Ref::from(&k1), Ref::from(&k2)) {
			CounterFor::<Prefix>::mutate(|value| value.saturating_inc());
		}
		<Self as MapWrapper>::Map::append(k1, k2, item)
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
	pub fn decode_len<KArg1, KArg2>(key1: KArg1, key2: KArg2) -> Option<usize>
	where
		KArg1: EncodeLike<Key1>,
		KArg2: EncodeLike<Key2>,
		Value: StorageDecodeLength,
	{
		<Self as MapWrapper>::Map::decode_len(key1, key2)
	}

	/// Migrate an item with the given `key1` and `key2` from defunct `OldHasher1` and
	/// `OldHasher2` to the current hashers.
	///
	/// If the key doesn't exist, then it's a no-op. If it does, then it returns its value.
	pub fn migrate_keys<
		OldHasher1: crate::StorageHasher,
		OldHasher2: crate::StorageHasher,
		KeyArg1: EncodeLike<Key1>,
		KeyArg2: EncodeLike<Key2>,
	>(
		key1: KeyArg1,
		key2: KeyArg2,
	) -> Option<Value> {
		<Self as MapWrapper>::Map::migrate_keys::<OldHasher1, OldHasher2, _, _>(key1, key2)
	}

	/// Remove all value of the storage.
	pub fn remove_all() {
		// NOTE: it is not possible to remove up to some limit because
		// `sp_io::storage::clear_prefix` and `StorageMap::remove_all` don't give the number of
		// value removed from the overlay.
		CounterFor::<Prefix>::set(0u32);
		<Self as MapWrapper>::Map::remove_all(None);
	}

	/// Iter over all value of the storage.
	///
	/// NOTE: If a value failed to decode because storage is corrupted then it is skipped.
	pub fn iter_values() -> crate::storage::PrefixIterator<Value, OnRemovalCounterUpdate<Prefix>> {
		let map_iterator = <Self as MapWrapper>::Map::iter_values();
		crate::storage::PrefixIterator {
			prefix: map_iterator.prefix,
			previous_key: map_iterator.previous_key,
			drain: map_iterator.drain,
			closure: map_iterator.closure,
			phantom: Default::default(),
		}
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

	// TODO: implement
	/// Try and append the given item to the value in the storage.
	///
	/// Is only available if `Value` of the storage implements [`StorageTryAppend`].
	// pub fn try_append<KArg1, KArg2, Item, EncodeLikeItem>(
	// 	key1: KArg1,
	// 	key2: KArg2,
	// 	item: EncodeLikeItem,
	// ) -> Result<(), ()>
	// where
	// 	KArg1: EncodeLike<Key1> + Clone,
	// 	KArg2: EncodeLike<Key2> + Clone,
	// 	Item: Encode,
	// 	EncodeLikeItem: EncodeLike<Item>,
	// 	Value: StorageTryAppend<Item>,
	// {
	// 	<Self as crate::storage::TryAppendDoubleMap<Key1, Key2, Value, Item>>::try_append(
	// 		key1, key2, item,
	// 	)
	// }

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

impl<Prefix, Hasher1, Key1, Hasher2, Key2, Value, QueryKind, OnEmpty, MaxValues>
	CountedStorageDoubleMap<Prefix, Hasher1, Key1, Hasher2, Key2, Value, QueryKind, OnEmpty, MaxValues>
where
	Prefix: CountedStorageDoubleMapInstance,
	Hasher1: crate::hash::StorageHasher + crate::ReversibleStorageHasher,
	Key1: FullCodec,
	Hasher2: crate::hash::StorageHasher + crate::ReversibleStorageHasher,
	Key2: FullCodec,
	Value: FullCodec,
	QueryKind: QueryKindTrait<Value, OnEmpty>,
	OnEmpty: Get<QueryKind::Query> + 'static,
	MaxValues: Get<Option<u32>>,
{
	/// Enumerate all elements in the map with first key `k1` in no particular order.
	///
	/// If you add or remove values whose first key is `k1` to the map while doing this, you'll get
	/// undefined results.
	pub fn iter_prefix(
		k1: impl EncodeLike<Key1>,
	) -> crate::storage::PrefixIterator<(Key2, Value), OnRemovalCounterUpdate<Prefix>> {
		let map_iterator = <Self as MapWrapper>::Map::iter_prefix(k1);
		crate::storage::PrefixIterator {
			prefix: map_iterator.prefix,
			previous_key: map_iterator.previous_key,
			drain: map_iterator.drain,
			closure: map_iterator.closure,
			phantom: Default::default(),
		}
	}

	/// Enumerate all elements in the map with first key `k1` after a specified `starting_raw_key`
	/// in no particular order.
	///
	/// If you add or remove values whose first key is `k1` to the map while doing this, you'll get
	/// undefined results.
	pub fn iter_prefix_from(
		k1: impl EncodeLike<Key1>,
		starting_raw_key: Vec<u8>,
	) -> crate::storage::PrefixIterator<(Key2, Value), OnRemovalCounterUpdate<Prefix>> {
		let map_iterator = <Self as MapWrapper>::Map::iter_prefix_from(k1, starting_raw_key);
		crate::storage::PrefixIterator {
			prefix: map_iterator.prefix,
			previous_key: map_iterator.previous_key,
			drain: map_iterator.drain,
			closure: map_iterator.closure,
			phantom: Default::default(),
		}
	}

	/// Enumerate all second keys `k2` in the map with the same first key `k1` in no particular
	/// order.
	///
	/// If you add or remove values whose first key is `k1` to the map while doing this, you'll get
	/// undefined results.
	pub fn iter_key_prefix(k1: impl EncodeLike<Key1>) -> crate::storage::KeyPrefixIterator<Key2> {
		<Self as MapWrapper>::Map::iter_key_prefix(k1)
	}

	/// Enumerate all second keys `k2` in the map with the same first key `k1` after a specified
	/// `starting_raw_key` in no particular order.
	///
	/// If you add or remove values whose first key is `k1` to the map while doing this, you'll get
	/// undefined results.
	pub fn iter_key_prefix_from(
		k1: impl EncodeLike<Key1>,
		starting_raw_key: Vec<u8>,
	) -> crate::storage::KeyPrefixIterator<Key2> {
		<Self as MapWrapper>::Map::iter_key_prefix_from(k1, starting_raw_key)
	}

	/// Remove all elements from the map with first key `k1` and iterate through them in no
	/// particular order.
	///
	/// If you add elements with first key `k1` to the map while doing this, you'll get undefined
	/// results.
	pub fn drain_prefix(
		k1: impl EncodeLike<Key1>,
	) -> crate::storage::PrefixIterator<(Key2, Value), OnRemovalCounterUpdate<Prefix>> {
		let map_iterator = <Self as MapWrapper>::Map::drain_prefix(k1);
		crate::storage::PrefixIterator {
			prefix: map_iterator.prefix,
			previous_key: map_iterator.previous_key,
			drain: map_iterator.drain,
			closure: map_iterator.closure,
			phantom: Default::default(),
		}
	}

	/// Enumerate all elements in the map in no particular order.
	///
	/// If you add or remove values to the map while doing this, you'll get undefined results.
	pub fn iter(
	) -> crate::storage::PrefixIterator<(Key1, Key2, Value), OnRemovalCounterUpdate<Prefix>> {
		let map_iterator = <Self as MapWrapper>::Map::iter();
		crate::storage::PrefixIterator {
			prefix: map_iterator.prefix,
			previous_key: map_iterator.previous_key,
			drain: map_iterator.drain,
			closure: map_iterator.closure,
			phantom: Default::default(),
		}
	}

	/// Enumerate all elements in the map after a specified `starting_raw_key` in no particular
	/// order.
	///
	/// If you add or remove values to the map while doing this, you'll get undefined results.
	pub fn iter_from(
		starting_raw_key: Vec<u8>,
	) -> crate::storage::PrefixIterator<(Key1, Key2, Value), OnRemovalCounterUpdate<Prefix>> {
		let map_iterator = <Self as MapWrapper>::Map::iter_from(starting_raw_key);
		crate::storage::PrefixIterator {
			prefix: map_iterator.prefix,
			previous_key: map_iterator.previous_key,
			drain: map_iterator.drain,
			closure: map_iterator.closure,
			phantom: Default::default(),
		}
	}

	/// Enumerate all keys `k1` and `k2` in the map in no particular order.
	///
	/// If you add or remove values to the map while doing this, you'll get undefined results.
	pub fn iter_keys() -> crate::storage::KeyPrefixIterator<(Key1, Key2)> {
		<Self as MapWrapper>::Map::iter_keys()
	}

	/// Enumerate all keys `k1` and `k2` in the map after a specified `starting_raw_key` in no
	/// particular order.
	///
	/// If you add or remove values to the map while doing this, you'll get undefined results.
	pub fn iter_keys_from(
		starting_raw_key: Vec<u8>,
	) -> crate::storage::KeyPrefixIterator<(Key1, Key2)> {
		<Self as MapWrapper>::Map::iter_keys_from(starting_raw_key)
	}

	/// Remove all elements from the map and iterate through them in no particular order.
	///
	/// If you add elements to the map while doing this, you'll get undefined results.
	pub fn drain(
	) -> crate::storage::PrefixIterator<(Key1, Key2, Value), OnRemovalCounterUpdate<Prefix>> {
		let map_iterator = <Self as MapWrapper>::Map::drain();
		crate::storage::PrefixIterator {
			prefix: map_iterator.prefix,
			previous_key: map_iterator.previous_key,
			drain: map_iterator.drain,
			closure: map_iterator.closure,
			phantom: Default::default(),
		}
	}

	/// Translate the values of all elements by a function `f`, in the map in no particular order.
	///
	/// By returning `None` from `f` for an element, you'll remove it from the map.
	///
	/// NOTE: If a value fail to decode because storage is corrupted then it is skipped.
	pub fn translate<O: Decode, F: FnMut(Key1, Key2, O) -> Option<Value>>(mut f: F) {
		<Self as MapWrapper>::Map::translate(|k1, k2, old_value| {
			let res = f(k1, k2, old_value);
			if res.is_none() {
				CounterFor::<Prefix>::mutate(|value| value.saturating_dec());
			}
			res
		})
	}
}
