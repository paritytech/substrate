use crate::{
	metadata::StorageEntryMetadata,
	storage::{
		types::{
			OptionQuery, QueryKindTrait, StorageDoubleMap, StorageEntryMetadataBuilder,
			StorageValue, ValueQuery,
		},
		StorageAppend, StorageDecodeLength, StorageTryAppend,
	},
	traits::{
		Get, GetDefault, PartialStorageInfoTrait, StorageInfo, StorageInfoTrait, StorageInstance,
	},
	Never,
};
use codec::{Decode, Encode, EncodeLike, FullCodec, MaxEncodedLen, Ref};
use sp_runtime::traits::Saturating;
use sp_std::prelude::*;

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
		let removed_value = <Self as MapWrapper>::Map::mutate_exists(k1, k2, |value| {
			core::mem::replace(value, None)
		});
		if removed_value.is_some() {
			CounterFor::<Prefix>::mutate(|value| value.saturating_dec());
		}
		QueryKind::from_optional_value_to_query(removed_value)
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
		if <Self as MapWrapper>::Map::contains_key(Ref::from(&k1), Ref::from(&k2)) {
			CounterFor::<Prefix>::mutate(|value| value.saturating_dec());
		}
		<Self as MapWrapper>::Map::remove(k1, k2)
	}

	/// Remove all values under the first key.
	///
	/// # Warning
	///
	/// Expensive operation, need to iterate over all 'k1' prefixes to calculate how many values
	/// need to remove
	pub fn remove_prefix<KArg1>(k1: KArg1)
	where
		KArg1: ?Sized + EncodeLike<Key1>,
	{
		let mut on_remove = 0;
		Self::iter_prefix_values(Ref::from(&k1)).for_each(|_| {
			on_remove += 1;
		});
		CounterFor::<Prefix>::mutate(|value| {
			*value = value.saturating_sub(on_remove);
		});
		<Self as MapWrapper>::Map::remove_prefix(k1, None);
	}

	/// Iterate over values that share the first key.
	pub fn iter_prefix_values<KArg1>(
		k1: KArg1,
	) -> crate::storage::PrefixIterator<Value, OnRemovalCounterUpdate<Prefix>>
	where
		KArg1: ?Sized + EncodeLike<Key1>,
	{
		<Self as MapWrapper>::Map::iter_prefix_values(k1).convert_on_removal()
	}

	/// Mutate the value under the given keys.
	pub fn mutate<KArg1, KArg2, R, F>(k1: KArg1, k2: KArg2, f: F) -> R
	where
		KArg1: EncodeLike<Key1>,
		KArg2: EncodeLike<Key2>,
		F: FnOnce(&mut QueryKind::Query) -> R,
	{
		Self::try_mutate(k1, k2, |v| Ok::<R, Never>(f(v)))
			.expect("`Never` can not be constructed; qed")
	}

	/// Mutate the value under the given keys when the closure returns `Ok`.
	pub fn try_mutate<KArg1, KArg2, R, E, F>(k1: KArg1, k2: KArg2, f: F) -> Result<R, E>
	where
		KArg1: EncodeLike<Key1>,
		KArg2: EncodeLike<Key2>,
		F: FnOnce(&mut QueryKind::Query) -> Result<R, E>,
	{
		Self::try_mutate_exists(k1, k2, |option_value_ref| {
			let option_value = core::mem::replace(option_value_ref, None);
			let mut query = QueryKind::from_optional_value_to_query(option_value);
			let res = f(&mut query);
			let option_value = QueryKind::from_query_to_optional_value(query);
			let _ = core::mem::replace(option_value_ref, option_value);
			res
		})
	}

	/// Mutate the value under the given keys. Deletes the item if mutated to a `None`.
	pub fn mutate_exists<KArg1, KArg2, R, F>(k1: KArg1, k2: KArg2, f: F) -> R
	where
		KArg1: EncodeLike<Key1>,
		KArg2: EncodeLike<Key2>,
		F: FnOnce(&mut Option<Value>) -> R,
	{
		Self::try_mutate_exists(k1, k2, |v| Ok::<R, Never>(f(v)))
			.expect("`Never` can not be constructed; qed")
	}

	/// Mutate the item, only if an `Ok` value is returned. Deletes the item if mutated to a `None`.
	pub fn try_mutate_exists<KArg1, KArg2, R, E, F>(k1: KArg1, k2: KArg2, f: F) -> Result<R, E>
	where
		KArg1: EncodeLike<Key1>,
		KArg2: EncodeLike<Key2>,
		F: FnOnce(&mut Option<Value>) -> Result<R, E>,
	{
		<Self as MapWrapper>::Map::try_mutate_exists(k1, k2, |option_value| {
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
		<Self as MapWrapper>::Map::iter_values().convert_on_removal()
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

	/// Try and append the given item to the value in the storage.
	///
	/// Is only available if `Value` of the storage implements [`StorageTryAppend`].
	pub fn try_append<KArg1, KArg2, Item, EncodeLikeItem>(
		key1: KArg1,
		key2: KArg2,
		item: EncodeLikeItem,
	) -> Result<(), ()>
	where
		KArg1: EncodeLike<Key1> + Clone,
		KArg2: EncodeLike<Key2> + Clone,
		Item: Encode,
		EncodeLikeItem: EncodeLike<Item>,
		Value: StorageTryAppend<Item>,
	{
		let bound = Value::bound();
		let current = <Self as MapWrapper>::Map::decode_len(Ref::from(&key1), Ref::from(&key2))
			.unwrap_or_default();
		if current < bound {
			CounterFor::<Prefix>::mutate(|value| value.saturating_inc());
			let key = <Self as MapWrapper>::Map::hashed_key_for(key1, key2);
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
		<Self as MapWrapper>::Map::iter_prefix(k1).convert_on_removal()
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
		<Self as MapWrapper>::Map::iter_prefix_from(k1, starting_raw_key).convert_on_removal()
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
		<Self as MapWrapper>::Map::drain_prefix(k1).convert_on_removal()
	}

	/// Enumerate all elements in the map in no particular order.
	///
	/// If you add or remove values to the map while doing this, you'll get undefined results.
	pub fn iter(
	) -> crate::storage::PrefixIterator<(Key1, Key2, Value), OnRemovalCounterUpdate<Prefix>> {
		<Self as MapWrapper>::Map::iter().convert_on_removal()
	}

	/// Enumerate all elements in the map after a specified `starting_raw_key` in no particular
	/// order.
	///
	/// If you add or remove values to the map while doing this, you'll get undefined results.
	pub fn iter_from(
		starting_raw_key: Vec<u8>,
	) -> crate::storage::PrefixIterator<(Key1, Key2, Value), OnRemovalCounterUpdate<Prefix>> {
		<Self as MapWrapper>::Map::iter_from(starting_raw_key).convert_on_removal()
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
		<Self as MapWrapper>::Map::drain().convert_on_removal()
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

impl<Prefix, Hasher1, Hasher2, Key1, Key2, Value, QueryKind, OnEmpty, MaxValues>
	StorageEntryMetadataBuilder
	for CountedStorageDoubleMap<
		Prefix,
		Hasher1,
		Key1,
		Hasher2,
		Key2,
		Value,
		QueryKind,
		OnEmpty,
		MaxValues,
	> where
	Prefix: CountedStorageDoubleMapInstance,
	Hasher1: crate::hash::StorageHasher,
	Hasher2: crate::hash::StorageHasher,
	Key1: FullCodec + scale_info::StaticTypeInfo,
	Key2: FullCodec + scale_info::StaticTypeInfo,
	Value: FullCodec + scale_info::StaticTypeInfo,
	QueryKind: QueryKindTrait<Value, OnEmpty>,
	OnEmpty: Get<QueryKind::Query> + 'static,
	MaxValues: Get<Option<u32>>,
{
	fn build_metadata(docs: Vec<&'static str>, entries: &mut Vec<StorageEntryMetadata>) {
		<Self as MapWrapper>::Map::build_metadata(docs, entries);
		CounterFor::<Prefix>::build_metadata(
			vec![&"Counter for the related counted storage map"],
			entries,
		);
	}
}

impl<Prefix, Hasher1, Hasher2, Key1, Key2, Value, QueryKind, OnEmpty, MaxValues> StorageInfoTrait
	for CountedStorageDoubleMap<
		Prefix,
		Hasher1,
		Key1,
		Hasher2,
		Key2,
		Value,
		QueryKind,
		OnEmpty,
		MaxValues,
	> where
	Prefix: CountedStorageDoubleMapInstance,
	Hasher1: crate::hash::StorageHasher,
	Hasher2: crate::hash::StorageHasher,
	Key1: FullCodec + MaxEncodedLen,
	Key2: FullCodec + MaxEncodedLen,
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
impl<Prefix, Hasher1, Hasher2, Key1, Key2, Value, QueryKind, OnEmpty, MaxValues>
	PartialStorageInfoTrait
	for CountedStorageDoubleMap<
		Prefix,
		Hasher1,
		Key1,
		Hasher2,
		Key2,
		Value,
		QueryKind,
		OnEmpty,
		MaxValues,
	> where
	Prefix: CountedStorageDoubleMapInstance,
	Hasher1: crate::hash::StorageHasher,
	Hasher2: crate::hash::StorageHasher,
	Key1: FullCodec,
	Key2: FullCodec,
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
		storage::bounded_vec::BoundedVec,
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
	impl CountedStorageDoubleMapInstance for Prefix {
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
		type A = CountedStorageDoubleMap<
			Prefix,
			Blake2_128Concat,
			u16,
			Twox64Concat,
			u8,
			u32,
			ValueQuery,
			ADefault,
		>;
		TestExternalities::default().execute_with(|| {
			let mut k: Vec<u8> = vec![];
			k.extend(&twox_128(b"test"));
			k.extend(&twox_128(b"foo"));
			k.extend(&3u16.blake2_128_concat());
			k.extend(&30u8.twox_64_concat());
			assert_eq!(A::hashed_key_for(3, 30).to_vec(), k);

			assert_eq!(A::contains_key(3, 30), false);
			assert_eq!(A::get(3, 30), ADefault::get());
			assert_eq!(A::try_get(3, 30), Err(()));
			assert_eq!(A::count(), 0);

			A::insert(3, 30, 10);
			assert_eq!(A::contains_key(3, 30), true);
			assert_eq!(A::get(3, 30), 10);
			assert_eq!(A::try_get(3, 30), Ok(10));
			assert_eq!(A::count(), 1);

			A::swap(3, 30, 2, 20);
			assert_eq!(A::contains_key(3, 30), false);
			assert_eq!(A::contains_key(2, 20), true);
			assert_eq!(A::get(3, 30), ADefault::get());
			assert_eq!(A::try_get(3, 30), Err(()));
			assert_eq!(A::get(2, 20), 10);
			assert_eq!(A::try_get(2, 20), Ok(10));
			assert_eq!(A::count(), 1);

			A::swap(3, 30, 2, 20);
			assert_eq!(A::contains_key(3, 30), true);
			assert_eq!(A::contains_key(2, 20), false);
			assert_eq!(A::get(3, 30), 10);
			assert_eq!(A::try_get(3, 30), Ok(10));
			assert_eq!(A::get(2, 20), ADefault::get());
			assert_eq!(A::try_get(2, 20), Err(()));
			assert_eq!(A::count(), 1);

			A::insert(4, 40, 11);
			assert_eq!(A::try_get(3, 30), Ok(10));
			assert_eq!(A::try_get(4, 40), Ok(11));
			assert_eq!(A::count(), 2);

			// Swap 2 existing.
			A::swap(3, 30, 4, 40);

			assert_eq!(A::try_get(3, 30), Ok(11));
			assert_eq!(A::try_get(4, 40), Ok(10));
			assert_eq!(A::count(), 2);

			// Insert an existing key, shouldn't increment counted values.
			A::insert(3, 30, 12);
			assert_eq!(A::try_get(3, 30), Ok(12));
			assert_eq!(A::count(), 2);

			// Remove non-existing.
			A::remove(2, 20);
			assert_eq!(A::contains_key(2, 20), false);
			assert_eq!(A::count(), 2);

			// Remove existing.
			A::remove(3, 30);

			assert_eq!(A::try_get(3, 30), Err(()));
			assert_eq!(A::count(), 1);

			// Mutate non-existing to existing.
			A::mutate(3, 30, |query| {
				assert_eq!(*query, ADefault::get());
				*query = 40;
			});

			assert_eq!(A::try_get(3, 30), Ok(40));
			assert_eq!(A::count(), 2);

			// Try fail mutate non-existing to existing.
			A::try_mutate(2, 20, |query| {
				assert_eq!(*query, ADefault::get());
				*query = 4;
				Result::<(), ()>::Err(())
			})
			.err()
			.unwrap();

			assert_eq!(A::try_get(2, 20), Err(()));
			assert_eq!(A::count(), 2);

			// Try succeed mutate non-existing to existing.
			A::try_mutate(2, 20, |query| {
				assert_eq!(*query, ADefault::get());
				*query = 41;
				Result::<(), ()>::Ok(())
			})
			.unwrap();

			assert_eq!(A::try_get(2, 20), Ok(41));
			assert_eq!(A::count(), 3);

			// Try succeed mutate existing to existing.
			A::try_mutate(2, 20, |query| {
				assert_eq!(*query, 41);
				*query = 41;
				Result::<(), ()>::Ok(())
			})
			.unwrap();

			assert_eq!(A::try_get(2, 20), Ok(41));
			assert_eq!(A::count(), 3);

			// Try fail mutate non-existing to existing.
			A::try_mutate_exists(1, 10, |query| {
				assert_eq!(*query, None);
				*query = Some(4);
				Result::<(), ()>::Err(())
			})
			.err()
			.unwrap();

			assert_eq!(A::try_get(1, 10), Err(()));
			assert_eq!(A::count(), 3);

			// Try succeed mutate non-existing to existing.
			A::try_mutate_exists(1, 10, |query| {
				assert_eq!(*query, None);
				*query = Some(43);
				Result::<(), ()>::Ok(())
			})
			.unwrap();

			assert_eq!(A::try_get(1, 10), Ok(43));
			assert_eq!(A::count(), 4);

			// Try succeed mutate existing to existing.
			A::try_mutate_exists(1, 10, |query| {
				assert_eq!(*query, Some(43));
				*query = Some(45);
				Result::<(), ()>::Ok(())
			})
			.unwrap();

			assert_eq!(A::try_get(1, 10), Ok(45));
			assert_eq!(A::count(), 4);

			// Try succeed mutate existing to non-existing.
			A::try_mutate_exists(1, 10, |query| {
				assert_eq!(*query, Some(45));
				*query = None;
				Result::<(), ()>::Ok(())
			})
			.unwrap();

			assert_eq!(A::try_get(1, 10), Err(()));
			assert_eq!(A::count(), 3);

			// Take exsisting.
			assert_eq!(A::take(4, 40), 10);

			assert_eq!(A::try_get(4, 40), Err(()));
			assert_eq!(A::count(), 2);

			// Take non-exsisting.
			assert_eq!(A::take(4, 40), ADefault::get());

			assert_eq!(A::try_get(4, 40), Err(()));
			assert_eq!(A::count(), 2);

			// Remove all.
			A::remove_all();

			assert_eq!(A::count(), 0);
			assert_eq!(A::initialize_counter(), 0);

			A::insert(1, 10, 1);
			A::insert(2, 20, 2);

			// Iter values.
			assert_eq!(A::iter_values().collect::<Vec<_>>(), vec![2, 1]);

			// Iter drain values.
			assert_eq!(A::iter_values().drain().collect::<Vec<_>>(), vec![2, 1]);
			assert_eq!(A::count(), 0);

			A::insert(1, 10, 1);
			A::insert(2, 20, 2);

			// Test initialize_counter.
			assert_eq!(A::initialize_counter(), 2);
		})
	}

	#[test]
	fn test_option_query() {
		type B = CountedStorageDoubleMap<Prefix, Blake2_256, u16, Twox64Concat, u8, u32>;
		TestExternalities::default().execute_with(|| {
			let mut k: Vec<u8> = vec![];
			k.extend(&twox_128(b"test"));
			k.extend(&twox_128(b"foo"));
			k.extend(&3u16.blake2_256());
			k.extend(&30u8.twox_64_concat());
			assert_eq!(B::hashed_key_for(3, 30).to_vec(), k);

			assert_eq!(B::contains_key(3, 30), false);
			assert_eq!(B::get(3, 30), None);
			assert_eq!(B::try_get(3, 30), Err(()));
			assert_eq!(B::count(), 0);

			// Insert non-existing.
			B::insert(3, 30, 10);

			assert_eq!(B::contains_key(3, 30), true);
			assert_eq!(B::get(3, 30), Some(10));
			assert_eq!(B::try_get(3, 30), Ok(10));
			assert_eq!(B::count(), 1);

			// Swap non-existing with existing.
			B::swap(4, 40, 3, 30);

			assert_eq!(B::contains_key(3, 30), false);
			assert_eq!(B::get(3, 30), None);
			assert_eq!(B::try_get(3, 30), Err(()));
			assert_eq!(B::contains_key(4, 40), true);
			assert_eq!(B::get(4, 40), Some(10));
			assert_eq!(B::try_get(4, 40), Ok(10));
			assert_eq!(B::count(), 1);

			// Swap existing with non-existing.
			B::swap(4, 40, 3, 30);

			assert_eq!(B::try_get(3, 30), Ok(10));
			assert_eq!(B::contains_key(4, 40), false);
			assert_eq!(B::get(4, 40), None);
			assert_eq!(B::try_get(4, 40), Err(()));
			assert_eq!(B::count(), 1);

			B::insert(4, 40, 11);

			assert_eq!(B::try_get(3, 30), Ok(10));
			assert_eq!(B::try_get(4, 40), Ok(11));
			assert_eq!(B::count(), 2);

			// Swap 2 existing.
			B::swap(3, 30, 4, 40);

			assert_eq!(B::try_get(3, 30), Ok(11));
			assert_eq!(B::try_get(4, 40), Ok(10));
			assert_eq!(B::count(), 2);

			// Insert an existing key, shouldn't increment counted values.
			B::insert(3, 30, 11);

			assert_eq!(B::count(), 2);

			// Remove non-existing.
			B::remove(2, 20);

			assert_eq!(B::contains_key(2, 20), false);
			assert_eq!(B::count(), 2);

			// Remove existing.
			B::remove(3, 30);

			assert_eq!(B::try_get(3, 30), Err(()));
			assert_eq!(B::count(), 1);

			// Mutate non-existing to existing.
			B::mutate(3, 30, |query| {
				assert_eq!(*query, None);
				*query = Some(40)
			});

			assert_eq!(B::try_get(3, 30), Ok(40));
			assert_eq!(B::count(), 2);

			// Mutate existing to existing.
			B::mutate(3, 30, |query| {
				assert_eq!(*query, Some(40));
				*query = Some(40)
			});

			assert_eq!(B::try_get(3, 30), Ok(40));
			assert_eq!(B::count(), 2);

			// Mutate existing to non-existing.
			B::mutate(3, 30, |query| {
				assert_eq!(*query, Some(40));
				*query = None
			});

			assert_eq!(B::try_get(3, 30), Err(()));
			assert_eq!(B::count(), 1);

			B::insert(3, 30, 40);

			// Try fail mutate non-existing to existing.
			B::try_mutate(2, 20, |query| {
				assert_eq!(*query, None);
				*query = Some(4);
				Result::<(), ()>::Err(())
			})
			.err()
			.unwrap();

			assert_eq!(B::try_get(2, 20), Err(()));
			assert_eq!(B::count(), 2);

			// Try succeed mutate non-existing to existing.
			B::try_mutate(2, 20, |query| {
				assert_eq!(*query, None);
				*query = Some(41);
				Result::<(), ()>::Ok(())
			})
			.unwrap();

			assert_eq!(B::try_get(2, 20), Ok(41));
			assert_eq!(B::count(), 3);

			// Try succeed mutate existing to existing.
			B::try_mutate(2, 20, |query| {
				assert_eq!(*query, Some(41));
				*query = Some(41);
				Result::<(), ()>::Ok(())
			})
			.unwrap();

			assert_eq!(B::try_get(2, 20), Ok(41));
			assert_eq!(B::count(), 3);

			// Try succeed mutate existing to non-existing.
			B::try_mutate(2, 20, |query| {
				assert_eq!(*query, Some(41));
				*query = None;
				Result::<(), ()>::Ok(())
			})
			.unwrap();

			assert_eq!(B::try_get(2, 20), Err(()));
			assert_eq!(B::count(), 2);

			B::insert(2, 20, 41);

			// Try fail mutate non-existing to existing.
			B::try_mutate_exists(1, 10, |query| {
				assert_eq!(*query, None);
				*query = Some(4);
				Result::<(), ()>::Err(())
			})
			.err()
			.unwrap();

			assert_eq!(B::try_get(1, 10), Err(()));
			assert_eq!(B::count(), 3);

			// Try succeed mutate non-existing to existing.
			B::try_mutate_exists(1, 10, |query| {
				assert_eq!(*query, None);
				*query = Some(43);
				Result::<(), ()>::Ok(())
			})
			.unwrap();

			assert_eq!(B::try_get(1, 10), Ok(43));
			assert_eq!(B::count(), 4);

			// Try succeed mutate existing to existing.
			B::try_mutate_exists(1, 10, |query| {
				assert_eq!(*query, Some(43));
				*query = Some(43);
				Result::<(), ()>::Ok(())
			})
			.unwrap();

			assert_eq!(B::try_get(1, 10), Ok(43));
			assert_eq!(B::count(), 4);

			// Try succeed mutate existing to non-existing.
			B::try_mutate_exists(1, 10, |query| {
				assert_eq!(*query, Some(43));
				*query = None;
				Result::<(), ()>::Ok(())
			})
			.unwrap();

			assert_eq!(B::try_get(1, 10), Err(()));
			assert_eq!(B::count(), 3);

			// Take exsisting.
			assert_eq!(B::take(4, 40), Some(10));

			assert_eq!(B::try_get(4, 40), Err(()));
			assert_eq!(B::count(), 2);

			// Take non-exsisting.
			assert_eq!(B::take(4, 40), None);

			assert_eq!(B::try_get(4, 40), Err(()));
			assert_eq!(B::count(), 2);

			// Remove all.
			B::remove_all();

			assert_eq!(B::count(), 0);
			assert_eq!(B::initialize_counter(), 0);

			B::insert(1, 10, 1);
			B::insert(2, 20, 2);

			// Iter values.
			assert_eq!(B::iter_values().collect::<Vec<_>>(), vec![1, 2]);

			// Iter drain values.
			assert_eq!(B::iter_values().drain().collect::<Vec<_>>(), vec![1, 2]);
			assert_eq!(B::count(), 0);

			B::insert(1, 10, 1);
			B::insert(2, 20, 2);

			// Test initialize_counter.
			assert_eq!(B::initialize_counter(), 2);
		})
	}

	#[test]
	fn append_decode_len_works() {
		type B = CountedStorageDoubleMap<Prefix, Blake2_256, u16, Twox64Concat, u8, Vec<u32>>;
		TestExternalities::default().execute_with(|| {
			assert_eq!(B::decode_len(1, 10), None);
			B::append(1, 10, 3);
			assert_eq!(B::decode_len(1, 10), Some(1));
			B::append(1, 10, 3);
			assert_eq!(B::decode_len(1, 10), Some(2));
			B::append(1, 10, 3);
			assert_eq!(B::decode_len(1, 10), Some(3));
		})
	}

	#[test]
	fn try_append_decode_len_works() {
		type B = CountedStorageDoubleMap<
			Prefix,
			Blake2_256,
			u16,
			Twox64Concat,
			u8,
			BoundedVec<u32, ConstU32<3u32>>,
		>;
		TestExternalities::default().execute_with(|| {
			assert_eq!(B::decode_len(1, 10), None);
			B::try_append(1, 10, 3).unwrap();
			assert_eq!(B::decode_len(1, 10), Some(1));
			B::try_append(1, 10, 3).unwrap();
			assert_eq!(B::decode_len(1, 10), Some(2));
			B::try_append(1, 10, 3).unwrap();
			assert_eq!(B::decode_len(1, 10), Some(3));
			B::try_append(1, 10, 3).err().unwrap();
			assert_eq!(B::decode_len(1, 10), Some(3));
		})
	}

	#[test]
	fn migrate_keys_works() {
		type A = CountedStorageDoubleMap<Prefix, Blake2_128, u16, Twox64Concat, u8, u32>;
		type B = CountedStorageDoubleMap<Prefix, Blake2_256, u16, Twox64Concat, u8, u32>;
		TestExternalities::default().execute_with(|| {
			A::insert(1, 10, 1);
			assert_eq!(B::migrate_keys::<Blake2_128, Twox64Concat, _, _>(1, 10), Some(1));
			assert_eq!(B::get(1, 10), Some(1));
		})
	}

	#[test]
	fn translate_values() {
		type A = CountedStorageDoubleMap<Prefix, Blake2_128, u16, Twox64Concat, u8, u32>;
		TestExternalities::default().execute_with(|| {
			A::insert(1, 10, 1);
			A::insert(2, 20, 2);
			A::translate_values::<u32, _>(|old_value| if old_value == 1 { None } else { Some(1) });
			assert_eq!(A::count(), 1);
			assert_eq!(A::get(2, 20), Some(1));
		})
	}

	#[test]
	fn test_iter_drain_translate() {
		type A = CountedStorageDoubleMap<Prefix, Blake2_128Concat, u16, Twox64Concat, u8, u32>;
		TestExternalities::default().execute_with(|| {
			A::insert(1, 10, 1);
			A::insert(2, 20, 2);

			assert_eq!(A::iter().collect::<Vec<_>>(), vec![(2, 20, 2), (1, 10, 1)]);

			assert_eq!(A::count(), 2);

			A::translate::<u32, _>(
				|key1, _key2, value| if key1 == 1 { None } else { Some(key1 as u32 * value) },
			);

			assert_eq!(A::count(), 1);

			assert_eq!(A::drain().collect::<Vec<_>>(), vec![(2, 20, 4)]);

			assert_eq!(A::count(), 0);
		})
	}

	#[test]
	fn test_iter_drain_prefix() {
		type A = CountedStorageDoubleMap<Prefix, Blake2_128Concat, u16, Twox64Concat, u8, u32>;
		TestExternalities::default().execute_with(|| {
			A::insert(1, 10, 1);
			A::insert(1, 11, 2);
			A::insert(2, 20, 3);
			A::insert(2, 21, 4);

			assert_eq!(A::iter_prefix_values(1).collect::<Vec<_>>(), vec![1, 2]);
			assert_eq!(A::iter_prefix(1).collect::<Vec<_>>(), vec![(10, 1), (11, 2)]);
			assert_eq!(A::iter_prefix_values(2).collect::<Vec<_>>(), vec![4, 3]);
			assert_eq!(A::iter_prefix(2).collect::<Vec<_>>(), vec![(21, 4), (20, 3)]);

			assert_eq!(A::count(), 4);

			A::remove_prefix(1);
			assert_eq!(A::iter_prefix(1).collect::<Vec<_>>(), vec![]);
			assert_eq!(A::iter_prefix(2).collect::<Vec<_>>(), vec![(21, 4), (20, 3)]);

			assert_eq!(A::count(), 2);

			assert_eq!(A::drain_prefix(2).collect::<Vec<_>>(), vec![(21, 4), (20, 3)]);
			assert_eq!(A::iter_prefix(2).collect::<Vec<_>>(), vec![]);
			assert_eq!(A::drain_prefix(2).collect::<Vec<_>>(), vec![]);

			assert_eq!(A::count(), 0);
		})
	}

	#[test]
	fn test_metadata() {
		type A = CountedStorageDoubleMap<
			Prefix,
			Blake2_128Concat,
			u16,
			Twox64Concat,
			u8,
			u32,
			ValueQuery,
			ADefault,
		>;
		let mut entries = vec![];
		A::build_metadata(vec![], &mut entries);
		assert_eq!(
			entries,
			vec![
				StorageEntryMetadata {
					name: "foo",
					modifier: StorageEntryModifier::Default,
					ty: StorageEntryType::Map {
						hashers: vec![StorageHasher::Blake2_128Concat, StorageHasher::Twox64Concat],
						key: scale_info::meta_type::<(u16, u8)>(),
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
					docs: vec!["Counter for the related counted storage map"],
				},
			]
		);
	}
}
