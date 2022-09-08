use crate::{
	storage::{self, StorageAppend, StorageDecodeLength, StorageTryAppend},
	StoragePrefixedMap,
};
use codec::{Decode, Encode, EncodeLike, FullCodec};
use sp_arithmetic::traits::Bounded;
use sp_std::marker::PhantomData;

mod counted;

/// This is fired IFF some value already existed in `key`.
///
/// This is fired AFTER `key` is already removed.
#[impl_trait_for_tuples::impl_for_tuples(0, 32)]
pub trait StorageOnRemove<K, V> {
	fn on_remove(key: &K, value: &V);
}

/// This is fired AFTER `key` is created.
#[impl_trait_for_tuples::impl_for_tuples(0, 32)]
pub trait StorageOnInsert<K, V> {
	fn on_insert(key: &K, value: &V);
}

/// This is fired AFTER `key` is updated.
#[impl_trait_for_tuples::impl_for_tuples(0, 32)]
pub trait StorageOnUpdate<K, V> {
	fn on_update(key: &K, old_value: &V, new_value: &V);
}

struct OnRemovalIteratorShim<K, V, SOR>(PhantomData<(K, V, SOR)>);
impl<K: FullCodec, V: FullCodec, SOR: StorageOnRemove<K, V>> crate::storage::PrefixIteratorOnRemoval for OnRemovalIteratorShim<K, V, SOR> {
	fn on_removal(key: &[u8], value: &[u8]) {
		let key = K::decode(&mut &*key).unwrap_or_default();
		let value = V::decode(&mut &*value).unwrap_or_default();
		SOR::on_remove(&key, &value)
	}
}

pub struct HookedMap<Map, Key, Value, OnRemove = (), OnInsert = (), OnUpdate = ()>(
	PhantomData<(Map, Key, Value, OnRemove, OnInsert, OnUpdate)>,
);

impl<Key, Value, Map, OnRemove, OnInsert, OnUpdate>
	HookedMap<Map, Key, Value, OnRemove, OnInsert, OnUpdate>
where
	OnRemove: StorageOnRemove<Key, Value>,
	OnInsert: StorageOnInsert<Key, Value>,
	OnUpdate: StorageOnUpdate<Key, Value>,
	Key: FullCodec + Clone,
	Value: FullCodec + Clone,
	Map: storage::StorageMap<
			Key,
			Value,
			Query = <Map as storage::generator::StorageMap<Key, Value>>::Query,
		> + storage::generator::StorageMap<Key, Value>
		+ StoragePrefixedMap<Value>,
{
	/// Maybe get the value for the given key from the map.
	///
	/// Returns `Some` if it exists, `None` if not.
	fn maybe_get<KeyArg: EncodeLike<Key>>(key: KeyArg) -> Option<Value> {
		Self::try_get(key).ok()
	}

	//NOTE: some methods do not support this KeyArg thingy for technical reasons.a
	fn post_mutate_hooks(key: Key, maybe_old_value: Option<Value>, maybe_new_value: Option<Value>) {
		match (maybe_old_value, maybe_new_value) {
			(Some(old_value), Some(new_value)) => {
				OnUpdate::on_update(&key, &old_value, &new_value);
			},
			(Some(old_value), None) => {
				OnRemove::on_remove(&key, &old_value);
			},
			(None, Some(new_value)) => {
				OnInsert::on_insert(&key, &new_value);
			},
			(None, None) => {},
		}
	}

	/// Get the storage key used to fetch a value corresponding to a specific key.
	pub fn hashed_key_for<KeyArg: EncodeLike<Key>>(key: KeyArg) -> Vec<u8> {
		<Map as storage::StorageMap<Key, Value>>::hashed_key_for(key)
	}

	/// Does the value (explicitly) exist in storage?
	pub fn contains_key<KeyArg: EncodeLike<Key>>(key: KeyArg) -> bool {
		<Map as storage::StorageMap<Key, Value>>::contains_key(key)
	}

	/// Load the value associated with the given key from the map.
	pub fn get<KeyArg: EncodeLike<Key>>(
		key: KeyArg,
	) -> <Map as storage::StorageMap<Key, Value>>::Query {
		<Map as storage::StorageMap<Key, Value>>::get(key)
	}

	/// Try to get the value for the given key from the map.
	///
	/// Returns `Ok` if it exists, `Err` if not.
	pub fn try_get<KeyArg: EncodeLike<Key>>(key: KeyArg) -> Result<Value, ()> {
		<Map as storage::StorageMap<Key, Value>>::try_get(key)
	}

	/// Swap the values of two keys.
	pub fn swap(key1: Key, key2: Key) {
		let maybe_value1 = Self::maybe_get(key1.clone());
		let maybe_value2 = Self::maybe_get(key2.clone());
		match (maybe_value1, maybe_value2) {
			(Some(value1), Some(value2)) => {
				// Both existed, and now swapped.
				OnUpdate::on_update(&key1, &value1, &value2);
				OnUpdate::on_update(&key2, &value2, &value1);
			},
			(Some(value1), None) => {
				// val1 will be removed, val2 will be created.
				OnRemove::on_remove(&key1, &value1);
				OnInsert::on_insert(&key2, &value1);
			},
			(None, Some(value2)) => {
				// val2 will be removed, val1 will be created.
				OnRemove::on_remove(&key2, &value2);
				OnInsert::on_insert(&key1, &value2);
			},
			(None, None) => {
				// noop, no hook is fired.
			},
		}
		<Map as storage::StorageMap<Key, Value>>::swap(key1, key2)
	}

	/// Store a value to be associated with the given key from the map.
	pub fn insert(key: Key, val: Value) {
		let maybe_old_value = Self::maybe_get(key.clone());
		<Map as storage::StorageMap<Key, Value>>::insert(key.clone(), val.clone());
		if let Some(old_value) = maybe_old_value {
			OnUpdate::on_update(&key, &old_value, &val);
		} else {
			OnInsert::on_insert(&key, &val);
		}
	}

	/// Remove the value under a key.
	pub fn remove(key: Key) {
		let maybe_old_value = Self::maybe_get(key.clone());
		<Map as storage::StorageMap<Key, Value>>::remove(key.clone());
		if let Some(old_value) = maybe_old_value {
			OnRemove::on_remove(&key, &old_value);
		}
	}

	/// Mutate the value under a key.
	pub fn mutate<R, F: FnOnce(&mut <Map as storage::StorageMap<Key, Value>>::Query) -> R>(
		key: Key,
		f: F,
	) -> R {
		let maybe_old_value = Self::maybe_get(key.clone());

		let result = <Map as storage::StorageMap<Key, Value>>::mutate(key.clone(), f);

		let maybe_new_value = Self::maybe_get(key.clone());
		Self::post_mutate_hooks(key, maybe_old_value, maybe_new_value);

		result
	}

	/// Mutate the item, only if an `Ok` value is returned.
	pub fn try_mutate<R, E, F>(key: Key, f: F) -> Result<R, E>
	where
		F: FnOnce(&mut <Map as storage::StorageMap<Key, Value>>::Query) -> Result<R, E>,
	{
		let maybe_old_value = Self::maybe_get(key.clone());
		let result = <Map as storage::StorageMap<Key, Value>>::try_mutate(key.clone(), f);

		if result.is_ok() {
			let maybe_new_value = Self::maybe_get(key.clone());
			Self::post_mutate_hooks(key, maybe_old_value, maybe_new_value);
		}

		result
	}

	/// Mutate the value under a key. Deletes the item if mutated to a `None`.
	pub fn mutate_exists<R, F: FnOnce(&mut Option<Value>) -> R>(key: Key, f: F) -> R {
		let maybe_old_value = Self::maybe_get(key.clone());
		let result = <Map as storage::StorageMap<Key, Value>>::mutate_exists(key.clone(), f);
		let maybe_new_value = Self::maybe_get(key.clone());

		Self::post_mutate_hooks(key, maybe_old_value, maybe_new_value);
		result
	}

	/// Mutate the item, only if an `Ok` value is returned. Deletes the item if mutated to a `None`.
	/// `f` will always be called with an option representing if the storage item exists (`Some<V>`)
	/// or if the storage item does not exist (`None`), independent of the `QueryType`.
	pub fn try_mutate_exists<R, E, F: FnOnce(&mut Option<Value>) -> Result<R, E>>(
		key: Key,
		f: F,
	) -> Result<R, E> {
		let maybe_old_value = Self::maybe_get(key.clone());
		let result = <Map as storage::StorageMap<Key, Value>>::try_mutate_exists(key.clone(), f);

		if result.is_ok() {
			let maybe_new_value = Self::maybe_get(key.clone());
			Self::post_mutate_hooks(key, maybe_old_value, maybe_new_value);
		}

		result
	}

	/// Take the value under a key.
	pub fn take(key: Key) -> <Map as storage::StorageMap<Key, Value>>::Query {
		let maybe_old_value = Self::maybe_get(key.clone());
		let r = <Map as storage::StorageMap<Key, Value>>::take(key.clone());

		if let Some(removed) = maybe_old_value {
			OnRemove::on_remove(&key, &removed);
		}

		r
	}

	/// Append the given items to the value in the storage.
	///
	/// `Value` is required to implement `codec::EncodeAppend`.
	///
	/// # Warning
	///
	/// If the storage item is not encoded properly, the storage will be overwritten
	/// and set to `[item]`. Any default value set for the storage item will be ignored
	/// on overwrite.
	pub fn append<Item, EncodeLikeItem, EncodeLikeKey>(key: Key, item: EncodeLikeItem)
	where
		Item: Encode,
		EncodeLikeItem: EncodeLike<Item> + Clone,
		Value: StorageAppend<Item>,
	{
		let maybe_old_value = Self::maybe_get(key.clone());
		<Map as storage::StorageMap<Key, Value>>::append(key.clone(), item);
		let maybe_new_value = Self::maybe_get(key.clone());
		Self::post_mutate_hooks(key, maybe_old_value, maybe_new_value);
	}

	/// Read the length of the storage value without decoding the entire value under the
	/// given `key`.
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
	pub fn decode_len<KeyArg: EncodeLike<Key>>(key: KeyArg) -> Option<usize>
	where
		Value: StorageDecodeLength,
	{
		<Map as storage::StorageMap<Key, Value>>::decode_len(key)
	}

	/// Migrate an item with the given `key` from a defunct `OldHasher` to the current hasher.
	///
	/// If the key doesn't exist, then it's a no-op. If it does, then it returns its value.
	pub fn migrate_key<OldHasher: crate::hash::StorageHasher, KeyArg: EncodeLike<Key>>(
		key: KeyArg,
	) -> Option<Value> {
		// NOTE: does not alter value in way, thus does not emit any hook events. The underlying key
		// in storage DOES change, but the user-facing key (i.e. the KeyArg) is not changing.
		<Map as storage::StorageMap<Key, Value>>::migrate_key::<OldHasher, _>(key)
	}

	/// Iter over all value of the storage.
	///
	/// NOTE: If a value failed to decode because storage is corrupted then it is skipped.
	pub fn iter_values() -> storage::PrefixIterator<Value> {
		<Map as storage::StoragePrefixedMap<Value>>::iter_values()
	}

	/// Try and append the given item to the value in the storage.
	///
	/// Is only available if `Value` of the storage implements [`StorageTryAppend`].
	pub fn try_append<Item, EncodeLikeItem>(key: Key, item: EncodeLikeItem) -> Result<(), ()>
	where
		Item: Encode,
		EncodeLikeItem: EncodeLike<Item>,
		Value: StorageTryAppend<Item>,
	{
		let maybe_old_value = Self::maybe_get(key.clone());
		let r = <Map as storage::TryAppendMap<Key, Value, Item>>::try_append(key.clone(), item);
		if r.is_ok() {
			let maybe_new_value = Self::maybe_get(key.clone());
			Self::post_mutate_hooks(key, maybe_old_value, maybe_new_value);
		}
		r
	}

	// TODO: the docs for functions that are just forwarded should also be forwarded to the trait.
	pub fn clear(limit: u32, maybe_cursor: Option<&[u8]>) -> sp_io::MultiRemovalResults {
		todo!();
		<Map as crate::storage::StoragePrefixedMap<Value>>::clear(limit, maybe_cursor)
	}
}

impl<Key, Value, Map, OnRemove, OnInsert, OnUpdate>
	HookedMap<Map, Key, Value, OnRemove, OnInsert, OnUpdate>
where
	OnRemove: StorageOnRemove<Key, Value>,
	OnInsert: StorageOnInsert<Key, Value>,
	OnUpdate: StorageOnUpdate<Key, Value>,
	Key: FullCodec,
	Value: FullCodec,
	Map: storage::generator::StorageMap<Key, Value>
		+ StoragePrefixedMap<Value>,
	<Map as storage::generator::StorageMap<Key, Value>>::Hasher:
		crate::hash::StorageHasher + crate::ReversibleStorageHasher,
{
	/// Remove all values of the storage in the overlay and up to `limit` in the backend.
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
	pub fn remove_all(limit: Option<u32>) -> sp_io::KillStorageResult {
		let mut removed = 0u32;
		Self::iter()
			.drain()
			.take(limit.unwrap_or(Bounded::max_value()) as usize)
			.for_each(|(k, v)| {
				OnRemove::on_remove(&k, &v);
				removed += 1;
			});

		// TODO: this one's a bit tricky.
		sp_io::KillStorageResult::AllRemoved(removed)
	}

	/// Enumerate all elements in the map in no particular order.
	///
	/// If you alter the map while doing this, you'll get undefined results.
	pub fn iter() -> storage::PrefixIterator<(Key, Value), OnRemovalIteratorShim<Key, Value, OnRemove>> {
		<Map as storage::IterableStorageMap<Key, Value>>::iter()
	}

	/// Enumerate all elements in the map after a specified `starting_raw_key` in no
	/// particular order.
	///
	/// If you alter the map while doing this, you'll get undefined results.
	pub fn iter_from(starting_raw_key: Vec<u8>) -> storage::PrefixIterator<(Key, Value)> {
		<Map as storage::IterableStorageMap<Key, Value>>::iter_from(starting_raw_key)
	}

	/// Enumerate all keys in the map in no particular order.
	///
	/// If you alter the map while doing this, you'll get undefined results.
	pub fn iter_keys() -> storage::KeyPrefixIterator<Key> {
		<Map as storage::IterableStorageMap<Key, Value>>::iter_keys()
	}

	/// Enumerate all keys in the map after a specified `starting_raw_key` in no particular
	/// order.
	///
	/// If you alter the map while doing this, you'll get undefined results.
	pub fn iter_keys_from(starting_raw_key: Vec<u8>) -> storage::KeyPrefixIterator<Key> {
		<Map as storage::IterableStorageMap<Key, Value>>::iter_keys_from(starting_raw_key)
	}

	// TODO: drain, translate, clear.
}

#[cfg(test)]
mod tests_value_query {
	use super::*;
	use crate::{
		hash::*,
		parameter_types,
		storage::{types, types::ValueQuery},
		traits::StorageInstance,
	};
	use sp_io::{hashing::twox_128, TestExternalities};

	parameter_types! {
		static Inserted: Vec<(u32, u32)> = Default::default();
		static Updated: Vec<(u32, u32, u32)> = Default::default();
		static Removed: Vec<(u32, u32)> = Default::default();
	}

	struct OnInsert;
	impl super::StorageOnInsert<u32, u32> for OnInsert {
		fn on_insert(key: &u32, value: &u32) {
			Inserted::mutate(|d| d.push((key.clone(), value.clone())));
		}
	}

	struct OnRemove;
	impl super::StorageOnRemove<u32, u32> for OnRemove {
		fn on_remove(key: &u32, value: &u32) {
			Removed::mutate(|d| d.push((key.clone(), value.clone())));
		}
	}

	struct OnUpdate;
	impl super::StorageOnUpdate<u32, u32> for OnUpdate {
		fn on_update(key: &u32, old_value: &u32, new_value: &u32) {
			Updated::mutate(|d| d.push((key.clone(), old_value.clone(), new_value.clone())));
		}
	}

	struct Prefix;
	impl StorageInstance for Prefix {
		fn pallet_prefix() -> &'static str {
			"test_pallet"
		}
		const STORAGE_PREFIX: &'static str = "Prefix";
	}

	// TODO: ui test for the wrong key-value (redundant) type.
	type ValueMap = types::StorageMap<Prefix, Twox64Concat, u32, u32, ValueQuery>;
	type ValueHooked = HookedMap<ValueMap, u32, u32, OnRemove, OnInsert, OnUpdate>;

	// type ValueMapDefault = types::StorageMap<Prefix, Twox64Concat, u32, u32,
	// ValueQuery>; type OptionMap = types::StorageMap<Prefix, Twox64Concat, u32, u32,
	// OptionQuery>; type OptionHooked = HookedMap<OptionMap, ()>;

	#[test]
	fn insert_works() {
		TestExternalities::new_empty().execute_with(|| {
			// inserting a new key.
			ValueHooked::insert(1, 1);
			assert_eq!(Inserted::take(), vec![(1, 1)]);

			// re-inserting will trigger an update.
			ValueHooked::insert(1, 2);
			// has not changed.
			assert_eq!(Inserted::take(), vec![]);
			assert_eq!(Updated::take(), vec![(1, 1, 2)]);
		});
	}

	#[test]
	fn remove_works() {
		TestExternalities::new_empty().execute_with(|| {
			// removing a non-existent key.
			ValueHooked::remove(1);
			assert_eq!(Removed::take(), vec![]);

			// removing an existent key.
			ValueHooked::insert(1, 42);
			assert_eq!(Inserted::take(), vec![(1, 42)]);
			ValueHooked::remove(1);
			assert_eq!(Removed::take(), vec![(1, 42)]);
		});
	}

	#[test]
	fn swap_works() {
		TestExternalities::new_empty().execute_with(|| {
			// swapping two non-existent.
			ValueHooked::swap(1, 2);
			assert_eq!(Removed::take(), vec![]);
			assert_eq!(Inserted::take(), vec![]);
			assert_eq!(Updated::take(), vec![]);

			// swapping existent to non-existent.
			ValueHooked::insert(1, 1);
			assert_eq!(Inserted::take(), vec![(1, 1)]);

			ValueHooked::swap(1, 2);
			assert_eq!(Removed::take(), vec![(1, 1)]);
			assert_eq!(Inserted::take(), vec![(2, 1)]);
			assert_eq!(Updated::take(), vec![]);

			// swapping non-existent to existent.
			ValueHooked::swap(3, 2);
			assert_eq!(Removed::take(), vec![(2, 1)]);
			assert_eq!(Inserted::take(), vec![(3, 1)]);
			assert_eq!(Updated::take(), vec![]);

			// swapping two existent.
			ValueHooked::insert(4, 4); // and the other key that has value is 3 with value 1.
			assert_eq!(Inserted::take(), vec![(4, 4)]);

			ValueHooked::swap(3, 4);
			assert_eq!(Removed::take(), vec![]);
			assert_eq!(Inserted::take(), vec![]);
			assert_eq!(Updated::take(), vec![(3, 1, 4), (4, 4, 1)]);
		});
	}

	#[test]
	fn take_works() {
		TestExternalities::new_empty().execute_with(|| {
			// take non-existent item.
			assert_eq!(0, ValueHooked::take(1));
			assert_eq!(Removed::take(), vec![]);
			assert_eq!(Inserted::take(), vec![]);
			assert_eq!(Updated::take(), vec![]);

			// take an existing one.
			ValueHooked::insert(1, 1);
			assert_eq!(Inserted::take(), vec![(1, 1)]);

			assert_eq!(1, ValueHooked::take(1));
			assert_eq!(Removed::take(), vec![(1, 1)]);
			assert_eq!(Inserted::take(), vec![]);
			assert_eq!(Updated::take(), vec![]);
		})
	}

	#[test]
	fn mutate_works() {
		todo!();
	}

	#[test]
	fn try_mutate_works() {
		todo!()
	}

	#[test]
	fn mutate_exists_works() {
		todo!();
	}

	#[test]
	fn append_works() {
		todo!();
	}

	#[test]
	fn try_append_works() {
		todo!();
	}

	#[test]
	fn remove_all_works() {
		todo!();
	}
}
