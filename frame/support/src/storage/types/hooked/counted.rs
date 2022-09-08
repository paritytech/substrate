use crate::{
	storage::{generator, IterableStorageMap},
	ReversibleStorageHasher,
};
use codec::FullCodec;
use sp_arithmetic::traits::Saturating;
use sp_std::{marker::PhantomData, ops::Deref};

type Counter = u32;

pub type CountedMap<M, K, V> = super::HookedMap<M, K, V, OnRemove<M, K, V>, OnInsert<M, K, V>, ()>;

impl<K: FullCodec, V: FullCodec, M: generator::StorageMap<K, V>> CountedMap<M, K, V>
where
	<M as generator::StorageMap<K, V>>::Hasher: ReversibleStorageHasher,
{
	pub fn count() -> Counter {
		let counter_key = counter_key::<M, K, V>();
		crate::storage::unhashed::get_or_default::<Counter>(&counter_key)
	}

	pub fn initialize_counter() -> u32 {
		let counter_key = counter_key::<M, K, V>();
		let counter_value = M::iter().count() as u32;
		crate::storage::unhashed::put::<Counter>(&counter_key, &counter_value);
		counter_value
	}
}

// NOTE: since I am designing this (for now) with the assumption of no macro magic, we can't
// generate prefixes at compile time and have to re-calc it. something to improve later.P
// TODO: don't like the order of generics here. Should be <U, T<U>>, not <T<U>, U>
fn counter_key<M: generator::StorageMap<K, V>, K: FullCodec, V: FullCodec>() -> Vec<u8> {
	let pallet = M::module_prefix();
	let map_prefix = M::storage_prefix();
	let counter_prefix = b"CounterFor";
	[pallet, counter_prefix, map_prefix].concat()
}

pub struct OnInsert<M, K, V>(PhantomData<(M, K, V)>);
impl<K: FullCodec, V: FullCodec, M: generator::StorageMap<K, V>> super::StorageOnInsert<K, V>
	for OnInsert<M, K, V>
{
	fn on_insert(_: &K, _: &V) {
		let counter_key = counter_key::<M, K, V>();
		let old = crate::storage::unhashed::get_or_default::<Counter>(&counter_key);
		crate::storage::unhashed::put::<Counter>(&counter_key, &old.saturating_add(1));
	}
}

pub struct OnRemove<M, K, V>(PhantomData<(M, K, V)>);
impl<K: FullCodec, V: FullCodec, M: generator::StorageMap<K, V>> super::StorageOnRemove<K, V>
	for OnRemove<M, K, V>
{
	fn on_remove(_: &K, _: &V) {
		let counter_key = counter_key::<M, K, V>();
		let old = crate::storage::unhashed::get_or_default::<Counter>(&counter_key);
		crate::storage::unhashed::put::<Counter>(&counter_key, &old.saturating_sub(1));
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::{
		storage::types,
		traits::{Get, StorageInstance},
		Hashable, Twox64Concat,
	};
	use sp_io::TestExternalities;
	use types::ValueQuery;

	struct Prefix;
	impl StorageInstance for Prefix {
		fn pallet_prefix() -> &'static str {
			"some_pallet"
		}
		const STORAGE_PREFIX: &'static str = "Prefix";
	}

	type Map = types::StorageMap<Prefix, Twox64Concat, u16, u32, ValueQuery, ADefault>;
	type A = CountedMap<Map, u16, u32>;

	struct ADefault;
	impl crate::traits::Get<u32> for ADefault {
		fn get() -> u32 {
			97
		}
	}

	// TODO: taken from the normal countedmap, find a way to reuse
	#[test]
	fn test_value_query() {
		TestExternalities::default().execute_with(|| {
			// let mut k: Vec<u8> = vec![];
			// k.extend(&twox_128(b"test"));
			// k.extend(&twox_128(b"foo"));
			// k.extend(&3u16.twox_64_concat());
			// assert_eq!(A::hashed_key_for(3).to_vec(), k);

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
			let _ = A::remove_all(None);
			// TODO: we don't have clear yet,

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
}
