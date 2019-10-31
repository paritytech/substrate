// Copyright 2019 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

#[cfg(not(feature = "std"))]
use rstd::prelude::*;
use rstd::borrow::Borrow;
use codec::{FullCodec, FullEncode, Encode, EncodeLike, Ref, EncodeAppend};
use crate::{storage::{self, unhashed}, hash::{Twox256, StorageHasher}, traits::Len};

/// Generator for `StoragePrefixedMap` used by `decl_storage`.
///
/// For each key value is stored at:
/// ```nocompile
/// twox_256(prefix) ++ Hasher(key)
/// ```
///
/// # Warning
///
/// If the keys are not trusted (e.g. can be set by a user), a cryptographic `hasher` such as
/// `blake2_256` must be used.  Otherwise, other values in storage can be compromised.
///
/// Besides this map no key prefixed with `twox_256(prefix)` must be inserted to the trie,
/// otherwise they are considered part of this map.
pub trait StoragePrefixedMap<K: FullEncode, V: FullCodec> {
	/// The type that get/take returns.
	type Query;

	/// Hasher used to insert into storage.
	type Hasher: StorageHasher;

	/// Prefix used to prepend each key.
	fn prefix() -> &'static [u8];

	/// Convert an optional value retrieved from storage to the type queried.
	fn from_optional_value_to_query(v: Option<V>) -> Self::Query;

	/// Convert a query to an optional value into storage.
	fn from_query_to_optional_value(v: Self::Query) -> Option<V>;

	/// Generate the full key used in top storage.
	fn storage_prefixed_map_final_key<KeyArg>(key: KeyArg) -> Vec<u8>
	where
		KeyArg: EncodeLike<K>,
	{
		let mut final_key = Twox256::hash(&Self::prefix()).to_vec();
		final_key.extend_from_slice(key.using_encoded(Self::Hasher::hash).as_ref());
		final_key
	}
}

impl<K: FullEncode, V: FullCodec, G: StoragePrefixedMap<K, V>>
	storage::StoragePrefixedMap<K, V> for G
{
	type Query = G::Query;

	fn remove_all() {
		unhashed::kill_prefix(&Twox256::hash(&Self::prefix()));
	}

	fn swap<KeyArg1: EncodeLike<K>, KeyArg2: EncodeLike<K>>(key1: KeyArg1, key2: KeyArg2) {
		let k1 = Self::storage_prefixed_map_final_key(key1);
		let k2 = Self::storage_prefixed_map_final_key(key2);

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

	fn exists<KeyArg: EncodeLike<K>>(key: KeyArg) -> bool {
		unhashed::exists(Self::storage_prefixed_map_final_key(key).as_ref())
	}

	fn get<KeyArg: EncodeLike<K>>(key: KeyArg) -> Self::Query {
		G::from_optional_value_to_query(unhashed::get(Self::storage_prefixed_map_final_key(key).as_ref()))
	}

	fn insert<KeyArg: EncodeLike<K>, ValArg: EncodeLike<V>>(key: KeyArg, val: ValArg) {
		unhashed::put(Self::storage_prefixed_map_final_key(key).as_ref(), &val.borrow())
	}

	fn remove<KeyArg: EncodeLike<K>>(key: KeyArg) {
		unhashed::kill(Self::storage_prefixed_map_final_key(key).as_ref())
	}

	fn mutate<KeyArg: EncodeLike<K>, R, F: FnOnce(&mut Self::Query) -> R>(key: KeyArg, f: F) -> R {
		let final_key = Self::storage_prefixed_map_final_key(key);
		let mut val = G::from_optional_value_to_query(unhashed::get(final_key.as_ref()));

		let ret = f(&mut val);
		match G::from_query_to_optional_value(val) {
			Some(ref val) => unhashed::put(final_key.as_ref(), &val.borrow()),
			None => unhashed::kill(final_key.as_ref()),
		}
		ret
	}

	fn take<KeyArg: EncodeLike<K>>(key: KeyArg) -> Self::Query {
		let key = Self::storage_prefixed_map_final_key(key);
		let value = unhashed::take(key.as_ref());
		G::from_optional_value_to_query(value)
	}

	fn append<Items, Item, EncodeLikeItem, KeyArg>(key: KeyArg, items: Items) -> Result<(), &'static str>
	where
		KeyArg: EncodeLike<K>,
		Item: Encode,
		EncodeLikeItem: EncodeLike<Item>,
		V: EncodeAppend<Item=Item>,
		Items: IntoIterator<Item=EncodeLikeItem>,
		Items::IntoIter: ExactSizeIterator,
	{
		let key = Self::storage_prefixed_map_final_key(key);
		let encoded_value = unhashed::get_raw(key.as_ref())
			.unwrap_or_else(|| {
				match G::from_query_to_optional_value(G::from_optional_value_to_query(None)) {
					Some(value) => value.encode(),
					None => vec![],
				}
			});

		let new_val = V::append_or_new(
			encoded_value,
			items,
		).map_err(|_| "Could not append given item")?;
		unhashed::put_raw(key.as_ref(), &new_val);
		Ok(())
	}

	fn append_or_insert<Items, Item, EncodeLikeItem, KeyArg>(key: KeyArg, items: Items)
	where
		KeyArg: EncodeLike<K>,
		Item: Encode,
		EncodeLikeItem: EncodeLike<Item>,
		V: EncodeAppend<Item=Item>,
		Items: IntoIterator<Item=EncodeLikeItem> + Clone + EncodeLike<V>,
		Items::IntoIter: ExactSizeIterator,
	{
		Self::append(Ref::from(&key), items.clone())
			.unwrap_or_else(|_| Self::insert(key, items));
	}

	fn decode_len<KeyArg: EncodeLike<K>>(key: KeyArg) -> Result<usize, &'static str>
		where V: codec::DecodeLength + Len
	{
		let key = Self::storage_prefixed_map_final_key(key);
		if let Some(v) = unhashed::get_raw(key.as_ref()) {
			<V as codec::DecodeLength>::len(&v).map_err(|e| e.what())
		} else {
			let len = G::from_query_to_optional_value(G::from_optional_value_to_query(None))
				.map(|v| v.len())
				.unwrap_or(0);

			Ok(len)
		}
	}
}

#[cfg(test)]
mod tests {
	pub trait Trait {
		type BlockNumber: codec::FullCodec + Default;
		type Origin;
	}

	// Put into module to avoid dead code warning.
	#[allow(dead_code)]
	mod module {
		use super::Trait;
		decl_module! {
			pub struct Module<T: Trait> for enum Call where origin: T::Origin {}
		}
	}
	use self::module::Module;

	crate::decl_storage! {
		trait Store for Module<T: Trait> as Example {
			pub BuildWorks build(|_| vec![(1, 2)]): prefixed_map u32 => u32;
			pub ConfigAndGetWorks get(fn getter) config(config): prefixed_map u32 => u32;
			pub PrefixedMap: prefixed_map hasher(blake2_128) u32 => u64;
			pub OptionPrefixedMap: prefixed_map hasher(blake2_128) u32 => Option<u64>;

			pub PrefixedMapVec: prefixed_map hasher(twox_256) u32 => Vec<u64>;
			pub OptionPrefixedMapVec: prefixed_map hasher(blake2_128) u32 => Option<Vec<u64>>;
			pub PrefixedMapVecWithDefault: prefixed_map u32 => Vec<u64> = vec![6, 9];
		}
	}

	struct Test;
	impl Trait for Test {
		type BlockNumber = u32;
		type Origin = u32;
	}

	fn new_test_ext() -> runtime_io::TestExternalities {
		GenesisConfig {
			config: vec![(3, 4)],
			.. Default::default()
		}.build_storage().unwrap().into()
	}

	#[test]
	fn prefixed_map_config_and_get_works() {
		new_test_ext().execute_with(|| {
			assert_eq!(ConfigAndGetWorks::get(3), 4);
			assert_eq!(<Module<Test>>::getter(3), 4);
		})
	}

	#[test]
	fn prefixed_map_build_works() {
		new_test_ext().execute_with(|| {
			assert_eq!(BuildWorks::get(1), 2);
		})
	}

	#[test]
	fn prefixed_map_basic_insert_remove_works() {
		new_test_ext().execute_with(|| {
			// get / insert / take
			let key = 17;
			assert_eq!(PrefixedMap::get(&key), 0);
			PrefixedMap::insert(key, 4);
			assert_eq!(PrefixedMap::get(&key), 4);
			assert_eq!(PrefixedMap::take(&key), 4);
			assert_eq!(PrefixedMap::get(&key), 0);

			// mutate
			PrefixedMap::mutate(&key, |val| {
				*val = 15;
			});
			assert_eq!(PrefixedMap::get(&key), 15);

			// remove
			PrefixedMap::remove(&key);
			assert_eq!(PrefixedMap::get(&key), 0);

			// swap
			PrefixedMap::insert(1, 1);
			PrefixedMap::insert(2, 2);
			PrefixedMap::swap(1, 2);
			assert_eq!(PrefixedMap::get(1), 2);
			assert_eq!(PrefixedMap::get(2), 1);
			PrefixedMap::swap(1, 3);
			assert_eq!(PrefixedMap::get(1), 0);
			assert_eq!(PrefixedMap::get(3), 2);

			// remove all
			PrefixedMap::insert(1, 1);
			PrefixedMap::insert(2, 2);
			PrefixedMap::remove_all();
			assert_eq!(PrefixedMap::get(1), 0);
			assert_eq!(PrefixedMap::get(2), 0);
		});
	}

	#[test]
	fn option_prefixed_map_basic_insert_remove_works() {
		new_test_ext().execute_with(|| {
			// get / insert / take
			let key = 17;
			assert_eq!(OptionPrefixedMap::get(&key), None);
			OptionPrefixedMap::insert(key, 4);
			assert_eq!(OptionPrefixedMap::get(&key), Some(4));
			assert_eq!(OptionPrefixedMap::take(&key), Some(4));
			assert_eq!(OptionPrefixedMap::get(&key), None);

			// mutate
			OptionPrefixedMap::mutate(&key, |val| {
				*val = Some(15);
			});
			assert_eq!(OptionPrefixedMap::get(&key), Some(15));
			OptionPrefixedMap::mutate(&key, |val| {
				*val = None;
			});
			assert_eq!(OptionPrefixedMap::get(&key), None);

			// remove
			OptionPrefixedMap::remove(&key);
			assert_eq!(OptionPrefixedMap::get(&key), None);

			// swap
			OptionPrefixedMap::insert(1, 1);
			OptionPrefixedMap::insert(2, 2);
			OptionPrefixedMap::swap(1, 2);
			assert_eq!(OptionPrefixedMap::get(1), Some(2));
			assert_eq!(OptionPrefixedMap::get(2), Some(1));
			OptionPrefixedMap::swap(1, 3);
			assert_eq!(OptionPrefixedMap::get(1), None);
			assert_eq!(OptionPrefixedMap::get(3), Some(2));

			// remove all
			OptionPrefixedMap::insert(1, 1);
			OptionPrefixedMap::insert(2, 2);
			OptionPrefixedMap::remove_all();
			assert_eq!(OptionPrefixedMap::get(1), None);
			assert_eq!(OptionPrefixedMap::get(2), None);
		});
	}

	#[test]
	fn append_works() {
		new_test_ext().execute_with(|| {
			let _ = PrefixedMapVec::append(1, [1, 2, 3].iter());
			let _ = PrefixedMapVec::append(1, [4, 5].iter());
			assert_eq!(PrefixedMapVec::get(1), vec![1, 2, 3, 4, 5]);
		});
	}

	#[test]
	fn append_works_for_default() {
		new_test_ext().execute_with(|| {
			assert_eq!(PrefixedMapVecWithDefault::exists(0), false);
			assert_eq!(PrefixedMapVecWithDefault::get(0), vec![6, 9]);
			let _ = PrefixedMapVecWithDefault::append(0, [1].iter());
			assert_eq!(PrefixedMapVecWithDefault::get(0), vec![6, 9, 1]);
		});
	}

	#[test]
	fn append_or_put_works() {
		new_test_ext().execute_with(|| {
			let _ = PrefixedMapVec::append_or_insert(1, &[1, 2, 3][..]);
			let _ = PrefixedMapVec::append_or_insert(1, &[4, 5][..]);
			assert_eq!(PrefixedMapVec::get(1), vec![1, 2, 3, 4, 5]);
		});
	}

	#[test]
	fn len_works() {
		new_test_ext().execute_with(|| {
			PrefixedMapVec::insert(1, &vec![1, 2, 3, 4, 5, 6]);
			assert_eq!(PrefixedMapVec::decode_len(1).unwrap(), 6);
		});
	}

	#[test]
	fn len_works_for_default() {
		new_test_ext().execute_with(|| {
			assert_eq!(PrefixedMapVec::get(0), vec![]);
			assert_eq!(PrefixedMapVec::decode_len(0), Ok(0));

			assert_eq!(PrefixedMapVecWithDefault::get(0), vec![6, 9]);
			assert_eq!(PrefixedMapVecWithDefault::decode_len(0), Ok(2));

			assert_eq!(OptionPrefixedMapVec::get(0), None);
			assert_eq!(OptionPrefixedMapVec::decode_len(0), Ok(0));
		});
	}
}
