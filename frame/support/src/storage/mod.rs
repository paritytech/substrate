// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
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

//! Stuff to do with the runtime's storage.

use sp_core::storage::ChildInfo;
use sp_std::prelude::*;
use sp_std::convert::TryFrom;
use codec::{FullCodec, FullEncode, Encode, EncodeLike, Decode};
use crate::{
	hash::{Twox128, StorageHasher, ReversibleStorageHasher},
	traits::Get,
};
use sp_runtime::generic::{Digest, DigestItem};
pub use sp_runtime::TransactionOutcome;

pub mod unhashed;
pub mod hashed;
pub mod child;
#[doc(hidden)]
pub mod generator;
pub mod migration;
pub mod types;

#[cfg(all(feature = "std", any(test, debug_assertions)))]
mod debug_helper {
	use std::cell::RefCell;

	thread_local! {
		static TRANSACTION_LEVEL: RefCell<u32> = RefCell::new(0);
	}

	pub fn require_transaction() {
		let level = TRANSACTION_LEVEL.with(|v| *v.borrow());
		if level == 0 {
			panic!("Require transaction not called within with_transaction");
		}
	}

	pub struct TransactionLevelGuard;

	impl Drop for TransactionLevelGuard {
		fn drop(&mut self) {
			TRANSACTION_LEVEL.with(|v| *v.borrow_mut() -= 1);
		}
	}

	/// Increments the transaction level.
	///
	/// Returns a guard that when dropped decrements the transaction level automatically.
	pub fn inc_transaction_level() -> TransactionLevelGuard {
		TRANSACTION_LEVEL.with(|v| {
			let mut val = v.borrow_mut();
			*val += 1;
			if *val > 10 {
				log::warn!(
					"Detected with_transaction with nest level {}. Nested usage of with_transaction is not recommended.",
					*val
				);
			}
		});

		TransactionLevelGuard
	}
}

/// Assert this method is called within a storage transaction.
/// This will **panic** if is not called within a storage transaction.
///
/// This assertion is enabled for native execution and when `debug_assertions` are enabled.
pub fn require_transaction() {
	#[cfg(all(feature = "std", any(test, debug_assertions)))]
	debug_helper::require_transaction();
}

/// Execute the supplied function in a new storage transaction.
///
/// All changes to storage performed by the supplied function are discarded if the returned
/// outcome is `TransactionOutcome::Rollback`.
///
/// Transactions can be nested to any depth. Commits happen to the parent transaction.
pub fn with_transaction<R>(f: impl FnOnce() -> TransactionOutcome<R>) -> R {
	use sp_io::storage::{
		start_transaction, commit_transaction, rollback_transaction,
	};
	use TransactionOutcome::*;

	start_transaction();

	#[cfg(all(feature = "std", any(test, debug_assertions)))]
	let _guard = debug_helper::inc_transaction_level();

	match f() {
		Commit(res) => { commit_transaction(); res },
		Rollback(res) => { rollback_transaction(); res },
	}
}

/// A trait for working with macro-generated storage values under the substrate storage API.
///
/// Details on implementation can be found at [`generator::StorageValue`].
pub trait StorageValue<T: FullCodec> {
	/// The type that get/take return.
	type Query;

	/// Get the storage key.
	fn hashed_key() -> [u8; 32];

	/// Does the value (explicitly) exist in storage?
	fn exists() -> bool;

	/// Load the value from the provided storage instance.
	fn get() -> Self::Query;

	/// Try to get the underlying value from the provided storage instance.
	///
	/// Returns `Ok` if it exists, `Err` if not.
	fn try_get() -> Result<T, ()>;

	/// Translate a value from some previous type (`O`) to the current type.
	///
	/// `f: F` is the translation function.
	///
	/// Returns `Err` if the storage item could not be interpreted as the old type, and Ok, along
	/// with the new value if it could.
	///
	/// NOTE: This operates from and to `Option<_>` types; no effort is made to respect the default
	/// value of the original type.
	///
	/// # Warning
	///
	/// This function must be used with care, before being updated the storage still contains the
	/// old type, thus other calls (such as `get`) will fail at decoding it.
	///
	/// # Usage
	///
	/// This would typically be called inside the module implementation of on_runtime_upgrade, while
	/// ensuring **no usage of this storage are made before the call to `on_runtime_upgrade`**. (More
	/// precisely prior initialized modules doesn't make use of this storage).
	fn translate<O: Decode, F: FnOnce(Option<O>) -> Option<T>>(f: F) -> Result<Option<T>, ()>;

	/// Store a value under this key into the provided storage instance.
	fn put<Arg: EncodeLike<T>>(val: Arg);

	/// Store a value under this key into the provided storage instance; this uses the query
	/// type rather than the underlying value.
	fn set(val: Self::Query);

	/// Mutate the value
	fn mutate<R, F: FnOnce(&mut Self::Query) -> R>(f: F) -> R;

	/// Mutate the value if closure returns `Ok`
	fn try_mutate<R, E, F: FnOnce(&mut Self::Query) -> Result<R, E>>(f: F) -> Result<R, E>;

	/// Clear the storage value.
	fn kill();

	/// Take a value from storage, removing it afterwards.
	fn take() -> Self::Query;

	/// Append the given item to the value in the storage.
	///
	/// `T` is required to implement [`StorageAppend`].
	///
	/// # Warning
	///
	/// If the storage item is not encoded properly, the storage item will be overwritten
	/// and set to `[item]`. Any default value set for the storage item will be ignored
	/// on overwrite.
	fn append<Item, EncodeLikeItem>(item: EncodeLikeItem)
	where
		Item: Encode,
		EncodeLikeItem: EncodeLike<Item>,
		T: StorageAppend<Item>;

	/// Read the length of the storage value without decoding the entire value.
	///
	/// `T` is required to implement [`StorageDecodeLength`].
	///
	/// If the value does not exists or it fails to decode the length, `None` is returned.
	/// Otherwise `Some(len)` is returned.
	///
	/// # Warning
	///
	/// `None` does not mean that `get()` does not return a value. The default value is completly
	/// ignored by this function.
	fn decode_len() -> Option<usize> where T: StorageDecodeLength {
		T::decode_len(&Self::hashed_key())
	}
}

/// A strongly-typed map in storage.
///
/// Details on implementation can be found at [`generator::StorageMap`].
pub trait StorageMap<K: FullEncode, V: FullCodec> {
	/// The type that get/take return.
	type Query;

	/// Get the storage key used to fetch a value corresponding to a specific key.
	fn hashed_key_for<KeyArg: EncodeLike<K>>(key: KeyArg) -> Vec<u8>;

	/// Does the value (explicitly) exist in storage?
	fn contains_key<KeyArg: EncodeLike<K>>(key: KeyArg) -> bool;

	/// Load the value associated with the given key from the map.
	fn get<KeyArg: EncodeLike<K>>(key: KeyArg) -> Self::Query;

	/// Try to get the value for the given key from the map.
	///
	/// Returns `Ok` if it exists, `Err` if not.
	fn try_get<KeyArg: EncodeLike<K>>(key: KeyArg) -> Result<V, ()>;

	/// Swap the values of two keys.
	fn swap<KeyArg1: EncodeLike<K>, KeyArg2: EncodeLike<K>>(key1: KeyArg1, key2: KeyArg2);

	/// Store a value to be associated with the given key from the map.
	fn insert<KeyArg: EncodeLike<K>, ValArg: EncodeLike<V>>(key: KeyArg, val: ValArg);

	/// Remove the value under a key.
	fn remove<KeyArg: EncodeLike<K>>(key: KeyArg);

	/// Mutate the value under a key.
	fn mutate<KeyArg: EncodeLike<K>, R, F: FnOnce(&mut Self::Query) -> R>(key: KeyArg, f: F) -> R;

	/// Mutate the item, only if an `Ok` value is returned.
	fn try_mutate<KeyArg: EncodeLike<K>, R, E, F: FnOnce(&mut Self::Query) -> Result<R, E>>(
		key: KeyArg,
		f: F,
	) -> Result<R, E>;

	/// Mutate the value under a key.
	///
	/// Deletes the item if mutated to a `None`.
	fn mutate_exists<KeyArg: EncodeLike<K>, R, F: FnOnce(&mut Option<V>) -> R>(key: KeyArg, f: F) -> R;

	/// Mutate the item, only if an `Ok` value is returned. Deletes the item if mutated to a `None`.
	fn try_mutate_exists<KeyArg: EncodeLike<K>, R, E, F: FnOnce(&mut Option<V>) -> Result<R, E>>(
		key: KeyArg,
		f: F,
	) -> Result<R, E>;

	/// Take the value under a key.
	fn take<KeyArg: EncodeLike<K>>(key: KeyArg) -> Self::Query;

	/// Append the given items to the value in the storage.
	///
	/// `V` is required to implement `codec::EncodeAppend`.
	///
	/// # Warning
	///
	/// If the storage item is not encoded properly, the storage will be overwritten
	/// and set to `[item]`. Any default value set for the storage item will be ignored
	/// on overwrite.
	fn append<Item, EncodeLikeItem, EncodeLikeKey>(key: EncodeLikeKey, item: EncodeLikeItem)
	where
		EncodeLikeKey: EncodeLike<K>,
		Item: Encode,
		EncodeLikeItem: EncodeLike<Item>,
		V: StorageAppend<Item>;

	/// Read the length of the storage value without decoding the entire value under the
	/// given `key`.
	///
	/// `V` is required to implement [`StorageDecodeLength`].
	///
	/// If the value does not exists or it fails to decode the length, `None` is returned.
	/// Otherwise `Some(len)` is returned.
	///
	/// # Warning
	///
	/// `None` does not mean that `get()` does not return a value. The default value is completly
	/// ignored by this function.
	fn decode_len<KeyArg: EncodeLike<K>>(key: KeyArg) -> Option<usize>
		where V: StorageDecodeLength,
	{
		V::decode_len(&Self::hashed_key_for(key))
	}

	/// Migrate an item with the given `key` from a defunct `OldHasher` to the current hasher.
	///
	/// If the key doesn't exist, then it's a no-op. If it does, then it returns its value.
	fn migrate_key<OldHasher: StorageHasher, KeyArg: EncodeLike<K>>(key: KeyArg) -> Option<V>;

	/// Migrate an item with the given `key` from a `blake2_256` hasher to the current hasher.
	///
	/// If the key doesn't exist, then it's a no-op. If it does, then it returns its value.
	fn migrate_key_from_blake<KeyArg: EncodeLike<K>>(key: KeyArg) -> Option<V> {
		Self::migrate_key::<crate::hash::Blake2_256, KeyArg>(key)
	}
}

/// A strongly-typed map in storage whose keys and values can be iterated over.
pub trait IterableStorageMap<K: FullEncode, V: FullCodec>: StorageMap<K, V> {
	/// The type that iterates over all `(key, value)`.
	type Iterator: Iterator<Item = (K, V)>;

	/// Enumerate all elements in the map in no particular order. If you alter the map while doing
	/// this, you'll get undefined results.
	fn iter() -> Self::Iterator;

	/// Remove all elements from the map and iterate through them in no particular order. If you
	/// add elements to the map while doing this, you'll get undefined results.
	fn drain() -> Self::Iterator;

	/// Translate the values of all elements by a function `f`, in the map in no particular order.
	/// By returning `None` from `f` for an element, you'll remove it from the map.
	///
	/// NOTE: If a value fail to decode because storage is corrupted then it is skipped.
	fn translate<O: Decode, F: FnMut(K, O) -> Option<V>>(f: F);
}

/// A strongly-typed double map in storage whose secondary keys and values can be iterated over.
pub trait IterableStorageDoubleMap<
	K1: FullCodec,
	K2: FullCodec,
	V: FullCodec
>: StorageDoubleMap<K1, K2, V> {
	/// The type that iterates over all `(key2, value)`.
	type PrefixIterator: Iterator<Item = (K2, V)>;

	/// The type that iterates over all `(key1, key2, value)`.
	type Iterator: Iterator<Item = (K1, K2, V)>;

	/// Enumerate all elements in the map with first key `k1` in no particular order. If you add or
	/// remove values whose first key is `k1` to the map while doing this, you'll get undefined
	/// results.
	fn iter_prefix(k1: impl EncodeLike<K1>) -> Self::PrefixIterator;

	/// Remove all elements from the map with first key `k1` and iterate through them in no
	/// particular order. If you add elements with first key `k1` to the map while doing this,
	/// you'll get undefined results.
	fn drain_prefix(k1: impl EncodeLike<K1>) -> Self::PrefixIterator;

	/// Enumerate all elements in the map in no particular order. If you add or remove values to
	/// the map while doing this, you'll get undefined results.
	fn iter() -> Self::Iterator;

	/// Remove all elements from the map and iterate through them in no particular order. If you
	/// add elements to the map while doing this, you'll get undefined results.
	fn drain() -> Self::Iterator;

	/// Translate the values of all elements by a function `f`, in the map in no particular order.
	/// By returning `None` from `f` for an element, you'll remove it from the map.
	///
	/// NOTE: If a value fail to decode because storage is corrupted then it is skipped.
	fn translate<O: Decode, F: FnMut(K1, K2, O) -> Option<V>>(f: F);
}

/// An implementation of a map with a two keys.
///
/// It provides an important ability to efficiently remove all entries
/// that have a common first key.
///
/// Details on implementation can be found at [`generator::StorageDoubleMap`].
pub trait StorageDoubleMap<K1: FullEncode, K2: FullEncode, V: FullCodec> {
	/// The type that get/take returns.
	type Query;

	/// Get the storage key used to fetch a value corresponding to a specific key.
	fn hashed_key_for<KArg1, KArg2>(k1: KArg1, k2: KArg2) -> Vec<u8>
	where
		KArg1: EncodeLike<K1>,
		KArg2: EncodeLike<K2>;

	/// Does the value (explicitly) exist in storage?
	fn contains_key<KArg1, KArg2>(k1: KArg1, k2: KArg2) -> bool
	where
		KArg1: EncodeLike<K1>,
		KArg2: EncodeLike<K2>;

	/// Load the value associated with the given key from the double map.
	fn get<KArg1, KArg2>(k1: KArg1, k2: KArg2) -> Self::Query
	where
		KArg1: EncodeLike<K1>,
		KArg2: EncodeLike<K2>;

	/// Try to get the value for the given key from the double map.
	///
	/// Returns `Ok` if it exists, `Err` if not.
	fn try_get<KArg1, KArg2>(k1: KArg1, k2: KArg2) -> Result<V, ()>
	where
		KArg1: EncodeLike<K1>,
		KArg2: EncodeLike<K2>;

	/// Take a value from storage, removing it afterwards.
	fn take<KArg1, KArg2>(k1: KArg1, k2: KArg2) -> Self::Query
	where
		KArg1: EncodeLike<K1>,
		KArg2: EncodeLike<K2>;

	/// Swap the values of two key-pairs.
	fn swap<XKArg1, XKArg2, YKArg1, YKArg2>(x_k1: XKArg1, x_k2: XKArg2, y_k1: YKArg1, y_k2: YKArg2)
	where
		XKArg1: EncodeLike<K1>,
		XKArg2: EncodeLike<K2>,
		YKArg1: EncodeLike<K1>,
		YKArg2: EncodeLike<K2>;

	/// Store a value to be associated with the given keys from the double map.
	fn insert<KArg1, KArg2, VArg>(k1: KArg1, k2: KArg2, val: VArg)
	where
		KArg1: EncodeLike<K1>,
		KArg2: EncodeLike<K2>,
		VArg: EncodeLike<V>;

	/// Remove the value under the given keys.
	fn remove<KArg1, KArg2>(k1: KArg1, k2: KArg2)
	where
		KArg1: EncodeLike<K1>,
		KArg2: EncodeLike<K2>;

	/// Remove all values under the first key.
	fn remove_prefix<KArg1>(k1: KArg1) where KArg1: ?Sized + EncodeLike<K1>;

	/// Iterate over values that share the first key.
	fn iter_prefix_values<KArg1>(k1: KArg1) -> PrefixIterator<V>
		where KArg1: ?Sized + EncodeLike<K1>;

	/// Mutate the value under the given keys.
	fn mutate<KArg1, KArg2, R, F>(k1: KArg1, k2: KArg2, f: F) -> R
	where
		KArg1: EncodeLike<K1>,
		KArg2: EncodeLike<K2>,
		F: FnOnce(&mut Self::Query) -> R;

	/// Mutate the value under the given keys when the closure returns `Ok`.
	fn try_mutate<KArg1, KArg2, R, E, F>(k1: KArg1, k2: KArg2, f: F) -> Result<R, E>
	where
		KArg1: EncodeLike<K1>,
		KArg2: EncodeLike<K2>,
		F: FnOnce(&mut Self::Query) -> Result<R, E>;

	/// Mutate the value under the given keys. Deletes the item if mutated to a `None`.
	fn mutate_exists<KArg1, KArg2, R, F>(k1: KArg1, k2: KArg2, f: F) -> R
	where
		KArg1: EncodeLike<K1>,
		KArg2: EncodeLike<K2>,
		F: FnOnce(&mut Option<V>) -> R;

	/// Mutate the item, only if an `Ok` value is returned. Deletes the item if mutated to a `None`.
	fn try_mutate_exists<KArg1, KArg2, R, E, F>(k1: KArg1, k2: KArg2, f: F) -> Result<R, E>
	where
		KArg1: EncodeLike<K1>,
		KArg2: EncodeLike<K2>,
		F: FnOnce(&mut Option<V>) -> Result<R, E>;

	/// Append the given item to the value in the storage.
	///
	/// `V` is required to implement [`StorageAppend`].
	///
	/// # Warning
	///
	/// If the storage item is not encoded properly, the storage will be overwritten
	/// and set to `[item]`. Any default value set for the storage item will be ignored
	/// on overwrite.
	fn append<Item, EncodeLikeItem, KArg1, KArg2>(
		k1: KArg1,
		k2: KArg2,
		item: EncodeLikeItem,
	) where
		KArg1: EncodeLike<K1>,
		KArg2: EncodeLike<K2>,
		Item: Encode,
		EncodeLikeItem: EncodeLike<Item>,
		V: StorageAppend<Item>;

	/// Read the length of the storage value without decoding the entire value under the
	/// given `key1` and `key2`.
	///
	/// `V` is required to implement [`StorageDecodeLength`].
	///
	/// If the value does not exists or it fails to decode the length, `None` is returned.
	/// Otherwise `Some(len)` is returned.
	///
	/// # Warning
	///
	/// `None` does not mean that `get()` does not return a value. The default value is completly
	/// ignored by this function.
	fn decode_len<KArg1, KArg2>(key1: KArg1, key2: KArg2) -> Option<usize>
		where
			KArg1: EncodeLike<K1>,
			KArg2: EncodeLike<K2>,
			V: StorageDecodeLength,
	{
		V::decode_len(&Self::hashed_key_for(key1, key2))
	}

	/// Migrate an item with the given `key1` and `key2` from defunct `OldHasher1` and
	/// `OldHasher2` to the current hashers.
	///
	/// If the key doesn't exist, then it's a no-op. If it does, then it returns its value.
	fn migrate_keys<
		OldHasher1: StorageHasher,
		OldHasher2: StorageHasher,
		KeyArg1: EncodeLike<K1>,
		KeyArg2: EncodeLike<K2>,
	>(key1: KeyArg1, key2: KeyArg2) -> Option<V>;
}

/// Iterate over a prefix and decode raw_key and raw_value into `T`.
///
/// If any decoding fails it skips it and continues to the next key.
pub struct PrefixIterator<T> {
	prefix: Vec<u8>,
	previous_key: Vec<u8>,
	/// If true then value are removed while iterating
	drain: bool,
	/// Function that take `(raw_key_without_prefix, raw_value)` and decode `T`.
	/// `raw_key_without_prefix` is the raw storage key without the prefix iterated on.
	closure: fn(&[u8], &[u8]) -> Result<T, codec::Error>,
}

impl<T> PrefixIterator<T> {
	/// Mutate this iterator into a draining iterator; items iterated are removed from storage.
	pub fn drain(mut self) -> Self {
		self.drain = true;
		self
	}
}

impl<T> Iterator for PrefixIterator<T> {
	type Item = T;

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			let maybe_next = sp_io::storage::next_key(&self.previous_key)
				.filter(|n| n.starts_with(&self.prefix));
			break match maybe_next {
				Some(next) => {
					self.previous_key = next;
					let raw_value = match unhashed::get_raw(&self.previous_key) {
						Some(raw_value) => raw_value,
						None => {
							log::error!(
								"next_key returned a key with no value at {:?}",
								self.previous_key,
							);
							continue
						}
					};
					if self.drain {
						unhashed::kill(&self.previous_key)
					}
					let raw_key_without_prefix = &self.previous_key[self.prefix.len()..];
					let item = match (self.closure)(raw_key_without_prefix, &raw_value[..]) {
						Ok(item) => item,
						Err(e) => {
							log::error!(
								"(key, value) failed to decode at {:?}: {:?}",
								self.previous_key,
								e,
							);
							continue
						}
					};

					Some(item)
				}
				None => None,
			}
		}
	}
}

/// Iterate over a prefix of a child trie and decode raw_key and raw_value into `T`.
///
/// If any decoding fails it skips the key and continues to the next one.
pub struct ChildTriePrefixIterator<T> {
	/// The prefix iterated on
	prefix: Vec<u8>,
	/// child info for child trie
	child_info: ChildInfo,
	/// The last key iterated on
	previous_key: Vec<u8>,
	/// If true then values are removed while iterating
	drain: bool,
	/// Whether or not we should fetch the previous key
	fetch_previous_key: bool,
	/// Function that takes `(raw_key_without_prefix, raw_value)` and decode `T`.
	/// `raw_key_without_prefix` is the raw storage key without the prefix iterated on.
	closure: fn(&[u8], &[u8]) -> Result<T, codec::Error>,
}

impl<T> ChildTriePrefixIterator<T> {
	/// Mutate this iterator into a draining iterator; items iterated are removed from storage.
	pub fn drain(mut self) -> Self {
		self.drain = true;
		self
	}
}

impl<T: Decode + Sized> ChildTriePrefixIterator<(Vec<u8>, T)> {
	/// Construct iterator to iterate over child trie items in `child_info` with the prefix `prefix`.
	///
	/// NOTE: Iterator with [`Self::drain`] will remove any value who failed to decode
	pub fn with_prefix(child_info: &ChildInfo, prefix: &[u8]) -> Self {
		let prefix = prefix.to_vec();
		let previous_key = prefix.clone();
		let closure = |raw_key_without_prefix: &[u8], raw_value: &[u8]| {
			let value = T::decode(&mut &raw_value[..])?;
			Ok((raw_key_without_prefix.to_vec(), value))
		};

		Self {
			prefix,
			child_info: child_info.clone(),
			previous_key,
			drain: false,
			fetch_previous_key: true,
			closure,
		}
	}
}

impl<K: Decode + Sized, T: Decode + Sized> ChildTriePrefixIterator<(K, T)> {
	/// Construct iterator to iterate over child trie items in `child_info` with the prefix `prefix`.
	///
	/// NOTE: Iterator with [`Self::drain`] will remove any key or value who failed to decode
	pub fn with_prefix_over_key<H: ReversibleStorageHasher>(child_info: &ChildInfo, prefix: &[u8]) -> Self {
		let prefix = prefix.to_vec();
		let previous_key = prefix.clone();
		let closure = |raw_key_without_prefix: &[u8], raw_value: &[u8]| {
			let mut key_material = H::reverse(raw_key_without_prefix);
			let key = K::decode(&mut key_material)?;
			let value = T::decode(&mut &raw_value[..])?;
			Ok((key, value))
		};

		Self {
			prefix,
			child_info: child_info.clone(),
			previous_key,
			drain: false,
			fetch_previous_key: true,
			closure,
		 }
	}
}

impl<T> Iterator for ChildTriePrefixIterator<T> {
	type Item = T;

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			let maybe_next = if self.fetch_previous_key {
				self.fetch_previous_key = false;
				Some(self.previous_key.clone())
			} else {
				sp_io::default_child_storage::next_key(
					&self.child_info.storage_key(),
					&self.previous_key,
				)
					.filter(|n| n.starts_with(&self.prefix))
			};
			break match maybe_next {
				Some(next) => {
					self.previous_key = next;
					let raw_value = match child::get_raw(&self.child_info, &self.previous_key) {
						Some(raw_value) => raw_value,
						None => {
							log::error!(
								"next_key returned a key with no value at {:?}",
								self.previous_key,
							);
							continue
						}
					};
					if self.drain {
						child::kill(&self.child_info, &self.previous_key)
					}
					let raw_key_without_prefix = &self.previous_key[self.prefix.len()..];
					let item = match (self.closure)(raw_key_without_prefix, &raw_value[..]) {
						Ok(item) => item,
						Err(e) => {
							log::error!(
								"(key, value) failed to decode at {:?}: {:?}",
								self.previous_key,
								e,
							);
							continue
						}
					};

					Some(item)
				}
				None => None,
			}
		}
	}
}

/// Trait for maps that store all its value after a unique prefix.
///
/// By default the final prefix is:
/// ```nocompile
/// Twox128(module_prefix) ++ Twox128(storage_prefix)
/// ```
pub trait StoragePrefixedMap<Value: FullCodec> {
	/// Module prefix. Used for generating final key.
	fn module_prefix() -> &'static [u8];

	/// Storage prefix. Used for generating final key.
	fn storage_prefix() -> &'static [u8];

	/// Final full prefix that prefixes all keys.
	fn final_prefix() -> [u8; 32] {
		let mut final_key = [0u8; 32];
		final_key[0..16].copy_from_slice(&Twox128::hash(Self::module_prefix()));
		final_key[16..32].copy_from_slice(&Twox128::hash(Self::storage_prefix()));
		final_key
	}

	/// Remove all value of the storage.
	fn remove_all() {
		sp_io::storage::clear_prefix(&Self::final_prefix())
	}

	/// Iter over all value of the storage.
	///
	/// NOTE: If a value failed to decode becaues storage is corrupted then it is skipped.
	fn iter_values() -> PrefixIterator<Value> {
		let prefix = Self::final_prefix();
		PrefixIterator {
			prefix: prefix.to_vec(),
			previous_key: prefix.to_vec(),
			drain: false,
			closure: |_raw_key, mut raw_value| Value::decode(&mut raw_value),
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
	fn translate_values<OldValue: Decode, F: FnMut(OldValue) -> Option<Value>>(mut f: F) {
		let prefix = Self::final_prefix();
		let mut previous_key = prefix.clone().to_vec();
		while let Some(next) = sp_io::storage::next_key(&previous_key)
			.filter(|n| n.starts_with(&prefix))
		{
			previous_key = next;
			let maybe_value = unhashed::get::<OldValue>(&previous_key);
			match maybe_value {
				Some(value) => match f(value) {
					Some(new) => unhashed::put::<Value>(&previous_key, &new),
					None => unhashed::kill(&previous_key),
				},
				None => {
					log::error!(
						"old key failed to decode at {:?}",
						previous_key,
					);
					continue
				},
			}
		}
	}
}

/// Marker trait that will be implemented for types that support the `storage::append` api.
///
/// This trait is sealed.
pub trait StorageAppend<Item: Encode>: private::Sealed {}

/// Marker trait that will be implemented for types that support to decode their length in an
/// effificent way. It is expected that the length is at the beginning of the encoded object
/// and that the length is a `Compact<u32>`.
///
/// This trait is sealed.
pub trait StorageDecodeLength: private::Sealed + codec::DecodeLength {
	/// Decode the length of the storage value at `key`.
	///
	/// This function assumes that the length is at the beginning of the encoded object
	/// and is a `Compact<u32>`.
	///
	/// Returns `None` if the storage value does not exist or the decoding failed.
	fn decode_len(key: &[u8]) -> Option<usize> {
		// `Compact<u32>` is 5 bytes in maximum.
		let mut data = [0u8; 5];
		let len = sp_io::storage::read(key, &mut data, 0)?;
		let len = data.len().min(len as usize);
		<Self as codec::DecodeLength>::len(&data[..len]).ok()
	}
}

/// Provides `Sealed` trait to prevent implementing trait `StorageAppend` & `StorageDecodeLength`
/// outside of this crate.
mod private {
	use super::*;

	pub trait Sealed {}

	impl<T: Encode> Sealed for Vec<T> {}
	impl<Hash: Encode> Sealed for Digest<Hash> {}
	impl<T: Value, S: Get<u32>> Sealed for BoundedVec<T, S> {}
}

impl<T: Encode> StorageAppend<T> for Vec<T> {}
impl<T: Encode> StorageDecodeLength for Vec<T> {}

/// We abuse the fact that SCALE does not put any marker into the encoding, i.e. we only encode the
/// internal vec and we can append to this vec. We have a test that ensures that if the `Digest`
/// format ever changes, we need to remove this here.
impl<Hash: Encode> StorageAppend<DigestItem<Hash>> for Digest<Hash> {}

/// Marker trait for types `T` that can be stored in storage as `Vec<T>`.
pub trait Value: FullCodec + Clone + sp_std::fmt::Debug + Eq + PartialEq {}
impl<T: FullCodec + Clone + sp_std::fmt::Debug + Eq + PartialEq> Value for T {}

/// A bounded vector.
///
/// It implementations for efficient append and length decoding, as with a normal `Vec<_>`, once put
/// into a [`StorageValue`].
///
/// As the name suggests, the length of the queue is always bounded. All internal operations ensure
/// this bound is respected.
#[derive(Encode, Decode, crate::DefaultNoBound, crate::CloneNoBound, crate::RuntimeDebugNoBound)]
pub struct BoundedVec<T: Value, S: Get<u32>>(Vec<T>, sp_std::marker::PhantomData<S>);

// NOTE: we could also implement this as:
// impl<T: Value, S1: Get<u32>, S2: Get<u32>> PartialEq<BoundedVec<T, S2>> for BoundedVec<T, S1>
// to allow comparison of bounded vectors with different bounds.
impl<T: Value, S: Get<u32>> PartialEq for BoundedVec<T, S> {
	fn eq(&self, rhs: &Self) -> bool {
		self.0 == rhs.0
	}
}
impl<T: Value, S: Get<u32>> Eq for BoundedVec<T, S> {}

impl<T: Value, S: Get<u32>> BoundedVec<T, S> {
	/// Create `Self` from `t` without any checks.
	///
	/// # WARNING
	///
	/// Only use when you are sure you know what you are doing.
	fn unchecked_from(t: Vec<T>) -> Self {
		Self(t, Default::default())
	}

	/// Create `Self` from `t` without any checks. Logs warnings if the bound is not being
	/// respected. The additional scope can be used to indicate where a potential overflow is
	/// happening.
	///
	/// # WARNING
	///
	/// Only use when you are sure you know what you are doing.
	pub fn force_from(t: Vec<T>, scope: Option<&'static str>) -> Self {
		if t.len() > Self::bound() {
			log::warn!(
				target: crate::LOG_TARGET,
				"length of a bounded vector in scope {} is not respected.",
				scope.unwrap_or("UNKNOWN"),
			);
		}

		Self::unchecked_from(t)
	}

	/// Get the bound of the type in `usize`.
	pub fn bound() -> usize {
		S::get() as usize
	}

	/// Consume self, and return the inner `Vec`. Henceforth, the `Vec<_>` can be altered in an
	/// arbitrary way. At some point, if the reverse conversion is required, `TryFrom<Vec<_>>` can
	/// be used.
	///
	/// This is useful for cases if you need access to an internal API of the inner `Vec<_>` which
	/// is not provided by the wrapper `BoundedVec`.
	pub fn into_inner(self) -> Vec<T> {
		debug_assert!(self.0.len() <= Self::bound());
		self.0
	}

	/// Exactly the same semantics as [`Vec::insert`], but returns an `Err` (and is a noop) if the
	/// new length of the vector exceeds `S`.
	///
	/// # Panics
	///
	/// Panics if `index > len`.
	pub fn try_insert(&mut self, index: usize, element: T) -> Result<(), ()> {
		if self.len() < Self::bound() {
			self.0.insert(index, element);
			Ok(())
		} else {
			Err(())
		}
	}

	/// Exactly the same semantics as [`Vec::remove`].
	///
	/// # Panics
	///
	/// Panics if `index` is out of bounds.
	pub fn remove(&mut self, index: usize) {
		self.0.remove(index);
	}

	/// Exactly the same semantics as [`Vec::swap_remove`].
	///
	/// # Panics
	///
	/// Panics if `index` is out of bounds.
	pub fn swap_remove(&mut self, index: usize) {
		self.0.swap_remove(index);
	}

	/// Exactly the same semantics as [`Vec::retain`].
	pub fn retain<F: FnMut(&T) -> bool>(&mut self, f: F) {
		self.0.retain(f)
	}
}

impl<T: Value, S: Get<u32>> TryFrom<Vec<T>> for BoundedVec<T, S> {
	type Error = ();
	fn try_from(t: Vec<T>) -> Result<Self, Self::Error> {
		if t.len() <= Self::bound() {
			Ok(Self::unchecked_from(t))
		} else {
			Err(())
		}
	}
}

// It is okay to give a non-mutable reference of the inner vec to anyone.
impl<T: Value, S: Get<u32>> AsRef<Vec<T>> for BoundedVec<T, S> {
	fn as_ref(&self) -> &Vec<T> {
		&self.0
	}
}

// will allow for immutable all operations of `Vec<T>` on `BoundedVec<T>`.
impl<T: Value, S: Get<u32>> sp_std::ops::Deref for BoundedVec<T, S> {
	type Target = Vec<T>;

	fn deref(&self) -> &Self::Target {
		&self.0
	}
}

impl<T: Value, S: Get<u32>> sp_std::ops::Index<usize> for BoundedVec<T, S> {
	type Output = T;
	fn index(&self, index: usize) -> &Self::Output {
		self.get(index).expect("index out of bound")
	}
}

impl<T: Value, S: Get<u32>> sp_std::iter::IntoIterator for BoundedVec<T, S> {
	type Item = T;
	type IntoIter = sp_std::vec::IntoIter<T>;
	fn into_iter(self) -> Self::IntoIter {
		self.0.into_iter()
	}
}

impl<T: Value, S: Get<u32>> codec::DecodeLength for BoundedVec<T, S> {
	fn len(self_encoded: &[u8]) -> Result<usize, codec::Error> {
		// `BoundedVec<T, _>` stored just a `Vec<T>`, thus the length is at the beginning in
		// `Compact` form, and same implementation as `Vec<T>` can be used.
		<Vec<T> as codec::DecodeLength>::len(self_encoded)
	}
}

impl<T: Value, S: Get<u32>> StorageDecodeLength for BoundedVec<T, S> {}

/// Storage value that is *maybe* capable of [`StorageAppend`].
pub trait TryAppendValue<T: Value, S: Get<u32>> {
	fn try_append<LikeT: EncodeLike<T>>(item: LikeT) -> Result<(), ()>;
}

/// Storage map that is *maybe* capable of [`StorageAppend`].
pub trait TryAppendMap<K: FullCodec, T: Value, S: Get<u32>> {
	fn try_append<LikeK: EncodeLike<K> + Clone, LikeT: EncodeLike<T>>(
		key: LikeK,
		item: LikeT,
	) -> Result<(), ()>;
}

impl<T: Value, S: Get<u32>, StorageValueT: generator::StorageValue<BoundedVec<T, S>>>
	TryAppendValue<T, S> for StorageValueT
{
	fn try_append<LikeT: EncodeLike<T>>(item: LikeT) -> Result<(), ()> {
		let bound = BoundedVec::<T, S>::bound();
		let current = Self::decode_len().unwrap_or_default();
		if current < bound {
			// NOTE: we cannot reuse the implementation for `Vec<T>` here because we never want to
			// mark `BoundedVec<T, S>` as `StorageAppend`.
			let key = Self::storage_value_final_key();
			sp_io::storage::append(&key, item.encode());
			Ok(())
		} else {
			Err(())
		}
	}
}

impl<
		K: FullCodec,
		T: Value,
		S: Get<u32>,
		StorageMapT: generator::StorageMap<K, BoundedVec<T, S>>,
	> TryAppendMap<K, T, S> for StorageMapT
{
	fn try_append<LikeK: EncodeLike<K> + Clone, LikeT: EncodeLike<T>>(
		key: LikeK,
		item: LikeT,
	) -> Result<(), ()> {
		let bound = BoundedVec::<T, S>::bound();
		let current = Self::decode_len(key.clone()).unwrap_or_default();
		if current < bound {
			let key = Self::storage_map_final_key(key);
			sp_io::storage::append(&key, item.encode());
			Ok(())
		} else {
			Err(())
		}
	}
}

#[cfg(test)]
pub mod bounded_vec {
	use super::*;
	use sp_io::TestExternalities;
	use sp_std::convert::TryInto;
	use crate::{assert_ok, Twox128};

	crate::parameter_types! {
		pub const Seven: u32 = 7;
	}

	crate::generate_storage_alias! { Prefix, Foo => Value<BoundedVec<u32, Seven>> }
	crate::generate_storage_alias! { Prefix, FooMap => Map<(u32, Twox128), BoundedVec<u32, Seven>> }

	#[test]
	fn decode_len_works() {
		TestExternalities::default().execute_with(|| {
			let bounded: BoundedVec<u32, Seven> = vec![1, 2, 3].try_into().unwrap();
			Foo::put(bounded);
			assert_eq!(Foo::decode_len().unwrap(), 3);
		});

		TestExternalities::default().execute_with(|| {
			let bounded: BoundedVec<u32, Seven> = vec![1, 2, 3].try_into().unwrap();
			FooMap::insert(1, bounded);
			assert_eq!(FooMap::decode_len(1).unwrap(), 3);
			assert!(FooMap::decode_len(0).is_none());
			assert!(FooMap::decode_len(2).is_none());
		});
	}

	#[test]
	fn try_append_works() {
		TestExternalities::default().execute_with(|| {
			let bounded: BoundedVec<u32, Seven> = vec![1, 2, 3].try_into().unwrap();
			Foo::put(bounded);
			assert_ok!(Foo::try_append(4));
			assert_ok!(Foo::try_append(5));
			assert_ok!(Foo::try_append(6));
			assert_ok!(Foo::try_append(7));
			assert_eq!(Foo::decode_len().unwrap(), 7);
			assert!(Foo::try_append(8).is_err());
		});

		TestExternalities::default().execute_with(|| {
			let bounded: BoundedVec<u32, Seven> = vec![1, 2, 3].try_into().unwrap();
			FooMap::insert(1, bounded);

			assert_ok!(FooMap::try_append(1, 4));
			assert_ok!(FooMap::try_append(1, 5));
			assert_ok!(FooMap::try_append(1, 6));
			assert_ok!(FooMap::try_append(1, 7));
			assert_eq!(FooMap::decode_len(1).unwrap(), 7);
			assert!(FooMap::try_append(1, 8).is_err());

			// append to a non-existing
			assert!(FooMap::get(2).is_none());
			assert_ok!(FooMap::try_append(2, 4));
			assert_eq!(FooMap::get(2).unwrap(), BoundedVec::<u32, Seven>::unchecked_from(vec![4]));
			assert_ok!(FooMap::try_append(2, 5));
			assert_eq!(
				FooMap::get(2).unwrap(),
				BoundedVec::<u32, Seven>::unchecked_from(vec![4, 5])
			);
		});
	}

	#[test]
	fn deref_coercion_works() {
		let bounded: BoundedVec<u32, Seven> = vec![1, 2, 3].try_into().unwrap();
		// these methods come from deref-ed vec.
		assert_eq!(bounded.len(), 3);
		assert!(bounded.iter().next().is_some());
		assert!(!bounded.is_empty());
	}
}

#[cfg(test)]
mod test {
	use super::*;
	use sp_core::hashing::twox_128;
	use crate::hash::Identity;
	use sp_io::TestExternalities;
	use generator::StorageValue as _;

	#[test]
	fn prefixed_map_works() {
		TestExternalities::default().execute_with(|| {
			struct MyStorage;
			impl StoragePrefixedMap<u64> for MyStorage {
				fn module_prefix() -> &'static [u8] {
					b"MyModule"
				}

				fn storage_prefix() -> &'static [u8] {
					b"MyStorage"
				}
			}

			let key_before = {
				let mut k = MyStorage::final_prefix();
				let last = k.iter_mut().last().unwrap();
				*last = last.checked_sub(1).unwrap();
				k
			};
			let key_after = {
				let mut k = MyStorage::final_prefix();
				let last = k.iter_mut().last().unwrap();
				*last = last.checked_add(1).unwrap();
				k
			};

			unhashed::put(&key_before[..], &32u64);
			unhashed::put(&key_after[..], &33u64);

			let k = [twox_128(b"MyModule"), twox_128(b"MyStorage")].concat();
			assert_eq!(MyStorage::final_prefix().to_vec(), k);

			// test iteration
			assert!(MyStorage::iter_values().collect::<Vec<_>>().is_empty());

			unhashed::put(&[&k[..], &vec![1][..]].concat(), &1u64);
			unhashed::put(&[&k[..], &vec![1, 1][..]].concat(), &2u64);
			unhashed::put(&[&k[..], &vec![8][..]].concat(), &3u64);
			unhashed::put(&[&k[..], &vec![10][..]].concat(), &4u64);

			assert_eq!(MyStorage::iter_values().collect::<Vec<_>>(), vec![1, 2, 3, 4]);

			// test removal
			MyStorage::remove_all();
			assert!(MyStorage::iter_values().collect::<Vec<_>>().is_empty());

			// test migration
			unhashed::put(&[&k[..], &vec![1][..]].concat(), &1u32);
			unhashed::put(&[&k[..], &vec![8][..]].concat(), &2u32);

			assert!(MyStorage::iter_values().collect::<Vec<_>>().is_empty());
			MyStorage::translate_values(|v: u32| Some(v as u64));
			assert_eq!(MyStorage::iter_values().collect::<Vec<_>>(), vec![1, 2]);
			MyStorage::remove_all();

			// test migration 2
			unhashed::put(&[&k[..], &vec![1][..]].concat(), &1u128);
			unhashed::put(&[&k[..], &vec![1, 1][..]].concat(), &2u64);
			unhashed::put(&[&k[..], &vec![8][..]].concat(), &3u128);
			unhashed::put(&[&k[..], &vec![10][..]].concat(), &4u32);

			// (contains some value that successfully decoded to u64)
			assert_eq!(MyStorage::iter_values().collect::<Vec<_>>(), vec![1, 2, 3]);
			MyStorage::translate_values(|v: u128| Some(v as u64));
			assert_eq!(MyStorage::iter_values().collect::<Vec<_>>(), vec![1, 2, 3]);
			MyStorage::remove_all();

			// test that other values are not modified.
			assert_eq!(unhashed::get(&key_before[..]), Some(32u64));
			assert_eq!(unhashed::get(&key_after[..]), Some(33u64));
		});
	}

	// This test ensures that the Digest encoding does not change without being noticied.
	#[test]
	fn digest_storage_append_works_as_expected() {
		TestExternalities::default().execute_with(|| {
			struct Storage;
			impl generator::StorageValue<Digest<u32>> for Storage {
				type Query = Digest<u32>;

				fn module_prefix() -> &'static [u8] {
					b"MyModule"
				}

				fn storage_prefix() -> &'static [u8] {
					b"Storage"
				}

				fn from_optional_value_to_query(v: Option<Digest<u32>>) -> Self::Query {
					v.unwrap()
				}

				fn from_query_to_optional_value(v: Self::Query) -> Option<Digest<u32>> {
					Some(v)
				}
			}

			Storage::append(DigestItem::ChangesTrieRoot(1));
			Storage::append(DigestItem::Other(Vec::new()));

			let value = unhashed::get_raw(&Storage::storage_value_final_key()).unwrap();

			let expected = Digest {
				logs: vec![DigestItem::ChangesTrieRoot(1), DigestItem::Other(Vec::new())],
			};
			assert_eq!(Digest::decode(&mut &value[..]).unwrap(), expected);
		});
	}

	#[test]
	#[should_panic(expected = "Require transaction not called within with_transaction")]
	fn require_transaction_should_panic() {
		TestExternalities::default().execute_with(|| {
			require_transaction();
		});
	}

	#[test]
	fn require_transaction_should_not_panic_in_with_transaction() {
		TestExternalities::default().execute_with(|| {
			with_transaction(|| {
				require_transaction();
				TransactionOutcome::Commit(())
			});

			with_transaction(|| {
				require_transaction();
				TransactionOutcome::Rollback(())
			});
		});
	}

	#[test]
	fn child_trie_prefixed_map_works() {
		TestExternalities::default().execute_with(|| {
			let child_info_a = child::ChildInfo::new_default(b"a");
			child::put(&child_info_a, &[1, 2, 3], &8u16);
			child::put(&child_info_a, &[2], &8u16);
			child::put(&child_info_a, &[2, 1, 3], &8u8);
			child::put(&child_info_a, &[2, 2, 3], &8u16);
			child::put(&child_info_a, &[3], &8u16);

			assert_eq!(
				ChildTriePrefixIterator::with_prefix(&child_info_a, &[2])
					.collect::<Vec<(Vec<u8>, u16)>>(),
				vec![
					(vec![], 8),
					(vec![2, 3], 8),
				],
			);

			assert_eq!(
				ChildTriePrefixIterator::with_prefix(&child_info_a, &[2])
					.drain()
					.collect::<Vec<(Vec<u8>, u16)>>(),
				vec![
					(vec![], 8),
					(vec![2, 3], 8),
				],
			);

			// The only remaining is the ones outside prefix
			assert_eq!(
				ChildTriePrefixIterator::with_prefix(&child_info_a, &[])
					.collect::<Vec<(Vec<u8>, u8)>>(),
				vec![
					(vec![1, 2, 3], 8),
					(vec![3], 8),
				],
			);

			child::put(&child_info_a, &[1, 2, 3], &8u16);
			child::put(&child_info_a, &[2], &8u16);
			child::put(&child_info_a, &[2, 1, 3], &8u8);
			child::put(&child_info_a, &[2, 2, 3], &8u16);
			child::put(&child_info_a, &[3], &8u16);

			assert_eq!(
				ChildTriePrefixIterator::with_prefix_over_key::<Identity>(&child_info_a, &[2])
					.collect::<Vec<(u16, u16)>>(),
				vec![
					(u16::decode(&mut &[2, 3][..]).unwrap(), 8),
				],
			);

			assert_eq!(
				ChildTriePrefixIterator::with_prefix_over_key::<Identity>(&child_info_a, &[2])
					.drain()
					.collect::<Vec<(u16, u16)>>(),
				vec![
					(u16::decode(&mut &[2, 3][..]).unwrap(), 8),
				],
			);

			// The only remaining is the ones outside prefix
			assert_eq!(
				ChildTriePrefixIterator::with_prefix(&child_info_a, &[])
					.collect::<Vec<(Vec<u8>, u8)>>(),
				vec![
					(vec![1, 2, 3], 8),
					(vec![3], 8),
				],
			);
		});
	}
}
