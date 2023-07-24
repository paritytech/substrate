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

//! Traits for encoding data related to pallet's storage items.

use crate::sp_std::collections::btree_set::BTreeSet;
use impl_trait_for_tuples::impl_for_tuples;
pub use sp_core::storage::TrackedStorageKey;
use sp_runtime::traits::Saturating;
use sp_std::prelude::*;

/// An instance of a pallet in the storage.
///
/// It is required that these instances are unique, to support multiple instances per pallet in the
/// same runtime!
///
/// E.g. for module MyModule default instance will have prefix "MyModule" and other instances
/// "InstanceNMyModule".
pub trait Instance: 'static {
	/// Unique module prefix. E.g. "InstanceNMyModule" or "MyModule"
	const PREFIX: &'static str;
	/// Unique numerical identifier for an instance.
	const INDEX: u8;
}

// Dummy implementation for `()`.
impl Instance for () {
	const PREFIX: &'static str = "";
	const INDEX: u8 = 0;
}

/// An instance of a storage in a pallet.
///
/// Define an instance for an individual storage inside a pallet.
/// The pallet prefix is used to isolate the storage between pallets, and the storage prefix is
/// used to isolate storages inside a pallet.
///
/// NOTE: These information can be used to define storages in pallet such as a `StorageMap` which
/// can use keys after `twox_128(pallet_prefix())++twox_128(STORAGE_PREFIX)`
pub trait StorageInstance {
	/// Prefix of a pallet to isolate it from other pallets.
	fn pallet_prefix() -> &'static str;

	/// Prefix given to a storage to isolate from other storages in the pallet.
	const STORAGE_PREFIX: &'static str;
}

/// Metadata about storage from the runtime.
#[derive(
	codec::Encode, codec::Decode, crate::RuntimeDebug, Eq, PartialEq, Clone, scale_info::TypeInfo,
)]
pub struct StorageInfo {
	/// Encoded string of pallet name.
	pub pallet_name: Vec<u8>,
	/// Encoded string of storage name.
	pub storage_name: Vec<u8>,
	/// The prefix of the storage. All keys after the prefix are considered part of this storage.
	pub prefix: Vec<u8>,
	/// The maximum number of values in the storage, or none if no maximum specified.
	pub max_values: Option<u32>,
	/// The maximum size of key/values in the storage, or none if no maximum specified.
	pub max_size: Option<u32>,
}

/// A trait to give information about storage.
///
/// It can be used to calculate PoV worst case size.
pub trait StorageInfoTrait {
	fn storage_info() -> Vec<StorageInfo>;
}

#[cfg_attr(all(not(feature = "tuples-96"), not(feature = "tuples-128")), impl_for_tuples(64))]
#[cfg_attr(all(feature = "tuples-96", not(feature = "tuples-128")), impl_for_tuples(96))]
#[cfg_attr(feature = "tuples-128", impl_for_tuples(128))]
impl StorageInfoTrait for Tuple {
	fn storage_info() -> Vec<StorageInfo> {
		let mut res = vec![];
		for_tuples!( #( res.extend_from_slice(&Tuple::storage_info()); )* );
		res
	}
}

/// Similar to [`StorageInfoTrait`], a trait to give partial information about storage.
///
/// This is useful when a type can give some partial information with its generic parameter doesn't
/// implement some bounds.
pub trait PartialStorageInfoTrait {
	fn partial_storage_info() -> Vec<StorageInfo>;
}

/// Allows a pallet to specify storage keys to whitelist during benchmarking.
/// This means those keys will be excluded from the benchmarking performance
/// calculation.
pub trait WhitelistedStorageKeys {
	/// Returns a [`Vec<TrackedStorageKey>`] indicating the storage keys that
	/// should be whitelisted during benchmarking. This means that those keys
	/// will be excluded from the benchmarking performance calculation.
	fn whitelisted_storage_keys() -> Vec<TrackedStorageKey>;
}

#[cfg_attr(all(not(feature = "tuples-96"), not(feature = "tuples-128")), impl_for_tuples(64))]
#[cfg_attr(all(feature = "tuples-96", not(feature = "tuples-128")), impl_for_tuples(96))]
#[cfg_attr(feature = "tuples-128", impl_for_tuples(128))]
impl WhitelistedStorageKeys for Tuple {
	fn whitelisted_storage_keys() -> Vec<TrackedStorageKey> {
		// de-duplicate the storage keys
		let mut combined_keys: BTreeSet<TrackedStorageKey> = BTreeSet::new();
		for_tuples!( #(
			for storage_key in Tuple::whitelisted_storage_keys() {
				combined_keys.insert(storage_key);
			}
		 )* );
		combined_keys.into_iter().collect::<Vec<_>>()
	}
}

macro_rules! impl_incrementable {
	($($type:ty),+) => {
		$(
			impl Incrementable for $type {
				fn increment(&self) -> Self {
					let mut val = self.clone();
					val.saturating_inc();
					val
				}

				fn initial_value() -> Self {
					0
				}
			}
		)+
	};
}

/// For example: allows new identifiers to be created in a linear fashion.
pub trait Incrementable {
	fn increment(&self) -> Self;
	fn initial_value() -> Self;
}

impl_incrementable!(u8, u16, u32, u64, u128, i8, i16, i32, i64, i128);
