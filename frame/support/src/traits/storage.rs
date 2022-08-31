// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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
use sp_core::storage::TrackedStorageKey;
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
#[derive(codec::Encode, codec::Decode, crate::RuntimeDebug, Eq, PartialEq, Clone)]
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

#[impl_for_tuples(5)]
impl WhitelistedStorageKeys for Tuple {
	fn whitelisted_storage_keys() -> Vec<TrackedStorageKey> {
		// use BTreeSet so the resulting list of keys is unique
		let mut combined_keys = BTreeSet::new();
		for_tuples!( #(
			for key in Tuple::whitelisted_storage_keys() {
				combined_keys.insert(key);
			}
		 )* );
		// flatten BTreeSet down to a vec
		let mut combined_keys_vec = Vec::new();
		for key in combined_keys {
			combined_keys_vec.push(key);
		}
		combined_keys_vec
	}
}
