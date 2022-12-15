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

use sp_io::hashing::twox_128;
use sp_std::str;

use frame_support::{
	storage::{generator::StorageValue, StoragePrefixedMap},
	traits::{
		Get, GetStorageVersion, PalletInfoAccess, StorageVersion,
		STORAGE_VERSION_STORAGE_KEY_POSTFIX,
	},
	weights::Weight,
};

use crate::historical as pallet_session_historical;

const OLD_PREFIX: &str = "Session";

/// Migrate the entire storage of this pallet to a new prefix.
///
/// This new prefix must be the same as the one set in construct_runtime.
///
/// The migration will look into the storage version in order not to trigger a migration on an up
/// to date storage. Thus the on chain storage version must be less than 1 in order to trigger the
/// migration.
pub fn migrate<T: pallet_session_historical::Config, P: GetStorageVersion + PalletInfoAccess>(
) -> Weight {
	let new_pallet_name = <P as PalletInfoAccess>::name();

	if new_pallet_name == OLD_PREFIX {
		log::info!(
			target: "runtime::session_historical",
			"New pallet name is equal to the old prefix. No migration needs to be done.",
		);
		return Weight::zero()
	}

	let on_chain_storage_version = <P as GetStorageVersion>::on_chain_storage_version();
	log::info!(
		target: "runtime::session_historical",
		"Running migration to v1 for session_historical with storage version {:?}",
		on_chain_storage_version,
	);

	if on_chain_storage_version < 1 {
		let storage_prefix = pallet_session_historical::HistoricalSessions::<T>::storage_prefix();
		frame_support::storage::migration::move_storage_from_pallet(
			storage_prefix,
			OLD_PREFIX.as_bytes(),
			new_pallet_name.as_bytes(),
		);
		log_migration("migration", storage_prefix, OLD_PREFIX, new_pallet_name);

		let storage_prefix = pallet_session_historical::StoredRange::<T>::storage_prefix();
		frame_support::storage::migration::move_storage_from_pallet(
			storage_prefix,
			OLD_PREFIX.as_bytes(),
			new_pallet_name.as_bytes(),
		);
		log_migration("migration", storage_prefix, OLD_PREFIX, new_pallet_name);

		StorageVersion::new(1).put::<P>();
		<T as frame_system::Config>::BlockWeights::get().max_block
	} else {
		log::warn!(
			target: "runtime::session_historical",
			"Attempted to apply migration to v1 but failed because storage version is {:?}",
			on_chain_storage_version,
		);
		Weight::zero()
	}
}

/// Some checks prior to migration. This can be linked to
/// `frame_support::traits::OnRuntimeUpgrade::pre_upgrade` for further testing.
///
/// Panics if anything goes wrong.
pub fn pre_migrate<
	T: pallet_session_historical::Config,
	P: GetStorageVersion + PalletInfoAccess,
>() {
	let new_pallet_name = <P as PalletInfoAccess>::name();

	let storage_prefix_historical_sessions =
		pallet_session_historical::HistoricalSessions::<T>::storage_prefix();
	let storage_prefix_stored_range = pallet_session_historical::StoredRange::<T>::storage_prefix();

	log_migration("pre-migration", storage_prefix_historical_sessions, OLD_PREFIX, new_pallet_name);
	log_migration("pre-migration", storage_prefix_stored_range, OLD_PREFIX, new_pallet_name);

	if new_pallet_name == OLD_PREFIX {
		return
	}

	let new_pallet_prefix = twox_128(new_pallet_name.as_bytes());
	let storage_version_key = twox_128(STORAGE_VERSION_STORAGE_KEY_POSTFIX);

	let mut new_pallet_prefix_iter = frame_support::storage::KeyPrefixIterator::new(
		new_pallet_prefix.to_vec(),
		new_pallet_prefix.to_vec(),
		|key| Ok(key.to_vec()),
	);

	// Ensure nothing except the storage_version_key is stored in the new prefix.
	assert!(new_pallet_prefix_iter.all(|key| key == storage_version_key));

	assert!(<P as GetStorageVersion>::on_chain_storage_version() < 1);
}

/// Some checks for after migration. This can be linked to
/// `frame_support::traits::OnRuntimeUpgrade::post_upgrade` for further testing.
///
/// Panics if anything goes wrong.
pub fn post_migrate<
	T: pallet_session_historical::Config,
	P: GetStorageVersion + PalletInfoAccess,
>() {
	let new_pallet_name = <P as PalletInfoAccess>::name();

	let storage_prefix_historical_sessions =
		pallet_session_historical::HistoricalSessions::<T>::storage_prefix();
	let storage_prefix_stored_range = pallet_session_historical::StoredRange::<T>::storage_prefix();

	log_migration(
		"post-migration",
		storage_prefix_historical_sessions,
		OLD_PREFIX,
		new_pallet_name,
	);
	log_migration("post-migration", storage_prefix_stored_range, OLD_PREFIX, new_pallet_name);

	if new_pallet_name == OLD_PREFIX {
		return
	}

	// Assert that no `HistoricalSessions` and `StoredRange` storages remains at the old prefix.
	let old_pallet_prefix = twox_128(OLD_PREFIX.as_bytes());
	let old_historical_sessions_key =
		[&old_pallet_prefix, &twox_128(storage_prefix_historical_sessions)[..]].concat();
	let old_historical_sessions_key_iter = frame_support::storage::KeyPrefixIterator::new(
		old_historical_sessions_key.to_vec(),
		old_historical_sessions_key.to_vec(),
		|_| Ok(()),
	);
	assert_eq!(old_historical_sessions_key_iter.count(), 0);

	let old_stored_range_key =
		[&old_pallet_prefix, &twox_128(storage_prefix_stored_range)[..]].concat();
	let old_stored_range_key_iter = frame_support::storage::KeyPrefixIterator::new(
		old_stored_range_key.to_vec(),
		old_stored_range_key.to_vec(),
		|_| Ok(()),
	);
	assert_eq!(old_stored_range_key_iter.count(), 0);

	// Assert that the `HistoricalSessions` and `StoredRange` storages (if they exist) have been
	// moved to the new prefix.
	// NOTE: storage_version_key is already in the new prefix.
	let new_pallet_prefix = twox_128(new_pallet_name.as_bytes());
	let new_pallet_prefix_iter = frame_support::storage::KeyPrefixIterator::new(
		new_pallet_prefix.to_vec(),
		new_pallet_prefix.to_vec(),
		|_| Ok(()),
	);
	assert!(new_pallet_prefix_iter.count() >= 1);

	assert_eq!(<P as GetStorageVersion>::on_chain_storage_version(), 1);
}

fn log_migration(stage: &str, storage_prefix: &[u8], old_pallet_name: &str, new_pallet_name: &str) {
	log::info!(
		target: "runtime::session_historical",
		"{} prefix of storage '{}': '{}' ==> '{}'",
		stage,
		str::from_utf8(storage_prefix).unwrap_or("<Invalid UTF8>"),
		old_pallet_name,
		new_pallet_name,
	);
}
