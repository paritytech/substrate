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

use frame_support::{
	storage::{generator::StorageValue, StoragePrefixedMap},
	traits::{
		Get, GetStorageVersion, PalletInfoAccess, StorageVersion,
		STORAGE_VERSION_STORAGE_KEY_POSTFIX,
	},
	weights::Weight,
};
use sp_core::hexdisplay::HexDisplay;
use sp_io::{hashing::twox_128, storage};
use sp_std::str;

use crate as pallet_bounties;

/// Migrate the storage of the bounties pallet to a new prefix, leaving all other storage untouched
///
/// This new prefix must be the same as the one set in construct_runtime. For safety, use
/// `PalletInfo` to get it, as:
/// `<Runtime as frame_system::Config>::PalletInfo::name::<BountiesPallet>`.
///
/// The migration will look into the storage version in order not to trigger a migration on an up
/// to date storage. Thus the on chain storage version must be less than 4 in order to trigger the
/// migration.
pub fn migrate<
	T: pallet_bounties::Config,
	P: GetStorageVersion + PalletInfoAccess,
	N: AsRef<str>,
>(
	old_pallet_name: N,
	new_pallet_name: N,
) -> Weight {
	let old_pallet_name = old_pallet_name.as_ref();
	let new_pallet_name = new_pallet_name.as_ref();

	if new_pallet_name == old_pallet_name {
		log::info!(
			target: "runtime::bounties",
			"New pallet name is equal to the old prefix. No migration needs to be done.",
		);
		return 0
	}

	let on_chain_storage_version = <P as GetStorageVersion>::on_chain_storage_version();
	log::info!(
		target: "runtime::bounties",
		"Running migration to v4 for bounties with storage version {:?}",
		on_chain_storage_version,
	);

	if on_chain_storage_version < 4 {
		let storage_prefix = pallet_bounties::BountyCount::<T>::storage_prefix();
		frame_support::storage::migration::move_storage_from_pallet(
			storage_prefix,
			old_pallet_name.as_bytes(),
			new_pallet_name.as_bytes(),
		);
		log_migration("migration", storage_prefix, old_pallet_name, new_pallet_name);

		let storage_prefix = pallet_bounties::Bounties::<T>::storage_prefix();
		frame_support::storage::migration::move_storage_from_pallet(
			storage_prefix,
			old_pallet_name.as_bytes(),
			new_pallet_name.as_bytes(),
		);
		log_migration("migration", storage_prefix, old_pallet_name, new_pallet_name);

		let storage_prefix = pallet_bounties::BountyDescriptions::<T>::storage_prefix();
		frame_support::storage::migration::move_storage_from_pallet(
			storage_prefix,
			old_pallet_name.as_bytes(),
			new_pallet_name.as_bytes(),
		);
		log_migration("migration", storage_prefix, old_pallet_name, new_pallet_name);

		let storage_prefix = pallet_bounties::BountyApprovals::<T>::storage_prefix();
		frame_support::storage::migration::move_storage_from_pallet(
			storage_prefix,
			old_pallet_name.as_bytes(),
			new_pallet_name.as_bytes(),
		);
		log_migration("migration", storage_prefix, old_pallet_name, new_pallet_name);

		StorageVersion::new(4).put::<P>();
		<T as frame_system::Config>::BlockWeights::get().max_block
	} else {
		log::warn!(
			target: "runtime::bounties",
			"Attempted to apply migration to v4 but failed because storage version is {:?}",
			on_chain_storage_version,
		);
		0
	}
}

/// Some checks prior to migration. This can be linked to
/// [`frame_support::traits::OnRuntimeUpgrade::pre_upgrade`] for further testing.
///
/// Panics if anything goes wrong.
pub fn pre_migration<T: pallet_bounties::Config, P: GetStorageVersion + 'static, N: AsRef<str>>(
	old_pallet_name: N,
	new_pallet_name: N,
) {
	let old_pallet_name = old_pallet_name.as_ref();
	let new_pallet_name = new_pallet_name.as_ref();
	let storage_prefix_bounties_count = pallet_bounties::BountyCount::<T>::storage_prefix();
	let storage_prefix_bounties = pallet_bounties::Bounties::<T>::storage_prefix();
	let storage_prefix_bounties_description =
		pallet_bounties::BountyDescriptions::<T>::storage_prefix();
	let storage_prefix_bounties_approvals = pallet_bounties::BountyApprovals::<T>::storage_prefix();
	log_migration("pre-migration", storage_prefix_bounties_count, old_pallet_name, new_pallet_name);
	log_migration("pre-migration", storage_prefix_bounties, old_pallet_name, new_pallet_name);
	log_migration(
		"pre-migration",
		storage_prefix_bounties_description,
		old_pallet_name,
		new_pallet_name,
	);
	log_migration(
		"pre-migration",
		storage_prefix_bounties_approvals,
		old_pallet_name,
		new_pallet_name,
	);

	let new_pallet_prefix = twox_128(new_pallet_name.as_bytes());
	let storage_version_key =
		[&new_pallet_prefix, &twox_128(STORAGE_VERSION_STORAGE_KEY_POSTFIX)[..]].concat();

	// ensure nothing is stored in the new prefix.
	assert!(
		storage::next_key(&new_pallet_prefix).map_or(
			// either nothing is there
			true,
			// or we ensure that the next key has no common prefix with twox_128(new),
			// or is the pallet version that is already stored using the pallet name
			|next_key| {
				storage::next_key(&next_key).map_or(true, |next_key| {
					!next_key.starts_with(&new_pallet_prefix) || next_key == storage_version_key
				})
			},
		),
		"unexpected next_key({}) = {:?}",
		new_pallet_name,
		HexDisplay::from(&sp_io::storage::next_key(&new_pallet_prefix).unwrap()),
	);
	assert!(<P as GetStorageVersion>::on_chain_storage_version() < 4);
}

/// Some checks for after migration. This can be linked to
/// [`frame_support::traits::OnRuntimeUpgrade::post_upgrade`] for further testing.
///
/// Panics if anything goes wrong.
pub fn post_migration<T: pallet_bounties::Config, P: GetStorageVersion, N: AsRef<str>>(
	old_pallet_name: N,
	new_pallet_name: N,
) {
	let old_pallet_name = old_pallet_name.as_ref();
	let new_pallet_name = new_pallet_name.as_ref();
	let storage_prefix_bounties_count = pallet_bounties::BountyCount::<T>::storage_prefix();
	let storage_prefix_bounties = pallet_bounties::Bounties::<T>::storage_prefix();
	let storage_prefix_bounties_description =
		pallet_bounties::BountyDescriptions::<T>::storage_prefix();
	let storage_prefix_bounties_approvals = pallet_bounties::BountyApprovals::<T>::storage_prefix();
	log_migration(
		"post-migration",
		storage_prefix_bounties_count,
		old_pallet_name,
		new_pallet_name,
	);
	log_migration("post-migration", storage_prefix_bounties, old_pallet_name, new_pallet_name);
	log_migration(
		"post-migration",
		storage_prefix_bounties_description,
		old_pallet_name,
		new_pallet_name,
	);
	log_migration(
		"post-migration",
		storage_prefix_bounties_approvals,
		old_pallet_name,
		new_pallet_name,
	);

	let old_pallet_prefix = twox_128(old_pallet_name.as_bytes());
	let old_bounties_count_key =
		[&old_pallet_prefix, &twox_128(storage_prefix_bounties_count)[..]].concat();
	let old_bounties_key = [&old_pallet_prefix, &twox_128(storage_prefix_bounties)[..]].concat();
	let old_bounties_description_key =
		[&old_pallet_prefix, &twox_128(storage_prefix_bounties_description)[..]].concat();
	let old_bounties_approvals_key =
		[&old_pallet_prefix, &twox_128(storage_prefix_bounties_approvals)[..]].concat();
	assert!(storage::next_key(&old_bounties_count_key)
		.map_or(true, |next_key| !next_key.starts_with(&old_bounties_count_key)));
	assert!(storage::next_key(&old_bounties_key)
		.map_or(true, |next_key| !next_key.starts_with(&old_bounties_key)));
	assert!(storage::next_key(&old_bounties_description_key)
		.map_or(true, |next_key| !next_key.starts_with(&old_bounties_description_key)));
	assert!(storage::next_key(&old_bounties_approvals_key)
		.map_or(true, |next_key| !next_key.starts_with(&old_bounties_approvals_key)));

	assert_eq!(<P as GetStorageVersion>::on_chain_storage_version(), 4);
}

fn log_migration(stage: &str, storage_prefix: &[u8], old_pallet_name: &str, new_pallet_name: &str) {
	log::info!(
		target: "runtime::bounties",
		"{} prefix of storage '{}': '{}' ==> '{}'",
		stage,
		str::from_utf8(storage_prefix).unwrap_or("<Invalid UTF8>"),
		old_pallet_name,
		new_pallet_name,
	);
}
