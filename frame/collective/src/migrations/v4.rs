// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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
	traits::{Get, GetStorageVersion},
	weights::Weight,
};
use sp_io::hashing::twox_128;

/// Migrate the entire storage of this pallet to a new prefix.
///
/// This new prefix must be the same as the one set in construct_runtime. For safety, use
/// `PalletInfo` to get it, as:
/// `<Runtime as frame_system::Config>::PalletInfo::name::<CollectivePallet>`.
///
/// The migration will look into the storage version in order not to trigger a migration on an up
/// to date storage. Thus the on chain storage version must be less than 4 in order to trigger the
/// migration.
pub fn migrate<T: frame_system::Config, P: GetStorageVersion, N: AsRef<str>>(
	old_pallet_name: N,
	new_pallet_name: N,
) -> Weight {
	if new_pallet_name.as_ref() == old_pallet_name.as_ref() {
		log::info!(
			target: "runtime::collective",
			"New pallet name is equal to the old prefix. No migration needs to be done.",
		);
		return 0
	}

	let on_chain_storage_version = <P as GetStorageVersion>::on_chain_storage_version();
	log::info!(
		target: "runtime::collective",
		"Running migration to v4 for collective with storage version {:?}",
		on_chain_storage_version,
	);

	if on_chain_storage_version < 4 {
		log::info!(target: "runtime::collective", "new prefix: {}", new_pallet_name.as_ref());
		frame_support::storage::migration::move_pallet(
			old_pallet_name.as_ref().as_bytes(),
			new_pallet_name.as_ref().as_bytes(),
		);
		<T as frame_system::Config>::BlockWeights::get().max_block
	} else {
		log::warn!(
			target: "runtime::collective",
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
pub fn pre_migration<T: frame_system::Config, P: GetStorageVersion + 'static, N: AsRef<str>>(
	old: N,
	new: N,
) {
	let new = new.as_ref();
	log::info!("pre-migration collective test with new = {}", new);

	// the next key must exist, and start with the hash of old prefix.
	let next_key = sp_io::storage::next_key(&twox_128(old.as_ref().as_bytes())).unwrap();
	assert!(next_key.starts_with(&twox_128(old.as_ref().as_bytes())));

	let new_prefix = twox_128(new.as_bytes());
	let pallet_version_key = [&new_prefix, &twox_128(b":__PALLET_VERSION__:")[..]].concat();
	let storage_version_key =
		[&new_prefix, &twox_128(frame_support::traits::STORAGE_VERSION_STORAGE_KEY_POSTFIX)[..]]
			.concat();

	// ensure nothing is stored in the new prefix.
	assert!(
		sp_io::storage::next_key(&new_prefix).map_or(
			// either nothing is there
			true,
			// or we ensure that it has no common prefix with twox_128(new),
			// or isn't the pallet version that is already stored using the pallet name
			|next_key| {
				!next_key.starts_with(&new_prefix) ||
					next_key == pallet_version_key ||
					next_key == storage_version_key
			},
		),
		"unexpected next_key({}) = {:?}",
		new,
		sp_core::hexdisplay::HexDisplay::from(
			&sp_io::storage::next_key(&twox_128(new.as_bytes())).unwrap()
		),
	);
	assert!(<P as GetStorageVersion>::on_chain_storage_version() < 4);
}

/// Some checks for after migration. This can be linked to
/// [`frame_support::traits::OnRuntimeUpgrade::post_upgrade`] for further testing.
///
/// Panics if anything goes wrong.
pub fn post_migration<P: GetStorageVersion, N: AsRef<str>>(old_pallet_name: N) {
	log::info!("post-migration collective");

	let old_pallet_name = old_pallet_name.as_ref().as_bytes();
	// Assert that nothing remains at the old prefix
	assert!(sp_io::storage::next_key(&twox_128(old_pallet_name))
		.map_or(true, |next_key| !next_key.starts_with(&twox_128(old_pallet_name))));
	assert_eq!(<P as GetStorageVersion>::on_chain_storage_version(), 4);
}
