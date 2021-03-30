// This file is part of Substrate.

// Copyright (C) 2019-2020 Parity Technologies (UK) Ltd.
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

//! Migrations to version [`4.0.0`], as denoted by the changelog.

use frame_support::{
	weights::Weight,
	traits::{GetPalletVersion, PalletVersion, Get},
};

/// The old prefix.
pub const OLD_PREFIX: &[u8] = b"PhragmenElection";

/// Migrate the entire storage of this pallet to a new prefix.
///
/// This new prefix must be the same as the one set in construct_runtime. For safety, use
/// `PalletInfo` to get it, as:
/// `<Runtime as frame_system::Config>::PalletInfo::name::<ElectionsPhragmenPallet>`.
///
/// The old storage prefix, `PhragmenElection` is hardcoded in the migration code.
pub fn migrate<
	T: frame_system::Config,
	P: GetPalletVersion,
	N: AsRef<str>,
>(new_pallet_name: N) -> Weight {
	let maybe_storage_version = <P as GetPalletVersion>::storage_version();
	log::info!(
		target: "runtime::elections-phragmen",
		"Running migration to v4 for elections-phragmen with storage version {:?}",
		maybe_storage_version,
	);

	match maybe_storage_version {
		Some(storage_version) if storage_version <= PalletVersion::new(3, 0, 0) => {
			log::info!("new prefix: {}", new_pallet_name.as_ref());
			frame_support::storage::migration::move_pallet(
				OLD_PREFIX,
				new_pallet_name.as_ref().as_bytes(),
			);
			<T as frame_system::Config>::BlockWeights::get().max_block
		}
		_ => {
			log::warn!(
				target: "runtime::elections-phragmen",
				"Attempted to apply migration to v4 but failed because storage version is {:?}",
				maybe_storage_version,
			);
			0
		},
	}
}

/// Some checks prior to migration. This can be linked to
/// [`frame_support::traits::OnRuntimeUpgrade::pre_upgrade`] for further testing.
///
/// Panics if anything goes wrong.
pub fn pre_migration<P: GetPalletVersion, N: AsRef<str>>(new: N) {
	// ensure some stuff exist in the old prefix.
	assert!(sp_io::storage::next_key(OLD_PREFIX).is_some());
	// ensure nothing is stored in the new prefix.
	assert!(sp_io::storage::next_key(new.as_ref().as_bytes()).is_none());
	// ensure storage version is 3.
	assert!(<P as GetPalletVersion>::storage_version().unwrap().major == 3);
}
