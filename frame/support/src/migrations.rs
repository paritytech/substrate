// This file is part of Substrate.

// Copyright (C) 2021-2022 Parity Technologies (UK) Ltd.
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

use crate::{
	traits::{GetStorageVersion, PalletInfoAccess},
	weights::{RuntimeDbWeight, Weight},
};

/// Trait used by [`migrate_from_pallet_version_to_storage_version`] to do the actual migration.
pub trait PalletVersionToStorageVersionHelper {
	fn migrate(db_weight: &RuntimeDbWeight) -> Weight;
}

impl<T: GetStorageVersion + PalletInfoAccess> PalletVersionToStorageVersionHelper for T {
	fn migrate(db_weight: &RuntimeDbWeight) -> Weight {
		const PALLET_VERSION_STORAGE_KEY_POSTFIX: &[u8] = b":__PALLET_VERSION__:";

		fn pallet_version_key(name: &str) -> [u8; 32] {
			crate::storage::storage_prefix(name.as_bytes(), PALLET_VERSION_STORAGE_KEY_POSTFIX)
		}

		sp_io::storage::clear(&pallet_version_key(<T as PalletInfoAccess>::name()));

		let version = <T as GetStorageVersion>::current_storage_version();
		version.put::<T>();

		db_weight.writes(2)
	}
}

#[impl_trait_for_tuples::impl_for_tuples(30)]
impl PalletVersionToStorageVersionHelper for T {
	fn migrate(db_weight: &RuntimeDbWeight) -> Weight {
		let mut weight: Weight = 0;

		for_tuples!( #( weight = weight.saturating_add(T::migrate(db_weight)); )* );

		weight
	}
}

/// Migrate from the `PalletVersion` struct to the new
/// [`StorageVersion`](crate::traits::StorageVersion) struct.
///
/// This will remove all `PalletVersion's` from the state and insert the current storage version.
pub fn migrate_from_pallet_version_to_storage_version<
	Pallets: PalletVersionToStorageVersionHelper,
>(
	db_weight: &RuntimeDbWeight,
) -> Weight {
	Pallets::migrate(db_weight)
}
