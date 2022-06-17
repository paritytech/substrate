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

//! Various pieces of common functionality.
use super::*;
use frame_support::{
	traits::{Get, GetStorageVersion, PalletInfoAccess, StorageVersion},
	weights::Weight,
};

/// Migrate the pallet storage to v1.
pub fn migrate_to_v1<T: Config<I>, I: 'static, P: GetStorageVersion + PalletInfoAccess>(
) -> frame_support::weights::Weight {
	let on_chain_storage_version = <P as GetStorageVersion>::on_chain_storage_version();
	log::info!(
		target: "runtime::uniques",
		"Running migration storage v1 for uniques with storage version {:?}",
		on_chain_storage_version,
	);

	if on_chain_storage_version < 1 {
		let mut count = 0;
		for (collection, detail) in Collection::<T, I>::iter() {
			CollectionAccount::<T, I>::insert(&detail.owner, &collection, ());
			count += 1;
		}
		StorageVersion::new(1).put::<P>();
		log::info!(
			target: "runtime::uniques",
			"Running migration storage v1 for uniques with storage version {:?} was complete",
			on_chain_storage_version,
		);
		// calculate and return migration weights
		T::DbWeight::get().reads_writes(count as Weight + 1, count as Weight + 1)
	} else {
		log::warn!(
			target: "runtime::uniques",
			"Attempted to apply migration to v1 but failed because storage version is {:?}",
			on_chain_storage_version,
		);
		T::DbWeight::get().reads(1)
	}
}
