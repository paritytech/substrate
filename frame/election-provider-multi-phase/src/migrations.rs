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

//! Storage migrations for the Election Provider Multi-phase pallet.
//!
//! The Election Provider Multi-phase pallet provides the necessary functionality
//! for running multi-phase elections in Substrate based blockchains. This module
//! contains storage migration implementations to transition the storage from
//! a previous version to the current one during runtime upgrades.
//!
//! Each runtime upgrade may introduce changes to the storage layout, and to ensure
//! smooth upgrades, a migration strategy is used.

/// This module contains the migration logic for transitioning the storage from version 0 to version 1.
///
///
/// The `MigrateToV1` struct implements the `OnRuntimeUpgrade` trait, which is called
/// during runtime upgrades. When the runtime is upgraded and this migration is executed,
/// it checks the current and on-chain storage versions to determine if the migration is
/// needed.
///
/// If the current storage version is 1 and the on-chain version is 0, the migration will
/// proceed. During migration, the module checks if the `SignedSubmissionIndices` storage
/// item exists. If it does, the module migrates its data to the new storage format.
///
/// The migration logic performs the following steps:
/// - Reads the existing `SignedSubmissionIndices` data from storage.
/// - Maps the data to the new format, including the current block number.
/// - Stores the new data in the storage with the updated format.
/// - Updates the current storage version to 1.
///
/// If `SignedSubmissionIndices` does not exist, the migration proceeds without performing
/// any changes, and only updates the storage version.
///
/// Developers should implement specific migration steps for each version change if needed.
/// The `OnRuntimeUpgrade` trait allows the module to perform complex migrations efficiently
/// and transparently to the blockchain's users.
pub mod v1 {
	use frame_support::{
		storage::unhashed,
		traits::{Defensive, GetStorageVersion, OnRuntimeUpgrade},
		BoundedVec,
	};
	use sp_std::collections::btree_map::BTreeMap;

	use crate::*;
	
	/// The migration struct to perform storage updates from storage V0 to V1.
	pub struct MigrateToV1<T>(sp_std::marker::PhantomData<T>);
	impl<T: Config> OnRuntimeUpgrade for MigrateToV1<T> {
		fn on_runtime_upgrade() -> Weight {
			let current = Pallet::<T>::current_storage_version();
			let onchain = Pallet::<T>::on_chain_storage_version();

			log!(
				info,
				"Running migration with current storage version {:?} / onchain {:?}",
				current,
				onchain
			);

			if current == 1 && onchain == 0 {
				if SignedSubmissionIndices::<T>::exists() {
					// This needs to be tested at a both a block height where this value exists, and
					// when it doesn't.
					let now = frame_system::Pallet::<T>::block_number();
					let map = unhashed::get::<BTreeMap<ElectionScore, u32>>(
						&SignedSubmissionIndices::<T>::hashed_key(),
					)
					.defensive_unwrap_or_default();
					let vector = map
						.into_iter()
						.map(|(score, index)| (score, now, index))
						.collect::<Vec<_>>();

					log!(
						debug,
						"{:?} SignedSubmissionIndices read from storage (max: {:?})",
						vector.len(),
						T::SignedMaxSubmissions::get()
					);

					// defensive-only, assuming a constant `SignedMaxSubmissions`.
					let bounded = BoundedVec::<_, _>::truncate_from(vector);
					SignedSubmissionIndices::<T>::put(bounded);

					log!(info, "SignedSubmissionIndices existed and got migrated");
				} else {
					log!(info, "SignedSubmissionIndices did NOT exist.");
				}

				current.put::<Pallet<T>>();
				T::DbWeight::get().reads_writes(2, 1)
			} else {
				log!(info, "Migration did not execute. This probably should be removed");
				T::DbWeight::get().reads(1)
			}
		}
	}
}
