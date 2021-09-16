// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
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

//! Storage migrations for the Staking pallet.

use super::*;

pub mod v8 {
	use frame_election_provider_support::SortedListProvider;
	use frame_support::traits::Get;

	use crate::{Config, Nominators, Pallet, StorageVersion, Weight};

	#[cfg(feature = "try-runtime")]
	pub fn pre_migrate<T: Config>() -> Result<(), &'static str> {
		frame_support::ensure!(
			StorageVersion::<T>::get() == crate::Releases::V7_0_0,
			"must upgrade linearly"
		);

		crate::log!(info, "👜 staking bags-list migration passes PRE migrate checks ✅",);
		Ok(())
	}

	/// Migration to sorted [`SortedListProvider`].
	pub fn migrate<T: Config>() -> Weight {
		if StorageVersion::<T>::get() == crate::Releases::V7_0_0 {
			crate::log!(info, "migrating staking to Releases::V8_0_0");

			let migrated = T::SortedListProvider::regenerate(
				Nominators::<T>::iter().map(|(id, _)| id),
				Pallet::<T>::weight_of_fn(),
			);
			debug_assert_eq!(T::SortedListProvider::sanity_check(), Ok(()));

			StorageVersion::<T>::put(crate::Releases::V8_0_0);
			crate::log!(
				info,
				"👜 completed staking migration to Releases::V8_0_0 with {} voters migrated",
				migrated,
			);

			T::BlockWeights::get().max_block
		} else {
			T::DbWeight::get().reads(1)
		}
	}

	#[cfg(feature = "try-runtime")]
	pub fn post_migrate<T: Config>() -> Result<(), &'static str> {
		T::SortedListProvider::sanity_check()
			.map_err(|_| "SortedListProvider is not in a sane state.")?;
		crate::log!(info, "👜 staking bags-list migration passes POST migrate checks ✅",);
		Ok(())
	}
}

pub mod v7 {
	use super::*;

	pub fn pre_migrate<T: Config>() -> Result<(), &'static str> {
		assert!(CounterForValidators::<T>::get().is_zero(), "CounterForValidators already set.");
		assert!(CounterForNominators::<T>::get().is_zero(), "CounterForNominators already set.");
		assert!(StorageVersion::<T>::get() == Releases::V6_0_0);
		Ok(())
	}

	pub fn migrate<T: Config>() -> Weight {
		log!(info, "Migrating staking to Releases::V7_0_0");
		let validator_count = Validators::<T>::iter().count() as u32;
		let nominator_count = Nominators::<T>::iter().count() as u32;

		CounterForValidators::<T>::put(validator_count);
		CounterForNominators::<T>::put(nominator_count);

		StorageVersion::<T>::put(Releases::V7_0_0);
		log!(info, "Completed staking migration to Releases::V7_0_0");

		T::DbWeight::get().reads_writes(validator_count.saturating_add(nominator_count).into(), 2)
	}
}

pub mod v6 {
	use super::*;
	use frame_support::{generate_storage_alias, traits::Get, weights::Weight};

	// NOTE: value type doesn't matter, we just set it to () here.
	generate_storage_alias!(Staking, SnapshotValidators => Value<()>);
	generate_storage_alias!(Staking, SnapshotNominators => Value<()>);
	generate_storage_alias!(Staking, QueuedElected => Value<()>);
	generate_storage_alias!(Staking, QueuedScore => Value<()>);
	generate_storage_alias!(Staking, EraElectionStatus => Value<()>);
	generate_storage_alias!(Staking, IsCurrentSessionFinal => Value<()>);

	/// check to execute prior to migration.
	pub fn pre_migrate<T: Config>() -> Result<(), &'static str> {
		// these may or may not exist.
		log!(info, "SnapshotValidators.exits()? {:?}", SnapshotValidators::exists());
		log!(info, "SnapshotNominators.exits()? {:?}", SnapshotNominators::exists());
		log!(info, "QueuedElected.exits()? {:?}", QueuedElected::exists());
		log!(info, "QueuedScore.exits()? {:?}", QueuedScore::exists());
		// these must exist.
		assert!(IsCurrentSessionFinal::exists(), "IsCurrentSessionFinal storage item not found!");
		assert!(EraElectionStatus::exists(), "EraElectionStatus storage item not found!");
		Ok(())
	}

	/// Migrate storage to v6.
	pub fn migrate<T: Config>() -> Weight {
		log!(info, "Migrating staking to Releases::V6_0_0");

		SnapshotValidators::kill();
		SnapshotNominators::kill();
		QueuedElected::kill();
		QueuedScore::kill();
		EraElectionStatus::kill();
		IsCurrentSessionFinal::kill();

		StorageVersion::<T>::put(Releases::V6_0_0);
		log!(info, "Done.");
		T::DbWeight::get().writes(6 + 1)
	}
}
