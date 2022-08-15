// This file is part of Substrate.

// Copyright (C) 2020-2022 Parity Technologies (UK) Ltd.
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
use frame_election_provider_support::SortedListProvider;
use frame_support::traits::OnRuntimeUpgrade;

pub mod v10 {
	use super::*;
	use frame_support::storage_alias;

	#[storage_alias]
	type EarliestUnappliedSlash<T: Config> = StorageValue<Pallet<T>, EraIndex>;

	/// Apply any pending slashes that where queued.
	///
	/// That means we might slash someone a bit too early, but we will definitely
	/// won't forget to slash them. The cap of 512 is somewhat randomly taken to
	/// prevent us from iterating over an arbitrary large number of keys `on_runtime_upgrade`.
	pub struct MigrateToV10<T>(sp_std::marker::PhantomData<T>);
	impl<T: Config> OnRuntimeUpgrade for MigrateToV10<T> {
		fn on_runtime_upgrade() -> frame_support::weights::Weight {
			if StorageVersion::<T>::get() == Releases::V9_0_0 {
				let pending_slashes = <Pallet<T> as Store>::UnappliedSlashes::iter().take(512);
				for (era, slashes) in pending_slashes {
					for slash in slashes {
						// in the old slashing scheme, the slash era was the key at which we read
						// from `UnappliedSlashes`.
						log!(warn, "prematurely applying a slash ({:?}) for era {:?}", slash, era);
						slashing::apply_slash::<T>(slash, era);
					}
				}

				EarliestUnappliedSlash::<T>::kill();
				StorageVersion::<T>::put(Releases::V10_0_0);

				log!(info, "MigrateToV10 executed successfully");
				T::DbWeight::get().reads_writes(1, 1)
			} else {
				log!(warn, "MigrateToV10 should be removed.");
				T::DbWeight::get().reads(1)
			}
		}
	}
}

pub mod v9 {
	use super::*;

	/// Migration implementation that injects all validators into sorted list.
	///
	/// This is only useful for chains that started their `VoterList` just based on nominators.
	pub struct InjectValidatorsIntoVoterList<T>(sp_std::marker::PhantomData<T>);
	impl<T: Config> OnRuntimeUpgrade for InjectValidatorsIntoVoterList<T> {
		fn on_runtime_upgrade() -> Weight {
			if StorageVersion::<T>::get() == Releases::V8_0_0 {
				let prev_count = T::VoterList::count();
				let weight_of_cached = Pallet::<T>::weight_of_fn();
				for (v, _) in Validators::<T>::iter() {
					let weight = weight_of_cached(&v);
					let _ = T::VoterList::on_insert(v.clone(), weight).map_err(|err| {
						log!(warn, "failed to insert {:?} into VoterList: {:?}", v, err)
					});
				}

				log!(
					info,
					"injected a total of {} new voters, prev count: {} next count: {}, updating to version 9",
					Validators::<T>::count(),
					prev_count,
					T::VoterList::count(),
				);

				StorageVersion::<T>::put(crate::Releases::V9_0_0);
				T::BlockWeights::get().max_block
			} else {
				log!(
					warn,
					"InjectValidatorsIntoVoterList being executed on the wrong storage \
				version, expected Releases::V8_0_0"
				);
				T::DbWeight::get().reads(1)
			}
		}

		#[cfg(feature = "try-runtime")]
		fn pre_upgrade() -> Result<(), &'static str> {
			use frame_support::traits::OnRuntimeUpgradeHelpersExt;
			frame_support::ensure!(
				StorageVersion::<T>::get() == crate::Releases::V8_0_0,
				"must upgrade linearly"
			);

			let prev_count = T::VoterList::count();
			Self::set_temp_storage(prev_count, "prev");
			Ok(())
		}

		#[cfg(feature = "try-runtime")]
		fn post_upgrade() -> Result<(), &'static str> {
			use frame_support::traits::OnRuntimeUpgradeHelpersExt;
			let post_count = T::VoterList::count();
			let prev_count = Self::get_temp_storage::<u32>("prev").unwrap();
			let validators = Validators::<T>::count();
			assert!(post_count == prev_count + validators);

			frame_support::ensure!(
				StorageVersion::<T>::get() == crate::Releases::V9_0_0,
				"must upgrade "
			);
			Ok(())
		}
	}
}

pub mod v8 {
	use crate::{Config, Nominators, Pallet, StorageVersion, Weight};
	use frame_election_provider_support::SortedListProvider;
	use frame_support::traits::Get;

	#[cfg(feature = "try-runtime")]
	pub fn pre_migrate<T: Config>() -> Result<(), &'static str> {
		frame_support::ensure!(
			StorageVersion::<T>::get() == crate::Releases::V7_0_0,
			"must upgrade linearly"
		);

		crate::log!(info, "👜 staking bags-list migration passes PRE migrate checks ✅",);
		Ok(())
	}

	/// Migration to sorted `VoterList`.
	pub fn migrate<T: Config>() -> Weight {
		if StorageVersion::<T>::get() == crate::Releases::V7_0_0 {
			crate::log!(info, "migrating staking to Releases::V8_0_0");

			let migrated = T::VoterList::unsafe_regenerate(
				Nominators::<T>::iter().map(|(id, _)| id),
				Pallet::<T>::weight_of_fn(),
			);
			debug_assert_eq!(T::VoterList::sanity_check(), Ok(()));

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
		T::VoterList::sanity_check().map_err(|_| "VoterList is not in a sane state.")?;
		crate::log!(info, "👜 staking bags-list migration passes POST migrate checks ✅",);
		Ok(())
	}
}

pub mod v7 {
	use super::*;
	use frame_support::storage_alias;

	#[storage_alias]
	type CounterForValidators<T: Config> = StorageValue<Pallet<T>, u32>;
	#[storage_alias]
	type CounterForNominators<T: Config> = StorageValue<Pallet<T>, u32>;

	pub fn pre_migrate<T: Config>() -> Result<(), &'static str> {
		assert!(
			CounterForValidators::<T>::get().unwrap().is_zero(),
			"CounterForValidators already set."
		);
		assert!(
			CounterForNominators::<T>::get().unwrap().is_zero(),
			"CounterForNominators already set."
		);
		assert!(Validators::<T>::count().is_zero(), "Validators already set.");
		assert!(Nominators::<T>::count().is_zero(), "Nominators already set.");
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
	use frame_support::{storage_alias, traits::Get, weights::Weight};

	// NOTE: value type doesn't matter, we just set it to () here.
	#[storage_alias]
	type SnapshotValidators<T: Config> = StorageValue<Pallet<T>, ()>;
	#[storage_alias]
	type SnapshotNominators<T: Config> = StorageValue<Pallet<T>, ()>;
	#[storage_alias]
	type QueuedElected<T: Config> = StorageValue<Pallet<T>, ()>;
	#[storage_alias]
	type QueuedScore<T: Config> = StorageValue<Pallet<T>, ()>;
	#[storage_alias]
	type EraElectionStatus<T: Config> = StorageValue<Pallet<T>, ()>;
	#[storage_alias]
	type IsCurrentSessionFinal<T: Config> = StorageValue<Pallet<T>, ()>;

	/// check to execute prior to migration.
	pub fn pre_migrate<T: Config>() -> Result<(), &'static str> {
		// these may or may not exist.
		log!(info, "SnapshotValidators.exits()? {:?}", SnapshotValidators::<T>::exists());
		log!(info, "SnapshotNominators.exits()? {:?}", SnapshotNominators::<T>::exists());
		log!(info, "QueuedElected.exits()? {:?}", QueuedElected::<T>::exists());
		log!(info, "QueuedScore.exits()? {:?}", QueuedScore::<T>::exists());
		// these must exist.
		assert!(
			IsCurrentSessionFinal::<T>::exists(),
			"IsCurrentSessionFinal storage item not found!"
		);
		assert!(EraElectionStatus::<T>::exists(), "EraElectionStatus storage item not found!");
		Ok(())
	}

	/// Migrate storage to v6.
	pub fn migrate<T: Config>() -> Weight {
		log!(info, "Migrating staking to Releases::V6_0_0");

		SnapshotValidators::<T>::kill();
		SnapshotNominators::<T>::kill();
		QueuedElected::<T>::kill();
		QueuedScore::<T>::kill();
		EraElectionStatus::<T>::kill();
		IsCurrentSessionFinal::<T>::kill();

		StorageVersion::<T>::put(Releases::V6_0_0);
		log!(info, "Done.");
		T::DbWeight::get().writes(6 + 1)
	}
}
