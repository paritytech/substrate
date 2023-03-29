// This file is part of Substrate.

// Copyright (C) 2023 Parity Technologies (UK) Ltd.
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

#![cfg_attr(not(feature = "std"), no_std)]

use codec::Decode;
use frame_election_provider_support::SortedListProvider;
use frame_support::{
	pallet_prelude::{Get, Weight},
	sp_io, storage,
};
pub use pallet::*;

use pallet_stake_tracker::{ApprovalStake, BalanceOf};
use pallet_staking::{Nominations, TemporaryMigrationLock, Validators};
use sp_runtime::Saturating;
use sp_staking::StakingInterface;
use sp_std::collections::btree_map::BTreeMap;

#[cfg(feature = "try-runtime")]
use sp_std::vec::Vec;

pub(crate) const LOG_TARGET: &str = "runtime::stake-tracker-initializer";

#[macro_export]
macro_rules! log {
	($level:tt, $patter:expr $(, $values:expr)* $(,)?) => {
		log::$level!(
			target: crate::LOG_TARGET,
			concat!("💸🧐", $patter), $(, $values)*
		)
	};
}

#[frame_support::pallet]
pub mod pallet {
	use crate::*;
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::BlockNumberFor;

	#[pallet::pallet]
	pub struct Pallet<T>(_);

	#[pallet::config]
	pub trait Config:
		frame_system::Config + pallet_staking::Config + pallet_stake_tracker::Config
	{
	}

	#[derive(
		Encode, Decode, CloneNoBound, PartialEqNoBound, EqNoBound, TypeInfo, MaxEncodedLen, Default,
	)]
	pub struct MigrationState {
		pub last_key: BoundedVec<u8, ConstU32<32>>,
		pub prefix: BoundedVec<u8, ConstU32<32>>,
		pub done: bool,
	}

	#[pallet::storage]
	pub(crate) type MigrationV1StateNominators<T: Config> =
		StorageValue<_, MigrationState, OptionQuery>;

	#[pallet::storage]
	pub(crate) type MigrationV1StateValidators<T: Config> =
		StorageValue<_, MigrationState, OptionQuery>;

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
		fn on_runtime_upgrade() -> Weight {
			// We have to set this manually, because we need this migration to happen in order for
			// the pallet to get all the data from staking-pallet.
			let current = StorageVersion::new(1);
			let onchain = pallet_stake_tracker::Pallet::<T>::on_chain_storage_version();

			if current == 1 && onchain == 0 {
				// This lets on_initialize code know to proceed with the migration. And pauses
				// Staking extrinsics.
				TemporaryMigrationLock::<T>::put(true);
				T::DbWeight::get().writes(1)
			} else {
				log!(warn, "This migration is being executed on a wrong storage version, probably needs to be removed.");
				T::DbWeight::get().reads(1)
			}
		}

		fn on_initialize(_n: BlockNumberFor<T>) -> Weight {
			// Abort if the lock does not exist, it means we're done migrating.
			if !TemporaryMigrationLock::<T>::exists() {
				return T::DbWeight::get().reads(1)
			}
			let max_weight = T::BlockWeights::get().max_block;

			let (approval_stakes, leftover_weight, is_finished) = Self::build_approval_stakes();

			for (who, approval_stake) in approval_stakes {
				if let Some(stake) = ApprovalStake::<T>::get(&who) {
					ApprovalStake::<T>::set(&who, Some(stake.saturating_add(approval_stake)));
				} else {
					ApprovalStake::<T>::insert(&who, approval_stake)
				}
			}

			// If there is enough weight - do this in one go. If there's max_weight, meaning
			// that we are finished with approval_stake aggregation  - do it in one go as well.
			if is_finished &&
				leftover_weight
					.all_gte(Weight::from_parts((Validators::<T>::count() * 2) as u64, 0)) ||
				leftover_weight == max_weight
			{
				for (key, value) in ApprovalStake::<T>::iter() {
					if Validators::<T>::contains_key(&key) {
						<T as pallet_stake_tracker::Config>::TargetList::on_insert(key, value)
							.unwrap();
					}
				}
				MigrationV1StateValidators::<T>::kill();
				MigrationV1StateNominators::<T>::kill();
			}

			TemporaryMigrationLock::<T>::kill();
			let current = StorageVersion::new(1);
			current.put::<pallet_stake_tracker::Pallet<T>>();
			max_weight
		}

		#[cfg(feature = "try-runtime")]
		// This isn't very useful as we aren't doing the actual migration OnRuntimeUpgrade, only
		// setting the flag for on_initialize to continue.
		fn pre_upgrade() -> Result<Vec<u8>, &'static str> {
			ensure!(Pallet::<T>::current_storage_version() == 0, "must upgrade linearly");
			ensure!(
				<T as pallet_stake_tracker::Config>::TargetList::count() == 0,
				"must be run on an empty TargetList instance"
			);
			Ok(Vec::new())
		}

		#[cfg(feature = "try-runtime")]
		// Same here, we can't really assume anything here as we aren't sure how many blocks it
		// takes for the migration to happen, assuming it's more than one already breaks most of the
		// promises we could verify here.
		fn post_upgrade(_state: Vec<u8>) -> Result<(), &'static str> {
			Ok(())
		}
	}
}

impl<T: Config> Pallet<T> {
	// Reimplemented to avoid leaking this from stake-tracker.
	pub(crate) fn active_stake_of(who: &T::AccountId) -> BalanceOf<T> {
		<T as pallet_stake_tracker::Config>::Staking::stake(&who)
			.map(|s| s.active)
			.unwrap_or_default()
	}

	fn nominator_state() -> MigrationState {
		MigrationV1StateNominators::<T>::get().unwrap_or(MigrationState {
			last_key: <pallet_staking::Nominators<T>>::map_storage_final_prefix()
				.try_into()
				.unwrap(),
			prefix: <pallet_staking::Nominators<T>>::map_storage_final_prefix().try_into().unwrap(),
			done: false,
		})
	}

	fn set_nominator_state(state: MigrationState) {
		MigrationV1StateNominators::<T>::set(Some(state))
	}

	fn validator_state() -> MigrationState {
		MigrationV1StateValidators::<T>::get().unwrap_or(MigrationState {
			last_key: <pallet_staking::Nominators<T>>::map_storage_final_prefix()
				.try_into()
				.unwrap(),
			prefix: <pallet_staking::Nominators<T>>::map_storage_final_prefix().try_into().unwrap(),
			done: false,
		})
	}

	fn set_validator_state(state: MigrationState) {
		MigrationV1StateValidators::<T>::set(Some(state))
	}

	// Build approval stakes based on available weight.
	pub(crate) fn build_approval_stakes() -> (BTreeMap<T::AccountId, BalanceOf<T>>, Weight, bool) {
		let mut approval_stakes = BTreeMap::<T::AccountId, BalanceOf<T>>::new();
		let mut leftover_weight = T::BlockWeights::get().max_block;

		let mut nominator_state = Self::nominator_state();

		if !nominator_state.done {
			// each iteration = 2 reads + 2 reads = 4 reads
			while let Some(next_key) = sp_io::storage::next_key(nominator_state.last_key.as_ref()) {
				if !next_key.starts_with(&nominator_state.prefix) {
					// Nothing else to iterate. Save the state and bail.
					nominator_state.done = true;
					Self::set_nominator_state(nominator_state.clone());
					break
				}

				// Should be safe due to the check above.
				let mut account_raw =
					next_key.strip_prefix(nominator_state.prefix.as_slice()).unwrap();
				let who = T::AccountId::decode(&mut account_raw).unwrap();

				match storage::unhashed::get::<Nominations<T>>(&next_key) {
					Some(nominations) => {
						let stake = Self::active_stake_of(&who);

						for target in nominations.targets {
							let current = approval_stakes.entry(target).or_default();
							*current = current.saturating_add(stake);
						}

						nominator_state.last_key = next_key.try_into().unwrap();
						let approval_stake_count = approval_stakes.len() as u64;
						leftover_weight = leftover_weight
							.saturating_sub(T::DbWeight::get().reads(4))
							.saturating_sub(
								T::DbWeight::get()
									.reads_writes(approval_stake_count, approval_stake_count),
							);

						if leftover_weight.all_lte(Weight::default()) {
							// We ran out of weight, also taking into account writing
							// approval_stakes here. Save the state and bail.
							Self::set_nominator_state(nominator_state.clone());

							return (approval_stakes, leftover_weight, false)
						}
					},
					None => {
						log!(warn, "an un-decodable nomination detected.");
						break
					},
				};
			}
		}

		let mut validator_state = Self::validator_state();

		if !validator_state.done {
			// each iteration = 1 read + 2 reads = 3 reads
			while let Some(next_key) = sp_io::storage::next_key(validator_state.last_key.as_ref()) {
				if !next_key.starts_with(&validator_state.prefix) {
					// Nothing else to iterate. Save the state and bail.
					validator_state.done = true;
					Self::set_validator_state(validator_state.clone());
					break
				}

				// Should be safe due to the check above.
				let mut account_raw =
					next_key.strip_prefix(validator_state.prefix.as_slice()).unwrap();

				let who = T::AccountId::decode(&mut account_raw).unwrap();
				let stake = Self::active_stake_of(&who);
				let current = approval_stakes.entry(who).or_default();
				*current = current.saturating_add(stake);
				validator_state.last_key = next_key.try_into().unwrap();

				let approval_stake_count = approval_stakes.len() as u64;
				leftover_weight =
					leftover_weight.saturating_sub(T::DbWeight::get().reads(3)).saturating_sub(
						T::DbWeight::get().reads_writes(approval_stake_count, approval_stake_count),
					);

				if leftover_weight.all_lte(Weight::default()) {
					// We ran out of weight, also taking into account writing
					// approval_stakes here. Save the state and bail.
					Self::set_validator_state(validator_state.clone());

					return (approval_stakes, leftover_weight, false)
				}
			}
		}

		(approval_stakes, leftover_weight, true)
	}
}
