// Copyright 2019-2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Storage migrations for srml-staking.

/// Indicator of a version of a storage layout.
pub type VersionNumber = u32;

// the current expected version of the storage
pub const CURRENT_VERSION: VersionNumber = 2;

#[cfg(any(test, feature = "migrate"))]
mod inner {
	use crate::{
		Store, Module, Trait, EraRewardPoints, SessionInterface, BalanceOf, StakingLedger,
		StakingLedgerV1,
	};
	use frame_support::{StorageLinkedMap, StorageValue, StorageMap, StorageDoubleMap, StoragePrefixedMap};
	use sp_std::vec::Vec;
	use super::{CURRENT_VERSION, VersionNumber};
	use sp_runtime::traits::Zero;

	// the minimum supported version of the migration logic.
	const MIN_SUPPORTED_VERSION: VersionNumber = 0;

	// migrate storage from v0 to v1.
	//
	// this upgrades the `Nominators` linked_map value type from `Vec<T::AccountId>` to
	// `Option<Nominations<T::AccountId>>`
	pub fn to_v1<T: Trait>(version: &mut VersionNumber) {
		if *version != 0 { return }
		*version += 1;

		let now = <Module<T>>::current_era();
		let res = <Module<T> as Store>::Nominators::translate::<T::AccountId, Vec<T::AccountId>, _, _>(
			|key| key,
			|targets| crate::Nominations {
				targets,
				submitted_in: now,
				suppressed: false,
			},
		);

		if let Err(e) = res {
			frame_support::print("Encountered error in migration of Staking::Nominators map.");
			if e.is_none() {
				frame_support::print("Staking::Nominators map reinitialized");
			}
		}

		frame_support::print("Finished migrating Staking storage to v1.");
	}


	pub fn from_v1_to_v2<T: Trait>(version: &mut VersionNumber) {
		if *version != 1 { return }
		*version += 1;

		// Fill new storages.

		// Do ActiveEra
		let current_era_start_index = <Module<T> as Store>::CurrentEraStartSessionIndex::get();
		let current_era = <Module<T> as Store>::CurrentEra::get();
		let active_era = if current_era_start_index > T::SessionInterface::current_index() {
			current_era - 1
		} else {
			current_era
		};
		<Module<T> as Store>::ActiveEra::put(active_era);

		// Do ErasStakers, ErasValidatorPrefs and ErasTotalStake
		let old_current_elected = <Module<T> as Store>::CurrentElected::get();
		let mut current_total_stake = <BalanceOf<T>>::zero();
		for validator in &old_current_elected {
			let exposure = <Module<T> as Store>::Stakers::get(validator);
			current_total_stake += exposure.total;
			let pref = <Module<T> as Store>::Validators::get(validator);
			<Module<T> as Store>::ErasStakers::insert(current_era, validator, exposure);
			<Module<T> as Store>::ErasValidatorPrefs::insert(current_era, validator, pref);
		}
		<Module<T> as Store>::ErasTotalStake::insert(current_era, current_total_stake);
		let mut active_total_stake = <BalanceOf<T>>::zero();
		for validator in &T::SessionInterface::validators() {
			let exposure = <Module<T> as Store>::Stakers::get(validator);
			active_total_stake += exposure.total;
			let pref = <Module<T> as Store>::Validators::get(validator);
			<Module<T> as Store>::ErasStakers::insert(active_era, validator, exposure);
			<Module<T> as Store>::ErasValidatorPrefs::insert(active_era, validator, pref);
		}
		<Module<T> as Store>::ErasTotalStake::insert(active_era, active_total_stake);

		// Do ErasRewardPoints
		let points = <Module<T> as Store>::CurrentEraPointsEarned::get();
		<Module<T> as Store>::ErasRewardPoints::insert(active_era, EraRewardPoints {
			total: points.total,
			individual: old_current_elected.iter().cloned().zip(points.individual.iter().cloned()).collect(),
		});

		// Do ActiveEraStart
		<Module<T> as Store>::ActiveEraStart::put(<Module<T> as Store>::CurrentEraStart::get());

		// Do StakingLedger
		let res = <Module<T> as Store>::Ledger::translate_values(
			|old: StakingLedgerV1<T::AccountId, BalanceOf<T>>| StakingLedger {
				stash: old.stash,
				total: old.total,
				active: old.active,
				unlocking: old.unlocking,
				next_reward: 0,
			}
		);
		if let Err(e) = res {
			frame_support::print("Encountered error in migration of Staking::Ledger map.");
			frame_support::print("The number of removed key/value is:");
			frame_support::print(e);
		}


		// Kill old storages
		<Module<T> as Store>::SlotStake::kill();
		<Module<T> as Store>::CurrentElected::kill();
		<Module<T> as Store>::CurrentEraStart::kill();
		<Module<T> as Store>::CurrentEraStartSessionIndex::kill();
		<Module<T> as Store>::CurrentEraPointsEarned::kill();

		frame_support::print("Finished migrating Staking storage to v2.");
	}

	pub(super) fn perform_migrations<T: Trait>() {
		<Module<T> as Store>::StorageVersion::mutate(|version| {
			if *version < MIN_SUPPORTED_VERSION {
				frame_support::print("Cannot migrate staking storage because version is less than\
					minimum.");
				frame_support::print(*version);
				return
			}

			if *version == CURRENT_VERSION { return }

			to_v1::<T>(version);
			from_v1_to_v2::<T>(version);
		});
	}
}

#[cfg(not(any(test, feature = "migrate")))]
mod inner {
	pub(super) fn perform_migrations<T>() { }
}

/// Perform all necessary storage migrations to get storage into the expected stsate for current
/// logic. No-op if fully upgraded.
pub(crate) fn perform_migrations<T: crate::Trait>() {
	inner::perform_migrations::<T>();
}
