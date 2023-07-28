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

//! Migrations to version [`3.0.0`], as denoted by the changelog.

use super::super::LOG_TARGET;
use crate::{Config, Pallet};
use codec::{Decode, Encode, FullCodec};
use frame_support::{
	pallet_prelude::ValueQuery, traits::StorageVersion, weights::Weight, RuntimeDebug, Twox64Concat,
};
use sp_std::prelude::*;

#[derive(Encode, Decode, Clone, Default, RuntimeDebug, PartialEq)]
struct SeatHolder<AccountId, Balance> {
	who: AccountId,
	stake: Balance,
	deposit: Balance,
}

#[derive(Encode, Decode, Clone, Default, RuntimeDebug, PartialEq)]
struct Voter<AccountId, Balance> {
	votes: Vec<AccountId>,
	stake: Balance,
	deposit: Balance,
}

/// Trait to implement to give information about types used for migration
pub trait V2ToV3 {
	/// System config account id
	type AccountId: 'static + FullCodec;

	/// Elections-phragmen currency balance.
	type Balance: 'static + FullCodec + Copy;
}

#[frame_support::storage_alias]
type Candidates<V, T: Config> =
	StorageValue<Pallet<T>, Vec<(<V as V2ToV3>::AccountId, <V as V2ToV3>::Balance)>, ValueQuery>;

#[frame_support::storage_alias]
type Members<V, T: Config> = StorageValue<
	Pallet<T>,
	Vec<SeatHolder<<V as V2ToV3>::AccountId, <V as V2ToV3>::Balance>>,
	ValueQuery,
>;

#[frame_support::storage_alias]
type RunnersUp<V, T: Config> = StorageValue<
	Pallet<T>,
	Vec<SeatHolder<<V as V2ToV3>::AccountId, <V as V2ToV3>::Balance>>,
	ValueQuery,
>;

#[frame_support::storage_alias]
type Voting<V, T: Config> = StorageMap<
	Pallet<T>,
	Twox64Concat,
	<V as V2ToV3>::AccountId,
	Voter<<V as V2ToV3>::AccountId, <V as V2ToV3>::Balance>,
>;

/// Apply all of the migrations from 2 to 3.
///
/// ### Warning
///
/// This code will **ONLY** check that the storage version is less than or equal to 2_0_0.
/// Further check might be needed at the user runtime.
///
/// Be aware that this migration is intended to be used only for the mentioned versions. Use
/// with care and run at your own risk.
pub fn apply<V: V2ToV3, T: Config>(
	old_voter_bond: V::Balance,
	old_candidacy_bond: V::Balance,
) -> Weight {
	let storage_version = StorageVersion::get::<Pallet<T>>();
	log::info!(
		target: LOG_TARGET,
		"Running migration for elections-phragmen with storage version {:?}",
		storage_version,
	);

	if storage_version <= 2 {
		migrate_voters_to_recorded_deposit::<V, T>(old_voter_bond);
		migrate_candidates_to_recorded_deposit::<V, T>(old_candidacy_bond);
		migrate_runners_up_to_recorded_deposit::<V, T>(old_candidacy_bond);
		migrate_members_to_recorded_deposit::<V, T>(old_candidacy_bond);

		StorageVersion::new(3).put::<Pallet<T>>();

		Weight::MAX
	} else {
		log::warn!(
			target: LOG_TARGET,
			"Attempted to apply migration to V3 but failed because storage version is {:?}",
			storage_version,
		);
		Weight::zero()
	}
}

/// Migrate from the old legacy voting bond (fixed) to the new one (per-vote dynamic).
pub fn migrate_voters_to_recorded_deposit<V: V2ToV3, T: Config>(old_deposit: V::Balance) {
	<Voting<V, T>>::translate::<(V::Balance, Vec<V::AccountId>), _>(|_who, (stake, votes)| {
		Some(Voter { votes, stake, deposit: old_deposit })
	});

	log::info!(target: LOG_TARGET, "migrated {} voter accounts.", <Voting<V, T>>::iter().count());
}

/// Migrate all candidates to recorded deposit.
pub fn migrate_candidates_to_recorded_deposit<V: V2ToV3, T: Config>(old_deposit: V::Balance) {
	let _ = <Candidates<V, T>>::translate::<Vec<V::AccountId>, _>(|maybe_old_candidates| {
		maybe_old_candidates.map(|old_candidates| {
			log::info!(target: LOG_TARGET, "migrated {} candidate accounts.", old_candidates.len());
			old_candidates.into_iter().map(|c| (c, old_deposit)).collect::<Vec<_>>()
		})
	});
}

/// Migrate all members to recorded deposit.
pub fn migrate_members_to_recorded_deposit<V: V2ToV3, T: Config>(old_deposit: V::Balance) {
	let _ = <Members<V, T>>::translate::<Vec<(V::AccountId, V::Balance)>, _>(|maybe_old_members| {
		maybe_old_members.map(|old_members| {
			log::info!(target: LOG_TARGET, "migrated {} member accounts.", old_members.len());
			old_members
				.into_iter()
				.map(|(who, stake)| SeatHolder { who, stake, deposit: old_deposit })
				.collect::<Vec<_>>()
		})
	});
}

/// Migrate all runners-up to recorded deposit.
pub fn migrate_runners_up_to_recorded_deposit<V: V2ToV3, T: Config>(old_deposit: V::Balance) {
	let _ = <RunnersUp<V, T>>::translate::<Vec<(V::AccountId, V::Balance)>, _>(
		|maybe_old_runners_up| {
			maybe_old_runners_up.map(|old_runners_up| {
				log::info!(
					target: LOG_TARGET,
					"migrated {} runner-up accounts.",
					old_runners_up.len(),
				);
				old_runners_up
					.into_iter()
					.map(|(who, stake)| SeatHolder { who, stake, deposit: old_deposit })
					.collect::<Vec<_>>()
			})
		},
	);
}
