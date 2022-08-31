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

//! Migrations to version [`3.0.0`], as denoted by the changelog.

use codec::{Encode, Decode, FullCodec};
use sp_std::prelude::*;
use frame_support::{
	RuntimeDebug, weights::Weight, Twox64Concat,
	storage::types::{StorageMap, StorageValue},
	traits::{GetPalletVersion, PalletVersion},
};

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
	/// elections-phragmen module, used to check storage version.
	type Module: GetPalletVersion;

	/// System config account id
	type AccountId: 'static + FullCodec;

	/// Elections-phragmen currency balance.
	type Balance: 'static + FullCodec + Copy;
}

struct __Candidates;
impl frame_support::traits::StorageInstance for __Candidates {
	fn pallet_prefix() -> &'static str { "PhragmenElection" }
	const STORAGE_PREFIX: &'static str = "Candidates";
}

#[allow(type_alias_bounds)]
type Candidates<T: V2ToV3> = StorageValue<__Candidates, Vec<(T::AccountId, T::Balance)>>;

struct __Members;
impl frame_support::traits::StorageInstance for __Members {
	fn pallet_prefix() -> &'static str { "PhragmenElection" }
	const STORAGE_PREFIX: &'static str = "Members";
}
#[allow(type_alias_bounds)]
type Members<T: V2ToV3> = StorageValue<__Members, Vec<SeatHolder<T::AccountId, T::Balance>>>;

struct __RunnersUp;
impl frame_support::traits::StorageInstance for __RunnersUp {
	fn pallet_prefix() -> &'static str { "PhragmenElection" }
	const STORAGE_PREFIX: &'static str = "RunnersUp";
}
#[allow(type_alias_bounds)]
type RunnersUp<T: V2ToV3> = StorageValue<__RunnersUp, Vec<SeatHolder<T::AccountId, T::Balance>>>;

struct __Voting;
impl frame_support::traits::StorageInstance for __Voting {
	fn pallet_prefix() -> &'static str { "PhragmenElection" }
	const STORAGE_PREFIX: &'static str = "Voting";
}
#[allow(type_alias_bounds)]
type Voting<T: V2ToV3> = StorageMap<__Voting, Twox64Concat, T::AccountId, Voter<T::AccountId, T::Balance>>;

/// Apply all of the migrations from 2_0_0 to 3_0_0.
///
/// ### Warning
///
/// This code will **ONLY** check that the storage version is less than or equal to 2_0_0.
/// Further check might be needed at the user runtime.
///
/// Be aware that this migration is intended to be used only for the mentioned versions. Use
/// with care and run at your own risk.
pub fn apply<T: V2ToV3>(old_voter_bond: T::Balance, old_candidacy_bond: T::Balance) -> Weight {
	let maybe_storage_version = <T::Module as GetPalletVersion>::storage_version();
	frame_support::debug::info!(
		"Running migration for elections-phragmen with storage version {:?}",
		maybe_storage_version
	);
	match maybe_storage_version {
		Some(storage_version) if storage_version <= PalletVersion::new(2, 0, 0) => {
			migrate_voters_to_recorded_deposit::<T>(old_voter_bond);
			migrate_candidates_to_recorded_deposit::<T>(old_candidacy_bond);
			migrate_runners_up_to_recorded_deposit::<T>(old_candidacy_bond);
			migrate_members_to_recorded_deposit::<T>(old_candidacy_bond);
			Weight::max_value()
		}
		_ => {
			frame_support::debug::warn!(
				"Attempted to apply migration to V3 but failed because storage version is {:?}",
				maybe_storage_version
			);
			0
		},
	}
}

/// Migrate from the old legacy voting bond (fixed) to the new one (per-vote dynamic).
pub fn migrate_voters_to_recorded_deposit<T: V2ToV3>(old_deposit: T::Balance) {
	<Voting<T>>::translate::<(T::Balance, Vec<T::AccountId>), _>(
		|_who, (stake, votes)| {
			Some(Voter {
				votes,
				stake,
				deposit: old_deposit,
			})
		},
	);

	frame_support::debug::info!(
		"migrated {} voter accounts.",
		<Voting<T>>::iter().count(),
	);
}

/// Migrate all candidates to recorded deposit.
pub fn migrate_candidates_to_recorded_deposit<T: V2ToV3>(old_deposit: T::Balance) {
	let _ = <Candidates<T>>::translate::<Vec<T::AccountId>, _>(
		|maybe_old_candidates| {
			maybe_old_candidates.map(|old_candidates| {
				frame_support::debug::info!(
					"migrated {} candidate accounts.",
					old_candidates.len()
				);
				old_candidates
					.into_iter()
					.map(|c| (c, old_deposit))
					.collect::<Vec<_>>()
			})
		},
	);
}

/// Migrate all members to recorded deposit.
pub fn migrate_members_to_recorded_deposit<T: V2ToV3>(old_deposit: T::Balance) {
	let _ = <Members<T>>::translate::<Vec<(T::AccountId, T::Balance)>, _>(
		|maybe_old_members| {
			maybe_old_members.map(|old_members| {
				frame_support::debug::info!("migrated {} member accounts.", old_members.len());
				old_members
					.into_iter()
					.map(|(who, stake)| SeatHolder {
						who,
						stake,
						deposit: old_deposit,
					})
					.collect::<Vec<_>>()
			})
		},
	);
}

/// Migrate all runners-up to recorded deposit.
pub fn migrate_runners_up_to_recorded_deposit<T: V2ToV3>(old_deposit: T::Balance) {
	let _ = <RunnersUp<T>>::translate::<Vec<(T::AccountId, T::Balance)>, _>(
		|maybe_old_runners_up| {
			maybe_old_runners_up.map(|old_runners_up| {
				frame_support::debug::info!(
					"migrated {} runner-up accounts.",
					old_runners_up.len()
				);
				old_runners_up
					.into_iter()
					.map(|(who, stake)| SeatHolder {
						who,
						stake,
						deposit: old_deposit,
					})
					.collect::<Vec<_>>()
			})
		},
	);
}
