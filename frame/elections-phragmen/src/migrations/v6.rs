// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

use crate::{BalanceOf, Config, Pallet, SeatHolder, Weight, MAXIMUM_VOTE};
use codec::{Decode, Encode};
use frame_support::{pallet_prelude::StorageVersion, traits::ConstU32, BoundedVec, RuntimeDebug};
use sp_core::Get;
use sp_runtime::Saturating;
use sp_std::prelude::*;

#[derive(Encode, Decode, Clone, Default, RuntimeDebug, PartialEq)]
struct DeprecatedVoter<AccountId, Balance> {
	votes: Vec<AccountId>,
	stake: Balance,
	deposit: Balance,
}

pub fn apply<T: Config>() -> Weight {
	let storage_version = StorageVersion::get::<Pallet<T>>();
	log::info!(
		target: "runtime::elections-phragmen",
		"Running migration for elections-phragmen with storage version {:?}",
		storage_version,
	);

	if storage_version <= 5 {
		let weight = migrate_voting::<T>();
		weight.saturating_add(migrate_members::<T>());
		weight.saturating_add(migrate_runners_up::<T>());
		weight.saturating_add(migrate_candidates::<T>());

		StorageVersion::new(6).put::<Pallet<T>>();

		weight
	} else {
		log::warn!(
			target: "runtime::elections-phragmen",
			"Attempted to apply migration to V6 but failed because storage version is {:?}",
			storage_version,
		);
		Weight::zero()
	}
}

pub fn migrate_voting<T: Config>() -> Weight {
	let mut translated = 0u64;
	crate::Voting::<T>::translate::<DeprecatedVoter<T::AccountId, BalanceOf<T>>, _>(|_, voter| {
		translated.saturating_inc();
		let bounded_votes: BoundedVec<T::AccountId, ConstU32<{ MAXIMUM_VOTE as u32 }>> =
			voter.votes.try_into().unwrap();
		Some(crate::Voter { votes: bounded_votes, stake: voter.stake, deposit: voter.deposit })
	});
	T::DbWeight::get().reads_writes(translated, translated)
}

pub fn migrate_members<T: Config>() -> Weight {
	let mut translated = 0u64;
	let _ = crate::Members::<T>::translate::<Vec<SeatHolder<T::AccountId, BalanceOf<T>>>, _>(
		|maybe_members| {
			translated.saturating_inc();
			maybe_members.map(|members| {
				let bounded_members: BoundedVec<
					SeatHolder<T::AccountId, BalanceOf<T>>,
					T::DesiredMembers,
				> = members.try_into().unwrap();
				bounded_members
			})
		},
	);
	T::DbWeight::get().reads_writes(translated, translated)
}

pub fn migrate_runners_up<T: Config>() -> Weight {
	let mut translated = 0u64;
	let _ = crate::RunnersUp::<T>::translate::<Vec<SeatHolder<T::AccountId, BalanceOf<T>>>, _>(
		|maybe_runners_up| {
			translated.saturating_inc();
			maybe_runners_up.map(|runners_up| {
				let bounded_runners_up: BoundedVec<
					SeatHolder<T::AccountId, BalanceOf<T>>,
					T::DesiredRunnersUp,
				> = runners_up.try_into().unwrap();
				bounded_runners_up
			})
		},
	);
	T::DbWeight::get().reads_writes(translated, translated)
}

pub fn migrate_candidates<T: Config>() -> Weight {
	let mut translated = 0u64;
	let _ = crate::Candidates::<T>::translate::<Vec<(T::AccountId, BalanceOf<T>)>, _>(
		|maybe_candidates| {
			translated.saturating_inc();
			maybe_candidates.map(|candidates| {
				let bounded_candidates: BoundedVec<(T::AccountId, BalanceOf<T>), T::MaxCandidates> =
					candidates.try_into().unwrap();
				bounded_candidates
			})
		},
	);
	T::DbWeight::get().reads_writes(translated, translated)
}

pub fn post_migration<T: Config>() {
	log::info!("post-migration elections-phragmen");

	assert_eq!(StorageVersion::get::<crate::Pallet<T>>(), 6);
}
