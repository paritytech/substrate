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
use frame_support::{
	pallet_prelude::StorageVersion,
	traits::{ConstU32, OnRuntimeUpgrade},
	BoundedVec, RuntimeDebug,
};
use sp_core::Get;
use sp_runtime::Saturating;
use sp_std::prelude::*;

#[cfg(feature = "try-runtime")]
use frame_support::traits::GetStorageVersion;

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

pub struct MigrateToV6<T>(sp_std::marker::PhantomData<T>);
impl<T: Config> OnRuntimeUpgrade for MigrateToV6<T> {
	#[cfg(feature = "try-runtime")]
	fn pre_upgrade() -> Result<Vec<u8>, &'static str> {
		let members_count = crate::Members::<T>::get().len();
		log::info!("{} members will be migrated.", members_count);

		let runners_up_count = crate::RunnersUp::<T>::get().len();
		log::info!("{} runners-up will be migrated.", runners_up_count);

		let candidates_count = crate::Candidates::<T>::get().len();
		log::info!("{} candidates will be migrated.", candidates_count);

		Ok((members_count as u32, runners_up_count as u32, candidates_count as u32).encode())
	}

	fn on_runtime_upgrade() -> Weight {
		apply::<T>()
	}

	#[cfg(feature = "try-runtime")]
	fn post_upgrade(state: Vec<u8>) -> Result<(), &'static str> {
		let (old_members_count, old_runners_up_count, old_candidates_count): (u32, u32, u32) =
			Decode::decode(&mut &state[..]).expect("pre_upgrade provides a valid state; qed");

		let post_members_count = crate::Members::<T>::get().len() as u32;
		let post_runners_up_count = crate::RunnersUp::<T>::get().len() as u32;
		let post_candidates_count = crate::Candidates::<T>::get().len() as u32;

		assert_eq!(
			old_members_count.min(T::DesiredMembers::get()),
			post_members_count,
			"The members count should be the same or less."
		);
		assert_eq!(
			old_runners_up_count.min(T::DesiredRunnersUp::get()),
			post_runners_up_count,
			"The runners-up count should be the same or less."
		);
		assert_eq!(
			old_candidates_count.min(T::MaxCandidates::get()),
			post_candidates_count,
			"The runners-up count should be the same or less."
		);

		// new version must be set.
		assert_eq!(Pallet::<T>::on_chain_storage_version(), 6);
		Ok(())
	}
}
