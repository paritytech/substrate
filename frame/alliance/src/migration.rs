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

use crate::{Config, Pallet, Weight, LOG_TARGET};
use frame_support::{pallet_prelude::*, storage::migration, traits::OnRuntimeUpgrade};
use log;

/// The current storage version.
pub const STORAGE_VERSION: StorageVersion = StorageVersion::new(2);

/// Wrapper for all migrations of this pallet.
pub fn migrate<T: Config<I>, I: 'static>() -> Weight {
	let onchain_version = Pallet::<T, I>::on_chain_storage_version();
	let mut weight: Weight = Weight::zero();

	if onchain_version < 1 {
		weight = weight.saturating_add(v0_to_v1::migrate::<T, I>());
	}

	if onchain_version < 2 {
		weight = weight.saturating_add(v1_to_v2::migrate::<T, I>());
	}

	STORAGE_VERSION.put::<Pallet<T, I>>();
	weight = weight.saturating_add(T::DbWeight::get().writes(1));

	weight
}

/// Implements `OnRuntimeUpgrade` trait.
pub struct Migration<T, I = ()>(PhantomData<(T, I)>);

impl<T: Config<I>, I: 'static> OnRuntimeUpgrade for Migration<T, I> {
	fn on_runtime_upgrade() -> Weight {
		migrate::<T, I>()
	}
}

/// v0_to_v1: `UpForKicking` is replaced by a retirement period.
mod v0_to_v1 {
	use super::*;

	pub fn migrate<T: Config<I>, I: 'static>() -> Weight {
		log::info!(target: LOG_TARGET, "Running migration v0_to_v1.");

		let res = migration::clear_storage_prefix(
			<Pallet<T, I>>::name().as_bytes(),
			b"UpForKicking",
			b"",
			None,
			None,
		);

		log::info!(
			target: LOG_TARGET,
			"Cleared '{}' entries from 'UpForKicking' storage prefix",
			res.unique
		);

		if res.maybe_cursor.is_some() {
			log::error!(
				target: LOG_TARGET,
				"Storage prefix 'UpForKicking' is not completely cleared."
			);
		}

		T::DbWeight::get().writes(res.unique.into())
	}
}

/// v1_to_v2: `Members` storage map collapses `Founder` and `Fellow` keys into one `Fellow`.
/// Total number of `Founder`s and `Fellow`s must not be higher than `T::MaxMembersCount`.
pub(crate) mod v1_to_v2 {
	use super::*;
	use crate::{MemberRole, Members};

	/// V1 Role set.
	#[derive(Copy, Clone, PartialEq, Eq, Encode, Decode, TypeInfo, MaxEncodedLen)]
	pub enum MemberRoleV1 {
		Founder,
		Fellow,
		Ally,
		Retiring,
	}

	pub fn migrate<T: Config<I>, I: 'static>() -> Weight {
		log::info!(target: LOG_TARGET, "Running migration v1_to_v2: `Members` storage map collapses `Founder` and `Fellow` keys into one `Fellow`.");
		// fetch into the scope all members.
		let founders_vec = take_members::<T, I>(MemberRoleV1::Founder).into_inner();
		let mut fellows_vec = take_members::<T, I>(MemberRoleV1::Fellow).into_inner();
		let allies = take_members::<T, I>(MemberRoleV1::Ally);
		let retiring = take_members::<T, I>(MemberRoleV1::Retiring);
		if founders_vec
			.len()
			.saturating_add(fellows_vec.len())
			.saturating_add(allies.len())
			.saturating_add(retiring.len()) ==
			0
		{
			return T::DbWeight::get().reads(4)
		}
		log::info!(
			target: LOG_TARGET,
			"Members storage v1 contains, '{}' founders, '{}' fellows, '{}' allies, '{}' retiring members.",
			founders_vec.len(),
			fellows_vec.len(),
			allies.len(),
			retiring.len(),
		);
		// merge founders with fellows and sort.
		fellows_vec.extend(founders_vec);
		fellows_vec.sort();
		if fellows_vec.len() as u32 > T::MaxMembersCount::get() {
			log::error!(
				target: LOG_TARGET,
				"Merged list of founders and fellows do not fit into `T::MaxMembersCount` bound. Truncating the merged set into max members count."
			);
			fellows_vec.truncate(T::MaxMembersCount::get() as usize);
		}
		let fellows: BoundedVec<T::AccountId, T::MaxMembersCount> =
			fellows_vec.try_into().unwrap_or_default();
		// insert members with new storage map key.
		Members::<T, I>::insert(&MemberRole::Fellow, fellows.clone());
		Members::<T, I>::insert(&MemberRole::Ally, allies.clone());
		Members::<T, I>::insert(&MemberRole::Retiring, retiring.clone());
		log::info!(
			target: LOG_TARGET,
			"Members storage updated with, '{}' fellows, '{}' allies, '{}' retiring members.",
			fellows.len(),
			allies.len(),
			retiring.len(),
		);
		T::DbWeight::get().reads_writes(4, 4)
	}

	fn take_members<T: Config<I>, I: 'static>(
		role: MemberRoleV1,
	) -> BoundedVec<T::AccountId, T::MaxMembersCount> {
		migration::take_storage_item::<
			MemberRoleV1,
			BoundedVec<T::AccountId, T::MaxMembersCount>,
			Twox64Concat,
		>(<Pallet<T, I>>::name().as_bytes(), b"Members", role)
		.unwrap_or_default()
	}
}

#[cfg(test)]
mod test {
	use super::*;
	use crate::{mock::*, MemberRole};

	#[test]
	fn migration_v1_to_v2_works() {
		new_test_ext().execute_with(|| {
			assert_ok!(Alliance::join_alliance(RuntimeOrigin::signed(4)));
			assert_eq!(Alliance::members(MemberRole::Ally), vec![4]);
			assert_eq!(Alliance::members(MemberRole::Fellow), vec![1, 2, 3]);
			v1_to_v2::migrate::<Test, ()>();
			assert_eq!(Alliance::members(MemberRole::Fellow), vec![1, 2, 3, 4]);
			assert_eq!(Alliance::members(MemberRole::Ally), vec![]);
			assert_eq!(Alliance::members(MemberRole::Retiring), vec![]);
		});
	}
}
