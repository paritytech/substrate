// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
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

use frame_support::{
	storage::{storage_prefix, unhashed, PrefixIterator},
	traits::{Currency, Get, GetStorageVersion, PalletInfoAccess, StorageVersion},
	weights::Weight,
};

/// Migrate the storage of this pallet for version 5:
///
/// Storage changing:
/// * Members: migrate from a `Vec<AccountId>` to `Vec<MemberInfo>`
/// * Voting: migrate value
///   * from `(u32, u32, Vec<AccountId>, Vec<AccountId>, BlockNumber)`
///   * to `(u32, u32, Vec<MemberVoteInfo>, Vec<MemberVoteInfo>, BlockNumber)`
///
/// New storage:
/// * LastPayment
/// * PaymentBase
///
/// The migration will look into the storage version in order not to trigger a migration on an up
/// to date storage. Thus the on chain storage version must be less than 4 in order to trigger the
/// migration.
pub fn migrate<T: crate::Config<I>, I: 'static>(payment_base: crate::BalanceOf<T, I>) -> Weight
where
	crate::Pallet<T, I>: GetStorageVersion,
{
	let on_chain_storage_version =
		<crate::Pallet<T, I> as GetStorageVersion>::on_chain_storage_version();

	if on_chain_storage_version < 5 {
		log::info!(
			target: "runtime::collective",
			"Running migration to v5 for collective with storage version {:?}",
			on_chain_storage_version,
		);

		// Create collective pot account.
		let pot_account_id = <crate::Pallet<T, I>>::pot_account_id();
		let min = T::Currency::minimum_balance();
		if T::Currency::total_balance(&pot_account_id) < min {
			let _ = T::Currency::make_free_balance_be(&pot_account_id, min);
		}

		let current_block_number = frame_system::Pallet::<T>::block_number();
		crate::LastPayment::<T, I>::put(current_block_number);
		crate::PaymentBase::<T, I>::put(payment_base);
		crate::Voting::<T, I>::translate_values::<
			(
				crate::ProposalIndex,
				crate::VoteCount,
				Vec<T::AccountId>,
				Vec<T::AccountId>,
				T::BlockNumber,
			),
			_,
		>(|(index, threshold, ayes, nays, end)| {
			let ayes = ayes.into_iter().map(|id| crate::MemberVoteInfo { id, votes: 1 }).collect();
			let nays = nays.into_iter().map(|id| crate::MemberVoteInfo { id, votes: 1 }).collect();
			Some(crate::Votes { index, threshold, ayes, nays, end })
		});
		let res = crate::Members::<T, I>::translate::<Vec<T::AccountId>, _>(|members| {
			members.map(|members| {
				members
					.into_iter()
					.map(|id| crate::MemberInfo {
						id,
						votes: 1,
						last_vote_increase: current_block_number,
					})
					.collect::<Vec<_>>()
			})
		});
		if let Err(_) = res {
			log::error!(target: "runtime::collective", "Migration of storage `Members` failed");
		}
		StorageVersion::new(5).put::<crate::Pallet<T, I>>();

		<T as frame_system::Config>::BlockWeights::get().max_block
	} else {
		0
	}
}

/// Some checks prior to migration. This can be linked to
/// [`frame_support::traits::OnRuntimeUpgrade::pre_upgrade`] for further testing.
///
/// Panics if anything goes wrong.
pub fn pre_migrate<T: crate::Config<I>, I: 'static>()
where
	crate::Pallet<T, I>: GetStorageVersion,
{
	let on_chain_storage_version =
		<crate::Pallet<T, I> as GetStorageVersion>::on_chain_storage_version();

	if on_chain_storage_version < 5 {
		assert!(!crate::LastPayment::<T, I>::exists());
		assert!(!crate::PaymentBase::<T, I>::exists());
	}
}

/// Some checks for after migration. This can be linked to
/// [`frame_support::traits::OnRuntimeUpgrade::post_upgrade`] for further testing.
///
/// Panics if anything goes wrong.
pub fn post_migrate<T: crate::Config<I>, I: 'static>()
where
	crate::Pallet<T, I>: GetStorageVersion,
{
	let on_chain_storage_version =
		<crate::Pallet<T, I> as GetStorageVersion>::on_chain_storage_version();

	assert_eq!(on_chain_storage_version, 5);
	assert!(crate::LastPayment::<T, I>::exists());
	assert!(crate::PaymentBase::<T, I>::exists());

	// Ensure members are decodable
	let prefix = storage_prefix(crate::Pallet::<T, I>::name().as_bytes(), b"Members");
	if unhashed::get_raw(&prefix).is_some() {
		unhashed::get::<crate::MemberInfo<T::AccountId, T::BlockNumber>>(&prefix)
			.expect("Members must be decodable");
	}

	// Ensure all votes are decodable
	let prefix = storage_prefix(crate::Pallet::<T, I>::name().as_bytes(), b"Voting").to_vec();
	let voting_count = PrefixIterator::<_, ()>::new(prefix.clone(), prefix, |_, _| Ok(())).count();
	assert_eq!(crate::Voting::<T, I>::iter().count(), voting_count);

	// Ensure pot is created
	let min = T::Currency::minimum_balance();
	let pot_account_id = <crate::Pallet<T, I>>::pot_account_id();
	assert!(T::Currency::total_balance(&pot_account_id) >= min);
}
