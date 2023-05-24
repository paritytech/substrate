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

//! This migration unlocks all `Voter` and `SeatHolder` `stake`s, and unreserves all `Voter` and
//! `SeatHolder` `deposit`s.

use codec::{Decode, Encode};
use core::iter::Sum;
use frame_support::traits::OnRuntimeUpgrade;

#[cfg(feature = "try-runtime")]
use frame_support::ensure;
#[cfg(feature = "try-runtime")]
use sp_std::collections::btree_map::BTreeMap;
#[cfg(feature = "try-runtime")]
use sp_std::vec::Vec;

#[cfg(feature = "try-runtime")]
#[derive(Debug, Encode, Decode)]
struct PreMigrationData<T: frame_system::Config + pallet_balances::Config> {
	account_locked_before: BTreeMap<T::AccountId, T::Balance>,
	account_reserved_before: BTreeMap<T::AccountId, T::Balance>,
}

pub struct UnlockAndUnreserveAllFunds<T: crate::Config + pallet_balances::Config>(
	sp_std::marker::PhantomData<T>,
);

impl<T: crate::Config + pallet_balances::Config> UnlockAndUnreserveAllFunds<T>
where
	<T as pallet_balances::Config>::Balance: From<
		<<T as crate::Config>::Currency as frame_support::traits::Currency<
			<T as frame_system::Config>::AccountId,
		>>::Balance,
	>,
	<T as pallet_balances::Config>::Balance: Sum<<T as pallet_balances::Config>::Balance>,
{
	/// Calculates and returns the total amounts deposited and staked by each account in the context
	/// of this pallet.
	///
	/// The deposited and staked amounts are returned in two separate `BTreeMap` collections.
	///
	/// The first `BTreeMap`, `account_deposited_sums`, contains each account's total amount
	/// deposited. This includes deposits made by Members, RunnerUps, Candidates, and Voters.
	///
	/// The second `BTreeMap`, `account_staked_sums`, contains each account's total amount staked.
	/// This includes stakes made by Voters.
	///
	/// # Returns
	///
	/// This function returns a tuple of two `BTreeMap` collections:
	///
	/// * `BTreeMap<T::AccountId, T::Balance>`: Map of account IDs to their respective total deposit
	///   sums.
	/// * `BTreeMap<T::AccountId, T::Balance>`: Map of account IDs to their respective total staked
	///   sums.
	fn get_account_deposited_and_staked_sums(
	) -> (BTreeMap<T::AccountId, T::Balance>, BTreeMap<T::AccountId, T::Balance>) {
		use sp_runtime::{traits::Zero, SaturatedConversion, Saturating};
		let members = crate::Members::<T>::get();
		let runner_ups = crate::RunnersUp::<T>::get();
		let candidates = crate::Candidates::<T>::get();
		let voters: Vec<(T::AccountId, crate::Voter<T::AccountId, crate::BalanceOf<T>>)> =
			crate::Voting::<T>::iter().collect::<Vec<_>>();

		// Get the total amount deposited by all Members, RunnerUps, and Candidates.
		let mut account_deposited_sums: BTreeMap<T::AccountId, T::Balance> = BTreeMap::new();
		for member in members.iter().chain(runner_ups.iter()) {
			let deposited_sum =
				account_deposited_sums.entry(member.who.clone()).or_insert(Zero::zero());
			*deposited_sum += member.deposit.into();
		}
		for (candidate, amount) in candidates.iter() {
			let deposited_sum =
				account_deposited_sums.entry(candidate.clone()).or_insert(Zero::zero());
			*deposited_sum += (*amount).saturated_into::<T::Balance>();
		}

		// Get the total amount staked and deposited by Voters.
		let mut account_staked_sums: BTreeMap<T::AccountId, T::Balance> = BTreeMap::new();
		for (account_id, voter) in voters.iter() {
			let staked_sum = account_staked_sums.entry(account_id.clone()).or_insert(Zero::zero());
			*staked_sum =
				staked_sum.saturating_add(voter.stake.saturated_into::<T::Balance>().into());

			let deposited_sum =
				account_deposited_sums.entry(account_id.clone()).or_insert(Zero::zero());
			*deposited_sum += voter.deposit.saturated_into::<T::Balance>();
		}

		(account_deposited_sums, account_staked_sums)
	}
}

impl<T: crate::Config + pallet_balances::Config> OnRuntimeUpgrade for UnlockAndUnreserveAllFunds<T>
where
	<T as pallet_balances::Config>::Balance: From<
		<<T as crate::Config>::Currency as frame_support::traits::Currency<
			<T as frame_system::Config>::AccountId,
		>>::Balance,
	>,
	<T as pallet_balances::Config>::Balance: Sum<<T as pallet_balances::Config>::Balance>,
{
	#[cfg(feature = "try-runtime")]
	fn pre_upgrade() -> Result<Vec<u8>, sp_runtime::TryRuntimeError> {
		use frame_support::traits::ReservableCurrency;
		use pallet_balances::{BalanceLock, Locks, Reasons};
		use sp_core::Get;
		use sp_runtime::{traits::Zero, SaturatedConversion};
		use sp_std::collections::btree_set::BTreeSet;

		// Get storage items containing locked and reserved balances.
		let (account_deposited_sums, account_staked_sums) =
			Self::get_account_deposited_and_staked_sums();

		// Now get the *actual* locked and reserved amounts for each account before the migration,
		// so we can check that the amounts are reduced by the expected amounts post-migration.
		let all_accounts: BTreeSet<T::AccountId> = account_staked_sums
			.keys()
			.chain(account_deposited_sums.keys())
			.cloned()
			.collect();
		let mut account_locked_before: BTreeMap<T::AccountId, T::Balance> = BTreeMap::new();
		let mut account_reserved_before: BTreeMap<T::AccountId, T::Balance> = BTreeMap::new();
		let empty_lock =
			BalanceLock { id: T::PalletId::get(), amount: Zero::zero(), reasons: Reasons::Misc };

		// Total deposited for each account *should* be less than or equal to the total reserved,
		// however this does not hold for all cases due to bugs in the reserve logic of this pallet.
		let mut bugged_deposits = 0;
		for account in all_accounts.iter() {
			// Question: how does this know where to get locks just from T? what if there were
			// multiple pallet_balance implementations in the runtime?
			let locked = Locks::<T>::get(account.clone())
				.iter()
				.find(|l| l.id == T::PalletId::get())
				.unwrap_or(&empty_lock)
				.amount
				.saturated_into::<T::Balance>();

			let reserved = T::Currency::reserved_balance(&account).saturated_into::<T::Balance>();
			ensure!(
				&locked == account_staked_sums.get(&account).unwrap_or(&Zero::zero()),
				"account locked != account staked"
			);
			if account_deposited_sums.get(&account).unwrap_or(&Zero::zero()) > &reserved {
				bugged_deposits += 1;
			}

			// Record the values in the Map
			account_locked_before.insert(account.clone(), locked);
			account_reserved_before.insert(account.clone(), reserved);
		}

		// Print some summary stats.
		let total_stake_to_unlock = account_staked_sums.clone().into_values().sum::<T::Balance>();
		let total_deposits_to_unreserve =
			account_deposited_sums.clone().into_values().sum::<T::Balance>();
		log::info!("Total accounts: {:?}", all_accounts.len());
		log::info!("Total stake to unlock: {:?}", total_stake_to_unlock);
		log::info!("Total deposit to unreserve: {:?}", total_deposits_to_unreserve);
		log::info!("Bugged deposits: {}/{}", bugged_deposits, all_accounts.len());

		let pre_migration_data =
			PreMigrationData::<T> { account_locked_before, account_reserved_before };
		Ok(pre_migration_data.encode())
	}

	fn on_runtime_upgrade() -> frame_support::weights::Weight {
		log::info!("on_runtime_upgrade");
		todo!()
	}

	#[cfg(feature = "try-runtime")]
	fn post_upgrade(pre_migration_data_bytes: Vec<u8>) -> Result<(), sp_runtime::TryRuntimeError> {
		let pre_migration_data = PreMigrationData::<T>::decode(&mut &pre_migration_data_bytes[..])
			.map_err(|_| "Failed to decode pre-migration data")?;

		log::info!("{:?}", pre_migration_data.account_locked_before);
		log::info!("{:?}", pre_migration_data.account_reserved_before);
		Ok(())
	}
}
