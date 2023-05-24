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
		use sp_runtime::{traits::Zero, SaturatedConversion};
		let members = crate::Members::<T>::get();
		let runner_ups = crate::RunnersUp::<T>::get();
		let candidates = crate::Candidates::<T>::get();
		let voters: Vec<(T::AccountId, crate::Voter<T::AccountId, crate::BalanceOf<T>>)> =
			crate::Voting::<T>::iter().collect::<Vec<_>>();

		// Get the total amount deposited (Members, RunnerUps, Candidates and Voters all can have
		// deposits).
		let account_deposited_sums: BTreeMap<T::AccountId, T::Balance> = members
			// Massage all data into (account_id, deposit) tuples.
			.iter()
			.chain(runner_ups.iter())
			.map(|member| (member.who.clone(), member.deposit.into()))
			.chain(candidates.iter().map(|(candidate, amount)| {
				(candidate.clone(), (*amount).saturated_into::<T::Balance>())
			}))
			.chain(voters.iter().map(|(account_id, voter)| {
				(account_id.clone(), voter.deposit.saturated_into::<T::Balance>())
			}))
			// Finally, aggregate the tuples into a Map.
			.fold(BTreeMap::new(), |mut acc, (id, deposit)| {
				*acc.entry(id).or_insert(Zero::zero()) += deposit;
				acc
			});

		// Get the total amount staked (only Voters stake).
		let account_staked_sums: BTreeMap<T::AccountId, T::Balance> = voters
			.iter()
			.map(|(account_id, voter)| {
				(account_id.clone(), voter.stake.saturated_into::<T::Balance>().into())
			})
			.fold(BTreeMap::new(), |mut acc, (id, stake)| {
				*acc.entry(id).or_insert(Zero::zero()) += stake;
				acc
			});

		(account_deposited_sums, account_staked_sums)
	}

	/// Helper function for returning the actual locked amount of an account under the ID of this
	/// pallet.
	///
	/// If there is no locked amount, returns zero.
	#[cfg(feature = "try-runtime")]
	fn get_actual_locked_amount(account: T::AccountId) -> T::Balance {
		use pallet_balances::Locks;
		use sp_core::Get;
		use sp_runtime::{traits::Zero, SaturatedConversion};

		Locks::<T>::get(account.clone())
			.iter()
			.find(|l| l.id == T::PalletId::get())
			.map(|lock| lock.amount.saturated_into::<T::Balance>())
			.unwrap_or(Zero::zero())
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
		use sp_runtime::{traits::Zero, SaturatedConversion};
		use sp_std::collections::btree_set::BTreeSet;

		// Get staked and deposited balances as reported by this pallet.
		let (account_deposited_sums, account_staked_sums) =
			Self::get_account_deposited_and_staked_sums();

		// Now get the *actual* locked and reserved amounts for each account before the migration,
		// so we can check that the amounts are reduced by the expected amounts post-migration.
		let all_accounts: BTreeSet<T::AccountId> = account_staked_sums
			.keys()
			.chain(account_deposited_sums.keys())
			.cloned()
			.collect();

		let account_locked_before: BTreeMap<T::AccountId, T::Balance> = all_accounts
			.iter()
			.map(|account| (account.clone(), Self::get_actual_locked_amount(account.clone())))
			.collect();

		let account_reserved_before: BTreeMap<T::AccountId, T::Balance> = all_accounts
			.iter()
			.map(|account| {
				(
					account.clone(),
					T::Currency::reserved_balance(&account).saturated_into::<T::Balance>(),
				)
			})
			.collect();

		// Total deposited for each account *should* be less than or equal to the total reserved,
		// however this does not hold for all cases due to bugs in the reserve logic of this pallet.
		let bugged_deposits = all_accounts
			.iter()
			.filter(|account| {
				account_deposited_sums.get(&account).unwrap_or(&Zero::zero()) >
					account_reserved_before.get(&account).unwrap_or(&Zero::zero())
			})
			.count();

		// The calculation of the locked & staked logic is not known to be bugged, so we assert
		// that the amounts staked in the pallet match the amounts actually locked in Balances.
		// If this fails, there is likely a bug in the migration and it should be investigated.
		ensure!(
			!all_accounts
				.iter()
				.any(|account| account_locked_before.get(&account).unwrap_or(&Zero::zero()) !=
					account_staked_sums.get(&account).unwrap_or(&Zero::zero())),
			"account locked != account staked"
		);

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
