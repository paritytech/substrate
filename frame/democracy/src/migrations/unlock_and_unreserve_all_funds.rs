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

//! A migration that unreserves all deposit and unlocks all stake held in the context of this
//! pallet.

use crate::DEMOCRACY_ID;
use core::iter::Sum;
use frame_support::{
	traits::{LockableCurrency, OnRuntimeUpgrade, ReservableCurrency},
	weights::constants::RocksDbWeight,
};
use sp_runtime::{traits::Zero, Saturating};
use sp_std::{
	collections::{btree_map::BTreeMap, btree_set::BTreeSet},
	vec::Vec,
};

#[cfg(feature = "try-runtime")]
use codec::{Decode, Encode};

#[cfg(feature = "try-runtime")]
#[derive(Debug, Encode, Decode)]
struct PreMigrationData<T: frame_system::Config + pallet_balances::Config> {
	account_reserved_before: BTreeMap<T::AccountId, T::Balance>,
}

/// A migration that unreserves all deposit and unlocks all stake held in the context of this
/// pallet.
///
/// Useful to prevent funds from being locked up when the pallet is being deprecated.
///
/// The pallet should be made inoperable before or immediately after this migration is run.
///
/// (See also the `RemovePallet` migration in `frame/support/src/migrations.rs`)
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
	/// Calculates and returns the total amounts reserved by each account by this pallet, and all
	/// accounts with locks in the context of this pallet.
	///
	/// There is no need to return the amount locked, because the entire lock is removed (always
	/// should be zero post-migration). We need to return the amounts reserved to check that the
	/// reserved amount is deducted correctly.
	///
	/// # Returns
	///
	/// This function returns a tuple of two `BTreeMap` collections and the weight of the reads:
	///
	/// * `BTreeMap<T::AccountId, T::Balance>`: Map of account IDs to their respective total
	///   reserved balance by this pallet
	/// * `BTreeSet<T::AccountId>`: Set of account IDs with some amount locked by this pallet.
	/// * frame_support::weights::Weight
	fn get_account_deposits_and_locks(
	) -> (BTreeMap<T::AccountId, T::Balance>, BTreeSet<T::AccountId>, frame_support::weights::Weight)
	{
		let deposit_of = crate::DepositOf::<T>::iter().collect::<Vec<_>>();
		let deposit_of_len = deposit_of.len();

		// Get all deposits (reserved).
		let account_deposits: BTreeMap<T::AccountId, T::Balance> = deposit_of
			.into_iter()
			.map(|(_prop_index, (accounts, balance))| {
				// Create a vec of tuples where each account is associated with the given balance
				accounts.into_iter().map(|account| (account, balance)).collect::<Vec<_>>()
			})
			.flatten()
			.fold(BTreeMap::new(), |mut acc, (account, balance)| {
				// Add the balance to the account's existing balance in the accumulator
				*acc.entry(account).or_insert(Zero::zero()) = acc
					.entry(account.clone())
					.or_insert(Zero::zero())
					.saturating_add(balance.into());
				acc
			});

		// Voter accounts have amounts locked.
		let voting_of = crate::VotingOf::<T>::iter().collect::<Vec<_>>();
		let voting_of_len = voting_of.len();
		let voting_accounts: BTreeSet<T::AccountId> =
			crate::VotingOf::<T>::iter().map(|(account_id, _voting)| account_id).collect();

		(
			account_deposits,
			voting_accounts,
			RocksDbWeight::get().reads(deposit_of_len as u64 + voting_of_len as u64),
		)
	}
}

impl<T: crate::Config + pallet_balances::Config> OnRuntimeUpgrade for UnlockAndUnreserveAllFunds<T>
where
	<T as pallet_balances::Config>::Balance: From<
		<<T as crate::Config>::Currency as frame_support::traits::Currency<
			<T as frame_system::Config>::AccountId,
		>>::Balance,
	>,
	<<T as crate::Config>::Currency as frame_support::traits::Currency<
		<T as frame_system::Config>::AccountId,
	>>::Balance: From<<T as pallet_balances::Config>::Balance>,
	<T as pallet_balances::Config>::Balance: Sum<<T as pallet_balances::Config>::Balance>,
{
	/// Collects pre-migration data useful for validating the migration was successful, and also
	/// checks the integrity of deposited and reserved balances.
	///
	/// Steps:
	/// 1. Gets the deposited balances for each account stored in this pallet.
	/// 2. Collects actual pre-migration reserved balances for each account.
	/// 3. Checks the integrity of the deposited balances.
	/// 4. Prints summary statistics about the state to be migrated.
	/// 5. Encodes and returns pre-migration data to be used in post_upgrade.
	///
	/// Fails with a `TryRuntimeError` if somehow the amount reserved by this pallet is greater than
	/// the actual total reserved amount for any accounts.
	#[cfg(feature = "try-runtime")]
	fn pre_upgrade() -> Result<Vec<u8>, sp_runtime::TryRuntimeError> {
		use frame_support::ensure;
		use sp_runtime::SaturatedConversion;

		// Get staked and deposited balances as reported by this pallet.
		let (account_deposits, _, _) = Self::get_account_deposits_and_locks();

		let all_accounts = account_deposits.keys().cloned().collect::<BTreeSet<_>>();
		let account_reserved_before: BTreeMap<T::AccountId, T::Balance> = all_accounts
			.iter()
			.map(|account| {
				(
					account.clone(),
					T::Currency::reserved_balance(&account).saturated_into::<T::Balance>(),
				)
			})
			.collect();

		// The deposit amount must be less than or equal to the reserved amount.
		// If it is higher, there is either a bug with the pallet or a bug in the calculation of the
		// deposit amount.
		ensure!(
			account_deposits.iter().all(
				|(account, deposit)| *deposit <= *account_reserved_before.get(account).unwrap()
			),
			"Deposit amount is greater than reserved amount"
		);

		let total_deposits_to_unreserve =
			account_deposits.clone().into_values().sum::<T::Balance>();
		log::info!("Total accounts: {:?}", all_accounts.len());
		log::info!("Total deposit to unreserve: {:?}", total_deposits_to_unreserve);

		let pre_migration_data = PreMigrationData::<T> { account_reserved_before };
		Ok(pre_migration_data.encode())
	}

	/// Executes the migration.
	///
	/// Steps:
	/// 1. Retrieves the deposit and accounts with locks for the pallet.
	/// 1. Unreserves the deposited funds for each account.
	/// 2. Unlocks the staked funds for each account.
	fn on_runtime_upgrade() -> frame_support::weights::Weight {
		// Get staked and deposited balances as reported by this pallet.
		let (account_deposits, accounts_with_locks, initial_reads_weight) =
			Self::get_account_deposits_and_locks();

		// Deposited funds need to be unreserved.
		for (account, unreserve_amount) in account_deposits.iter() {
			if unreserve_amount.is_zero() {
				continue
			}
			T::Currency::unreserve(&account, unreserve_amount.clone().into());
		}

		// Staked funds need to be unlocked.
		for account in accounts_with_locks {
			// There are lots of "Unexpected underflow in reducing consumer" errors logged when
			// removing this lock, even when the lock is checked to be present like this:
			// ```ignore
			// let locks = Locks::<T>::get(&account);
			// let has_democracy_lock = locks.iter().any(|lock| lock.id == DEMOCRACY_ID);
			// if has_democracy_lock {
			//     T::Currency::remove_lock(DEMOCRACY_ID, &account);
			// }
			// ```
			// Question for reviewers: is this safe to ignore?
			T::Currency::remove_lock(DEMOCRACY_ID, &account);
		}

		// Question for reviewers: how do I know the weight of the unreserve & remove_lock calls?
		RocksDbWeight::get().reads_writes(1, 1) + initial_reads_weight
	}

	/// Performs post-upgrade sanity checks:
	///
	/// 1. No locks remain for this pallet in Balances.
	/// 2. The reserved balance for each account has been reduced by the expected amount.
	#[cfg(feature = "try-runtime")]
	fn post_upgrade(pre_migration_data_bytes: Vec<u8>) -> Result<(), sp_runtime::TryRuntimeError> {
		let pre_migration_data = PreMigrationData::<T>::decode(&mut &pre_migration_data_bytes[..])
			.map_err(|_| "Failed to decode pre-migration data")?;

		// Get staked and deposited balances as reported by this pallet.
		let (account_deposits, _, _) = Self::get_account_deposits_and_locks();

		// Ensure there're no hanging locks for this pallet.
		pallet_balances::Locks::<T>::iter().for_each(|(_, lock_vec)| {
			for lock in lock_vec {
				assert!(lock.id != DEMOCRACY_ID, "Locks still exist for this pallet!");
			}
		});

		// Check that the reserved balance is reduced by the expected deposited amount.
		for (account, actual_reserved_before) in pre_migration_data.account_reserved_before {
			let actual_reserved_after = T::Currency::reserved_balance(&account);
			let expected_amount_deducted = account_deposits
				.get(&account)
				.unwrap_or(&Zero::zero())
				.min(&actual_reserved_before)
				.clone();
			let expected_reserved_after =
				actual_reserved_before.saturating_sub(expected_amount_deducted);
			assert!(
				actual_reserved_after == expected_reserved_after.into(),
				"Reserved balance for {:?} is incorrect. actual before: {:?}, actual after, {:?}, expected deducted: {:?}",
				account,
				actual_reserved_before,
				actual_reserved_after,
				expected_amount_deducted,
			);
		}

		Ok(())
	}
}
