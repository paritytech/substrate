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

use crate::{BalanceOf, DEMOCRACY_ID};
use core::iter::Sum;
use frame_support::{
	traits::{LockableCurrency, OnRuntimeUpgrade, ReservableCurrency},
	weights::constants::RocksDbWeight,
};
use sp_core::Get;
use sp_runtime::{traits::Zero, Saturating};
use sp_std::{
	collections::{btree_map::BTreeMap, btree_set::BTreeSet},
	vec::Vec,
};

/// A migration that unreserves all deposit and unlocks all stake held in the context of this
/// pallet.
///
/// Useful to prevent funds from being locked up when the pallet is being deprecated.
///
/// The pallet should be made inoperable before or immediately after this migration is run.
///
/// (See also the `RemovePallet` migration in `frame/support/src/migrations.rs`)
pub struct UnlockAndUnreserveAllFunds<T: crate::Config>(sp_std::marker::PhantomData<T>);

impl<T: crate::Config> UnlockAndUnreserveAllFunds<T>
where
	BalanceOf<T>: Sum,
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
	/// * `BTreeMap<T::AccountId, BalanceOf<T>>`: Map of account IDs to their respective total
	///   reserved balance by this pallet
	/// * `BTreeSet<T::AccountId>`: Set of account IDs with some amount locked by this pallet.
	/// * `frame_support::weights::Weight`: the weight consumed by this call.
	fn get_account_deposits_and_locks() -> (
		BTreeMap<T::AccountId, BalanceOf<T>>,
		BTreeSet<T::AccountId>,
		frame_support::weights::Weight,
	) {
		let deposit_of = crate::DepositOf::<T>::iter().collect::<Vec<_>>();
		let deposit_of_len = deposit_of.len() as u64;

		// Get all deposits (reserved).
		let mut total_voting_vec_entries: u64 = 0;
		let account_deposits: BTreeMap<T::AccountId, BalanceOf<T>> = deposit_of
			.into_iter()
			.flat_map(|(_prop_index, (accounts, balance))| {
				// Track the total number of vec entries to calculate the weight of the reads.
				total_voting_vec_entries += accounts.len() as u64;
				// Create a vec of tuples where each account is associated with the given balance
				accounts.into_iter().map(|account| (account, balance)).collect::<Vec<_>>()
			})
			.fold(BTreeMap::new(), |mut acc, (account, balance)| {
				// Add the balance to the account's existing balance in the accumulator
				*acc.entry(account).or_insert(Zero::zero()) =
					acc.entry(account.clone()).or_insert(Zero::zero()).saturating_add(balance);
				acc
			});

		// Voter accounts have amounts locked.
		let voting_of = crate::VotingOf::<T>::iter().collect::<Vec<_>>();
		let voting_of_len = voting_of.len() as u64;
		let voting_accounts: BTreeSet<T::AccountId> =
			crate::VotingOf::<T>::iter().map(|(account_id, _voting)| account_id).collect();

		(
			account_deposits,
			voting_accounts,
			RocksDbWeight::get().reads(
				deposit_of_len +
				voting_of_len +
				// Max items in a Voting enum is MaxVotes + 5
				total_voting_vec_entries * (T::MaxVotes::get() as u64 + 5),
			),
		)
	}
}

impl<T: crate::Config> OnRuntimeUpgrade for UnlockAndUnreserveAllFunds<T>
where
	BalanceOf<T>: Sum,
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
	#[cfg(any(feature = "try-runtime", test))]
	fn pre_upgrade() -> Result<Vec<u8>, sp_runtime::TryRuntimeError> {
		use codec::Encode;
		use frame_support::ensure;

		// Get staked and deposited balances as reported by this pallet.
		let (account_deposits, account_locks, _) = Self::get_account_deposits_and_locks();

		let all_accounts = account_deposits.keys().cloned().collect::<BTreeSet<_>>();
		let account_reserved_before: BTreeMap<T::AccountId, BalanceOf<T>> = all_accounts
			.iter()
			.map(|account| (account.clone(), T::Currency::reserved_balance(&account)))
			.collect();

		// The deposit amount must be less than or equal to the reserved amount.
		// If it is higher, there is either a bug with the pallet or a bug in the calculation of the
		// deposit amount.
		ensure!(
			account_deposits.iter().all(|(account, deposit)| *deposit <=
				*account_reserved_before.get(account).unwrap_or(&Zero::zero())),
			"Deposit amount is greater than reserved amount"
		);

		let total_deposits_to_unreserve =
			account_deposits.clone().into_values().sum::<BalanceOf<T>>();

		log::info!("Total accounts: {:?}", all_accounts.len());
		log::info!("Total deposit to unreserve: {:?}", total_deposits_to_unreserve);
		log::info!("Accounts with locks: {:?}", account_locks.len());

		Ok(account_reserved_before.encode())
	}

	/// Executes the migration.
	///
	/// Steps:
	/// 1. Retrieves the deposit and accounts with locks for the pallet.
	/// 2. Unreserves the deposited funds for each account.
	/// 3. Unlocks the staked funds for each account.
	fn on_runtime_upgrade() -> frame_support::weights::Weight {
		// Get staked and deposited balances as reported by this pallet.
		let (account_deposits, accounts_with_locks, initial_reads) =
			Self::get_account_deposits_and_locks();

		// Deposited funds need to be unreserved.
		for (account, unreserve_amount) in account_deposits.iter() {
			if unreserve_amount.is_zero() {
				continue
			}
			T::Currency::unreserve(&account, *unreserve_amount);
		}

		// Staked funds need to be unlocked.
		for account in accounts_with_locks.iter() {
			T::Currency::remove_lock(DEMOCRACY_ID, account);
		}

		RocksDbWeight::get().reads_writes(
			accounts_with_locks.len() as u64 + account_deposits.iter().count() as u64,
			accounts_with_locks.len() as u64 + account_deposits.iter().count() as u64,
		) + initial_reads
	}

	/// Performs post-upgrade sanity checks:
	///
	/// 1. No locks remain for this pallet in Balances.
	/// 2. The reserved balance for each account has been reduced by the expected amount.
	#[cfg(any(feature = "try-runtime", test))]
	fn post_upgrade(
		account_reserved_before_bytes: Vec<u8>,
	) -> Result<(), sp_runtime::TryRuntimeError> {
		use codec::Decode;

		let account_reserved_before =
			BTreeMap::<T::AccountId, BalanceOf<T>>::decode(&mut &account_reserved_before_bytes[..])
				.map_err(|_| "Failed to decode account_reserved_before_bytes")?;

		// Get staked and deposited balances as reported by this pallet.
		let (account_deposits, _, _) = Self::get_account_deposits_and_locks();

		// Check that the reserved balance is reduced by the expected deposited amount.
		for (account, actual_reserved_before) in account_reserved_before {
			let actual_reserved_after = T::Currency::reserved_balance(&account);
			let expected_amount_deducted = *account_deposits
				.get(&account)
				.expect("account deposit must exist to be in pre_migration_data, qed");
			let expected_reserved_after =
				actual_reserved_before.saturating_sub(expected_amount_deducted);
			assert!(
				actual_reserved_after == expected_reserved_after,
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

#[cfg(test)]
mod test {
	use super::*;
	use crate::{
		tests::{new_test_ext, Test},
		DepositOf, Voting, VotingOf,
	};
	use frame_support::{
		assert_ok,
		traits::{Currency, OnRuntimeUpgrade, ReservableCurrency, WithdrawReasons},
		BoundedVec,
	};

	#[test]
	fn unreserve_works_for_depositer() {
		let depositer_0 = 10;
		let depositer_1 = 11;
		let deposit = 25;
		let depositer_0_initial_reserved = 0;
		let depositer_1_initial_reserved = 15;
		let initial_balance = 100_000;
		new_test_ext().execute_with(|| {
			// Set up initial state.
			<Test as crate::Config>::Currency::make_free_balance_be(&depositer_0, initial_balance);
			<Test as crate::Config>::Currency::make_free_balance_be(&depositer_1, initial_balance);
			assert_ok!(<Test as crate::Config>::Currency::reserve(
				&depositer_0,
				depositer_0_initial_reserved + deposit
			));
			assert_ok!(<Test as crate::Config>::Currency::reserve(
				&depositer_1,
				depositer_1_initial_reserved + deposit
			));
			let depositors =
				BoundedVec::<_, <Test as crate::Config>::MaxDeposits>::truncate_from(vec![
					depositer_0,
					depositer_1,
				]);
			DepositOf::<Test>::insert(0, (depositors, deposit));

			// Sanity check: ensure initial reserved balance was set correctly.
			assert_eq!(
				<Test as crate::Config>::Currency::reserved_balance(&depositer_0),
				depositer_0_initial_reserved + deposit
			);
			assert_eq!(
				<Test as crate::Config>::Currency::reserved_balance(&depositer_1),
				depositer_1_initial_reserved + deposit
			);

			// Run the migration.
			let bytes = UnlockAndUnreserveAllFunds::<Test>::pre_upgrade()
				.unwrap_or_else(|e| panic!("pre_upgrade failed: {:?}", e));
			UnlockAndUnreserveAllFunds::<Test>::on_runtime_upgrade();
			assert_ok!(UnlockAndUnreserveAllFunds::<Test>::post_upgrade(bytes));

			// Assert the reserved balance was reduced by the expected amount.
			assert_eq!(
				<Test as crate::Config>::Currency::reserved_balance(&depositer_0),
				depositer_0_initial_reserved
			);
			assert_eq!(
				<Test as crate::Config>::Currency::reserved_balance(&depositer_1),
				depositer_1_initial_reserved
			);
		});
	}

	#[test]
	fn unlock_works_for_voter() {
		let voter = 10;
		let stake = 25;
		let initial_locks = vec![(b"somethin", 10)];
		let initial_balance = 100_000;
		new_test_ext().execute_with(|| {
			// Set up initial state.
			<Test as crate::Config>::Currency::make_free_balance_be(&voter, initial_balance);
			for lock in initial_locks.clone() {
				<Test as crate::Config>::Currency::set_lock(
					*lock.0,
					&voter,
					lock.1,
					WithdrawReasons::all(),
				);
			}
			VotingOf::<Test>::insert(voter, Voting::default());
			<Test as crate::Config>::Currency::set_lock(
				DEMOCRACY_ID,
				&voter,
				stake,
				WithdrawReasons::all(),
			);

			// Sanity check: ensure initial Balance state was set up correctly.
			let mut voter_all_locks = initial_locks.clone();
			voter_all_locks.push((&DEMOCRACY_ID, stake));
			assert_eq!(
				<Test as crate::Config>::Currency::locks(&voter)
					.iter()
					.map(|lock| (&lock.id, lock.amount))
					.collect::<Vec<_>>(),
				voter_all_locks
			);

			// Run the migration.
			let bytes = UnlockAndUnreserveAllFunds::<Test>::pre_upgrade()
				.unwrap_or_else(|e| panic!("pre_upgrade failed: {:?}", e));
			UnlockAndUnreserveAllFunds::<Test>::on_runtime_upgrade();
			assert_ok!(UnlockAndUnreserveAllFunds::<Test>::post_upgrade(bytes));

			// Assert the voter lock was removed
			assert_eq!(
				<Test as crate::Config>::Currency::locks(&voter)
					.iter()
					.map(|lock| (&lock.id, lock.amount))
					.collect::<Vec<_>>(),
				initial_locks
			);
		});
	}
}
