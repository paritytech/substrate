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

use crate::BalanceOf;
use core::iter::Sum;
use frame_support::{
	traits::{LockableCurrency, OnRuntimeUpgrade, ReservableCurrency},
	weights::constants::RocksDbWeight,
};
use sp_core::Get;
use sp_runtime::traits::Zero;
use sp_std::{collections::btree_map::BTreeMap, vec::Vec};

#[cfg(feature = "try-runtime")]
use codec::{Decode, Encode};

#[cfg(feature = "try-runtime")]
use frame_support::ensure;

#[cfg(feature = "try-runtime")]
#[derive(Debug, Encode, Decode)]
struct PreMigrationData<T: crate::Config> {
	account_locked_before: BTreeMap<T::AccountId, BalanceOf<T>>,
	account_reserved_before: BTreeMap<T::AccountId, BalanceOf<T>>,
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
	BalanceOf<T>: From<<T as pallet_balances::Config>::Balance>,
	BalanceOf<T>: Sum,
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
	/// This function returns a tuple of two `BTreeMap` collections and the weight of the reads:
	///
	/// * `BTreeMap<T::AccountId, BalanceOf<T>>`: Map of account IDs to their respective total
	///   deposit sums.
	/// * `BTreeMap<T::AccountId, BalanceOf<T>>`: Map of account IDs to their respective total
	///   staked sums.
	/// * frame_support::weights::Weight
	fn get_account_deposited_and_staked_sums() -> (
		BTreeMap<T::AccountId, BalanceOf<T>>,
		BTreeMap<T::AccountId, BalanceOf<T>>,
		frame_support::weights::Weight,
	) {
		use sp_runtime::Saturating;

		let members = crate::Members::<T>::get();
		let runner_ups = crate::RunnersUp::<T>::get();
		let candidates = crate::Candidates::<T>::get();
		let voters: Vec<(T::AccountId, crate::Voter<T::AccountId, BalanceOf<T>>)> =
			crate::Voting::<T>::iter().collect::<Vec<_>>();

		// Get the total amount deposited (Members, RunnerUps, Candidates and Voters all can have
		// deposits).
		let account_deposited_sums: BTreeMap<T::AccountId, BalanceOf<T>> = members
			// Massage all data structures into (account_id, deposit) tuples.
			.iter()
			.chain(runner_ups.iter())
			.map(|member| (member.who.clone(), member.deposit))
			.chain(candidates.iter().map(|(candidate, amount)| (candidate.clone(), *amount)))
			.chain(voters.iter().map(|(account_id, voter)| (account_id.clone(), voter.deposit)))
			// Finally, aggregate the tuples into a Map.
			.fold(BTreeMap::new(), |mut acc, (id, deposit)| {
				*acc.entry(id).or_insert(Zero::zero()) =
					acc.entry(id.clone()).or_insert(Zero::zero()).saturating_add(deposit);
				acc
			});

		// Get the total amount staked (only Voters stake).
		let account_staked_sums: BTreeMap<T::AccountId, BalanceOf<T>> = voters
			.iter()
			.map(|(account_id, voter)| (account_id.clone(), voter.stake))
			.fold(BTreeMap::new(), |mut acc, (id, stake)| {
				*acc.entry(id).or_insert(Zero::zero()) =
					acc.entry(id.clone()).or_insert(Zero::zero()).saturating_add(stake);

				acc
			});

		(
			account_deposited_sums,
			account_staked_sums,
			RocksDbWeight::get().reads(
				members.len() as u64 +
					runner_ups.len() as u64 +
					candidates.len() as u64 +
					voters.len() as u64,
			),
		)
	}

	/// Helper function for returning the locked amount of an account under the ID of this
	/// pallet.
	#[cfg(feature = "try-runtime")]
	fn get_actual_locked_amount(account: T::AccountId) -> Option<BalanceOf<T>> {
		use pallet_balances::Locks;
		use sp_runtime::SaturatedConversion;

		Locks::<T>::get(account.clone())
			.iter()
			.find(|l| l.id == T::PalletId::get())
			.map(|lock| lock.amount.saturated_into::<BalanceOf<T>>())
	}
}

impl<T: crate::Config + pallet_balances::Config> OnRuntimeUpgrade for UnlockAndUnreserveAllFunds<T>
where
	BalanceOf<T>: From<<T as pallet_balances::Config>::Balance>,
	BalanceOf<T>: Sum,
{
	/// Collects pre-migration data useful for validating the migration was successful, and also
	/// checks the integrity of deposited and reserved balances.
	///
	/// Steps:
	/// 1. Gets the deposited and staked balances for each account stored in this pallet.
	/// 2. Collects actual pre-migration locked and reserved balances for each account.
	/// 3. Checks the integrity of the deposited and reserved balances.
	/// 4. Prints summary statistics about the state to be migrated.
	/// 5. Encodes and returns pre-migration data to be used in post_upgrade.
	///
	/// Fails with a `TryRuntimeError` if there's a discrepancy between the amount
	/// reported as staked by the pallet and the amount actually locked in `Balances`.
	#[cfg(feature = "try-runtime")]
	fn pre_upgrade() -> Result<Vec<u8>, sp_runtime::TryRuntimeError> {
		use sp_std::collections::btree_set::BTreeSet;

		// Get staked and deposited balances as reported by this pallet.
		let (account_deposited_sums, account_staked_sums, _) =
			Self::get_account_deposited_and_staked_sums();

		// Now get the *actual* locked and reserved amounts for each account before the migration,
		// so we can check that the amounts are reduced by the expected amounts post-migration.
		let all_accounts: BTreeSet<T::AccountId> = account_staked_sums
			.keys()
			.chain(account_deposited_sums.keys())
			.cloned()
			.collect();

		let account_locked_before: BTreeMap<T::AccountId, BalanceOf<T>> = all_accounts
			.iter()
			.map(|account| {
				(
					account.clone(),
					Self::get_actual_locked_amount(account.clone()).unwrap_or(Zero::zero()),
				)
			})
			.collect();

		let account_reserved_before: BTreeMap<T::AccountId, BalanceOf<T>> = all_accounts
			.iter()
			.map(|account| (account.clone(), T::Currency::reserved_balance(&account)))
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
		let total_stake_to_unlock = account_staked_sums.clone().into_values().sum::<BalanceOf<T>>();
		let total_deposits_to_unreserve =
			account_deposited_sums.clone().into_values().sum::<BalanceOf<T>>();
		log::info!("Total accounts: {:?}", all_accounts.len());
		log::info!("Total stake to unlock: {:?}", total_stake_to_unlock);
		log::info!("Total deposit to unreserve: {:?}", total_deposits_to_unreserve);
		log::info!("Bugged deposits: {}/{}", bugged_deposits, all_accounts.len());

		let pre_migration_data =
			PreMigrationData::<T> { account_locked_before, account_reserved_before };
		Ok(pre_migration_data.encode())
	}

	/// Executes the migration.
	///
	/// Steps:
	/// 1. Retrieves the deposit and stake amounts from the pallet.
	/// 1. Unreserves the deposited funds for each account.
	/// 2. Unlocks the staked funds for each account.
	fn on_runtime_upgrade() -> frame_support::weights::Weight {
		// Get staked and deposited balances as reported by this pallet.
		let (account_deposited_sums, account_staked_sums, initial_reads_weight) =
			Self::get_account_deposited_and_staked_sums();

		// Deposited funds need to be unreserved.
		for (account, unreserve_amount) in account_deposited_sums {
			if unreserve_amount.is_zero() {
				continue
			}
			T::Currency::unreserve(&account, unreserve_amount);
		}

		// Staked funds need to be unlocked.
		for (account, amount) in account_staked_sums {
			if amount.is_zero() {
				continue
			}
			// Question for reviewers:
			// remove_lock triggers a few
			// `ERROR main runtime::system: Logic error: Unexpected underflow in reducing consumer`
			// errors. are they safe to ignore?
			//
			// I have verified that a non-zero lock always exists before remove_lock is called.
			T::Currency::remove_lock(T::PalletId::get(), &account);
		}

		// Question for reviewers: how do I know the weight of the unreserve & remove_lock calls?
		RocksDbWeight::get().reads_writes(1, 1) + initial_reads_weight
	}

	/// Performs post-upgrade sanity checks:
	///
	/// 1. All expected locks were removed after the migration.
	/// 2. There are no 'hanging' locks for this pallet in Balances.
	/// 3. The reserved balance for each account has been reduced by the expected amount.
	#[cfg(feature = "try-runtime")]
	fn post_upgrade(pre_migration_data_bytes: Vec<u8>) -> Result<(), sp_runtime::TryRuntimeError> {
		use sp_runtime::Saturating;

		let pre_migration_data = PreMigrationData::<T>::decode(&mut &pre_migration_data_bytes[..])
			.map_err(|_| "Failed to decode pre-migration data")?;

		// Get staked and deposited balances as reported by this pallet.
		let (account_deposited_sums, account_staked_sums, _) =
			Self::get_account_deposited_and_staked_sums();

		// Check that all expected locks were removed.
		account_staked_sums.iter().for_each(|(acc, _)| {
			assert_eq!(Self::get_actual_locked_amount(acc.clone()), None, "Lock still exists!");
		});

		// Extra sanity check to ensure there're no 'hanging' locks.
		pallet_balances::Locks::<T>::iter().for_each(|(_, lock_vec)| {
			for lock in lock_vec {
				assert!(lock.id != T::PalletId::get(), "Locks still exist for this pallet!");
			}
		});

		// Check that the reserved balance is reduced by the expected deposited amount.
		for (account, actual_reserved_before) in pre_migration_data.account_reserved_before {
			let actual_reserved_after = T::Currency::reserved_balance(&account);
			let expected_amount_deducted = *account_deposited_sums
				.get(&account)
				.unwrap_or(&Zero::zero())
				.min(&actual_reserved_before);
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
	use crate::tests::{ExtBuilder, Members};

	#[test]
	fn unreserving_deposits_works() {
		ExtBuilder::default().build_and_execute(|| {
			log::info!("{:?}", Members::get());

			// TODO: test
		});
	}

	#[test]
	fn unlocking_stakes_works() {
		ExtBuilder::default().build_and_execute(|| {
			// TODO: test
		});
	}
}
