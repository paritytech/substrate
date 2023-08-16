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

use core::iter::Sum;
use frame_support::{
	pallet_prelude::ValueQuery,
	storage_alias,
	traits::{Currency, LockIdentifier, LockableCurrency, OnRuntimeUpgrade, ReservableCurrency},
	weights::RuntimeDbWeight,
	Parameter, Twox64Concat,
};
use sp_core::Get;
use sp_runtime::traits::Zero;
use sp_std::{collections::btree_map::BTreeMap, vec::Vec};

const LOG_TARGET: &str = "elections_phragmen::migrations::unlock_and_unreserve_all_funds";

type BalanceOf<T> =
	<<T as UnlockConfig>::Currency as Currency<<T as UnlockConfig>::AccountId>>::Balance;

/// The configuration for [`UnlockAndUnreserveAllFunds`].
pub trait UnlockConfig: 'static {
	/// The account ID used in the runtime.
	type AccountId: Parameter + Ord;
	/// The currency type used in the runtime.
	///
	/// Should match the currency type previously used for the pallet, if applicable.
	type Currency: LockableCurrency<Self::AccountId> + ReservableCurrency<Self::AccountId>;
	/// The name of the pallet as previously configured in
	/// [`construct_runtime!`](frame_support::construct_runtime).
	type PalletName: Get<&'static str>;
	/// The maximum number of votes per voter as configured previously in the previous runtime.
	type MaxVotesPerVoter: Get<u32>;
	/// Identifier for the elections-phragmen pallet's lock, as previously configured in the
	/// runtime.
	type PalletId: Get<LockIdentifier>;
	/// The DB weight as configured in the runtime to calculate the correct weight.
	type DbWeight: Get<RuntimeDbWeight>;
	/// The block number as configured in the runtime.
	type BlockNumber: Parameter + Zero + Copy + Ord;
}

#[storage_alias(dynamic)]
type Members<T: UnlockConfig> = StorageValue<
	<T as UnlockConfig>::PalletName,
	Vec<crate::SeatHolder<<T as UnlockConfig>::AccountId, BalanceOf<T>>>,
	ValueQuery,
>;

#[storage_alias(dynamic)]
type RunnersUp<T: UnlockConfig> = StorageValue<
	<T as UnlockConfig>::PalletName,
	Vec<crate::SeatHolder<<T as UnlockConfig>::AccountId, BalanceOf<T>>>,
	ValueQuery,
>;

#[storage_alias(dynamic)]
type Candidates<T: UnlockConfig> = StorageValue<
	<T as UnlockConfig>::PalletName,
	Vec<(<T as UnlockConfig>::AccountId, BalanceOf<T>)>,
	ValueQuery,
>;

#[storage_alias(dynamic)]
type Voting<T: UnlockConfig> = StorageMap<
	<T as UnlockConfig>::PalletName,
	Twox64Concat,
	<T as UnlockConfig>::AccountId,
	crate::Voter<<T as UnlockConfig>::AccountId, BalanceOf<T>>,
	ValueQuery,
>;

/// A migration that unreserves all deposit and unlocks all stake held in the context of this
/// pallet.
///
/// Useful to prevent funds from being locked up when the pallet is being deprecated.
///
/// The pallet should be made inoperable before this migration is run.
///
/// (See also [`RemovePallet`][frame_support::migrations::RemovePallet])
pub struct UnlockAndUnreserveAllFunds<T: UnlockConfig>(sp_std::marker::PhantomData<T>);

impl<T: UnlockConfig> UnlockAndUnreserveAllFunds<T> {
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
	/// * `frame_support::weights::Weight`: The weight of reading the storage.
	fn get_account_deposited_and_staked_sums() -> (
		BTreeMap<T::AccountId, BalanceOf<T>>,
		BTreeMap<T::AccountId, BalanceOf<T>>,
		frame_support::weights::Weight,
	) {
		use sp_runtime::Saturating;

		let members = Members::<T>::get();
		let runner_ups = RunnersUp::<T>::get();
		let candidates = Candidates::<T>::get();

		// Get the total amount deposited (Members, RunnerUps, Candidates and Voters all can have
		// deposits).
		let account_deposited_sums: BTreeMap<T::AccountId, BalanceOf<T>> = members
			// Massage all data structures into (account_id, deposit) tuples.
			.iter()
			.chain(runner_ups.iter())
			.map(|member| (member.who.clone(), member.deposit))
			.chain(candidates.iter().map(|(candidate, amount)| (candidate.clone(), *amount)))
			.chain(
				Voting::<T>::iter().map(|(account_id, voter)| (account_id.clone(), voter.deposit)),
			)
			// Finally, aggregate the tuples into a Map.
			.fold(BTreeMap::new(), |mut acc, (id, deposit)| {
				acc.entry(id.clone()).or_insert(Zero::zero()).saturating_accrue(deposit);
				acc
			});

		// Get the total amount staked (only Voters stake) and count the number of voters.
		let mut voters_len = 0;
		let account_staked_sums: BTreeMap<T::AccountId, BalanceOf<T>> = Voting::<T>::iter()
			.map(|(account_id, voter)| (account_id.clone(), voter.stake))
			.fold(BTreeMap::new(), |mut acc, (id, stake)| {
				voters_len.saturating_accrue(1);
				acc.entry(id.clone()).or_insert(Zero::zero()).saturating_accrue(stake);
				acc
			});

		(
			account_deposited_sums,
			account_staked_sums,
			T::DbWeight::get().reads(
				members
					.len()
					.saturating_add(runner_ups.len())
					.saturating_add(candidates.len())
					.saturating_add(voters_len.saturating_mul(T::MaxVotesPerVoter::get() as usize))
					as u64,
			),
		)
	}
}

impl<T: UnlockConfig> OnRuntimeUpgrade for UnlockAndUnreserveAllFunds<T>
where
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
		use codec::Encode;
		use sp_std::collections::btree_set::BTreeSet;

		// Get staked and deposited balances as reported by this pallet.
		let (account_deposited_sums, account_staked_sums, _) =
			Self::get_account_deposited_and_staked_sums();

		let all_accounts: BTreeSet<T::AccountId> = account_staked_sums
			.keys()
			.chain(account_deposited_sums.keys())
			.cloned()
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

		// Print some summary stats.
		let total_stake_to_unlock = account_staked_sums.clone().into_values().sum::<BalanceOf<T>>();
		let total_deposits_to_unreserve =
			account_deposited_sums.clone().into_values().sum::<BalanceOf<T>>();
		log::info!(target: LOG_TARGET, "Total accounts: {:?}", all_accounts.len());
		log::info!(target: LOG_TARGET, "Total stake to unlock: {:?}", total_stake_to_unlock);
		log::info!(
			target: LOG_TARGET,
			"Total deposit to unreserve: {:?}",
			total_deposits_to_unreserve
		);
		if bugged_deposits > 0 {
			log::warn!(
				target: LOG_TARGET,
				"Bugged deposits: {}/{}",
				bugged_deposits,
				all_accounts.len()
			);
		}

		Ok(account_reserved_before.encode())
	}

	/// Executes the migration.
	///
	/// Steps:
	/// 1. Retrieves the deposit and stake amounts from the pallet.
	/// 2. Unreserves the deposited funds for each account.
	/// 3. Unlocks the staked funds for each account.
	fn on_runtime_upgrade() -> frame_support::weights::Weight {
		// Get staked and deposited balances as reported by this pallet.
		let (account_deposited_sums, account_staked_sums, initial_reads) =
			Self::get_account_deposited_and_staked_sums();

		// Deposited funds need to be unreserved.
		for (account, unreserve_amount) in account_deposited_sums.iter() {
			if unreserve_amount.is_zero() {
				log::warn!(target: LOG_TARGET, "Unexpected zero amount to unreserve");
				continue
			}
			T::Currency::unreserve(&account, *unreserve_amount);
		}

		// Staked funds need to be unlocked.
		for (account, amount) in account_staked_sums.iter() {
			if amount.is_zero() {
				log::warn!(target: LOG_TARGET, "Unexpected zero amount to unlock");
				continue
			}
			T::Currency::remove_lock(T::PalletId::get(), account);
		}

		T::DbWeight::get()
			.reads_writes(
				(account_deposited_sums.len().saturating_add(account_staked_sums.len())) as u64,
				(account_deposited_sums.len().saturating_add(account_staked_sums.len())) as u64,
			)
			.saturating_add(initial_reads)
	}

	/// Performs post-upgrade sanity checks:
	///
	/// 1. All expected locks were removed after the migration.
	/// 2. The reserved balance for each account has been reduced by the expected amount.
	#[cfg(feature = "try-runtime")]
	fn post_upgrade(
		account_reserved_before_bytes: Vec<u8>,
	) -> Result<(), sp_runtime::TryRuntimeError> {
		use codec::Decode;
		use sp_runtime::Saturating;

		let account_reserved_before =
			BTreeMap::<T::AccountId, BalanceOf<T>>::decode(&mut &account_reserved_before_bytes[..])
				.map_err(|_| "Failed to decode account_reserved_before_bytes")?;

		// Get deposited balances as reported by this pallet.
		let (account_deposited_sums, _, _) = Self::get_account_deposited_and_staked_sums();

		// Check that the reserved balance is reduced by the expected deposited amount.
		for (account, actual_reserved_before) in account_reserved_before {
			let actual_reserved_after = T::Currency::reserved_balance(&account);
			let expected_amount_deducted = *account_deposited_sums
				.get(&account)
				.unwrap_or(&Zero::zero())
				// .min here to handle bugged deposits where actual_reserved_before is less than the
				// amount the pallet reports is reserved
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

#[cfg(all(feature = "try-runtime", test))]
mod test {
	use super::*;
	use crate::{
		tests::{Balances, ElectionsPhragmenPalletId, ExtBuilder, PhragmenMaxVoters, Test},
		Candidates, Members, RunnersUp, SeatHolder, Voter, Voting,
	};
	use frame_support::{
		assert_ok, parameter_types,
		traits::{Currency, OnRuntimeUpgrade, ReservableCurrency, WithdrawReasons},
	};
	use frame_system::pallet_prelude::BlockNumberFor;

	parameter_types! {
		const PalletName: &'static str = "Elections";
	}

	struct UnlockConfigImpl;
	impl super::UnlockConfig for UnlockConfigImpl {
		type Currency = Balances;
		type AccountId = u64;
		type BlockNumber = BlockNumberFor<Test>;
		type DbWeight = ();
		type PalletName = PalletName;
		type MaxVotesPerVoter = PhragmenMaxVoters;
		type PalletId = ElectionsPhragmenPalletId;
	}

	#[test]
	fn unreserve_works_for_candidate() {
		let candidate = 10;
		let deposit = 100;
		let initial_reserved = 15;
		let initial_balance = 100_000;
		ExtBuilder::default().build_and_execute(|| {
			// Set up initial state.
			<Test as crate::Config>::Currency::make_free_balance_be(&candidate, initial_balance);
			assert_ok!(<Test as crate::Config>::Currency::reserve(&candidate, initial_reserved));
			Candidates::<Test>::set(vec![(candidate, deposit)]);
			assert_ok!(<Test as crate::Config>::Currency::reserve(&candidate, deposit));

			// Sanity check: ensure initial Balance state was set up correctly.
			assert_eq!(
				<Test as crate::Config>::Currency::reserved_balance(&candidate),
				deposit + initial_reserved
			);

			// Run the migration.
			let bytes = UnlockAndUnreserveAllFunds::<UnlockConfigImpl>::pre_upgrade()
				.unwrap_or_else(|e| panic!("pre_upgrade failed: {:?}", e));
			UnlockAndUnreserveAllFunds::<UnlockConfigImpl>::on_runtime_upgrade();
			assert_ok!(UnlockAndUnreserveAllFunds::<UnlockConfigImpl>::post_upgrade(bytes));

			// Assert the candidate reserved balance was reduced by the expected amount.
			assert_eq!(
				<Test as crate::Config>::Currency::reserved_balance(&candidate),
				initial_reserved
			);
		});
	}

	#[test]
	fn unreserve_works_for_runner_up() {
		let runner_up = 10;
		let deposit = 100;
		let initial_reserved = 15;
		let initial_balance = 100_000;
		ExtBuilder::default().build_and_execute(|| {
			// Set up initial state.
			<Test as crate::Config>::Currency::make_free_balance_be(&runner_up, initial_balance);
			assert_ok!(<Test as crate::Config>::Currency::reserve(&runner_up, initial_reserved));
			RunnersUp::<Test>::set(vec![SeatHolder { who: runner_up, deposit, stake: 10 }]);
			assert_ok!(<Test as crate::Config>::Currency::reserve(&runner_up, deposit));

			// Sanity check: ensure initial Balance state was set up correctly.
			assert_eq!(
				<Test as crate::Config>::Currency::reserved_balance(&runner_up),
				deposit + initial_reserved
			);

			// Run the migration.
			let bytes = UnlockAndUnreserveAllFunds::<UnlockConfigImpl>::pre_upgrade()
				.unwrap_or_else(|e| panic!("pre_upgrade failed: {:?}", e));
			UnlockAndUnreserveAllFunds::<UnlockConfigImpl>::on_runtime_upgrade();
			assert_ok!(UnlockAndUnreserveAllFunds::<UnlockConfigImpl>::post_upgrade(bytes));

			// Assert the reserved balance was reduced by the expected amount.
			assert_eq!(
				<Test as crate::Config>::Currency::reserved_balance(&runner_up),
				initial_reserved
			);
		});
	}

	#[test]
	fn unreserve_works_for_member() {
		let member = 10;
		let deposit = 100;
		let initial_reserved = 15;
		let initial_balance = 100_000;
		ExtBuilder::default().build_and_execute(|| {
			// Set up initial state.
			<Test as crate::Config>::Currency::make_free_balance_be(&member, initial_balance);
			assert_ok!(<Test as crate::Config>::Currency::reserve(&member, initial_reserved));
			Members::<Test>::set(vec![SeatHolder { who: member, deposit, stake: 10 }]);
			assert_ok!(<Test as crate::Config>::Currency::reserve(&member, deposit));

			// Sanity check: ensure initial Balance state was set up correctly.
			assert_eq!(
				<Test as crate::Config>::Currency::reserved_balance(&member),
				deposit + initial_reserved
			);

			// Run the migration.
			let bytes = UnlockAndUnreserveAllFunds::<UnlockConfigImpl>::pre_upgrade()
				.unwrap_or_else(|e| panic!("pre_upgrade failed: {:?}", e));
			UnlockAndUnreserveAllFunds::<UnlockConfigImpl>::on_runtime_upgrade();
			assert_ok!(UnlockAndUnreserveAllFunds::<UnlockConfigImpl>::post_upgrade(bytes));

			// Assert the reserved balance was reduced by the expected amount.
			assert_eq!(
				<Test as crate::Config>::Currency::reserved_balance(&member),
				initial_reserved
			);
		});
	}

	#[test]
	fn unlock_and_unreserve_works_for_voter() {
		let voter = 10;
		let deposit = 100;
		let initial_reserved = 15;
		let initial_locks = vec![(b"somethin", 10)];
		let stake = 25;
		let initial_balance = 100_000;
		ExtBuilder::default().build_and_execute(|| {
			let pallet_id = <Test as crate::Config>::PalletId::get();

			// Set up initial state.
			<Test as crate::Config>::Currency::make_free_balance_be(&voter, initial_balance);
			assert_ok!(<Test as crate::Config>::Currency::reserve(&voter, initial_reserved));
			for lock in initial_locks.clone() {
				<Test as crate::Config>::Currency::set_lock(
					*lock.0,
					&voter,
					lock.1,
					WithdrawReasons::all(),
				);
			}
			Voting::<Test>::insert(voter, Voter { votes: vec![], deposit, stake });
			assert_ok!(<Test as crate::Config>::Currency::reserve(&voter, deposit));
			<Test as crate::Config>::Currency::set_lock(
				<Test as crate::Config>::PalletId::get(),
				&voter,
				stake,
				WithdrawReasons::all(),
			);

			// Sanity check: ensure initial Balance state was set up correctly.
			assert_eq!(
				<Test as crate::Config>::Currency::reserved_balance(&voter),
				deposit + initial_reserved
			);
			let mut voter_all_locks = initial_locks.clone();
			voter_all_locks.push((&pallet_id, stake));
			assert_eq!(
				<Test as crate::Config>::Currency::locks(&voter)
					.iter()
					.map(|lock| (&lock.id, lock.amount))
					.collect::<Vec<_>>(),
				voter_all_locks
			);

			// Run the migration.
			let bytes = UnlockAndUnreserveAllFunds::<UnlockConfigImpl>::pre_upgrade()
				.unwrap_or_else(|e| panic!("pre_upgrade failed: {:?}", e));
			UnlockAndUnreserveAllFunds::<UnlockConfigImpl>::on_runtime_upgrade();
			assert_ok!(UnlockAndUnreserveAllFunds::<UnlockConfigImpl>::post_upgrade(bytes));

			// Assert the voter lock was removed and the reserved balance was reduced by the
			// expected amount.
			assert_eq!(
				<Test as crate::Config>::Currency::reserved_balance(&voter),
				initial_reserved
			);
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
