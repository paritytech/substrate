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
use frame_support::traits::{OnRuntimeUpgrade, ReservableCurrency};
use pallet_treasury::BalanceOf;
use sp_runtime::{traits::Zero, Saturating};
use sp_std::collections::btree_map::BTreeMap;

#[cfg(feature = "try-runtime")]
use sp_std::vec::Vec;

/// A migration that unreserves all tip deposits.
///
/// Useful to prevent funds from being locked up when the pallet is deprecated.
///
/// The pallet should be made inoperable before or immediately after this migration is run.
///
/// (See also the `RemovePallet` migration in `frame/support/src/migrations.rs`)
pub struct UnreserveDeposits<T: crate::Config<I>, I: 'static>(sp_std::marker::PhantomData<(T, I)>);

impl<T: crate::Config<I>, I: 'static> UnreserveDeposits<T, I> {
	/// Calculates and returns the total amount reserved by each account by this pallet from open
	/// tips.
	///
	/// # Returns
	///
	/// * `BTreeMap<T::AccountId, T::Balance>`: Map of account IDs to their respective total
	///   reserved balance by this pallet
	/// * `frame_support::weights::Weight`: The weight of this operation.
	fn get_deposits() -> (BTreeMap<T::AccountId, BalanceOf<T, I>>, frame_support::weights::Weight) {
		use frame_support::traits::Get;

		let mut tips_len = 0;
		let account_deposits: BTreeMap<T::AccountId, BalanceOf<T, I>> = crate::Tips::<T, I>::iter()
			.map(|(_hash, open_tip)| open_tip)
			.fold(BTreeMap::new(), |mut acc, tip| {
				// Count the total number of tips
				tips_len.saturating_accrue(1);

				// Add the balance to the account's existing deposit in the accumulator
				acc.entry(tip.finder).or_insert(Zero::zero()).saturating_accrue(tip.deposit);
				acc
			});

		(account_deposits, T::DbWeight::get().reads(tips_len))
	}
}

impl<T: crate::Config<I>, I: 'static> OnRuntimeUpgrade for UnreserveDeposits<T, I>
where
	BalanceOf<T, I>: Sum,
{
	/// Gets the actual reserved amount for each account before the migration, performs integrity
	/// checks and prints some summary information.
	///
	/// Steps:
	/// 1. Gets the deposited balances for each account stored in this pallet.
	/// 2. Collects actual pre-migration reserved balances for each account.
	/// 3. Checks the integrity of the deposited balances.
	/// 4. Prints summary statistics about the state to be migrated.
	/// 5. Returns the pre-migration actual reserved balance for each account that will
	/// be part of the migration.
	///
	/// Fails with a `TryRuntimeError` if somehow the amount reserved by this pallet is greater than
	/// the actual total reserved amount for any accounts.
	#[cfg(feature = "try-runtime")]
	fn pre_upgrade() -> Result<Vec<u8>, sp_runtime::TryRuntimeError> {
		use codec::Encode;
		use frame_support::ensure;

		// Get the Tips pallet view of balances it has reserved
		let (account_deposits, _) = Self::get_deposits();

		// Get the actual amounts reserved for accounts with open tips
		let account_reserved_before: BTreeMap<T::AccountId, BalanceOf<T, I>> = account_deposits
			.keys()
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

		// Print some summary stats
		let total_deposits_to_unreserve =
			account_deposits.clone().into_values().sum::<BalanceOf<T, I>>();
		log::info!("Total accounts: {}", account_deposits.keys().count());
		log::info!("Total amount to unreserve: {:?}", total_deposits_to_unreserve);

		// Return the actual amount reserved before the upgrade to verify integrity of the upgrade
		// in the post_upgrade hook.
		Ok(account_reserved_before.encode())
	}

	/// Executes the migration, unreserving funds that are locked in Tip deposits.
	fn on_runtime_upgrade() -> frame_support::weights::Weight {
		use frame_support::traits::Get;

		// Get staked and deposited balances as reported by this pallet.
		let (account_deposits, initial_reads) = Self::get_deposits();

		// Deposited funds need to be unreserved.
		for (account, unreserve_amount) in account_deposits.iter() {
			if unreserve_amount.is_zero() {
				continue
			}
			T::Currency::unreserve(&account, *unreserve_amount);
		}

		T::DbWeight::get()
			.reads_writes(account_deposits.len() as u64, account_deposits.len() as u64)
			.saturating_add(initial_reads)
	}

	/// Verifies that the account reserved balances were reduced by the actual expected amounts.
	#[cfg(feature = "try-runtime")]
	fn post_upgrade(
		account_reserved_before_bytes: Vec<u8>,
	) -> Result<(), sp_runtime::TryRuntimeError> {
		use codec::Decode;

		let account_reserved_before = BTreeMap::<T::AccountId, BalanceOf<T, I>>::decode(
			&mut &account_reserved_before_bytes[..],
		)
		.map_err(|_| "Failed to decode account_reserved_before_bytes")?;

		// Get deposited balances as reported by this pallet.
		let (account_deposits, _) = Self::get_deposits();

		// Check that the reserved balance is reduced by the expected deposited amount.
		for (account, actual_reserved_before) in account_reserved_before {
			let actual_reserved_after = T::Currency::reserved_balance(&account);
			let expected_amount_deducted = *account_deposits
				.get(&account)
				.expect("account deposit must exist to be in account_reserved_before, qed");
			let expected_reserved_after =
				actual_reserved_before.saturating_sub(expected_amount_deducted);

			if actual_reserved_after != expected_reserved_after {
				log::error!(
					"Reserved balance for {:?} is incorrect. actual before: {:?}, actual after, {:?}, expected deducted: {:?}",
					account,
					actual_reserved_before,
					actual_reserved_after,
					expected_amount_deducted
				);
				return Err("Reserved balance is incorrect".into())
			}
		}

		Ok(())
	}
}

#[cfg(all(feature = "try-runtime", test))]
mod test {
	use super::*;
	use crate::{
		migrations::unreserve_deposits::UnreserveDeposits,
		tests::{new_test_ext, RuntimeOrigin, Test, Tips},
	};
	use frame_support::{assert_ok, traits::TypedGet};

	#[test]
	fn unreserve_all_funds_works() {
		let tipper_0 = 0;
		let tipper_1 = 1;
		let tipper_0_initial_reserved = 0;
		let tipper_1_initial_reserved = 5;
		let recipient = 100;
		let tip_0_reason = b"what_is_really_not_awesome".to_vec();
		let tip_1_reason = b"pineapple_on_pizza".to_vec();
		new_test_ext().execute_with(|| {
			// Set up
			assert_ok!(<Test as pallet_treasury::Config>::Currency::reserve(
				&tipper_0,
				tipper_0_initial_reserved
			));
			assert_ok!(<Test as pallet_treasury::Config>::Currency::reserve(
				&tipper_1,
				tipper_1_initial_reserved
			));

			// Make some tips
			assert_ok!(Tips::report_awesome(
				RuntimeOrigin::signed(tipper_0),
				tip_0_reason.clone(),
				recipient
			));
			assert_ok!(Tips::report_awesome(
				RuntimeOrigin::signed(tipper_1),
				tip_1_reason.clone(),
				recipient
			));

			// Verify the expected amount is reserved
			assert_eq!(
				<Test as pallet_treasury::Config>::Currency::reserved_balance(&tipper_0),
				tipper_0_initial_reserved +
					<Test as crate::Config>::TipReportDepositBase::get() +
					<Test as crate::Config>::DataDepositPerByte::get() *
						tip_0_reason.len() as u64
			);
			assert_eq!(
				<Test as pallet_treasury::Config>::Currency::reserved_balance(&tipper_1),
				tipper_1_initial_reserved +
					<Test as crate::Config>::TipReportDepositBase::get() +
					<Test as crate::Config>::DataDepositPerByte::get() *
						tip_1_reason.len() as u64
			);

			// Execute the migration
			let bytes = match UnreserveDeposits::<Test, ()>::pre_upgrade() {
				Ok(bytes) => bytes,
				Err(e) => panic!("pre_upgrade failed: {:?}", e),
			};
			UnreserveDeposits::<Test, ()>::on_runtime_upgrade();
			assert_ok!(UnreserveDeposits::<Test, ()>::post_upgrade(bytes));

			// Check the deposits were were unreserved
			assert_eq!(
				<Test as pallet_treasury::Config>::Currency::reserved_balance(&tipper_0),
				tipper_0_initial_reserved
			);
			assert_eq!(
				<Test as pallet_treasury::Config>::Currency::reserved_balance(&tipper_1),
				tipper_1_initial_reserved
			);
		});
	}
}
