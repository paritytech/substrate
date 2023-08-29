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

pub mod mutate {
	use crate::traits::{
		fungible::{Inspect, Mutate},
		tokens::{
			DepositConsequence, Fortitude, Precision, Preservation, Provenance, WithdrawConsequence,
		},
	};
	use core::fmt::Debug;
	use sp_arithmetic::traits::AtLeast8BitUnsigned;
	use sp_runtime::traits::{Bounded, Zero};

	/// Test [`Mutate::mint_into`] for successful token minting.
	///
	/// It ensures that account balances and total issuance values are updated correctly after
	/// minting tokens into two distinct accounts.
	pub fn mint_into_success<T, AccountId>()
	where
		T: Mutate<AccountId>,
		<T as Inspect<AccountId>>::Balance: AtLeast8BitUnsigned + Debug,
		AccountId: AtLeast8BitUnsigned,
	{
		let initial_total_issuance = T::total_issuance();
		let initial_active_issuance = T::active_issuance();
		let account_0 = AccountId::from(0);
		let account_1 = AccountId::from(1);

		// Test: Mint an amount into each account
		let amount_0 = T::minimum_balance();
		let amount_1 = T::minimum_balance() + 5.into();
		T::mint_into(&account_0, amount_0).unwrap();
		T::mint_into(&account_1, amount_1).unwrap();

		// Verify: Account balances are updated correctly
		assert_eq!(T::total_balance(&account_0), amount_0);
		assert_eq!(T::total_balance(&account_1), amount_1);
		assert_eq!(T::balance(&account_0), amount_0);
		assert_eq!(T::balance(&account_1), amount_1);

		// Verify: Total issuance is updated correctly
		assert_eq!(T::total_issuance(), initial_total_issuance + amount_0 + amount_1);
		assert_eq!(T::active_issuance(), initial_active_issuance + amount_0 + amount_1);
	}

	/// Test [`Mutate::mint_into`] for overflow prevention.
	///
	/// This test ensures that minting tokens beyond the maximum balance value for an account
	/// returns an error and does not change the account balance or total issuance values.
	pub fn mint_into_overflow<T, AccountId>()
	where
		T: Mutate<AccountId>,
		<T as Inspect<AccountId>>::Balance: AtLeast8BitUnsigned + Debug,
		AccountId: AtLeast8BitUnsigned,
	{
		let initial_total_issuance = T::total_issuance();
		let initial_active_issuance = T::active_issuance();
		let account = AccountId::from(10);
		let amount = T::Balance::max_value() - 5.into() - initial_total_issuance;

		// Mint just below the maximum balance
		T::mint_into(&account, amount).unwrap();

		// Verify: Minting beyond the maximum balance value returns an Err
		T::mint_into(&account, 10.into()).unwrap_err();

		// Verify: The balance did not change
		assert_eq!(T::total_balance(&account), amount);
		assert_eq!(T::balance(&account), amount);

		// Verify: The total issuance did not change
		assert_eq!(T::total_issuance(), initial_total_issuance + amount);
		assert_eq!(T::active_issuance(), initial_active_issuance + amount);
	}

	/// Test [`Mutate::mint_into`] for handling balances below the minimum value.
	///
	/// This test verifies that minting tokens below the minimum balance for an account
	/// returns an error and has no impact on the account balance or total issuance values.
	pub fn mint_into_below_minimum<T, AccountId>()
	where
		T: Mutate<AccountId>,
		<T as Inspect<AccountId>>::Balance: AtLeast8BitUnsigned + Debug,
		AccountId: AtLeast8BitUnsigned,
	{
		// Skip if there is no minimum balance
		if T::minimum_balance() == T::Balance::zero() {
			return
		}

		let initial_total_issuance = T::total_issuance();
		let initial_active_issuance = T::active_issuance();
		let account = AccountId::from(10);
		let amount = T::minimum_balance() - 1.into();

		// Verify: Minting below the minimum balance returns Err
		T::mint_into(&account, amount).unwrap_err();

		// Verify: noop
		assert_eq!(T::total_balance(&account), T::Balance::zero());
		assert_eq!(T::balance(&account), T::Balance::zero());
		assert_eq!(T::total_issuance(), initial_total_issuance);
		assert_eq!(T::active_issuance(), initial_active_issuance);
	}

	/// Test [`Mutate::burn_from`] for successfully burning an exact amount of tokens.
	///
	/// This test checks that burning tokens with [`Precision::Exact`] correctly reduces the account
	/// balance and total issuance values by the burned amount.
	pub fn burn_from_exact_success<T, AccountId>()
	where
		T: Mutate<AccountId>,
		<T as Inspect<AccountId>>::Balance: AtLeast8BitUnsigned + Debug,
		AccountId: AtLeast8BitUnsigned,
	{
		let initial_total_issuance = T::total_issuance();
		let initial_active_issuance = T::active_issuance();

		// Setup account
		let account = AccountId::from(5);
		let initial_balance = T::minimum_balance() + 10.into();
		T::mint_into(&account, initial_balance).unwrap();

		// Test: Burn an exact amount from the account
		let amount_to_burn = T::Balance::from(5);
		let precision = Precision::Exact;
		let force = Fortitude::Polite;
		T::burn_from(&account, amount_to_burn, precision, force).unwrap();

		// Verify: The balance and total issuance should be reduced by the burned amount
		assert_eq!(T::balance(&account), initial_balance - amount_to_burn);
		assert_eq!(T::total_balance(&account), initial_balance - amount_to_burn);
		assert_eq!(T::total_issuance(), initial_total_issuance + initial_balance - amount_to_burn);
		assert_eq!(
			T::active_issuance(),
			initial_active_issuance + initial_balance - amount_to_burn
		);
	}

	/// Test [`Mutate::burn_from`] for successfully burning tokens with [`Precision::BestEffort`].
	///
	/// This test verifies that the burning tokens with best-effort precision correctly reduces the
	/// account balance and total issuance values by the reducible balance when attempting to burn
	/// an amount greater than the reducible balance.
	pub fn burn_from_best_effort_success<T, AccountId>()
	where
		T: Mutate<AccountId>,
		<T as Inspect<AccountId>>::Balance: AtLeast8BitUnsigned + Debug,
		AccountId: AtLeast8BitUnsigned,
	{
		let initial_total_issuance = T::total_issuance();
		let initial_active_issuance = T::active_issuance();

		// Setup account
		let account = AccountId::from(5);
		let initial_balance = T::minimum_balance() + 10.into();
		T::mint_into(&account, initial_balance).unwrap();

		// Get reducible balance
		let force = Fortitude::Polite;
		let reducible_balance = T::reducible_balance(&account, Preservation::Expendable, force);

		// Test: Burn a best effort amount from the account that is greater than the reducible
		// balance
		let amount_to_burn = reducible_balance + 5.into();
		let precision = Precision::BestEffort;
		assert!(amount_to_burn > reducible_balance);
		assert!(amount_to_burn > T::balance(&account));
		T::burn_from(&account, amount_to_burn, precision, force).unwrap();

		// Verify: The balance and total issuance should be reduced by the reducible_balance
		assert_eq!(T::balance(&account), initial_balance - reducible_balance);
		assert_eq!(T::total_balance(&account), initial_balance - reducible_balance);
		assert_eq!(
			T::total_issuance(),
			initial_total_issuance + initial_balance - reducible_balance
		);
		assert_eq!(
			T::active_issuance(),
			initial_active_issuance + initial_balance - reducible_balance
		);
	}

	/// Test [`Mutate::burn_from`] handling of insufficient funds when called with
	/// [`Precision::Exact`].
	///
	/// This test verifies that burning an amount greater than the account's balance with exact
	/// precision returns an error and does not change the account balance or total issuance values.
	pub fn burn_from_exact_insufficient_funds<T, AccountId>()
	where
		T: Mutate<AccountId>,
		<T as Inspect<AccountId>>::Balance: AtLeast8BitUnsigned + Debug,
		AccountId: AtLeast8BitUnsigned,
	{
		// Set up the initial conditions and parameters for the test
		let account = AccountId::from(5);
		let initial_balance = T::minimum_balance() + 10.into();
		T::mint_into(&account, initial_balance).unwrap();
		let initial_total_issuance = T::total_issuance();
		let initial_active_issuance = T::active_issuance();

		// Verify: Burn an amount greater than the account's balance with Exact precision returns
		// Err
		let amount_to_burn = initial_balance + 10.into();
		let precision = Precision::Exact;
		let force = Fortitude::Polite;
		T::burn_from(&account, amount_to_burn, precision, force).unwrap_err();

		// Verify: The balance and total issuance should remain unchanged
		assert_eq!(T::balance(&account), initial_balance);
		assert_eq!(T::total_balance(&account), initial_balance);
		assert_eq!(T::total_issuance(), initial_total_issuance);
		assert_eq!(T::active_issuance(), initial_active_issuance);
	}

	/// Test [`Mutate::restore`] for successful restoration.
	///
	/// This test verifies that restoring an amount into each account updates their balances and the
	/// total issuance values correctly.
	pub fn restore_success<T, AccountId>()
	where
		T: Mutate<AccountId>,
		<T as Inspect<AccountId>>::Balance: AtLeast8BitUnsigned + Debug,
		AccountId: AtLeast8BitUnsigned,
	{
		let account_0 = AccountId::from(0);
		let account_1 = AccountId::from(1);

		// Test: Restore an amount into each account
		let amount_0 = T::minimum_balance();
		let amount_1 = T::minimum_balance() + 5.into();
		let initial_total_issuance = T::total_issuance();
		let initial_active_issuance = T::active_issuance();
		T::restore(&account_0, amount_0).unwrap();
		T::restore(&account_1, amount_1).unwrap();

		// Verify: Account balances are updated correctly
		assert_eq!(T::total_balance(&account_0), amount_0);
		assert_eq!(T::total_balance(&account_1), amount_1);
		assert_eq!(T::balance(&account_0), amount_0);
		assert_eq!(T::balance(&account_1), amount_1);

		// Verify: Total issuance is updated correctly
		assert_eq!(T::total_issuance(), initial_total_issuance + amount_0 + amount_1);
		assert_eq!(T::active_issuance(), initial_active_issuance + amount_0 + amount_1);
	}

	/// Test [`Mutate::restore`] handles balance overflow.
	///
	/// This test verifies that restoring an amount beyond the maximum balance returns an error and
	/// does not change the account balance or total issuance values.
	pub fn restore_overflow<T, AccountId>()
	where
		T: Mutate<AccountId>,
		<T as Inspect<AccountId>>::Balance: AtLeast8BitUnsigned + Debug,
		AccountId: AtLeast8BitUnsigned,
	{
		let initial_total_issuance = T::total_issuance();
		let initial_active_issuance = T::active_issuance();
		let account = AccountId::from(10);
		let amount = T::Balance::max_value() - 5.into() - initial_total_issuance;

		// Restore just below the maximum balance
		T::restore(&account, amount).unwrap();

		// Verify: Restoring beyond the maximum balance returns an Err
		T::restore(&account, 10.into()).unwrap_err();

		// Verify: The balance and total issuance did not change
		assert_eq!(T::total_balance(&account), amount);
		assert_eq!(T::balance(&account), amount);
		assert_eq!(T::total_issuance(), initial_total_issuance + amount);
		assert_eq!(T::active_issuance(), initial_active_issuance + amount);
	}

	/// Test [`Mutate::restore`] handles restoration below the minimum balance.
	///
	/// This test verifies that restoring an amount below the minimum balance returns an error and
	/// does not change the account balance or total issuance values.
	pub fn restore_below_minimum<T, AccountId>()
	where
		T: Mutate<AccountId>,
		<T as Inspect<AccountId>>::Balance: AtLeast8BitUnsigned + Debug,
		AccountId: AtLeast8BitUnsigned,
	{
		// Skip if there is no minimum balance
		if T::minimum_balance() == T::Balance::zero() {
			return
		}

		let account = AccountId::from(10);
		let amount = T::minimum_balance() - 1.into();
		let initial_total_issuance = T::total_issuance();
		let initial_active_issuance = T::active_issuance();

		// Verify: Restoring below the minimum balance returns Err
		T::restore(&account, amount).unwrap_err();

		// Verify: noop
		assert_eq!(T::total_balance(&account), T::Balance::zero());
		assert_eq!(T::balance(&account), T::Balance::zero());
		assert_eq!(T::total_issuance(), initial_total_issuance);
		assert_eq!(T::active_issuance(), initial_active_issuance);
	}

	/// Test [`Mutate::shelve`] for successful shelving.
	///
	/// This test verifies that shelving an amount from an account reduces the account balance and
	/// total issuance values by the shelved amount.
	pub fn shelve_success<T, AccountId>()
	where
		T: Mutate<AccountId>,
		<T as Inspect<AccountId>>::Balance: AtLeast8BitUnsigned + Debug,
		AccountId: AtLeast8BitUnsigned,
	{
		let initial_total_issuance = T::total_issuance();
		let initial_active_issuance = T::active_issuance();

		// Setup account
		let account = AccountId::from(5);
		let initial_balance = T::minimum_balance() + 10.into();

		T::restore(&account, initial_balance).unwrap();

		// Test: Shelve an amount from the account
		let amount_to_shelve = T::Balance::from(5);
		T::shelve(&account, amount_to_shelve).unwrap();

		// Verify: The balance and total issuance should be reduced by the shelved amount
		assert_eq!(T::balance(&account), initial_balance - amount_to_shelve);
		assert_eq!(T::total_balance(&account), initial_balance - amount_to_shelve);
		assert_eq!(
			T::total_issuance(),
			initial_total_issuance + initial_balance - amount_to_shelve
		);
		assert_eq!(
			T::active_issuance(),
			initial_active_issuance + initial_balance - amount_to_shelve
		);
	}

	/// Test [`Mutate::shelve`] handles insufficient funds correctly.
	///
	/// This test verifies that attempting to shelve an amount greater than the account's balance
	/// returns an error and does not change the account balance or total issuance values.
	pub fn shelve_insufficient_funds<T, AccountId>()
	where
		T: Mutate<AccountId>,
		<T as Inspect<AccountId>>::Balance: AtLeast8BitUnsigned + Debug,
		AccountId: AtLeast8BitUnsigned,
	{
		let initial_total_issuance = T::total_issuance();
		let initial_active_issuance = T::active_issuance();

		// Set up the initial conditions and parameters for the test
		let account = AccountId::from(5);
		let initial_balance = T::minimum_balance() + 10.into();
		T::restore(&account, initial_balance).unwrap();

		// Verify: Shelving greater than the balance with Exact precision returns Err
		let amount_to_shelve = initial_balance + 10.into();
		T::shelve(&account, amount_to_shelve).unwrap_err();

		// Verify: The balance and total issuance should remain unchanged
		assert_eq!(T::balance(&account), initial_balance);
		assert_eq!(T::total_balance(&account), initial_balance);
		assert_eq!(T::total_issuance(), initial_total_issuance + initial_balance);
		assert_eq!(T::active_issuance(), initial_active_issuance + initial_balance);
	}

	/// Test [`Mutate::transfer`] for a successful transfer.
	///
	/// This test verifies that transferring an amount between two accounts with updates the account
	/// balances and maintains correct total issuance and active issuance values.
	pub fn transfer_success<T, AccountId>()
	where
		T: Mutate<AccountId>,
		<T as Inspect<AccountId>>::Balance: AtLeast8BitUnsigned + Debug,
		AccountId: AtLeast8BitUnsigned,
	{
		let initial_total_issuance = T::total_issuance();
		let initial_active_issuance = T::active_issuance();
		let account_0 = AccountId::from(0);
		let account_1 = AccountId::from(1);
		let initial_balance = T::minimum_balance() + 10.into();
		T::set_balance(&account_0, initial_balance);
		T::set_balance(&account_1, initial_balance);

		// Test: Transfer an amount from account_0 to account_1
		let transfer_amount = T::Balance::from(3);
		T::transfer(&account_0, &account_1, transfer_amount, Preservation::Expendable).unwrap();

		// Verify: Account balances are updated correctly
		assert_eq!(T::total_balance(&account_0), initial_balance - transfer_amount);
		assert_eq!(T::total_balance(&account_1), initial_balance + transfer_amount);
		assert_eq!(T::balance(&account_0), initial_balance - transfer_amount);
		assert_eq!(T::balance(&account_1), initial_balance + transfer_amount);

		// Verify: Total issuance doesn't change
		assert_eq!(T::total_issuance(), initial_total_issuance + initial_balance * 2.into());
		assert_eq!(T::active_issuance(), initial_active_issuance + initial_balance * 2.into());
	}

	/// Test calling [`Mutate::transfer`] with [`Preservation::Expendable`] correctly transfers the
	/// entire balance.
	///
	/// This test verifies that transferring the entire balance from one account to another with
	/// when preservation is expendable updates the account balances and maintains the total
	/// issuance and active issuance values.
	pub fn transfer_expendable_all<T, AccountId>()
	where
		T: Mutate<AccountId>,
		<T as Inspect<AccountId>>::Balance: AtLeast8BitUnsigned + Debug,
		AccountId: AtLeast8BitUnsigned,
	{
		let initial_total_issuance = T::total_issuance();
		let initial_active_issuance = T::active_issuance();
		let account_0 = AccountId::from(0);
		let account_1 = AccountId::from(1);
		let initial_balance = T::minimum_balance() + 10.into();
		T::set_balance(&account_0, initial_balance);
		T::set_balance(&account_1, initial_balance);

		// Test: Transfer entire balance from account_0 to account_1
		let preservation = Preservation::Expendable;
		let transfer_amount = initial_balance;
		T::transfer(&account_0, &account_1, transfer_amount, preservation).unwrap();

		// Verify: Account balances are updated correctly
		assert_eq!(T::total_balance(&account_0), T::Balance::zero());
		assert_eq!(T::total_balance(&account_1), initial_balance * 2.into());
		assert_eq!(T::balance(&account_0), T::Balance::zero());
		assert_eq!(T::balance(&account_1), initial_balance * 2.into());

		// Verify: Total issuance doesn't change
		assert_eq!(T::total_issuance(), initial_total_issuance + initial_balance * 2.into());
		assert_eq!(T::active_issuance(), initial_active_issuance + initial_balance * 2.into());
	}

	/// Test calling [`Mutate::transfer`] function with [`Preservation::Expendable`] and an amount
	/// that results in some dust.
	///
	/// This test verifies that dust is handled correctly when an account is reaped, with and
	/// without a dust trap.
	///
	/// # Parameters
	///
	/// - dust_trap: An optional account identifier to which dust will be collected. If `None`, dust
	///   is expected to be removed from the total and active issuance.
	pub fn transfer_expendable_dust<T, AccountId>(dust_trap: Option<AccountId>)
	where
		T: Mutate<AccountId>,
		<T as Inspect<AccountId>>::Balance: AtLeast8BitUnsigned + Debug,
		AccountId: AtLeast8BitUnsigned,
	{
		if T::minimum_balance() == T::Balance::zero() {
			return
		}

		let account_0 = AccountId::from(10);
		let account_1 = AccountId::from(20);
		let initial_balance = T::minimum_balance() + 10.into();
		T::set_balance(&account_0, initial_balance);
		T::set_balance(&account_1, initial_balance);

		let initial_total_issuance = T::total_issuance();
		let initial_active_issuance = T::active_issuance();
		let initial_dust_trap_balance = match dust_trap.clone() {
			Some(dust_trap) => T::total_balance(&dust_trap),
			None => T::Balance::zero(),
		};

		// Test: Transfer balance
		let preservation = Preservation::Expendable;
		let transfer_amount = T::Balance::from(11);
		T::transfer(&account_0, &account_1, transfer_amount, preservation).unwrap();

		// Verify: Account balances are updated correctly
		assert_eq!(T::total_balance(&account_0), T::Balance::zero());
		assert_eq!(T::total_balance(&account_1), initial_balance + transfer_amount);
		assert_eq!(T::balance(&account_0), T::Balance::zero());
		assert_eq!(T::balance(&account_1), initial_balance + transfer_amount);

		match dust_trap {
			Some(dust_trap) => {
				// Verify: Total issuance and active issuance don't change
				assert_eq!(T::total_issuance(), initial_total_issuance);
				assert_eq!(T::active_issuance(), initial_active_issuance);
				// Verify: Dust is collected into dust trap
				assert_eq!(
					T::total_balance(&dust_trap),
					initial_dust_trap_balance + T::minimum_balance() - 1.into()
				);
				assert_eq!(
					T::balance(&dust_trap),
					initial_dust_trap_balance + T::minimum_balance() - 1.into()
				);
			},
			None => {
				// Verify: Total issuance and active issuance are reduced by the dust amount
				assert_eq!(
					T::total_issuance(),
					initial_total_issuance - T::minimum_balance() + 1.into()
				);
				assert_eq!(
					T::active_issuance(),
					initial_active_issuance - T::minimum_balance() + 1.into()
				);
			},
		}
	}

	/// Test [`Mutate::transfer`] with [`Preservation::Protect`] and [`Preservation::Preserve`]
	/// transferring the entire balance.
	///
	/// This test verifies that attempting to transfer the entire balance with returns an error when
	/// preservation should not allow it, and the account balances, total issuance, and active
	/// issuance values remain unchanged.
	pub fn transfer_protect_preserve<T, AccountId>()
	where
		T: Mutate<AccountId>,
		<T as Inspect<AccountId>>::Balance: AtLeast8BitUnsigned + Debug,
		AccountId: AtLeast8BitUnsigned,
	{
		// This test means nothing if there is no minimum balance
		if T::minimum_balance() == T::Balance::zero() {
			return
		}

		let initial_total_issuance = T::total_issuance();
		let initial_active_issuance = T::active_issuance();
		let account_0 = AccountId::from(0);
		let account_1 = AccountId::from(1);
		let initial_balance = T::minimum_balance() + 10.into();
		T::set_balance(&account_0, initial_balance);
		T::set_balance(&account_1, initial_balance);

		// Verify: Transfer Protect entire balance from account_0 to account_1 should Err
		let preservation = Preservation::Protect;
		let transfer_amount = initial_balance;
		T::transfer(&account_0, &account_1, transfer_amount, preservation).unwrap_err();

		// Verify: Noop
		assert_eq!(T::total_balance(&account_0), initial_balance);
		assert_eq!(T::total_balance(&account_1), initial_balance);
		assert_eq!(T::balance(&account_0), initial_balance);
		assert_eq!(T::balance(&account_1), initial_balance);
		assert_eq!(T::total_issuance(), initial_total_issuance + initial_balance * 2.into());
		assert_eq!(T::active_issuance(), initial_active_issuance + initial_balance * 2.into());

		// Verify: Transfer Preserve entire balance from account_0 to account_1 should Err
		let preservation = Preservation::Preserve;
		T::transfer(&account_0, &account_1, transfer_amount, preservation).unwrap_err();

		// Verify: Noop
		assert_eq!(T::total_balance(&account_0), initial_balance);
		assert_eq!(T::total_balance(&account_1), initial_balance);
		assert_eq!(T::balance(&account_0), initial_balance);
		assert_eq!(T::balance(&account_1), initial_balance);
		assert_eq!(T::total_issuance(), initial_total_issuance + initial_balance * 2.into());
		assert_eq!(T::active_issuance(), initial_active_issuance + initial_balance * 2.into());
	}

	/// Test [`Mutate::set_balance`] mints balances correctly.
	///
	/// This test verifies that minting a balance using `set_balance` updates the account balance,
	/// total issuance, and active issuance correctly.
	pub fn set_balance_mint_success<T, AccountId>()
	where
		T: Mutate<AccountId>,
		<T as Inspect<AccountId>>::Balance: AtLeast8BitUnsigned + Debug,
		AccountId: AtLeast8BitUnsigned,
	{
		let initial_total_issuance = T::total_issuance();
		let initial_active_issuance = T::active_issuance();
		let account = AccountId::from(10);
		let initial_balance = T::minimum_balance() + 10.into();
		T::mint_into(&account, initial_balance).unwrap();

		// Test: Increase the account balance with set_balance
		let increase_amount: T::Balance = 5.into();
		let new = T::set_balance(&account, initial_balance + increase_amount);

		// Verify: set_balance returned the new balance
		let expected_new = initial_balance + increase_amount;
		assert_eq!(new, expected_new);

		// Verify: Balance and issuance is updated correctly
		assert_eq!(T::total_balance(&account), expected_new);
		assert_eq!(T::balance(&account), expected_new);
		assert_eq!(T::total_issuance(), initial_total_issuance + expected_new);
		assert_eq!(T::active_issuance(), initial_active_issuance + expected_new);
	}

	/// Test [`Mutate::set_balance`] burns balances correctly.
	///
	/// This test verifies that burning a balance using `set_balance` updates the account balance,
	/// total issuance, and active issuance correctly.
	pub fn set_balance_burn_success<T, AccountId>()
	where
		T: Mutate<AccountId>,
		<T as Inspect<AccountId>>::Balance: AtLeast8BitUnsigned + Debug,
		AccountId: AtLeast8BitUnsigned,
	{
		let initial_total_issuance = T::total_issuance();
		let initial_active_issuance = T::active_issuance();
		let account = AccountId::from(10);
		let initial_balance = T::minimum_balance() + 10.into();
		T::mint_into(&account, initial_balance).unwrap();

		// Test: Increase the account balance with set_balance
		let burn_amount: T::Balance = 5.into();
		let new = T::set_balance(&account, initial_balance - burn_amount);

		// Verify: set_balance returned the new balance
		let expected_new = initial_balance - burn_amount;
		assert_eq!(new, expected_new);

		// Verify: Balance and issuance is updated correctly
		assert_eq!(T::total_balance(&account), expected_new);
		assert_eq!(T::balance(&account), expected_new);
		assert_eq!(T::total_issuance(), initial_total_issuance + expected_new);
		assert_eq!(T::active_issuance(), initial_active_issuance + expected_new);
	}

	/// Test [`Inspect::can_deposit`] works correctly returns [`DepositConsequence::Success`]
	/// when depositing an amount that should succeed.
	pub fn can_deposit_success<T, AccountId>()
	where
		T: Mutate<AccountId>,
		<T as Inspect<AccountId>>::Balance: AtLeast8BitUnsigned + Debug,
		AccountId: AtLeast8BitUnsigned,
	{
		let account = AccountId::from(10);
		let initial_balance = T::minimum_balance() + 10.into();
		T::mint_into(&account, initial_balance).unwrap();

		// Test: can_deposit a reasonable amount
		let ret = T::can_deposit(&account, 5.into(), Provenance::Minted);

		// Verify: Returns success
		assert_eq!(ret, DepositConsequence::Success);
	}

	/// Test [`Inspect::can_deposit`] returns [`DepositConsequence::BelowMinimum`] when depositing
	/// below the minimum balance.
	pub fn can_deposit_below_minimum<T, AccountId>()
	where
		T: Mutate<AccountId>,
		<T as Inspect<AccountId>>::Balance: AtLeast8BitUnsigned + Debug,
		AccountId: AtLeast8BitUnsigned,
	{
		// can_deposit always returns Success for amount 0
		if T::minimum_balance() < 2.into() {
			return
		}

		let account = AccountId::from(10);

		// Test: can_deposit below the minimum
		let ret = T::can_deposit(&account, T::minimum_balance() - 1.into(), Provenance::Minted);

		// Verify: Returns success
		assert_eq!(ret, DepositConsequence::BelowMinimum);
	}

	/// Test [`Inspect::can_deposit`] returns [`DepositConsequence::Overflow`] when
	/// depositing an amount that would overflow.
	pub fn can_deposit_overflow<T, AccountId>()
	where
		T: Mutate<AccountId>,
		<T as Inspect<AccountId>>::Balance: AtLeast8BitUnsigned + Debug,
		AccountId: AtLeast8BitUnsigned,
	{
		let account = AccountId::from(10);

		// Test: Try deposit over the max balance
		let initial_balance = T::Balance::max_value() - 5.into() - T::total_issuance();
		T::mint_into(&account, initial_balance).unwrap();
		let ret = T::can_deposit(&account, 10.into(), Provenance::Minted);

		// Verify: Returns success
		assert_eq!(ret, DepositConsequence::Overflow);
	}

	/// Test [`Inspect::can_withdraw`] returns [`WithdrawConsequence::Success`] when withdrawing an
	/// amount that should succeed.
	pub fn can_withdraw_success<T, AccountId>()
	where
		T: Mutate<AccountId>,
		<T as Inspect<AccountId>>::Balance: AtLeast8BitUnsigned + Debug,
		AccountId: AtLeast8BitUnsigned,
	{
		let account = AccountId::from(10);
		let initial_balance = T::minimum_balance() + 10.into();
		T::mint_into(&account, initial_balance).unwrap();

		// Test: can_withdraw a reasonable amount
		let ret = T::can_withdraw(&account, 5.into());

		// Verify: Returns success
		assert_eq!(ret, WithdrawConsequence::Success);
	}

	/// Test [`Inspect::can_withdraw`] returns [`WithdrawConsequence::ReducedToZero`] when
	/// withdrawing an amount that would reduce the account balance below the minimum balance.
	pub fn can_withdraw_reduced_to_zero<T, AccountId>()
	where
		T: Mutate<AccountId>,
		<T as Inspect<AccountId>>::Balance: AtLeast8BitUnsigned + Debug,
		AccountId: AtLeast8BitUnsigned,
	{
		if T::minimum_balance() == T::Balance::zero() {
			return
		}

		let account = AccountId::from(10);
		let initial_balance = T::minimum_balance();
		T::mint_into(&account, initial_balance).unwrap();

		// Verify: can_withdraw below the minimum balance returns ReducedToZero
		let ret = T::can_withdraw(&account, 1.into());
		assert_eq!(ret, WithdrawConsequence::ReducedToZero(T::minimum_balance() - 1.into()));
	}

	/// Test [`Inspect::can_withdraw`] returns [`WithdrawConsequence::BalanceLow`] when withdrawing
	/// an amount that would result in an account balance below the current balance.
	pub fn can_withdraw_balance_low<T, AccountId>()
	where
		T: Mutate<AccountId>,
		<T as Inspect<AccountId>>::Balance: AtLeast8BitUnsigned + Debug,
		AccountId: AtLeast8BitUnsigned,
	{
		if T::minimum_balance() == T::Balance::zero() {
			return
		}

		let account = AccountId::from(10);
		let other_account = AccountId::from(100);
		let initial_balance = T::minimum_balance() + 5.into();
		T::mint_into(&account, initial_balance).unwrap();
		T::mint_into(&other_account, initial_balance * 2.into()).unwrap();

		// Verify: can_withdraw below the account balance returns BalanceLow
		let ret = T::can_withdraw(&account, initial_balance + 1.into());
		assert_eq!(ret, WithdrawConsequence::BalanceLow);
	}

	/// Test [`Inspect::reducible_balance`] returns the full account balance when called with
	/// [`Preservation::Expendable`].
	pub fn reducible_balance_expendable<T, AccountId>()
	where
		T: Mutate<AccountId>,
		<T as Inspect<AccountId>>::Balance: AtLeast8BitUnsigned + Debug,
		AccountId: AtLeast8BitUnsigned,
	{
		let account = AccountId::from(10);
		let initial_balance = T::minimum_balance() + 10.into();
		T::mint_into(&account, initial_balance).unwrap();

		// Verify: reducible_balance returns the full balance
		let ret = T::reducible_balance(&account, Preservation::Expendable, Fortitude::Polite);
		assert_eq!(ret, initial_balance);
	}

	/// Tests [`Inspect::reducible_balance`] returns [`Inspect::balance`] -
	/// [`Inspect::minimum_balance`] when called with either [`Preservation::Protect`] or
	/// [`Preservation::Preserve`].
	pub fn reducible_balance_protect_preserve<T, AccountId>()
	where
		T: Mutate<AccountId>,
		<T as Inspect<AccountId>>::Balance: AtLeast8BitUnsigned + Debug,
		AccountId: AtLeast8BitUnsigned,
	{
		let account = AccountId::from(10);
		let initial_balance = T::minimum_balance() + 10.into();
		T::mint_into(&account, initial_balance).unwrap();

		// Verify: reducible_balance returns the full balance - min balance
		let ret = T::reducible_balance(&account, Preservation::Protect, Fortitude::Polite);
		assert_eq!(ret, initial_balance - T::minimum_balance());
		let ret = T::reducible_balance(&account, Preservation::Preserve, Fortitude::Polite);
		assert_eq!(ret, initial_balance - T::minimum_balance());
	}
}

pub mod unbalanced {
	use crate::traits::{
		fungible::{Inspect, Unbalanced},
		tokens::{Fortitude, Precision, Preservation},
	};
	use core::fmt::Debug;
	use sp_arithmetic::{traits::AtLeast8BitUnsigned, ArithmeticError};
	use sp_runtime::{traits::Bounded, TokenError};

	/// Tests [`Unbalanced::write_balance`].
	///
	/// We don't need to test the Error case for this function, because the trait makes no
	/// assumptions about the ways it can fail. That is completely an implementation detail.
	pub fn write_balance<T, AccountId>()
	where
		T: Unbalanced<AccountId>,
		<T as Inspect<AccountId>>::Balance: AtLeast8BitUnsigned + Debug,
		AccountId: AtLeast8BitUnsigned,
	{
		// Setup some accounts to test varying initial balances
		let account_0_ed = AccountId::from(0);
		let account_1_gt_ed = AccountId::from(1);
		let account_2_empty = AccountId::from(2);
		T::increase_balance(&account_0_ed, T::minimum_balance(), Precision::Exact).unwrap();
		T::increase_balance(&account_1_gt_ed, T::minimum_balance() + 5.into(), Precision::Exact)
			.unwrap();

		// Test setting the balances of each account by gt the minimum balance succeeds with no
		// dust.
		let amount = T::minimum_balance() + 10.into();
		assert_eq!(T::write_balance(&account_0_ed, amount), Ok(None));
		assert_eq!(T::write_balance(&account_1_gt_ed, amount), Ok(None));
		assert_eq!(T::write_balance(&account_2_empty, amount), Ok(None));
		assert_eq!(T::balance(&account_0_ed), amount);
		assert_eq!(T::balance(&account_1_gt_ed), amount);
		assert_eq!(T::balance(&account_2_empty), amount);

		// Test setting the balances of each account to below the minimum balance succeeds with
		// the expected dust.
		// If the minimum balance is 1, then the dust is 0, represented as None.
		// If the minimum balance is >1, then the dust is the remaining balance that will be wiped
		// as the account is reaped.
		let amount = T::minimum_balance() - 1.into();
		if T::minimum_balance() == 1.into() {
			assert_eq!(T::write_balance(&account_0_ed, amount), Ok(None));
			assert_eq!(T::write_balance(&account_1_gt_ed, amount), Ok(None));
			assert_eq!(T::write_balance(&account_2_empty, amount), Ok(None));
		} else if T::minimum_balance() > 1.into() {
			assert_eq!(T::write_balance(&account_0_ed, amount), Ok(Some(amount)));
			assert_eq!(T::write_balance(&account_1_gt_ed, amount), Ok(Some(amount)));
			assert_eq!(T::write_balance(&account_2_empty, amount), Ok(Some(amount)));
		}
	}

	/// Tests [`Unbalanced::decrease_balance`] called with [`Preservation::Expendable`].
	pub fn decrease_balance_expendable<T, AccountId>()
	where
		T: Unbalanced<AccountId>,
		<T as Inspect<AccountId>>::Balance: AtLeast8BitUnsigned + Debug,
		AccountId: AtLeast8BitUnsigned,
	{
		// Setup account with some balance
		let account_0 = AccountId::from(0);
		let account_0_initial_balance = T::minimum_balance() + 10.into();
		T::increase_balance(&account_0, account_0_initial_balance, Precision::Exact).unwrap();

		// Decreasing the balance still above the minimum balance should not reap the account.
		let amount = 1.into();
		assert_eq!(
			T::decrease_balance(
				&account_0,
				amount,
				Precision::Exact,
				Preservation::Expendable,
				Fortitude::Polite,
			),
			Ok(amount),
		);
		assert_eq!(T::balance(&account_0), account_0_initial_balance - amount);

		// Decreasing the balance below funds avalibale should fail when Precision::Exact
		let balance_before = T::balance(&account_0);
		assert_eq!(
			T::decrease_balance(
				&account_0,
				account_0_initial_balance,
				Precision::Exact,
				Preservation::Expendable,
				Fortitude::Polite,
			),
			Err(TokenError::FundsUnavailable.into())
		);
		// Balance unchanged
		assert_eq!(T::balance(&account_0), balance_before);

		// And reap the account when Precision::BestEffort
		assert_eq!(
			T::decrease_balance(
				&account_0,
				account_0_initial_balance,
				Precision::BestEffort,
				Preservation::Expendable,
				Fortitude::Polite,
			),
			Ok(balance_before),
		);
		// Account reaped
		assert_eq!(T::balance(&account_0), 0.into());
	}

	/// Tests [`Unbalanced::decrease_balance`] called with [`Preservation::Preserve`].
	pub fn decrease_balance_preserve<T, AccountId>()
	where
		T: Unbalanced<AccountId>,
		<T as Inspect<AccountId>>::Balance: AtLeast8BitUnsigned + Debug,
		AccountId: AtLeast8BitUnsigned,
	{
		// Setup account with some balance
		let account_0 = AccountId::from(0);
		let account_0_initial_balance = T::minimum_balance() + 10.into();
		T::increase_balance(&account_0, account_0_initial_balance, Precision::Exact).unwrap();

		// Decreasing the balance below the minimum when Precision::Exact should fail.
		let amount = 11.into();
		assert_eq!(
			T::decrease_balance(
				&account_0,
				amount,
				Precision::Exact,
				Preservation::Preserve,
				Fortitude::Polite,
			),
			Err(TokenError::BelowMinimum.into()),
		);
		// Balance should not have changed.
		assert_eq!(T::balance(&account_0), account_0_initial_balance);

		// Decreasing the balance below the minimum when Precision::BestEffort should reduce to
		// minimum balance.
		let amount = 11.into();
		assert_eq!(
			T::decrease_balance(
				&account_0,
				amount,
				Precision::BestEffort,
				Preservation::Preserve,
				Fortitude::Polite,
			),
			Ok(account_0_initial_balance - T::minimum_balance()),
		);
		assert_eq!(T::balance(&account_0), T::minimum_balance());
	}

	/// Tests [`Unbalanced::increase_balance`].
	pub fn increase_balance<T, AccountId>()
	where
		T: Unbalanced<AccountId>,
		<T as Inspect<AccountId>>::Balance: AtLeast8BitUnsigned + Debug,
		AccountId: AtLeast8BitUnsigned,
	{
		let account_0 = AccountId::from(0);
		assert_eq!(T::balance(&account_0), 0.into());

		// Increasing the bal below the ED errors when precision is Exact
		if T::minimum_balance() > 0.into() {
			assert_eq!(
				T::increase_balance(&account_0, T::minimum_balance() - 1.into(), Precision::Exact),
				Err(TokenError::BelowMinimum.into()),
			);
		}
		assert_eq!(T::balance(&account_0), 0.into());

		// Increasing the bal below the ED leaves the balance at zero when precision is BestEffort
		if T::minimum_balance() > 0.into() {
			assert_eq!(
				T::increase_balance(
					&account_0,
					T::minimum_balance() - 1.into(),
					Precision::BestEffort
				),
				Ok(0.into()),
			);
		}
		assert_eq!(T::balance(&account_0), 0.into());

		// Can increase if new bal is >= ED
		assert_eq!(
			T::increase_balance(&account_0, T::minimum_balance(), Precision::Exact),
			Ok(T::minimum_balance()),
		);
		assert_eq!(T::balance(&account_0), T::minimum_balance());
		assert_eq!(T::increase_balance(&account_0, 5.into(), Precision::Exact), Ok(5.into()),);
		assert_eq!(T::balance(&account_0), T::minimum_balance() + 5.into());

		// Increasing by amount that would overflow fails when precision is Exact
		assert_eq!(
			T::increase_balance(&account_0, T::Balance::max_value(), Precision::Exact),
			Err(ArithmeticError::Overflow.into()),
		);

		// Increasing by amount that would overflow saturates when precision is BestEffort
		let balance_before = T::balance(&account_0);
		assert_eq!(
			T::increase_balance(&account_0, T::Balance::max_value(), Precision::BestEffort),
			Ok(T::Balance::max_value() - balance_before),
		);
		assert_eq!(T::balance(&account_0), T::Balance::max_value());
	}

	/// Tests [`Unbalanced::set_total_issuance`].
	pub fn set_total_issuance<T, AccountId>()
	where
		T: Unbalanced<AccountId>,
		<T as Inspect<AccountId>>::Balance: AtLeast8BitUnsigned + Debug,
		AccountId: AtLeast8BitUnsigned,
	{
		T::set_total_issuance(1.into());
		assert_eq!(T::total_issuance(), 1.into());

		T::set_total_issuance(0.into());
		assert_eq!(T::total_issuance(), 0.into());

		T::set_total_issuance(T::minimum_balance());
		assert_eq!(T::total_issuance(), T::minimum_balance());

		T::set_total_issuance(T::minimum_balance() + 5.into());
		assert_eq!(T::total_issuance(), T::minimum_balance() + 5.into());

		if T::minimum_balance() > 0.into() {
			T::set_total_issuance(T::minimum_balance() - 1.into());
			assert_eq!(T::total_issuance(), T::minimum_balance() - 1.into());
		}
	}

	/// Tests [`Unbalanced::deactivate`] and [`Unbalanced::reactivate`].
	pub fn deactivate_and_reactivate<T, AccountId>()
	where
		T: Unbalanced<AccountId>,
		<T as Inspect<AccountId>>::Balance: AtLeast8BitUnsigned + Debug,
		AccountId: AtLeast8BitUnsigned,
	{
		T::set_total_issuance(10.into());
		assert_eq!(T::total_issuance(), 10.into());
		assert_eq!(T::active_issuance(), 10.into());

		T::deactivate(2.into());
		assert_eq!(T::total_issuance(), 10.into());
		assert_eq!(T::active_issuance(), 8.into());

		// Saturates at total_issuance
		T::reactivate(4.into());
		assert_eq!(T::total_issuance(), 10.into());
		assert_eq!(T::active_issuance(), 10.into());

		// Decrements correctly after saturating at total_issuance
		T::deactivate(1.into());
		assert_eq!(T::total_issuance(), 10.into());
		assert_eq!(T::active_issuance(), 9.into());

		// Saturates at zero
		T::deactivate(15.into());
		assert_eq!(T::total_issuance(), 10.into());
		assert_eq!(T::active_issuance(), 0.into());

		// Increments correctly after saturating at zero
		T::reactivate(1.into());
		assert_eq!(T::total_issuance(), 10.into());
		assert_eq!(T::active_issuance(), 1.into());
	}
}

pub mod balanced {
	use crate::traits::{
		fungible::{Balanced, Inspect},
		tokens::{imbalance::Imbalance as ImbalanceT, Fortitude, Precision, Preservation},
	};
	use core::fmt::Debug;
	use frame_support::traits::tokens::fungible::imbalance::{Credit, Debt};
	use sp_arithmetic::{traits::AtLeast8BitUnsigned, ArithmeticError};
	use sp_runtime::{traits::Bounded, TokenError};

	/// Tests issuing and resolving [`Credit`] imbalances with [`Balanced::issue`] and
	/// [`Balanced::resolve`].
	pub fn issue_and_resolve_credit<T, AccountId>()
	where
		T: Balanced<AccountId>,
		<T as Inspect<AccountId>>::Balance: AtLeast8BitUnsigned + Debug,
		AccountId: AtLeast8BitUnsigned,
	{
		let account = AccountId::from(0);
		assert_eq!(T::total_issuance(), 0.into());
		assert_eq!(T::balance(&account), 0.into());

		// Account that doesn't exist yet can't be credited below the minimum balance
		let credit: Credit<AccountId, T> = T::issue(T::minimum_balance() - 1.into());
		// issue temporarily increases total issuance
		assert_eq!(T::total_issuance(), credit.peek());
		match T::resolve(&account, credit) {
			Ok(_) => panic!("Balanced::resolve should have failed"),
			Err(c) => assert_eq!(c.peek(), T::minimum_balance() - 1.into()),
		};
		// Credit was unused and dropped from total issuance
		assert_eq!(T::total_issuance(), 0.into());
		assert_eq!(T::balance(&account), 0.into());

		// Credit account with minimum balance
		let credit: Credit<AccountId, T> = T::issue(T::minimum_balance());
		match T::resolve(&account, credit) {
			Ok(()) => {},
			Err(_) => panic!("resolve failed"),
		};
		assert_eq!(T::total_issuance(), T::minimum_balance());
		assert_eq!(T::balance(&account), T::minimum_balance());

		// Now that account has been created, it can be credited with an amount below the minimum
		// balance.
		let total_issuance_before = T::total_issuance();
		let balance_before = T::balance(&account);
		let amount = T::minimum_balance() - 1.into();
		let credit: Credit<AccountId, T> = T::issue(amount);
		match T::resolve(&account, credit) {
			Ok(()) => {},
			Err(_) => panic!("resolve failed"),
		};
		assert_eq!(T::total_issuance(), total_issuance_before + amount);
		assert_eq!(T::balance(&account), balance_before + amount);

		// Unhandled issuance is dropped from total issuance
		// `let _ = ...` immediately drops the issuance, so everything should be unchanged when
		// logic gets to the assertions.
		let total_issuance_before = T::total_issuance();
		let balance_before = T::balance(&account);
		let _ = T::issue(5.into());
		assert_eq!(T::total_issuance(), total_issuance_before);
		assert_eq!(T::balance(&account), balance_before);
	}

	/// Tests issuing and resolving [`Debt`] imbalances with [`Balanced::rescind`] and
	/// [`Balanced::settle`].
	pub fn rescind_and_settle_debt<T, AccountId>()
	where
		T: Balanced<AccountId>,
		<T as Inspect<AccountId>>::Balance: AtLeast8BitUnsigned + Debug,
		AccountId: AtLeast8BitUnsigned,
	{
		// Credit account with some balance
		let account = AccountId::from(0);
		let initial_bal = T::minimum_balance() + 10.into();
		let credit = T::issue(initial_bal);
		match T::resolve(&account, credit) {
			Ok(()) => {},
			Err(_) => panic!("resolve failed"),
		};
		assert_eq!(T::total_issuance(), initial_bal);
		assert_eq!(T::balance(&account), initial_bal);

		// Rescind some balance
		let rescind_amount = 2.into();
		let debt: Debt<AccountId, T> = T::rescind(rescind_amount);
		assert_eq!(debt.peek(), rescind_amount);
		match T::settle(&account, debt, Preservation::Expendable) {
			Ok(c) => {
				// We settled the full debt and account was not dusted, so there is no left over
				// credit.
				assert_eq!(c.peek(), 0.into());
			},
			Err(_) => panic!("settle failed"),
		};
		assert_eq!(T::total_issuance(), initial_bal - rescind_amount);
		assert_eq!(T::balance(&account), initial_bal - rescind_amount);

		// Unhandled debt is added from total issuance
		// `let _ = ...` immediately drops the debt, so everything should be unchanged when
		// logic gets to the assertions.
		let _ = T::rescind(T::minimum_balance());
		assert_eq!(T::total_issuance(), initial_bal - rescind_amount);
		assert_eq!(T::balance(&account), initial_bal - rescind_amount);

		// Preservation::Preserve will not allow the account to be dusted on settle
		let balance_before = T::balance(&account);
		let total_issuance_before = T::total_issuance();
		let rescind_amount = balance_before - T::minimum_balance() + 1.into();
		let debt: Debt<AccountId, T> = T::rescind(rescind_amount);
		assert_eq!(debt.peek(), rescind_amount);
		// The new debt is temporarily removed from total_issuance
		assert_eq!(T::total_issuance(), total_issuance_before - debt.peek().into());
		match T::settle(&account, debt, Preservation::Preserve) {
			Ok(_) => panic!("Balanced::settle should have failed"),
			Err(d) => assert_eq!(d.peek(), rescind_amount),
		};
		// The debt is added back to total_issuance because it was dropped, leaving the operation a
		// noop.
		assert_eq!(T::total_issuance(), total_issuance_before);
		assert_eq!(T::balance(&account), balance_before);

		// Preservation::Expendable allows the account to be dusted on settle
		let debt: Debt<AccountId, T> = T::rescind(rescind_amount);
		match T::settle(&account, debt, Preservation::Expendable) {
			Ok(c) => {
				// Dusting happens internally, there is no left over credit.
				assert_eq!(c.peek(), 0.into());
			},
			Err(_) => panic!("settle failed"),
		};
		// The account is dusted and debt dropped from total_issuance
		assert_eq!(T::total_issuance(), 0.into());
		assert_eq!(T::balance(&account), 0.into());
	}

	/// Tests [`Balanced::deposit`].
	pub fn deposit<T, AccountId>()
	where
		T: Balanced<AccountId>,
		<T as Inspect<AccountId>>::Balance: AtLeast8BitUnsigned + Debug,
		AccountId: AtLeast8BitUnsigned,
	{
		// Cannot deposit < minimum balance into non-existent account
		let account = AccountId::from(0);
		let amount = T::minimum_balance() - 1.into();
		match T::deposit(&account, amount, Precision::Exact) {
			Ok(_) => panic!("Balanced::deposit should have failed"),
			Err(e) => assert_eq!(e, TokenError::BelowMinimum.into()),
		};
		assert_eq!(T::total_issuance(), 0.into());
		assert_eq!(T::balance(&account), 0.into());

		// Can deposit minimum balance into non-existent account
		let amount = T::minimum_balance();
		match T::deposit(&account, amount, Precision::Exact) {
			Ok(d) => assert_eq!(d.peek(), amount),
			Err(_) => panic!("Balanced::deposit failed"),
		};
		assert_eq!(T::total_issuance(), amount);
		assert_eq!(T::balance(&account), amount);

		// Depositing amount that would overflow when Precision::Exact fails and is a noop
		let amount = T::Balance::max_value();
		let balance_before = T::balance(&account);
		let total_issuance_before = T::total_issuance();
		match T::deposit(&account, amount, Precision::Exact) {
			Ok(_) => panic!("Balanced::deposit should have failed"),
			Err(e) => assert_eq!(e, ArithmeticError::Overflow.into()),
		};
		assert_eq!(T::total_issuance(), total_issuance_before);
		assert_eq!(T::balance(&account), balance_before);

		// Depositing amount that would overflow when Precision::BestEffort saturates
		match T::deposit(&account, amount, Precision::BestEffort) {
			Ok(d) => assert_eq!(d.peek(), T::Balance::max_value() - balance_before),
			Err(_) => panic!("Balanced::deposit failed"),
		};
		assert_eq!(T::total_issuance(), T::Balance::max_value());
		assert_eq!(T::balance(&account), T::Balance::max_value());
	}

	/// Tests [`Balanced::withdraw`].
	pub fn withdraw<T, AccountId>()
	where
		T: Balanced<AccountId>,
		<T as Inspect<AccountId>>::Balance: AtLeast8BitUnsigned + Debug,
		AccountId: AtLeast8BitUnsigned,
	{
		let account = AccountId::from(0);

		// Init an account with some balance
		let initial_balance = T::minimum_balance() + 10.into();
		match T::deposit(&account, initial_balance, Precision::Exact) {
			Ok(_) => {},
			Err(_) => panic!("Balanced::deposit failed"),
		};
		assert_eq!(T::total_issuance(), initial_balance);
		assert_eq!(T::balance(&account), initial_balance);

		// Withdrawing an amount smaller than the balance works when Precision::Exact
		let amount = 1.into();
		match T::withdraw(
			&account,
			amount,
			Precision::Exact,
			Preservation::Expendable,
			Fortitude::Polite,
		) {
			Ok(c) => assert_eq!(c.peek(), amount),
			Err(_) => panic!("withdraw failed"),
		};
		assert_eq!(T::total_issuance(), initial_balance - amount);
		assert_eq!(T::balance(&account), initial_balance - amount);

		// Withdrawing an amount greater than the balance fails when Precision::Exact
		let balance_before = T::balance(&account);
		let amount = balance_before + 1.into();
		match T::withdraw(
			&account,
			amount,
			Precision::Exact,
			Preservation::Expendable,
			Fortitude::Polite,
		) {
			Ok(_) => panic!("should have failed"),
			Err(e) => assert_eq!(e, TokenError::FundsUnavailable.into()),
		};
		assert_eq!(T::total_issuance(), balance_before);
		assert_eq!(T::balance(&account), balance_before);

		// Withdrawing an amount greater than the balance works when Precision::BestEffort
		let balance_before = T::balance(&account);
		let amount = balance_before + 1.into();
		match T::withdraw(
			&account,
			amount,
			Precision::BestEffort,
			Preservation::Expendable,
			Fortitude::Polite,
		) {
			Ok(c) => assert_eq!(c.peek(), balance_before),
			Err(_) => panic!("withdraw failed"),
		};
		assert_eq!(T::total_issuance(), 0.into());
		assert_eq!(T::balance(&account), 0.into());
	}

	/// Tests [`Balanced::pair`].
	pub fn pair<T, AccountId>()
	where
		T: Balanced<AccountId>,
		<T as Inspect<AccountId>>::Balance: AtLeast8BitUnsigned + Debug,
		AccountId: AtLeast8BitUnsigned,
	{
		// Pair zero balance works
		let (credit, debt) = T::pair(0.into());
		assert_eq!(debt.peek(), 0.into());
		assert_eq!(credit.peek(), 0.into());

		// Pair with non-zero balance: the credit and debt cancel each other out
		let balance = 10.into();
		let (credit, debt) = T::pair(balance);
		assert_eq!(credit.peek(), balance);
		assert_eq!(debt.peek(), balance);

		// Pair with max balance: the credit and debt still cancel each other out
		let balance = T::Balance::max_value() - 1.into();
		let (debt, credit) = T::pair(balance);
		assert_eq!(debt.peek(), balance);
		assert_eq!(credit.peek(), balance);
	}
}
