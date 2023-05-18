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

use crate::traits::{
	fungible::{Inspect, Mutate},
	tokens::{
		DepositConsequence, Fortitude, Precision, Preservation, Provenance, WithdrawConsequence,
	},
};
use core::fmt::Debug;
use sp_arithmetic::traits::AtLeast8BitUnsigned;
use sp_runtime::traits::{Bounded, Zero};

/// Test the `mint_into` function for successful token minting.
///
/// This test checks the `mint_into` function in the `Mutate` trait implementation for type `T`.
/// It ensures that account balances and total issuance values are updated correctly after minting
/// tokens into two distinct accounts.
///
/// # Type Parameters
///
/// ```text
/// - `T`: Implements `Mutate<AccountId>`.
/// - `AccountId`: Account identifier implementing `AtLeast8BitUnsigned`.
/// ```
pub fn mint_into_success<T, AccountId>(_dust_trap: Option<AccountId>)
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

/// Test the `mint_into` function for overflow prevention.
///
/// This test ensures that minting tokens beyond the maximum balance value for an account
/// returns an error and does not change the account balance or total issuance values.
///
/// # Type Parameters
///
/// ```text
/// - `T`: Implements `Mutate<AccountId>`.
/// - `AccountId`: Account identifier implementing `AtLeast8BitUnsigned`.
/// ```
pub fn mint_into_overflow<T, AccountId>(_dust_trap: Option<AccountId>)
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

/// Test the `mint_into` function for handling balances below the minimum value.
///
/// This test verifies that minting tokens below the minimum balance for an account
/// returns an error and has no impact on the account balance or total issuance values.
///
/// # Type Parameters
///
/// ```text
/// - `T`: Implements `Mutate<AccountId>`.
/// - `AccountId`: Account identifier implementing `AtLeast8BitUnsigned`.
/// ```
pub fn mint_into_below_minimum<T, AccountId>(_dust_trap: Option<AccountId>)
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

/// Test the `burn_from` function for successfully burning an exact amount of tokens.
///
/// This test checks that the `burn_from` function with `Precision::Exact` correctly
/// reduces the account balance and total issuance values by the burned amount.
///
/// # Type Parameters
///
/// ```text
/// - `T`: Implements `Mutate` for `AccountId`.
/// - `AccountId`: Account identifier implementing `AtLeast8BitUnsigned`.
/// ```
pub fn burn_from_exact_success<T, AccountId>(_dust_trap: Option<AccountId>)
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
	assert_eq!(T::active_issuance(), initial_active_issuance + initial_balance - amount_to_burn);
}

/// Test the `burn_from` function for successfully burning tokens with a best-effort approach.
///
/// This test verifies that the `burn_from` function with `Precision::BestEffort` correctly
/// reduces the account balance and total issuance values by the reducible balance when
/// attempting to burn an amount greater than the reducible balance.
///
/// # Type Parameters
///
/// ```text
/// - `T`: Implements `Mutate` for `AccountId`.
/// - `AccountId`: Account identifier implementing `AtLeast8BitUnsigned`.
/// ```
pub fn burn_from_best_effort_success<T, AccountId>(_dust_trap: Option<AccountId>)
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

	// Test: Burn a best effort amount from the account that is greater than the reducible balance
	let amount_to_burn = reducible_balance + 5.into();
	let precision = Precision::BestEffort;
	assert!(amount_to_burn > reducible_balance);
	assert!(amount_to_burn > T::balance(&account));
	T::burn_from(&account, amount_to_burn, precision, force).unwrap();

	// Verify: The balance and total issuance should be reduced by the reducible_balance
	assert_eq!(T::balance(&account), initial_balance - reducible_balance);
	assert_eq!(T::total_balance(&account), initial_balance - reducible_balance);
	assert_eq!(T::total_issuance(), initial_total_issuance + initial_balance - reducible_balance);
	assert_eq!(T::active_issuance(), initial_active_issuance + initial_balance - reducible_balance);
}

/// Test the `burn_from` function for handling insufficient funds with `Precision::Exact`.
///
/// This test verifies that burning an amount greater than the account's balance with
/// `Precision::Exact` returns an error and does not change the account balance or total issuance
/// values.
///
/// # Type Parameters
///
/// ```text
/// - `T`: Implements `Mutate<AccountId>`.
/// - `AccountId`: Account identifier implementing `AtLeast8BitUnsigned`.
/// ```
pub fn burn_from_exact_insufficient_funds<T, AccountId>(_dust_trap: Option<AccountId>)
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

	// Verify: Burn an amount greater than the account's balance with Exact precision returns Err
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

/// Test the `restore` function for successful restoration.
///
/// This test verifies that restoring an amount into each account updates their balances and the
/// total issuance values correctly.
///
/// # Type Parameters
///
/// ```text
/// - `T`: Implements `Mutate<AccountId>`.
/// - `AccountId`: Account identifier implementing `AtLeast8BitUnsigned`.
/// ```
pub fn restore_success<T, AccountId>(_dust_trap: Option<AccountId>)
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

/// Test the `restore` function for handling balance overflow.
///
/// This test verifies that restoring an amount beyond the maximum balance returns an error and
/// does not change the account balance or total issuance values.
///
/// # Type Parameters
///
/// ```text
/// - `T`: Implements `Mutate<AccountId>`.
/// - `AccountId`: Account identifier implementing `AtLeast8BitUnsigned`.
/// ```
pub fn restore_overflow<T, AccountId>(_dust_trap: Option<AccountId>)
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

/// Test the `restore` function for handling restoration below the minimum balance.
///
/// This test verifies that restoring an amount below the minimum balance returns an error and
/// does not change the account balance or total issuance values.
///
/// # Type Parameters
///
/// ```text
/// - `T`: Implements `Mutate<AccountId>`.
/// - `AccountId`: Account identifier implementing `AtLeast8BitUnsigned`.
/// ```
pub fn restore_below_minimum<T, AccountId>(_dust_trap: Option<AccountId>)
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

/// Test the `shelve` function for successful shelving.
///
/// This test verifies that shelving an amount from an account reduces the account balance and
/// total issuance values by the shelved amount.
///
/// # Type Parameters
///
/// ```text
/// - `T`: Implements `Mutate<AccountId>`.
/// - `AccountId`: Account identifier implementing `AtLeast8BitUnsigned`.
/// ```
pub fn shelve_success<T, AccountId>(_dust_trap: Option<AccountId>)
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
	assert_eq!(T::total_issuance(), initial_total_issuance + initial_balance - amount_to_shelve);
	assert_eq!(T::active_issuance(), initial_active_issuance + initial_balance - amount_to_shelve);
}

/// Test the `shelve` function for handling insufficient funds.
///
/// This test verifies that attempting to shelve an amount greater than the account's balance
/// returns an error and does not change the account balance or total issuance values.
///
/// # Type Parameters
///
/// ```text
/// - `T`: Implements `Mutate<AccountId>`.
/// - `AccountId`: Account identifier implementing `AtLeast8BitUnsigned`.
/// ```
pub fn shelve_insufficient_funds<T, AccountId>(_dust_trap: Option<AccountId>)
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

/// Test the `transfer` function for a successful transfer.
///
/// This test verifies that transferring an amount between two accounts with
/// `Preservation::Expendable` updates the account balances and maintains the total issuance and
/// active issuance values.
///
/// # Type Parameters
///
/// ```text
/// - `T`: Implements `Mutate<AccountId>`.
/// - `AccountId`: Account identifier implementing `AtLeast8BitUnsigned`.
/// ```
pub fn transfer_success<T, AccountId>(_dust_trap: Option<AccountId>)
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

/// Test the `transfer` function with `Preservation::Expendable` for transferring the entire
/// balance.
///
/// This test verifies that transferring the entire balance from one account to another with
/// `Preservation::Expendable` updates the account balances and maintains the total issuance and
/// active issuance values.
///
/// # Type Parameters
///
/// ```text
/// - `T`: Implements `Mutate<AccountId>`.
/// - `AccountId`: Account identifier implementing `AtLeast8BitUnsigned`.
/// ```
pub fn transfer_expendable_all<T, AccountId>(_dust_trap: Option<AccountId>)
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

/// Test the transfer function with Preservation::Expendable for transferring amounts that leaves
/// an account with less than the minimum balance.
///
/// This test verifies that when transferring an amount using Preservation::Expendable and an
/// account will be left with less than the minimum balance, the account balances are updated, dust
/// is collected properly depending on whether a dust_trap exists, and the total issuance and active
/// issuance values remain consistent.
///
/// # Parameters
///
/// - dust_trap: An optional account identifier to which dust will be collected. If None, dust will
///   be removed from the total and active issuance.
///
/// # Type Parameters
///
/// ```text
/// - T: Implements Mutate<AccountId>.
/// - AccountId: Account identifier implementing AtLeast8BitUnsigned.
/// ```
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

/// Test the `transfer` function with `Preservation::Protect` and `Preservation::Preserve` for
/// transferring the entire balance.
///
/// This test verifies that attempting to transfer the entire balance with `Preservation::Protect`
/// or `Preservation::Preserve` returns an error, and the account balances, total issuance, and
/// active issuance values remain unchanged.
///
/// # Type Parameters
///
/// ```text
/// - `T`: Implements `Mutate<AccountId>`.
/// - `AccountId`: Account identifier implementing `AtLeast8BitUnsigned`.
/// ```
pub fn transfer_protect_preserve<T, AccountId>(_dust_trap: Option<AccountId>)
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

/// Test the set_balance function for successful minting.
///
/// This test verifies that minting a balance using set_balance updates the account balance, total
/// issuance, and active issuance correctly.
///
/// # Type Parameters
///
/// ```text
/// - T: Implements Mutate<AccountId>.
/// - AccountId: Account identifier implementing AtLeast8BitUnsigned.
/// ```
pub fn set_balance_mint_success<T, AccountId>(_dust_trap: Option<AccountId>)
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

/// Test the set_balance function for successful burning.
///
/// This test verifies that burning a balance using set_balance updates the account balance, total
/// issuance, and active issuance correctly.
///
/// # Type Parameters
///
/// ```text
/// - T: Implements Mutate<AccountId>.
/// - AccountId: Account identifier implementing AtLeast8BitUnsigned.
/// ```
pub fn set_balance_burn_success<T, AccountId>(_dust_trap: Option<AccountId>)
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

/// Test the can_deposit function for returning a success value.
///
/// This test verifies that the can_deposit function returns DepositConsequence::Success when
/// depositing a reasonable amount.
///
/// # Type Parameters
///
/// ```text
/// - T: Implements Mutate<AccountId>.
/// - AccountId: Account identifier implementing AtLeast8BitUnsigned.
/// ```
pub fn can_deposit_success<T, AccountId>(_dust_trap: Option<AccountId>)
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

/// Test the can_deposit function for returning a minimum balance error.
///
/// This test verifies that the can_deposit function returns DepositConsequence::BelowMinimum when
/// depositing below the minimum balance.
///
/// # Type Parameters
///
/// ```text
/// - T: Implements Mutate<AccountId>.
/// - AccountId: Account identifier implementing AtLeast8BitUnsigned.
/// ```
pub fn can_deposit_below_minimum<T, AccountId>(_dust_trap: Option<AccountId>)
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

/// Test the can_deposit function for returning an overflow error.
///
/// This test verifies that the can_deposit function returns DepositConsequence::Overflow when
/// depositing an amount that would cause an overflow.
///
/// # Type Parameters
///
/// ```text
/// - T: Implements Mutate<AccountId>.
/// - AccountId: Account identifier implementing AtLeast8BitUnsigned.
/// ```
pub fn can_deposit_overflow<T, AccountId>(_dust_trap: Option<AccountId>)
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

/// Test the can_withdraw function for returning a success value.
///
/// This test verifies that the can_withdraw function returns WithdrawConsequence::Success when
/// withdrawing a reasonable amount.
///
/// # Type Parameters
///
/// ```text
/// - T: Implements Mutate<AccountId>.
/// - AccountId: Account identifier implementing AtLeast8BitUnsigned.
/// ```
pub fn can_withdraw_success<T, AccountId>(_dust_trap: Option<AccountId>)
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

/// Test the can_withdraw function for withdrawal resulting in a reduced balance of zero.
///
/// This test verifies that the can_withdraw function returns WithdrawConsequence::ReducedToZero
/// when withdrawing an amount that would reduce the account balance below the minimum balance.
///
/// # Type Parameters
///
/// ```text
/// - T: Implements Mutate<AccountId>.
/// - AccountId: Account identifier implementing AtLeast8BitUnsigned.
/// ```
pub fn can_withdraw_reduced_to_zero<T, AccountId>(_dust_trap: Option<AccountId>)
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

/// Test the can_withdraw function for returning a low balance error.
///
/// This test verifies that the can_withdraw function returns WithdrawConsequence::BalanceLow when
/// withdrawing an amount that would result in an account balance below the current balance.
///
/// # Type Parameters
///
/// ```text
/// - T: Implements Mutate<AccountId>.
/// - AccountId: Account identifier implementing AtLeast8BitUnsigned.
/// ```
pub fn can_withdraw_balance_low<T, AccountId>(_dust_trap: Option<AccountId>)
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

/// Test the reducible_balance function with Preservation::Expendable.
///
/// This test verifies that the reducible_balance function returns the full account balance when
/// using Preservation::Expendable.
///
/// # Type Parameters
///
/// ```text
/// - T: Implements Mutate<AccountId>.
/// - AccountId: Account identifier implementing AtLeast8BitUnsigned.
/// ```
pub fn reducible_balance_expendable<T, AccountId>(_dust_trap: Option<AccountId>)
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

/// Test the reducible_balance function with Preservation::Protect and Preservation::Preserve.
///
/// This test verifies that the reducible_balance function returns the account balance minus the
/// minimum balance when using either Preservation::Protect or Preservation::Preserve.
///
/// # Type Parameters
///
/// ```text
/// - T: Implements Mutate<AccountId>.
/// - AccountId: Account identifier implementing AtLeast8BitUnsigned.
/// ```
pub fn reducible_balance_protect_preserve<T, AccountId>(_dust_trap: Option<AccountId>)
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
