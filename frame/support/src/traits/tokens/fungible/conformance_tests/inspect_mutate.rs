// This file is part of Substrate.

// Copyright (C) 2017-2023 Parity Technologies (UK) Ltd.
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

//
// mint_into
//

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
	T::mint_into(&account_0, amount_0.clone()).unwrap();
	T::mint_into(&account_1, amount_1.clone()).unwrap();

	// Verify: Account balances are updated correctly
	assert_eq!(T::total_balance(&account_0), amount_0.clone());
	assert_eq!(T::total_balance(&account_1), amount_1.clone());
	assert_eq!(T::balance(&account_0), amount_0.clone());
	assert_eq!(T::balance(&account_1), amount_1.clone());

	// Verify: Total issuance is updated correctly
	assert_eq!(T::total_issuance(), initial_total_issuance + amount_0.clone() + amount_1.clone());
	assert_eq!(T::active_issuance(), initial_active_issuance + amount_0 + amount_1);
}

pub fn mint_into_overflow<T, AccountId>(_dust_trap: Option<AccountId>)
where
	T: Mutate<AccountId>,
	<T as Inspect<AccountId>>::Balance: AtLeast8BitUnsigned + Debug,
	AccountId: AtLeast8BitUnsigned,
{
	let initial_total_issuance = T::total_issuance();
	let initial_active_issuance = T::active_issuance();
	let account = AccountId::from(10);
	let amount = T::Balance::max_value() - 5.into() - initial_total_issuance.clone();

	// Mint just below the maximum balance
	T::mint_into(&account, amount.clone()).unwrap();

	// Verify: Minting beyond the maximum balance value returns an Err
	T::mint_into(&account, 10.into()).unwrap_err();

	// Verify: The balance did not change
	assert_eq!(T::total_balance(&account), amount.clone());
	assert_eq!(T::balance(&account), amount.clone());

	// Verify: The total issuance did not change
	assert_eq!(T::total_issuance(), initial_total_issuance + amount.clone());
	assert_eq!(T::active_issuance(), initial_active_issuance + amount);
}

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
	T::mint_into(&account, amount.clone()).unwrap_err();

	// Verify: noop
	assert_eq!(T::total_balance(&account), T::Balance::zero());
	assert_eq!(T::balance(&account), T::Balance::zero());
	assert_eq!(T::total_issuance(), initial_total_issuance);
	assert_eq!(T::active_issuance(), initial_active_issuance);
}

//
// burn_from
//

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
	T::mint_into(&account, initial_balance.clone()).unwrap();

	// Test: Burn an exact amount from the account
	let amount_to_burn = T::Balance::from(5);
	let precision = Precision::Exact;
	let force = Fortitude::Polite;
	T::burn_from(&account, amount_to_burn.clone(), precision, force).unwrap();

	// Verify: The balance and total issuance should be reduced by the burned amount
	assert_eq!(T::balance(&account), initial_balance.clone() - amount_to_burn.clone());
	assert_eq!(T::total_balance(&account), initial_balance.clone() - amount_to_burn.clone());
	assert_eq!(
		T::total_issuance(),
		initial_total_issuance + initial_balance.clone() - amount_to_burn.clone()
	);
	assert_eq!(T::active_issuance(), initial_active_issuance + initial_balance - amount_to_burn);
}

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
	T::mint_into(&account, initial_balance.clone()).unwrap();

	// Get reducible balance
	let force = Fortitude::Polite;
	let reducible_balance = T::reducible_balance(&account, Preservation::Expendable, force);

	// Test: Burn a best effort amount from the account that is greater than the reducible balance
	let amount_to_burn = reducible_balance.clone() + 5.into();
	let precision = Precision::BestEffort;
	assert!(amount_to_burn > reducible_balance);
	assert!(amount_to_burn > T::balance(&account));
	T::burn_from(&account, amount_to_burn.clone(), precision, force).unwrap();

	// Verify: The balance and total issuance should be reduced by the reducible_balance
	assert_eq!(T::balance(&account), initial_balance.clone() - reducible_balance.clone());
	assert_eq!(T::total_balance(&account), initial_balance.clone() - reducible_balance.clone());
	assert_eq!(
		T::total_issuance(),
		initial_total_issuance + initial_balance.clone() - reducible_balance.clone()
	);
	assert_eq!(T::active_issuance(), initial_active_issuance + initial_balance - reducible_balance);
}

pub fn burn_from_exact_insufficient_funds<T, AccountId>(_dust_trap: Option<AccountId>)
where
	T: Mutate<AccountId>,
	<T as Inspect<AccountId>>::Balance: AtLeast8BitUnsigned + Debug,
	AccountId: AtLeast8BitUnsigned,
{
	// Set up the initial conditions and parameters for the test
	let account = AccountId::from(5);
	let initial_balance = T::minimum_balance() + 10.into();
	T::mint_into(&account, initial_balance.clone()).unwrap();
	let initial_total_issuance = T::total_issuance();
	let initial_active_issuance = T::active_issuance();

	// Verify: Burn an amount greater than the account's balance with Exact precision returns Err
	let amount_to_burn = initial_balance.clone() + 10.into();
	let precision = Precision::Exact;
	let force = Fortitude::Polite;
	T::burn_from(&account, amount_to_burn, precision, force).unwrap_err();

	// Verify: The balance and total issuance should remain unchanged
	assert_eq!(T::balance(&account), initial_balance);
	assert_eq!(T::total_balance(&account), initial_balance);
	assert_eq!(T::total_issuance(), initial_total_issuance);
	assert_eq!(T::active_issuance(), initial_active_issuance);
}

//
// restore
//

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
	T::restore(&account_0, amount_0.clone()).unwrap();
	T::restore(&account_1, amount_1.clone()).unwrap();

	// Verify: Account balances are updated correctly
	assert_eq!(T::total_balance(&account_0), amount_0.clone());
	assert_eq!(T::total_balance(&account_1), amount_1.clone());
	assert_eq!(T::balance(&account_0), amount_0.clone());
	assert_eq!(T::balance(&account_1), amount_1.clone());

	// Verify: Total issuance is updated correctly
	assert_eq!(T::total_issuance(), initial_total_issuance + amount_0.clone() + amount_1.clone());
	assert_eq!(T::active_issuance(), initial_active_issuance + amount_0 + amount_1);
}

pub fn restore_overflow<T, AccountId>(_dust_trap: Option<AccountId>)
where
	T: Mutate<AccountId>,
	<T as Inspect<AccountId>>::Balance: AtLeast8BitUnsigned + Debug,
	AccountId: AtLeast8BitUnsigned,
{
	let initial_total_issuance = T::total_issuance();
	let initial_active_issuance = T::active_issuance();
	let account = AccountId::from(10);
	let amount = T::Balance::max_value() - 5.into() - initial_total_issuance.clone();

	// Restore just below the maximum balance
	T::restore(&account, amount.clone()).unwrap();

	// Verify: Restoring beyond the maximum balance returns an Err
	T::restore(&account, 10.into()).unwrap_err();

	// Verify: The balance and total issuance did not change
	assert_eq!(T::total_balance(&account), amount.clone());
	assert_eq!(T::balance(&account), amount.clone());
	assert_eq!(T::total_issuance(), initial_total_issuance + amount.clone());
	assert_eq!(T::active_issuance(), initial_active_issuance + amount);
}

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
	T::restore(&account, amount.clone()).unwrap_err();

	// Verify: noop
	assert_eq!(T::total_balance(&account), T::Balance::zero());
	assert_eq!(T::balance(&account), T::Balance::zero());
	assert_eq!(T::total_issuance(), initial_total_issuance);
	assert_eq!(T::active_issuance(), initial_active_issuance);
}

//
// shelve tests
//

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

	T::restore(&account, initial_balance.clone()).unwrap();

	// Test: Shelve an amount from the account
	let amount_to_shelve = T::Balance::from(5);
	T::shelve(&account, amount_to_shelve.clone()).unwrap();

	// Verify: The balance and total issuance should be reduced by the shelved amount
	assert_eq!(T::balance(&account), initial_balance.clone() - amount_to_shelve.clone());
	assert_eq!(T::total_balance(&account), initial_balance.clone() - amount_to_shelve.clone());
	assert_eq!(
		T::total_issuance(),
		initial_total_issuance + initial_balance.clone() - amount_to_shelve.clone()
	);
	assert_eq!(T::active_issuance(), initial_active_issuance + initial_balance - amount_to_shelve);
}

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
	T::restore(&account, initial_balance.clone()).unwrap();

	// Verify: Shelving greater than the balance with Exact precision returns Err
	let amount_to_shelve = initial_balance.clone() + 10.into();
	T::shelve(&account, amount_to_shelve).unwrap_err();

	// Verify: The balance and total issuance should remain unchanged
	assert_eq!(T::balance(&account), initial_balance);
	assert_eq!(T::total_balance(&account), initial_balance);
	assert_eq!(T::total_issuance(), initial_total_issuance + initial_balance.clone());
	assert_eq!(T::active_issuance(), initial_active_issuance + initial_balance);
}

//
// transfer
//

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
	T::set_balance(&account_0, initial_balance.clone());
	T::set_balance(&account_1, initial_balance.clone());

	// Test: Transfer an amount from account_0 to account_1
	let transfer_amount = T::Balance::from(3);
	T::transfer(&account_0, &account_1, transfer_amount.clone(), Preservation::Expendable).unwrap();

	// Verify: Account balances are updated correctly
	assert_eq!(T::total_balance(&account_0), initial_balance.clone() - transfer_amount.clone());
	assert_eq!(T::total_balance(&account_1), initial_balance.clone() + transfer_amount.clone());
	assert_eq!(T::balance(&account_0), initial_balance.clone() - transfer_amount.clone());
	assert_eq!(T::balance(&account_1), initial_balance.clone() + transfer_amount.clone());

	// Verify: Total issuance doesn't change
	assert_eq!(T::total_issuance(), initial_total_issuance + initial_balance.clone() * 2.into());
	assert_eq!(T::active_issuance(), initial_active_issuance + initial_balance * 2.into());
}

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
	T::set_balance(&account_0, initial_balance.clone());
	T::set_balance(&account_1, initial_balance.clone());

	// Test: Transfer entire balance from account_0 to account_1
	let preservation = Preservation::Expendable;
	let transfer_amount = initial_balance.clone();
	T::transfer(&account_0, &account_1, transfer_amount.clone(), preservation).unwrap();

	// Verify: Account balances are updated correctly
	assert_eq!(T::total_balance(&account_0), T::Balance::zero());
	assert_eq!(T::total_balance(&account_1), initial_balance.clone() * 2.into());
	assert_eq!(T::balance(&account_0), T::Balance::zero());
	assert_eq!(T::balance(&account_1), initial_balance.clone() * 2.into());

	// Verify: Total issuance doesn't change
	assert_eq!(T::total_issuance(), initial_total_issuance + initial_balance.clone() * 2.into());
	assert_eq!(T::active_issuance(), initial_active_issuance + initial_balance * 2.into());
}

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
	T::set_balance(&account_0, initial_balance.clone());
	T::set_balance(&account_1, initial_balance.clone());

	let initial_total_issuance = T::total_issuance();
	let initial_active_issuance = T::active_issuance();
	let initial_dust_trap_balance = match dust_trap.clone() {
		Some(dust_trap) => T::total_balance(&dust_trap),
		None => T::Balance::zero(),
	};

	// Test: Transfer balance
	let preservation = Preservation::Expendable;
	let transfer_amount = T::Balance::from(11);
	T::transfer(&account_0, &account_1, transfer_amount.clone(), preservation).unwrap();

	// Verify: Account balances are updated correctly
	assert_eq!(T::total_balance(&account_0), T::Balance::zero());
	assert_eq!(T::total_balance(&account_1), initial_balance.clone() + transfer_amount.clone());
	assert_eq!(T::balance(&account_0), T::Balance::zero());
	assert_eq!(T::balance(&account_1), initial_balance.clone() + transfer_amount.clone());

	match dust_trap {
		Some(dust_trap) => {
			// Verify: Total issuance and active issuance don't change
			assert_eq!(T::total_issuance(), initial_total_issuance.clone());
			assert_eq!(T::active_issuance(), initial_active_issuance.clone());
			// Verify: Dust is collected into dust trap
			assert_eq!(
				T::total_balance(&dust_trap),
				initial_dust_trap_balance.clone() + T::minimum_balance() - 1.into()
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
	T::set_balance(&account_0, initial_balance.clone());
	T::set_balance(&account_1, initial_balance.clone());

	// Verify: Transfer Protect entire balance from account_0 to account_1 should Err
	let preservation = Preservation::Protect;
	let transfer_amount = initial_balance.clone();
	T::transfer(&account_0, &account_1, transfer_amount.clone(), preservation).unwrap_err();

	// Verify: Noop
	assert_eq!(T::total_balance(&account_0), initial_balance.clone());
	assert_eq!(T::total_balance(&account_1), initial_balance.clone());
	assert_eq!(T::balance(&account_0), initial_balance.clone());
	assert_eq!(T::balance(&account_1), initial_balance.clone());
	assert_eq!(
		T::total_issuance(),
		initial_total_issuance.clone() + initial_balance.clone() * 2.into()
	);
	assert_eq!(
		T::active_issuance(),
		initial_active_issuance.clone() + initial_balance.clone() * 2.into()
	);

	// Verify: Transfer Preserve entire balance from account_0 to account_1 should Err
	let preservation = Preservation::Preserve;
	T::transfer(&account_0, &account_1, transfer_amount.clone(), preservation).unwrap_err();

	// Verify: Noop
	assert_eq!(T::total_balance(&account_0), initial_balance.clone());
	assert_eq!(T::total_balance(&account_1), initial_balance.clone());
	assert_eq!(T::balance(&account_0), initial_balance.clone());
	assert_eq!(T::balance(&account_1), initial_balance.clone());
	assert_eq!(T::total_issuance(), initial_total_issuance + initial_balance.clone() * 2.into());
	assert_eq!(T::active_issuance(), initial_active_issuance + initial_balance * 2.into());
}

//
// set_balance
//

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
	T::mint_into(&account, initial_balance.clone()).unwrap();

	// Test: Increase the account balance with set_balance
	let increase_amount: T::Balance = 5.into();
	let new = T::set_balance(&account, initial_balance.clone() + increase_amount.clone());

	// Verify: set_balance returned the new balance
	let expected_new = initial_balance + increase_amount;
	assert_eq!(new, expected_new);

	// Verify: Balance and issuance is updated correctly
	assert_eq!(T::total_balance(&account), expected_new.clone());
	assert_eq!(T::balance(&account), expected_new.clone());
	assert_eq!(T::total_issuance(), initial_total_issuance + expected_new.clone());
	assert_eq!(T::active_issuance(), initial_active_issuance + expected_new);
}

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
	T::mint_into(&account, initial_balance.clone()).unwrap();

	// Test: Increase the account balance with set_balance
	let burn_amount: T::Balance = 5.into();
	let new = T::set_balance(&account, initial_balance.clone() - burn_amount.clone());

	// Verify: set_balance returned the new balance
	let expected_new = initial_balance - burn_amount;
	assert_eq!(new, expected_new);

	// Verify: Balance and issuance is updated correctly
	assert_eq!(T::total_balance(&account), expected_new.clone());
	assert_eq!(T::balance(&account), expected_new.clone());
	assert_eq!(T::total_issuance(), initial_total_issuance + expected_new.clone());
	assert_eq!(T::active_issuance(), initial_active_issuance + expected_new);
}

//
// can_deposit
//

pub fn can_deposit_success<T, AccountId>(_dust_trap: Option<AccountId>)
where
	T: Mutate<AccountId>,
	<T as Inspect<AccountId>>::Balance: AtLeast8BitUnsigned + Debug,
	AccountId: AtLeast8BitUnsigned,
{
	let account = AccountId::from(10);
	let initial_balance = T::minimum_balance() + 10.into();
	T::mint_into(&account, initial_balance.clone()).unwrap();

	// Test: can_deposit a reasonable amount
	let ret = T::can_deposit(&account, 5.into(), Provenance::Minted);

	// Verify: Returns success
	assert_eq!(ret, DepositConsequence::Success);
}

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

pub fn can_deposit_overflow<T, AccountId>(_dust_trap: Option<AccountId>)
where
	T: Mutate<AccountId>,
	<T as Inspect<AccountId>>::Balance: AtLeast8BitUnsigned + Debug,
	AccountId: AtLeast8BitUnsigned,
{
	let account = AccountId::from(10);

	// Test: Try deposit over the max balance
	let initial_balance = T::Balance::max_value() - 5.into() - T::total_issuance();
	T::mint_into(&account, initial_balance.clone()).unwrap();
	let ret = T::can_deposit(&account, 10.into(), Provenance::Minted);

	// Verify: Returns success
	assert_eq!(ret, DepositConsequence::Overflow);
}

//
// can_withdraw
//

pub fn can_withdraw_success<T, AccountId>(_dust_trap: Option<AccountId>)
where
	T: Mutate<AccountId>,
	<T as Inspect<AccountId>>::Balance: AtLeast8BitUnsigned + Debug,
	AccountId: AtLeast8BitUnsigned,
{
	let account = AccountId::from(10);
	let initial_balance = T::minimum_balance() + 10.into();
	T::mint_into(&account, initial_balance.clone()).unwrap();

	// Test: can_withdraw a reasonable amount
	let ret = T::can_withdraw(&account, 5.into());

	// Verify: Returns success
	assert_eq!(ret, WithdrawConsequence::Success);
}

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
	T::mint_into(&account, initial_balance.clone()).unwrap();

	// Verify: can_withdraw below the minimum balance returns ReducedToZero
	let ret = T::can_withdraw(&account, 1.into());
	assert_eq!(ret, WithdrawConsequence::ReducedToZero(T::minimum_balance() - 1.into()));
}

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
	T::mint_into(&account, initial_balance.clone()).unwrap();
	T::mint_into(&other_account, initial_balance.clone() * 2.into()).unwrap();

	// Verify: can_withdraw below the account balance returns BalanceLow
	let ret = T::can_withdraw(&account, initial_balance + 1.into());
	assert_eq!(ret, WithdrawConsequence::BalanceLow);
}

//
// reducible_balance
//

pub fn reducible_balance_expendable<T, AccountId>(_dust_trap: Option<AccountId>)
where
	T: Mutate<AccountId>,
	<T as Inspect<AccountId>>::Balance: AtLeast8BitUnsigned + Debug,
	AccountId: AtLeast8BitUnsigned,
{
	let account = AccountId::from(10);
	let initial_balance = T::minimum_balance() + 10.into();
	T::mint_into(&account, initial_balance.clone()).unwrap();

	// Verify: reducible_balance returns the full balance
	let ret = T::reducible_balance(&account, Preservation::Expendable, Fortitude::Polite);
	assert_eq!(ret, initial_balance);
}

pub fn reducible_balance_protect_preserve<T, AccountId>(_dust_trap: Option<AccountId>)
where
	T: Mutate<AccountId>,
	<T as Inspect<AccountId>>::Balance: AtLeast8BitUnsigned + Debug,
	AccountId: AtLeast8BitUnsigned,
{
	let account = AccountId::from(10);
	let initial_balance = T::minimum_balance() + 10.into();
	T::mint_into(&account, initial_balance.clone()).unwrap();

	// Verify: reducible_balance returns the full balance - min balance
	let ret = T::reducible_balance(&account, Preservation::Protect, Fortitude::Polite);
	assert_eq!(ret, initial_balance.clone() - T::minimum_balance());
	let ret = T::reducible_balance(&account, Preservation::Preserve, Fortitude::Polite);
	assert_eq!(ret, initial_balance - T::minimum_balance());
}
