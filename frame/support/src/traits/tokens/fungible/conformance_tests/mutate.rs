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
	tokens::{Fortitude, Precision, Preservation},
};
use core::fmt::Debug;
use sp_arithmetic::traits::AtLeast8BitUnsigned;

//
// mint_into tests
//

pub fn mint_into_success<T, AccountId, Balance>()
where
	T: Mutate<AccountId> + Inspect<AccountId, Balance = Balance>,
	AccountId: AtLeast8BitUnsigned,
	Balance: AtLeast8BitUnsigned + Debug,
{
	let account_0 = AccountId::from(0);
	let account_1 = AccountId::from(1);

	// Sanity check that balances and total issuance start with zero balance
	assert_eq!(T::total_balance(&account_0), Balance::zero());
	assert_eq!(T::total_balance(&account_1), Balance::zero());
	assert_eq!(T::total_issuance(), Balance::zero());

	// Test: Mint an amount into each account
	let amount_0 = T::minimum_balance();
	let amount_1 = T::minimum_balance() + 5.into();
	T::mint_into(&account_0, amount_0.clone()).unwrap();
	T::mint_into(&account_1, amount_1.clone()).unwrap();

	// Verify: Account balances are updated correctly
	assert_eq!(T::total_balance(&account_0), amount_0.clone());
	assert_eq!(T::total_balance(&account_1), amount_1.clone());

	// Verify: Total issuance is updated correctly
	assert_eq!(T::total_issuance(), amount_0 + amount_1);
}

pub fn mint_into_overflow<T, AccountId, Balance>()
where
	T: Mutate<AccountId> + Inspect<AccountId, Balance = Balance>,
	AccountId: AtLeast8BitUnsigned,
	Balance: AtLeast8BitUnsigned + Debug,
{
	let account = AccountId::from(10);
	let amount = Balance::max_value() - 5.into();

	// Mint just below the maximum balance
	T::mint_into(&account, amount.clone()).unwrap();

	// Test: Try minting beyond the maximum balance value
	T::mint_into(&account, 10.into()).unwrap_err();

	// Verify: The balance did not change
	assert_eq!(T::total_balance(&account), amount.clone());

	// Verify: The total issuance did not change
	assert_eq!(T::total_issuance(), amount);
}

pub fn mint_into_done_mint_into<T, AccountId, Balance>()
where
	T: Mutate<AccountId> + Inspect<AccountId, Balance = Balance>,
	AccountId: AtLeast8BitUnsigned,
	Balance: AtLeast8BitUnsigned + Debug,
{
	// TODO: How can we test this?
	assert!(true);
}

//
// burn_from tests
//

pub fn burn_from_exact_success<T, AccountId, Balance>()
where
	T: Mutate<AccountId> + Inspect<AccountId, Balance = Balance>,
	AccountId: AtLeast8BitUnsigned,
	Balance: AtLeast8BitUnsigned + Debug,
{
	// Setup account
	let account = AccountId::from(5);
	let initial_balance = Balance::from(100);
	T::mint_into(&account, initial_balance.clone()).unwrap();

	// Test: Burn an exact amount from the account
	let amount_to_burn = Balance::from(50);
	let precision = Precision::Exact;
	let force = Fortitude::Polite;
	T::burn_from(&account, amount_to_burn.clone(), precision, force).unwrap();

	// Verify: The balance and total issuance should be reduced by the burned amount
	assert_eq!(T::balance(&account), initial_balance.clone() - amount_to_burn.clone());
	assert_eq!(T::total_issuance(), initial_balance - amount_to_burn);
}

pub fn burn_from_best_effort_success<T, AccountId, Balance>()
where
	T: Mutate<AccountId> + Inspect<AccountId, Balance = Balance>,
	AccountId: AtLeast8BitUnsigned,
	Balance: AtLeast8BitUnsigned + Debug,
{
	// Setup account
	let account = AccountId::from(5);
	let initial_balance = Balance::from(100);
	T::mint_into(&account, initial_balance.clone()).unwrap();

	// Get reducible balance
	let force = Fortitude::Polite;
	let reducible_balance = T::reducible_balance(&account, Preservation::Expendable, force);

	// Test: Burn a best effort amount from the account that is greater than the reducible balance
	let amount_to_burn = initial_balance.clone() + 10.into();
	let precision = Precision::BestEffort;
	assert!(amount_to_burn > reducible_balance);
	assert!(amount_to_burn > T::balance(&account));
	T::burn_from(&account, amount_to_burn.clone(), precision, force).unwrap();

	// Verify: The balance and total issuance should be reduced by the reducible_balance
	assert_eq!(T::balance(&account), initial_balance.clone() - reducible_balance.clone());
	assert_eq!(T::total_issuance(), initial_balance - reducible_balance);
}

pub fn burn_from_exact_insufficient_funds<T, AccountId, Balance>()
where
	T: Mutate<AccountId> + Inspect<AccountId, Balance = Balance>,
	AccountId: AtLeast8BitUnsigned,
	Balance: AtLeast8BitUnsigned + Debug,
{
	// Set up the initial conditions and parameters for the test
	let account = AccountId::from(5);
	let initial_balance = Balance::from(100);
	T::mint_into(&account, initial_balance.clone()).unwrap();

	// Test: Attempt to burn an amount greater than the account's balance with Exact precision
	let amount_to_burn = initial_balance.clone() + 10.into();
	let precision = Precision::Exact;
	let force = Fortitude::Polite;
	T::burn_from(&account, amount_to_burn, precision, force).unwrap_err();

	// Verify: The balance and total issuance should remain unchanged
	assert_eq!(T::balance(&account), initial_balance);
	assert_eq!(T::total_issuance(), initial_balance);
}

//
// restore tests
//

pub fn restore_success<T, AccountId, Balance>()
where
	T: Mutate<AccountId> + Inspect<AccountId, Balance = Balance>,
	AccountId: AtLeast8BitUnsigned,
	Balance: AtLeast8BitUnsigned + Debug,
{
	let account_0 = AccountId::from(0);
	let account_1 = AccountId::from(1);

	// Test: Restore an amount into each account
	let amount_0 = T::minimum_balance();
	let amount_1 = T::minimum_balance() + 5.into();
	T::restore(&account_0, amount_0.clone()).unwrap();
	T::restore(&account_1, amount_1.clone()).unwrap();

	// Verify: Account balances are updated correctly
	assert_eq!(T::total_balance(&account_0), amount_0.clone());
	assert_eq!(T::total_balance(&account_1), amount_1.clone());

	// Verify: Total issuance is updated correctly
	assert_eq!(T::total_issuance(), amount_0 + amount_1);
}

pub fn restore_overflow<T, AccountId, Balance>()
where
	T: Mutate<AccountId> + Inspect<AccountId, Balance = Balance>,
	AccountId: AtLeast8BitUnsigned,
	Balance: AtLeast8BitUnsigned + Debug,
{
	let account = AccountId::from(10);
	let amount = Balance::max_value() - 5.into();

	// Restore just below the maximum balance
	T::restore(&account, amount.clone()).unwrap();

	// Test: Try restoring beyond the maximum balance value
	T::restore(&account, 10.into()).unwrap_err();

	// Verify: The balance and total issuance did not change
	assert_eq!(T::total_balance(&account), amount.clone());
	assert_eq!(T::total_issuance(), amount);
}

pub fn restore_done_restore<T, AccountId, Balance>()
where
	T: Mutate<AccountId> + Inspect<AccountId, Balance = Balance>,
	AccountId: AtLeast8BitUnsigned,
	Balance: AtLeast8BitUnsigned + Debug,
{
	// TODO: How can we test this?
	assert!(true);
}

//
// shelve tests
//

pub fn shelve_success<T, AccountId, Balance>()
where
	T: Mutate<AccountId> + Inspect<AccountId, Balance = Balance>,
	AccountId: AtLeast8BitUnsigned,
	Balance: AtLeast8BitUnsigned + Debug,
{
	// Setup account
	let account = AccountId::from(5);
	let initial_balance = Balance::from(100);
	T::restore(&account, initial_balance.clone()).unwrap();

	// Test: Shelve an amount from the account
	let amount_to_shelve = Balance::from(50);
	T::shelve(&account, amount_to_shelve.clone()).unwrap();

	// Verify: The balance and total issuance should be reduced by the shelved amount
	assert_eq!(T::balance(&account), initial_balance.clone() - amount_to_shelve.clone());
	assert_eq!(T::total_issuance(), initial_balance - amount_to_shelve);
}

pub fn shelve_insufficient_funds<T, AccountId, Balance>()
where
	T: Mutate<AccountId> + Inspect<AccountId, Balance = Balance>,
	AccountId: AtLeast8BitUnsigned,
	Balance: AtLeast8BitUnsigned + Debug,
{
	// Set up the initial conditions and parameters for the test
	let account = AccountId::from(5);
	let initial_balance = Balance::from(100);
	T::restore(&account, initial_balance.clone()).unwrap();

	// Test: Attempt to shelve an amount greater than the account's balance with Exact precision
	let amount_to_shelve = initial_balance.clone() + 10.into();
	T::shelve(&account, amount_to_shelve).unwrap_err();

	// Verify: The balance and total issuance should remain unchanged
	assert_eq!(T::balance(&account), initial_balance);
	assert_eq!(T::total_issuance(), initial_balance);
}
