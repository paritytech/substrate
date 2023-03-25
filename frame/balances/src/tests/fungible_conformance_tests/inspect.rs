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

//! Conformance tests regarding the functionality of the `fungible` Inspect trait.
//!
//! TODO: Decouple these tests from balances and abstract them into a macro so that they can be
//! used by any pallet that implements the `fungible` Inspect trait.

use super::*;
use frame_support::traits::tokens::{
	Fortitude::{Force, Polite},
	Preservation::{Expendable, Preserve, Protect},
};
use fungible::{Inspect, Mutate, MutateFreeze};

#[test]
fn total_issuance_works() {
	ExtBuilder::default().build_and_execute_with(|| {
		assert_eq!(Balances::total_issuance(), 0);
		Balances::set_balance(&1, 100);
		assert_eq!(Balances::total_issuance(), 100);
		Balances::set_balance(&2, 100);
		assert_eq!(Balances::total_issuance(), 200);
		Balances::set_balance(&2, 101);
		assert_eq!(Balances::total_issuance(), 201);
	});
}

#[test]
fn active_issuance_works() {
	ExtBuilder::default().existential_deposit(10).build_and_execute_with(|| {
		// fungible docs on active_issuance:
		// "The total amount of issuance in the system excluding those which are controlled by
		// the system."
		//
		// TODO: What does it mean for some issuance to be 'controlled by the system'?
		// If there is no offical definition, then I think it cannot be tested in a generic way and
		// we should remove this test.
		assert!(true);
	});
}

#[test]
fn minimum_balance_works() {
	ExtBuilder::default().existential_deposit(5).build_and_execute_with(|| {
		assert_eq!(Balances::minimum_balance(), 5);
	});
	ExtBuilder::default().existential_deposit(10).build_and_execute_with(|| {
		assert_eq!(Balances::minimum_balance(), 10);
	});
}

#[test]
fn total_balance_works() {
	ExtBuilder::default().existential_deposit(10).build_and_execute_with(|| {
		assert_eq!(Balances::total_balance(&1), 0);
		Balances::set_balance(&1, 100);
		assert_eq!(Balances::total_balance(&1), 100);
		Balances::set_balance(&2, 100);
		assert_eq!(Balances::total_balance(&2), 100);
		Balances::set_balance(&2, 101);
		assert_eq!(Balances::total_balance(&2), 101);
	});
}

// TODO: Properly understand Preservation and Fortitude enums, and ensure every permutation is
// thoroughly tested.
#[test]
fn reducible_balance_basic_works() {
	ExtBuilder::default().existential_deposit(10).build_and_execute_with(|| {
		Balances::set_balance(&1, 100);
		assert_eq!(Balances::reducible_balance(&1, Expendable, Polite), 100);
		assert_eq!(Balances::reducible_balance(&1, Protect, Polite), 90);
		assert_eq!(Balances::reducible_balance(&1, Preserve, Polite), 90);
		assert_eq!(Balances::reducible_balance(&1, Expendable, Force), 100);
		assert_eq!(Balances::reducible_balance(&1, Protect, Force), 90);
		assert_eq!(Balances::reducible_balance(&1, Preserve, Force), 90);
	});
}

#[test]
fn reducible_balance_other_provide_works() {
	ExtBuilder::default().existential_deposit(10).build_and_execute_with(|| {
		Balances::set_balance(&1, 100);
		System::inc_providers(&1);
		assert_eq!(Balances::reducible_balance(&1, Expendable, Polite), 100);
		assert_eq!(Balances::reducible_balance(&1, Protect, Polite), 100);
		assert_eq!(Balances::reducible_balance(&1, Preserve, Polite), 90);
		assert_eq!(Balances::reducible_balance(&1, Expendable, Force), 100);
		assert_eq!(Balances::reducible_balance(&1, Protect, Force), 100);
		assert_eq!(Balances::reducible_balance(&1, Preserve, Force), 90);
	});
}

#[test]
fn reducible_balance_frozen_works() {
	ExtBuilder::default().existential_deposit(10).build_and_execute_with(|| {
		Balances::set_balance(&1, 100);
		assert_ok!(Balances::set_freeze(&TestId::Foo, &1, 50));
		assert_eq!(Balances::reducible_balance(&1, Expendable, Polite), 50);
		assert_eq!(Balances::reducible_balance(&1, Protect, Polite), 50);
		assert_eq!(Balances::reducible_balance(&1, Preserve, Polite), 50);
		assert_eq!(Balances::reducible_balance(&1, Expendable, Force), 90);
		assert_eq!(Balances::reducible_balance(&1, Protect, Force), 90);
		assert_eq!(Balances::reducible_balance(&1, Preserve, Force), 90);
	});
}

#[test]
fn can_deposit_works() {
	ExtBuilder::default().build_and_execute_with(|| {
		// TODO
		assert!(true);
	});
}

#[test]
fn can_deposit_withdraw_works() {
	ExtBuilder::default().build_and_execute_with(|| {
		// TODO
		assert!(true);
	});
}
