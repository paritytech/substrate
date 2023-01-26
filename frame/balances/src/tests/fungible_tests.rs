// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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

//! Tests regarding the functionality of the `fungible` trait set implementations.

use super::*;
use frame_support::traits::tokens::KeepAlive::CanKill;
use fungible::{Inspect, InspectHold, MutateHold, InspectFreeze, MutateFreeze, Unbalanced};

#[test]
fn unbalanced_trait_set_balance_works() {
	ExtBuilder::default().build_and_execute_with(|| {
		assert_eq!(<Balances as fungible::Inspect<_>>::balance(&1337), 0);
		assert_ok!(Balances::force_set_balance(&1337, 100));
		assert_eq!(<Balances as fungible::Inspect<_>>::balance(&1337), 100);

		assert_ok!(<Balances as fungible::MutateHold<_>>::hold(&TestId::Foo, &1337, 60));
		assert_eq!(<Balances as fungible::Inspect<_>>::balance(&1337), 40);
		assert_eq!(<Balances as fungible::InspectHold<_>>::total_balance_on_hold(&1337), 60);
		assert_eq!(<Balances as fungible::InspectHold<_>>::balance_on_hold(&TestId::Foo, &1337), 60);

		assert_noop!(Balances::force_set_balance(&1337, 0), Error::<Test>::InsufficientBalance);

		assert_ok!(Balances::force_set_balance(&1337, 1));
		assert_eq!(<Balances as fungible::Inspect<_>>::balance(&1337), 1);
		assert_eq!(<Balances as fungible::InspectHold<_>>::balance_on_hold(&TestId::Foo, &1337), 60);

		assert_ok!(<Balances as fungible::MutateHold<_>>::release(&TestId::Foo, &1337, 60, false));
		assert_eq!(<Balances as fungible::InspectHold<_>>::balance_on_hold(&TestId::Foo, &1337), 0);
		assert_eq!(<Balances as fungible::InspectHold<_>>::total_balance_on_hold(&1337), 0);
	});
}

#[test]
fn unbalanced_trait_set_total_issuance_works() {
	ExtBuilder::default().build_and_execute_with(|| {
		assert_eq!(<Balances as fungible::Inspect<_>>::total_issuance(), 0);
		Balances::set_total_issuance(100);
		assert_eq!(<Balances as fungible::Inspect<_>>::total_issuance(), 100);
	});
}

#[test]
fn unbalanced_trait_decrease_balance_simple_works() {
	ExtBuilder::default().build_and_execute_with(|| {
		// An Account that starts at 100
		assert_ok!(Balances::force_set_balance(&1337, 100));
		assert_eq!(<Balances as fungible::Inspect<_>>::balance(&1337), 100);
		// and reserves 50
		assert_ok!(<Balances as fungible::MutateHold<_>>::hold(&TestId::Foo, &1337, 50));
		assert_eq!(<Balances as fungible::Inspect<_>>::balance(&1337), 50);
		// and is decreased by 20
		assert_ok!(Balances::decrease_balance(&1337, 20, false, CanKill, false));
		assert_eq!(<Balances as fungible::Inspect<_>>::balance(&1337), 30);
	});
}

#[test]
fn unbalanced_trait_decrease_balance_works_1() {
	ExtBuilder::default().build_and_execute_with(|| {
		assert_ok!(Balances::force_set_balance(&1337, 100));
		assert_eq!(<Balances as fungible::Inspect<_>>::balance(&1337), 100);

		assert_noop!(
			Balances::decrease_balance(&1337, 101, false, CanKill, false),
			TokenError::FundsUnavailable
		);
		assert_eq!(
			Balances::decrease_balance(&1337, 100, false, CanKill, false),
			Ok(100)
		);
		assert_eq!(<Balances as fungible::Inspect<_>>::balance(&1337), 0);
	});
}

#[test]
fn unbalanced_trait_decrease_balance_works_2() {
	ExtBuilder::default().build_and_execute_with(|| {
		// free: 40, reserved: 60
		assert_ok!(Balances::force_set_balance(&1337, 100));
		assert_ok!(Balances::hold(&TestId::Foo, &1337, 60));
		assert_eq!(<Balances as fungible::Inspect<_>>::balance(&1337), 40);
		assert_eq!(Balances::total_balance_on_hold(&1337), 60);
		assert_noop!(
			Balances::decrease_balance(&1337, 40, false, CanKill, false),
			Error::<Test>::InsufficientBalance
		);
		assert_eq!(
			Balances::decrease_balance(&1337, 39, false, CanKill, false),
			Ok(39)
		);
		assert_eq!(<Balances as fungible::Inspect<_>>::balance(&1337), 1);
		assert_eq!(Balances::total_balance_on_hold(&1337), 60);
	});
}

#[test]
fn unbalanced_trait_decrease_balance_at_most_works_1() {
	ExtBuilder::default().build_and_execute_with(|| {
		assert_ok!(Balances::force_set_balance(&1337, 100));
		assert_eq!(<Balances as fungible::Inspect<_>>::balance(&1337), 100);

		assert_eq!(
			Balances::decrease_balance(&1337, 101, true, CanKill, false),
			Ok(100)
		);
		assert_eq!(<Balances as fungible::Inspect<_>>::balance(&1337), 0);
	});
}

#[test]
fn unbalanced_trait_decrease_balance_at_most_works_2() {
	ExtBuilder::default().build_and_execute_with(|| {
		assert_ok!(Balances::force_set_balance(&1337, 99));
		assert_eq!(
			Balances::decrease_balance(&1337, 99, true, CanKill, false),
			Ok(99)
		);
		assert_eq!(<Balances as fungible::Inspect<_>>::balance(&1337), 0);
	});
}

#[test]
fn unbalanced_trait_decrease_balance_at_most_works_3() {
	ExtBuilder::default().build_and_execute_with(|| {
		// free: 40, reserved: 60
		assert_ok!(Balances::force_set_balance(&1337, 100));
		assert_ok!(Balances::hold(&TestId::Foo, &1337, 60));
		assert_eq!(Balances::free_balance(1337), 40);
		assert_eq!(Balances::total_balance_on_hold(&1337), 60);
		assert_eq!(
			Balances::decrease_balance(&1337, 0, true, CanKill, false),
			Ok(0)
		);
		assert_eq!(Balances::free_balance(1337), 40);
		assert_eq!(Balances::total_balance_on_hold(&1337), 60);
		assert_eq!(
			Balances::decrease_balance(&1337, 10, true, CanKill, false),
			Ok(10)
		);
		assert_eq!(Balances::free_balance(1337), 30);
		assert_eq!(
			Balances::decrease_balance(&1337, 200, true, CanKill, false),
			Ok(29)
		);
		assert_eq!(<Balances as fungible::Inspect<_>>::balance(&1337), 1);
		assert_eq!(Balances::free_balance(1337), 1);
		assert_eq!(Balances::total_balance_on_hold(&1337), 60);
	});
}

#[test]
fn unbalanced_trait_increase_balance_works() {
	ExtBuilder::default().build_and_execute_with(|| {
		assert_noop!(
			Balances::increase_balance(&1337, 0, false),
			TokenError::BelowMinimum
		);
		assert_eq!(
			Balances::increase_balance(&1337, 1, false),
			Ok(1)
		);
		assert_noop!(
			Balances::increase_balance(&1337, u64::MAX, false),
			ArithmeticError::Overflow
		);
	});
}

#[test]
fn unbalanced_trait_increase_balance_at_most_works() {
	ExtBuilder::default().build_and_execute_with(|| {
		assert_eq!(
			Balances::increase_balance(&1337, 0, true),
			Ok(0)
		);
		assert_eq!(
			Balances::increase_balance(&1337, 1, true),
			Ok(1)
		);
		assert_eq!(
			Balances::increase_balance(&1337, u64::MAX, true),
			Ok(u64::MAX - 1)
		);
	});
}

#[test]
fn freezing_and_holds_should_overlap() {
	ExtBuilder::default().existential_deposit(1).monied(true).build_and_execute_with(|| {
		assert_ok!(Balances::set_freeze(&TestId::Foo, &1, 10));
		assert_ok!(Balances::hold(&TestId::Foo, &1, 9));
		assert_eq!(Balances::account(&1).free, 1);
		assert_eq!(System::consumers(&1), 1);
		assert_eq!(Balances::account(&1).free, 1);
		assert_eq!(Balances::account(&1).frozen, 10);
		assert_eq!(Balances::account(&1).reserved, 9);
		assert_eq!(Balances::total_balance_on_hold(&1), 9);
	});
}

#[test]
fn frozen_hold_balance_cannot_be_moved_without_force() {
	ExtBuilder::default().existential_deposit(1).monied(true).build_and_execute_with(|| {
		assert_ok!(Balances::set_freeze(&TestId::Foo, &1, 10));
		assert_ok!(Balances::hold(&TestId::Foo, &1, 9));
		assert_eq!(Balances::reducible_total_balance_on_hold(&1, true), 9);
		assert_eq!(Balances::reducible_total_balance_on_hold(&1, false), 0);
		let e = TokenError::Frozen;
		assert_noop!(Balances::transfer_on_hold(&TestId::Foo, &1, &2, 1, false, false, false), e);
		assert_ok!(Balances::transfer_on_hold(&TestId::Foo, &1, &2, 1, false, false, true));
	});
}

#[test]
fn frozen_hold_balance_best_effort_transfer_works() {
	ExtBuilder::default().existential_deposit(1).monied(true).build_and_execute_with(|| {
		assert_ok!(Balances::set_freeze(&TestId::Foo, &1, 5));
		assert_ok!(Balances::hold(&TestId::Foo, &1, 9));
		assert_eq!(Balances::reducible_total_balance_on_hold(&1, true), 9);
		assert_eq!(Balances::reducible_total_balance_on_hold(&1, false), 5);
		assert_ok!(Balances::transfer_on_hold(&TestId::Foo, &1, &2, 10, true, false, false));
		assert_eq!(Balances::total_balance(&1), 5);
		assert_eq!(Balances::total_balance(&2), 25);
	});
}

#[test]
fn partial_freezing_should_work() {
	ExtBuilder::default().existential_deposit(1).monied(true).build_and_execute_with(|| {
		assert_ok!(Balances::set_freeze(&TestId::Foo, &1, 5));
		assert_eq!(System::consumers(&1), 1);
		assert_ok!(<Balances as fungible::Mutate<_>>::transfer(&1, &2, 5, CanKill));
		assert_noop!(<Balances as fungible::Mutate<_>>::transfer(&1, &2, 1, CanKill), TokenError::Frozen);
	});
}

#[test]
fn thaw_should_work() {
	ExtBuilder::default().existential_deposit(1).monied(true).build_and_execute_with(|| {
		assert_ok!(Balances::set_freeze(&TestId::Foo, &1, u64::MAX));
		assert_ok!(Balances::thaw(&TestId::Foo, &1));
		assert_eq!(System::consumers(&1), 0);
		assert_eq!(Balances::balance_frozen(&TestId::Foo, &1), 0);
		assert_eq!(Balances::account(&1).frozen, 0);
		assert_ok!(<Balances as fungible::Mutate<_>>::transfer(&1, &2, 10, CanKill));
	});
}

#[test]
fn set_freeze_zero_should_work() {
	ExtBuilder::default().existential_deposit(1).monied(true).build_and_execute_with(|| {
		assert_ok!(Balances::set_freeze(&TestId::Foo, &1, u64::MAX));
		assert_ok!(Balances::set_freeze(&TestId::Foo, &1, 0));
		assert_eq!(System::consumers(&1), 0);
		assert_eq!(Balances::balance_frozen(&TestId::Foo, &1), 0);
		assert_eq!(Balances::account(&1).frozen, 0);
		assert_ok!(<Balances as fungible::Mutate<_>>::transfer(&1, &2, 10, CanKill));
	});
}

#[test]
fn set_freeze_should_work() {
	ExtBuilder::default().existential_deposit(1).monied(true).build_and_execute_with(|| {
		assert_ok!(Balances::set_freeze(&TestId::Foo, &1, u64::MAX));
		assert_ok!(Balances::set_freeze(&TestId::Foo, &1, 5));
		assert_ok!(<Balances as fungible::Mutate<_>>::transfer(&1, &2, 5, CanKill));
		assert_noop!(<Balances as fungible::Mutate<_>>::transfer(&1, &2, 1, CanKill), TokenError::Frozen);
	});
}

#[test]
fn extend_freeze_should_work() {
	ExtBuilder::default().existential_deposit(1).monied(true).build_and_execute_with(|| {
		assert_ok!(Balances::set_freeze(&TestId::Foo, &1, 5));
		assert_ok!(Balances::extend_freeze(&TestId::Foo, &1, 10));
		assert_eq!(Balances::account(&1).frozen, 10);
		assert_eq!(Balances::balance_frozen(&TestId::Foo, &1), 10);
		assert_noop!(<Balances as fungible::Mutate<_>>::transfer(&1, &2, 1, CanKill), TokenError::Frozen);
	});
}

#[test]
fn double_freezing_should_work() {
	ExtBuilder::default().existential_deposit(1).monied(true).build_and_execute_with(|| {
		assert_ok!(Balances::set_freeze(&TestId::Foo, &1, 5));
		assert_ok!(Balances::set_freeze(&TestId::Bar, &1, 5));
		assert_eq!(System::consumers(&1), 1);
		assert_ok!(<Balances as fungible::Mutate<_>>::transfer(&1, &2, 5, CanKill));
		assert_noop!(<Balances as fungible::Mutate<_>>::transfer(&1, &2, 1, CanKill), TokenError::Frozen);
	});
}

#[test]
fn can_hold_entire_balance_when_second_provider() {
	ExtBuilder::default().existential_deposit(1).monied(false).build_and_execute_with(|| {
		<Balances as fungible::Mutate<_>>::make_balance_be(&1, 100);
		assert_noop!(Balances::hold(&TestId::Foo, &1, 100), TokenError::FundsUnavailable);
		System::inc_providers(&1);
		assert_eq!(System::providers(&1), 2);
		assert_ok!(Balances::hold(&TestId::Foo, &1, 100));
		assert_eq!(System::providers(&1), 1);
		assert_noop!(System::dec_providers(&1), DispatchError::ConsumerRemaining);
	});
}
