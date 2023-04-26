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
use frame_support::traits::tokens::{
	Fortitude::{Force, Polite},
	Precision::{BestEffort, Exact},
	Preservation::{Expendable, Preserve, Protect},
	Restriction::Free,
};
use fungible::{Inspect, InspectFreeze, InspectHold, Mutate, MutateFreeze, MutateHold, Unbalanced};

#[test]
fn inspect_trait_reducible_balance_basic_works() {
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
fn inspect_trait_reducible_balance_other_provide_works() {
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
fn inspect_trait_reducible_balance_frozen_works() {
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
fn unbalanced_trait_set_balance_works() {
	ExtBuilder::default().build_and_execute_with(|| {
		assert_eq!(<Balances as fungible::Inspect<_>>::balance(&1337), 0);
		assert_ok!(Balances::write_balance(&1337, 100));
		assert_eq!(<Balances as fungible::Inspect<_>>::balance(&1337), 100);

		assert_ok!(<Balances as fungible::MutateHold<_>>::hold(&TestId::Foo, &1337, 60));
		assert_eq!(<Balances as fungible::Inspect<_>>::balance(&1337), 40);
		assert_eq!(<Balances as fungible::InspectHold<_>>::total_balance_on_hold(&1337), 60);
		assert_eq!(
			<Balances as fungible::InspectHold<_>>::balance_on_hold(&TestId::Foo, &1337),
			60
		);

		assert_noop!(Balances::write_balance(&1337, 0), Error::<Test>::InsufficientBalance);

		assert_ok!(Balances::write_balance(&1337, 1));
		assert_eq!(<Balances as fungible::Inspect<_>>::balance(&1337), 1);
		assert_eq!(
			<Balances as fungible::InspectHold<_>>::balance_on_hold(&TestId::Foo, &1337),
			60
		);

		assert_ok!(<Balances as fungible::MutateHold<_>>::release(&TestId::Foo, &1337, 60, Exact));
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
		assert_ok!(Balances::write_balance(&1337, 100));
		assert_eq!(<Balances as fungible::Inspect<_>>::balance(&1337), 100);
		// and reserves 50
		assert_ok!(<Balances as fungible::MutateHold<_>>::hold(&TestId::Foo, &1337, 50));
		assert_eq!(<Balances as fungible::Inspect<_>>::balance(&1337), 50);
		// and is decreased by 20
		assert_ok!(Balances::decrease_balance(&1337, 20, Exact, Expendable, Polite));
		assert_eq!(<Balances as fungible::Inspect<_>>::balance(&1337), 30);
	});
}

#[test]
fn unbalanced_trait_decrease_balance_works_1() {
	ExtBuilder::default().build_and_execute_with(|| {
		assert_ok!(Balances::write_balance(&1337, 100));
		assert_eq!(<Balances as fungible::Inspect<_>>::balance(&1337), 100);

		assert_noop!(
			Balances::decrease_balance(&1337, 101, Exact, Expendable, Polite),
			TokenError::FundsUnavailable
		);
		assert_eq!(Balances::decrease_balance(&1337, 100, Exact, Expendable, Polite), Ok(100));
		assert_eq!(<Balances as fungible::Inspect<_>>::balance(&1337), 0);
	});
}

#[test]
fn unbalanced_trait_decrease_balance_works_2() {
	ExtBuilder::default().build_and_execute_with(|| {
		// free: 40, reserved: 60
		assert_ok!(Balances::write_balance(&1337, 100));
		assert_ok!(Balances::hold(&TestId::Foo, &1337, 60));
		assert_eq!(<Balances as fungible::Inspect<_>>::balance(&1337), 40);
		assert_eq!(Balances::total_balance_on_hold(&1337), 60);
		assert_noop!(
			Balances::decrease_balance(&1337, 40, Exact, Expendable, Polite),
			Error::<Test>::InsufficientBalance
		);
		assert_eq!(Balances::decrease_balance(&1337, 39, Exact, Expendable, Polite), Ok(39));
		assert_eq!(<Balances as fungible::Inspect<_>>::balance(&1337), 1);
		assert_eq!(Balances::total_balance_on_hold(&1337), 60);
	});
}

#[test]
fn unbalanced_trait_decrease_balance_at_most_works_1() {
	ExtBuilder::default().build_and_execute_with(|| {
		assert_ok!(Balances::write_balance(&1337, 100));
		assert_eq!(<Balances as fungible::Inspect<_>>::balance(&1337), 100);

		assert_eq!(Balances::decrease_balance(&1337, 101, BestEffort, Expendable, Polite), Ok(100));
		assert_eq!(<Balances as fungible::Inspect<_>>::balance(&1337), 0);
	});
}

#[test]
fn unbalanced_trait_decrease_balance_at_most_works_2() {
	ExtBuilder::default().build_and_execute_with(|| {
		assert_ok!(Balances::write_balance(&1337, 99));
		assert_eq!(Balances::decrease_balance(&1337, 99, BestEffort, Expendable, Polite), Ok(99));
		assert_eq!(<Balances as fungible::Inspect<_>>::balance(&1337), 0);
	});
}

#[test]
fn unbalanced_trait_decrease_balance_at_most_works_3() {
	ExtBuilder::default().build_and_execute_with(|| {
		// free: 40, reserved: 60
		assert_ok!(Balances::write_balance(&1337, 100));
		assert_ok!(Balances::hold(&TestId::Foo, &1337, 60));
		assert_eq!(Balances::free_balance(1337), 40);
		assert_eq!(Balances::total_balance_on_hold(&1337), 60);
		assert_eq!(Balances::decrease_balance(&1337, 0, BestEffort, Expendable, Polite), Ok(0));
		assert_eq!(Balances::free_balance(1337), 40);
		assert_eq!(Balances::total_balance_on_hold(&1337), 60);
		assert_eq!(Balances::decrease_balance(&1337, 10, BestEffort, Expendable, Polite), Ok(10));
		assert_eq!(Balances::free_balance(1337), 30);
		assert_eq!(Balances::decrease_balance(&1337, 200, BestEffort, Expendable, Polite), Ok(29));
		assert_eq!(<Balances as fungible::Inspect<_>>::balance(&1337), 1);
		assert_eq!(Balances::free_balance(1337), 1);
		assert_eq!(Balances::total_balance_on_hold(&1337), 60);
	});
}

#[test]
fn unbalanced_trait_increase_balance_works() {
	ExtBuilder::default().build_and_execute_with(|| {
		assert_noop!(Balances::increase_balance(&1337, 0, Exact), TokenError::BelowMinimum);
		assert_eq!(Balances::increase_balance(&1337, 1, Exact), Ok(1));
		assert_noop!(Balances::increase_balance(&1337, u64::MAX, Exact), ArithmeticError::Overflow);
	});
}

#[test]
fn unbalanced_trait_increase_balance_at_most_works() {
	ExtBuilder::default().build_and_execute_with(|| {
		assert_eq!(Balances::increase_balance(&1337, 0, BestEffort), Ok(0));
		assert_eq!(Balances::increase_balance(&1337, 1, BestEffort), Ok(1));
		assert_eq!(Balances::increase_balance(&1337, u64::MAX, BestEffort), Ok(u64::MAX - 1));
	});
}

#[test]
fn freezing_and_holds_should_overlap() {
	ExtBuilder::default()
		.existential_deposit(1)
		.monied(true)
		.build_and_execute_with(|| {
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
	ExtBuilder::default()
		.existential_deposit(1)
		.monied(true)
		.build_and_execute_with(|| {
			assert_ok!(Balances::set_freeze(&TestId::Foo, &1, 10));
			assert_ok!(Balances::hold(&TestId::Foo, &1, 9));
			assert_eq!(Balances::reducible_total_balance_on_hold(&1, Force), 9);
			assert_eq!(Balances::reducible_total_balance_on_hold(&1, Polite), 0);
			let e = TokenError::Frozen;
			assert_noop!(
				Balances::transfer_on_hold(&TestId::Foo, &1, &2, 1, Exact, Free, Polite),
				e
			);
			assert_ok!(Balances::transfer_on_hold(&TestId::Foo, &1, &2, 1, Exact, Free, Force));
		});
}

#[test]
fn frozen_hold_balance_best_effort_transfer_works() {
	ExtBuilder::default()
		.existential_deposit(1)
		.monied(true)
		.build_and_execute_with(|| {
			assert_ok!(Balances::set_freeze(&TestId::Foo, &1, 5));
			assert_ok!(Balances::hold(&TestId::Foo, &1, 9));
			assert_eq!(Balances::reducible_total_balance_on_hold(&1, Force), 9);
			assert_eq!(Balances::reducible_total_balance_on_hold(&1, Polite), 5);
			assert_ok!(Balances::transfer_on_hold(
				&TestId::Foo,
				&1,
				&2,
				10,
				BestEffort,
				Free,
				Polite
			));
			assert_eq!(Balances::total_balance(&1), 5);
			assert_eq!(Balances::total_balance(&2), 25);
		});
}

#[test]
fn partial_freezing_should_work() {
	ExtBuilder::default()
		.existential_deposit(1)
		.monied(true)
		.build_and_execute_with(|| {
			assert_ok!(Balances::set_freeze(&TestId::Foo, &1, 5));
			assert_eq!(System::consumers(&1), 1);
			assert_ok!(<Balances as fungible::Mutate<_>>::transfer(&1, &2, 5, Expendable));
			assert_noop!(
				<Balances as fungible::Mutate<_>>::transfer(&1, &2, 1, Expendable),
				TokenError::Frozen
			);
		});
}

#[test]
fn thaw_should_work() {
	ExtBuilder::default()
		.existential_deposit(1)
		.monied(true)
		.build_and_execute_with(|| {
			assert_ok!(Balances::set_freeze(&TestId::Foo, &1, u64::MAX));
			assert_ok!(Balances::thaw(&TestId::Foo, &1));
			assert_eq!(System::consumers(&1), 0);
			assert_eq!(Balances::balance_frozen(&TestId::Foo, &1), 0);
			assert_eq!(Balances::account(&1).frozen, 0);
			assert_ok!(<Balances as fungible::Mutate<_>>::transfer(&1, &2, 10, Expendable));
		});
}

#[test]
fn set_freeze_zero_should_work() {
	ExtBuilder::default()
		.existential_deposit(1)
		.monied(true)
		.build_and_execute_with(|| {
			assert_ok!(Balances::set_freeze(&TestId::Foo, &1, u64::MAX));
			assert_ok!(Balances::set_freeze(&TestId::Foo, &1, 0));
			assert_eq!(System::consumers(&1), 0);
			assert_eq!(Balances::balance_frozen(&TestId::Foo, &1), 0);
			assert_eq!(Balances::account(&1).frozen, 0);
			assert_ok!(<Balances as fungible::Mutate<_>>::transfer(&1, &2, 10, Expendable));
		});
}

#[test]
fn set_freeze_should_work() {
	ExtBuilder::default()
		.existential_deposit(1)
		.monied(true)
		.build_and_execute_with(|| {
			assert_ok!(Balances::set_freeze(&TestId::Foo, &1, u64::MAX));
			assert_ok!(Balances::set_freeze(&TestId::Foo, &1, 5));
			assert_ok!(<Balances as fungible::Mutate<_>>::transfer(&1, &2, 5, Expendable));
			assert_noop!(
				<Balances as fungible::Mutate<_>>::transfer(&1, &2, 1, Expendable),
				TokenError::Frozen
			);
		});
}

#[test]
fn extend_freeze_should_work() {
	ExtBuilder::default()
		.existential_deposit(1)
		.monied(true)
		.build_and_execute_with(|| {
			assert_ok!(Balances::set_freeze(&TestId::Foo, &1, 5));
			assert_ok!(Balances::extend_freeze(&TestId::Foo, &1, 10));
			assert_eq!(Balances::account(&1).frozen, 10);
			assert_eq!(Balances::balance_frozen(&TestId::Foo, &1), 10);
			assert_noop!(
				<Balances as fungible::Mutate<_>>::transfer(&1, &2, 1, Expendable),
				TokenError::Frozen
			);
		});
}

#[test]
fn double_freezing_should_work() {
	ExtBuilder::default()
		.existential_deposit(1)
		.monied(true)
		.build_and_execute_with(|| {
			assert_ok!(Balances::set_freeze(&TestId::Foo, &1, 5));
			assert_ok!(Balances::set_freeze(&TestId::Bar, &1, 5));
			assert_eq!(System::consumers(&1), 1);
			assert_ok!(<Balances as fungible::Mutate<_>>::transfer(&1, &2, 5, Expendable));
			assert_noop!(
				<Balances as fungible::Mutate<_>>::transfer(&1, &2, 1, Expendable),
				TokenError::Frozen
			);
		});
}

#[test]
fn can_hold_entire_balance_when_second_provider() {
	ExtBuilder::default()
		.existential_deposit(1)
		.monied(false)
		.build_and_execute_with(|| {
			<Balances as fungible::Mutate<_>>::set_balance(&1, 100);
			assert_noop!(Balances::hold(&TestId::Foo, &1, 100), TokenError::FundsUnavailable);
			System::inc_providers(&1);
			assert_eq!(System::providers(&1), 2);
			assert_ok!(Balances::hold(&TestId::Foo, &1, 100));
			assert_eq!(System::providers(&1), 1);
			assert_noop!(System::dec_providers(&1), DispatchError::ConsumerRemaining);
		});
}

#[test]
fn unholding_frees_hold_slot() {
	ExtBuilder::default()
		.existential_deposit(1)
		.monied(false)
		.build_and_execute_with(|| {
			<Balances as fungible::Mutate<_>>::set_balance(&1, 100);
			assert_ok!(Balances::hold(&TestId::Foo, &1, 10));
			assert_ok!(Balances::hold(&TestId::Bar, &1, 10));
			assert_ok!(Balances::release(&TestId::Foo, &1, 10, Exact));
			assert_ok!(Balances::hold(&TestId::Baz, &1, 10));
		});
}

#[test]
fn sufficients_work_properly_with_reference_counting() {
	ExtBuilder::default()
		.existential_deposit(1)
		.monied(true)
		.build_and_execute_with(|| {
			// Only run PoC when the system pallet is enabled, since the underlying bug is in the
			// system pallet it won't work with BalancesAccountStore
			if UseSystem::get() {
				// Start with a balance of 100
				<Balances as fungible::Mutate<_>>::set_balance(&1, 100);
				// Emulate a sufficient, in reality this could be reached by transferring a
				// sufficient asset to the account
				System::inc_sufficients(&1);
				// Spend the same balance multiple times
				assert_ok!(<Balances as fungible::Mutate<_>>::transfer(&1, &1337, 100, Expendable));
				assert_eq!(Balances::free_balance(&1), 0);
				assert_noop!(
					<Balances as fungible::Mutate<_>>::transfer(&1, &1337, 100, Expendable),
					TokenError::FundsUnavailable
				);
			}
		});
}

#[test]
fn emit_events_with_changing_freezes() {
	ExtBuilder::default().build_and_execute_with(|| {
		let _ = Balances::set_balance(&1, 100);
		System::reset_events();

		// Freeze = [] --> [10]
		assert_ok!(Balances::set_freeze(&TestId::Foo, &1, 10));
		assert_eq!(events(), [RuntimeEvent::Balances(crate::Event::Frozen { who: 1, amount: 10 })]);

		// Freeze = [10] --> [15]
		assert_ok!(Balances::set_freeze(&TestId::Foo, &1, 15));
		assert_eq!(events(), [RuntimeEvent::Balances(crate::Event::Frozen { who: 1, amount: 5 })]);

		// Freeze = [15] --> [15, 20]
		assert_ok!(Balances::set_freeze(&TestId::Bar, &1, 20));
		assert_eq!(events(), [RuntimeEvent::Balances(crate::Event::Frozen { who: 1, amount: 5 })]);

		// Freeze = [15, 20] --> [17, 20]
		assert_ok!(Balances::set_freeze(&TestId::Foo, &1, 17));
		for event in events() {
			match event {
				RuntimeEvent::Balances(crate::Event::Frozen { .. }) => {
					assert!(false, "unexpected freeze event")
				},
				RuntimeEvent::Balances(crate::Event::Thawed { .. }) => {
					assert!(false, "unexpected thaw event")
				},
				_ => continue,
			}
		}

		// Freeze = [17, 20] --> [17, 15]
		assert_ok!(Balances::set_freeze(&TestId::Bar, &1, 15));
		assert_eq!(events(), [RuntimeEvent::Balances(crate::Event::Thawed { who: 1, amount: 3 })]);

		// Freeze = [17, 15] --> [15]
		assert_ok!(Balances::thaw(&TestId::Foo, &1));
		assert_eq!(events(), [RuntimeEvent::Balances(crate::Event::Thawed { who: 1, amount: 2 })]);

		// Freeze = [15] --> []
		assert_ok!(Balances::thaw(&TestId::Bar, &1));
		assert_eq!(events(), [RuntimeEvent::Balances(crate::Event::Thawed { who: 1, amount: 15 })]);
	});
}
