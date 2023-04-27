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

//! Tests regarding the functionality of the dispatchables/extrinsics.

use super::*;
use frame_support::traits::tokens::Preservation::Expendable;
use fungible::{hold::Mutate as HoldMutate, Inspect, Mutate};

#[test]
fn default_indexing_on_new_accounts_should_not_work2() {
	ExtBuilder::default()
		.existential_deposit(10)
		.monied(true)
		.build_and_execute_with(|| {
			// account 5 should not exist
			// ext_deposit is 10, value is 9, not satisfies for ext_deposit
			assert_noop!(
				Balances::transfer_allow_death(Some(1).into(), 5, 9),
				TokenError::BelowMinimum,
			);
			assert_eq!(Balances::free_balance(1), 100);
		});
}

#[test]
fn dust_account_removal_should_work() {
	ExtBuilder::default()
		.existential_deposit(100)
		.monied(true)
		.build_and_execute_with(|| {
			System::inc_account_nonce(&2);
			assert_eq!(System::account_nonce(&2), 1);
			assert_eq!(Balances::total_balance(&2), 2000);
			// index 1 (account 2) becomes zombie
			assert_ok!(Balances::transfer_allow_death(Some(2).into(), 5, 1901));
			assert_eq!(Balances::total_balance(&2), 0);
			assert_eq!(Balances::total_balance(&5), 1901);
			assert_eq!(System::account_nonce(&2), 0);
		});
}

#[test]
fn balance_transfer_works() {
	ExtBuilder::default().build_and_execute_with(|| {
		let _ = Balances::mint_into(&1, 111);
		assert_ok!(Balances::transfer_allow_death(Some(1).into(), 2, 69));
		assert_eq!(Balances::total_balance(&1), 42);
		assert_eq!(Balances::total_balance(&2), 69);
	});
}

#[test]
fn force_transfer_works() {
	ExtBuilder::default().build_and_execute_with(|| {
		let _ = Balances::mint_into(&1, 111);
		assert_noop!(Balances::force_transfer(Some(2).into(), 1, 2, 69), BadOrigin,);
		assert_ok!(Balances::force_transfer(RawOrigin::Root.into(), 1, 2, 69));
		assert_eq!(Balances::total_balance(&1), 42);
		assert_eq!(Balances::total_balance(&2), 69);
	});
}

#[test]
fn balance_transfer_when_on_hold_should_not_work() {
	ExtBuilder::default().build_and_execute_with(|| {
		let _ = Balances::mint_into(&1, 111);
		assert_ok!(Balances::hold(&TestId::Foo, &1, 69));
		assert_noop!(
			Balances::transfer_allow_death(Some(1).into(), 2, 69),
			TokenError::FundsUnavailable,
		);
	});
}

#[test]
fn transfer_keep_alive_works() {
	ExtBuilder::default().existential_deposit(1).build_and_execute_with(|| {
		let _ = Balances::mint_into(&1, 100);
		assert_noop!(
			Balances::transfer_keep_alive(Some(1).into(), 2, 100),
			TokenError::NotExpendable
		);
		assert_eq!(Balances::total_balance(&1), 100);
		assert_eq!(Balances::total_balance(&2), 0);
	});
}

#[test]
fn transfer_keep_alive_all_free_succeed() {
	ExtBuilder::default().existential_deposit(100).build_and_execute_with(|| {
		assert_ok!(Balances::force_set_balance(RuntimeOrigin::root(), 1, 300));
		assert_ok!(Balances::hold(&TestId::Foo, &1, 100));
		assert_ok!(Balances::transfer_keep_alive(Some(1).into(), 2, 100));
		assert_eq!(Balances::total_balance(&1), 200);
		assert_eq!(Balances::total_balance(&2), 100);
	});
}

#[test]
fn transfer_all_works_1() {
	ExtBuilder::default().existential_deposit(100).build().execute_with(|| {
		// setup
		assert_ok!(Balances::force_set_balance(RuntimeOrigin::root(), 1, 200));
		assert_ok!(Balances::force_set_balance(RuntimeOrigin::root(), 2, 0));
		// transfer all and allow death
		assert_ok!(Balances::transfer_all(Some(1).into(), 2, false));
		assert_eq!(Balances::total_balance(&1), 0);
		assert_eq!(Balances::total_balance(&2), 200);
	});
}

#[test]
fn transfer_all_works_2() {
	ExtBuilder::default().existential_deposit(100).build().execute_with(|| {
		// setup
		assert_ok!(Balances::force_set_balance(RuntimeOrigin::root(), 1, 200));
		assert_ok!(Balances::force_set_balance(RuntimeOrigin::root(), 2, 0));
		// transfer all and keep alive
		assert_ok!(Balances::transfer_all(Some(1).into(), 2, true));
		assert_eq!(Balances::total_balance(&1), 100);
		assert_eq!(Balances::total_balance(&2), 100);
	});
}

#[test]
fn transfer_all_works_3() {
	ExtBuilder::default().existential_deposit(100).build().execute_with(|| {
		// setup
		assert_ok!(Balances::force_set_balance(RuntimeOrigin::root(), 1, 210));
		assert_ok!(Balances::hold(&TestId::Foo, &1, 10));
		assert_ok!(Balances::force_set_balance(RuntimeOrigin::root(), 2, 0));
		// transfer all and allow death w/ reserved
		assert_ok!(Balances::transfer_all(Some(1).into(), 2, false));
		assert_eq!(Balances::total_balance(&1), 110);
		assert_eq!(Balances::total_balance(&2), 100);
	});
}

#[test]
fn transfer_all_works_4() {
	ExtBuilder::default().existential_deposit(100).build().execute_with(|| {
		// setup
		assert_ok!(Balances::force_set_balance(RuntimeOrigin::root(), 1, 210));
		assert_ok!(Balances::hold(&TestId::Foo, &1, 10));
		assert_ok!(Balances::force_set_balance(RuntimeOrigin::root(), 2, 0));
		// transfer all and keep alive w/ reserved
		assert_ok!(Balances::transfer_all(Some(1).into(), 2, true));
		assert_eq!(Balances::total_balance(&1), 110);
		assert_eq!(Balances::total_balance(&2), 100);
	});
}

#[test]
fn set_balance_handles_killing_account() {
	ExtBuilder::default().build_and_execute_with(|| {
		let _ = Balances::mint_into(&1, 111);
		assert_ok!(frame_system::Pallet::<Test>::inc_consumers(&1));
		assert_noop!(
			Balances::force_set_balance(RuntimeOrigin::root(), 1, 0),
			DispatchError::ConsumerRemaining,
		);
	});
}

#[test]
fn set_balance_handles_total_issuance() {
	ExtBuilder::default().build_and_execute_with(|| {
		let old_total_issuance = Balances::total_issuance();
		assert_ok!(Balances::force_set_balance(RuntimeOrigin::root(), 1337, 69));
		assert_eq!(Balances::total_issuance(), old_total_issuance + 69);
		assert_eq!(Balances::total_balance(&1337), 69);
		assert_eq!(Balances::free_balance(&1337), 69);
	});
}

#[test]
fn upgrade_accounts_should_work() {
	ExtBuilder::default()
		.existential_deposit(1)
		.monied(true)
		.build_and_execute_with(|| {
			System::inc_providers(&7);
			assert_ok!(<Test as Config>::AccountStore::try_mutate_exists(
				&7,
				|a| -> DispatchResult {
					*a = Some(AccountData {
						free: 5,
						reserved: 5,
						frozen: Zero::zero(),
						flags: crate::types::ExtraFlags::old_logic(),
					});
					Ok(())
				}
			));
			assert!(!Balances::account(&7).flags.is_new_logic());
			assert_eq!(System::providers(&7), 1);
			assert_eq!(System::consumers(&7), 0);
			assert_ok!(Balances::upgrade_accounts(Some(1).into(), vec![7]));
			assert!(Balances::account(&7).flags.is_new_logic());
			assert_eq!(System::providers(&7), 1);
			assert_eq!(System::consumers(&7), 1);

			<Balances as frame_support::traits::ReservableCurrency<_>>::unreserve(&7, 5);
			assert_ok!(<Balances as fungible::Mutate<_>>::transfer(&7, &1, 10, Expendable));
			assert_eq!(Balances::total_balance(&7), 0);
			assert_eq!(System::providers(&7), 0);
			assert_eq!(System::consumers(&7), 0);
		});
}
