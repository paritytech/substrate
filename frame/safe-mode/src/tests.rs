// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

//! Test utilities for the safe mode pallet.

use super::*;
use crate::mock::{Call, *};

use frame_support::{assert_err, assert_noop, assert_ok};
use frame_support::dispatch::Dispatchable;

#[test]
fn enabled_cannot_filter_calls_to_itself() {
	new_test_ext().execute_with(|| {
		assert_ok!(SafeMode::enable(Origin::signed(1)));
		let call = Call::Balances(pallet_balances::Call::transfer{dest: 1, value: 1});
		assert_err!(call.dispatch(Origin::signed(3)), frame_system::Error::<Test>::CallFiltered);
		// TODO ^^^ should be filtered (and ideally throw a safe mode error,
		// not something generic or simply a call filter). done :)
		assert_ok!(SafeMode::extend(Origin::signed(2)));
		assert_ok!(SafeMode::extend(Origin::signed(3)));
		assert_ok!(SafeMode::force_disable(Origin::root()));
	});
}

#[test]
fn extend_fails_if_not_enabled() {
	new_test_ext().execute_with(|| {
		assert_eq!(SafeMode::enabled(), None);
		assert_noop!(SafeMode::extend(Origin::signed(2)), Error::<Test>::IsDisabled);
	});
}

#[test]
fn automatically_disable_after_timeout() {
	new_test_ext().execute_with(|| {
		let enabled_at_block = System::block_number();
		assert_ok!(SafeMode::force_enable(Origin::root()));
		run_to(mock::EnableDuration::get() + enabled_at_block + 1);
		SafeMode::on_initialize(System::block_number());
		assert_eq!(SafeMode::enabled(), None);
	});
}

#[test]
fn enabled_filters_balance_calls() {
	new_test_ext().execute_with(|| {
		assert_ok!(Balances::transfer(Origin::signed(1), 2, 1));
		assert_ok!(SafeMode::enable(Origin::signed(2)));
		let call = Call::Balances(pallet_balances::Call::transfer{dest:3,value: 1});
		assert_err!(call.dispatch(Origin::signed(3)), frame_system::Error::<Test>::CallFiltered);
		// TODO ^^^ should be filtered (and ideally throw a safe mode error,
		// not something generic or simply a call filter)
		// Now we get a `CallFiltered` error. The trick is to `.dispatch` the calls.
	});
}

// SIGNED ORIGIN TESTS ---------------------

#[test]
fn signed_origin_can_enable() {
	new_test_ext().execute_with(|| {
		assert_ok!(SafeMode::enable(Origin::signed(1)));
		assert_eq!(
			SafeMode::enabled().unwrap(),
			System::block_number() + mock::EnableDuration::get()
		);
		// TODO check stake reserved correctly here? yep
		assert_noop!(SafeMode::enable(Origin::signed(1)), Error::<Test>::IsEnabled);
		// Assert the stake.
		assert_eq!(Stakes::<Test>::get(1, 1), Some(mock::EnableStakeAmount::get()));
	});
}

#[test]
fn signed_origin_can_extend() {
	new_test_ext().execute_with(|| {
		assert_ok!(SafeMode::enable(Origin::signed(1)));
		assert_ok!(SafeMode::extend(Origin::signed(2)));
		assert_eq!(
			SafeMode::enabled().unwrap(),
			System::block_number() + mock::EnableDuration::get() + mock::ExtendDuration::get()
		);
	});
}

// CONFIGURED ORIGIN TESTS ---------------------

#[test]
fn force_disable_fails_if_not_enabled() {
	new_test_ext().execute_with(|| {
		assert_noop!(SafeMode::force_disable(Origin::root()), Error::<Test>::IsDisabled);
		assert_noop!(
			SafeMode::force_disable(Origin::signed(mock::DisableOrigin::get())),
			Error::<Test>::IsDisabled
		);
	});
}

#[test]
fn config_origin_can_force_enable() {
	new_test_ext().execute_with(|| {
		assert_ok!(SafeMode::force_enable(Origin::signed(mock::EnableOrigin::get())));
		assert_eq!(
			SafeMode::enabled().unwrap(),
			System::block_number() + mock::EnableDuration::get()
		);
		assert_noop!(
			SafeMode::force_enable(Origin::signed(mock::EnableOrigin::get())),
			Error::<Test>::IsEnabled
		);
	});
}

#[test]
fn config_origin_can_force_disable() {
	new_test_ext().execute_with(|| {
		assert_eq!(SafeMode::enabled(), None);
		assert_err!(
			SafeMode::force_disable(Origin::signed(mock::DisableOrigin::get())),
			Error::<Test>::IsDisabled
		);
		assert_ok!(SafeMode::force_enable(Origin::signed(mock::EnableOrigin::get())));
		assert_ok!(SafeMode::force_disable(Origin::signed(mock::DisableOrigin::get())));
	});
}

#[test]
fn config_origin_can_force_extend() {
	new_test_ext().execute_with(|| {
		assert_ok!(SafeMode::force_enable(Origin::signed(mock::EnableOrigin::get())));
		assert_eq!(
			SafeMode::enabled().unwrap(),
			System::block_number() + mock::EnableDuration::get()
		);
		assert_ok!(SafeMode::force_extend(Origin::signed(mock::ExtendOrigin::get())));
		assert_eq!(
			SafeMode::enabled().unwrap(),
			System::block_number() + mock::EnableDuration::get() + mock::ExtendDuration::get()
		);
	});
}

#[test]
fn config_origin_can_repay_stake() {
	new_test_ext().execute_with(|| {
		let enabled_at_block = System::block_number();
		assert_ok!(SafeMode::enable(Origin::signed(1)));
		assert_err!(
			SafeMode::repay_stake(Origin::signed(mock::RepayOrigin::get()), 1, enabled_at_block),
			Error::<Test>::IsEnabled
		);
		run_to(mock::EnableDuration::get() + enabled_at_block + 1);
		SafeMode::on_initialize(System::block_number());
		assert_ok!(SafeMode::repay_stake(Origin::signed(mock::RepayOrigin::get()), 1, enabled_at_block));
	});
}

#[test]
fn config_origin_can_slash_stake() {
	new_test_ext().execute_with(|| {
		let enabled_at_block = System::block_number();
		assert_ok!(SafeMode::enable(Origin::signed(1)));
		assert_err!(
			SafeMode::slash_stake(Origin::signed(mock::RepayOrigin::get()), 1, enabled_at_block),
			Error::<Test>::IsEnabled
		);
		run_to(mock::EnableDuration::get() + enabled_at_block + 1);
		SafeMode::on_initialize(System::block_number());
		assert_ok!(SafeMode::slash_stake(Origin::signed(mock::RepayOrigin::get()), 1, enabled_at_block));
	});
}

// ROOT TESTS ---------------------

#[test]
fn root_can_force_enable() {
	new_test_ext().execute_with(|| {
		assert_ok!(SafeMode::force_enable(Origin::root()));
		assert_eq!(
			SafeMode::enabled().unwrap(),
			System::block_number() + mock::EnableDuration::get()
		); // TODO read mock::EnableDuration instead of hard coded? Yes please
		assert_noop!(SafeMode::force_enable(Origin::root()), Error::<Test>::IsEnabled);
	});
}

#[test]
fn root_can_force_disable() {
	new_test_ext().execute_with(|| {
		assert_eq!(SafeMode::enabled(), None);
		assert_err!(SafeMode::force_disable(Origin::root()), Error::<Test>::IsDisabled);
		assert_ok!(SafeMode::force_enable(Origin::root()));
		assert_ok!(SafeMode::force_disable(Origin::root()));
	});
}

#[test]
fn root_can_force_extend() {
	new_test_ext().execute_with(|| {
		assert_ok!(SafeMode::force_enable(Origin::root()));
		assert_eq!(
			SafeMode::enabled().unwrap(),
			System::block_number() + mock::EnableDuration::get()
		);
		assert_ok!(SafeMode::force_extend(Origin::root()));
		assert_eq!(
			SafeMode::enabled().unwrap(),
			System::block_number() + mock::EnableDuration::get() + mock::ExtendDuration::get()
		);
	});
}

#[test]
fn root_can_repay_stake() {
	new_test_ext().execute_with(|| {
		let enabled_at_block = System::block_number();
		assert_ok!(SafeMode::enable(Origin::signed(1)));
		assert_err!(
			SafeMode::repay_stake(Origin::root(), 1, enabled_at_block),
			Error::<Test>::IsEnabled
		);
		run_to(mock::EnableDuration::get() + enabled_at_block + 1);
		SafeMode::on_initialize(System::block_number());
		assert_ok!(SafeMode::repay_stake(Origin::root(), 1, enabled_at_block));
	});
}

#[test]
fn root_can_slash_stake() {
	new_test_ext().execute_with(|| {
		let enabled_at_block = System::block_number();
		assert_ok!(SafeMode::enable(Origin::signed(1)));
		assert_err!(
			SafeMode::slash_stake(Origin::root(), 1, enabled_at_block),
			Error::<Test>::IsEnabled
		);
		run_to(mock::EnableDuration::get() + enabled_at_block + 1);
		assert_ok!(SafeMode::slash_stake(Origin::root(), 1, enabled_at_block));
	});
}
