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
use crate::mock::{RuntimeCall, *};

use frame_support::{assert_err, assert_noop, assert_ok, dispatch::Dispatchable};

// GENERAL FAIL/NEGATIVE TESTS ---------------------

#[test]
fn fails_to_filter_calls_to_safe_mode_pallet() {
	new_test_ext().execute_with(|| {
		assert_ok!(SafeMode::activate(Origin::signed(0)));
		let activated_at_block = System::block_number();
		let call = RuntimeCall::Balances(pallet_balances::Call::transfer { dest: 1, value: 1 });

		assert_err!(
			call.clone().dispatch(Origin::signed(0)),
			frame_system::Error::<Test>::CallFiltered
		);
		// TODO ^^^ consider refactor to throw a safe mode error, not generic `CallFiltered`

		next_block();
		assert_ok!(SafeMode::extend(Origin::signed(0)));
		assert_ok!(SafeMode::force_extend(ForceExtendOrigin::Weak.signed()));
		assert_err!(
			call.clone().dispatch(Origin::signed(0)),
			frame_system::Error::<Test>::CallFiltered
		);
		assert_ok!(SafeMode::force_inactivate(Origin::signed(mock::DeactivateOrigin::get())));
		assert_ok!(SafeMode::repay_stake(
			Origin::signed(mock::RepayOrigin::get()),
			0,
			activated_at_block
		));

		next_block();
		assert_ok!(SafeMode::activate(Origin::signed(0)));
		assert_err!(
			call.clone().dispatch(Origin::signed(0)),
			frame_system::Error::<Test>::CallFiltered
		);
		assert_ok!(SafeMode::force_inactivate(Origin::signed(mock::DeactivateOrigin::get())));
		assert_ok!(SafeMode::slash_stake(
			Origin::signed(mock::RepayOrigin::get()),
			0,
			activated_at_block + 2
		));
	});
}

#[test]
fn fails_to_extend_if_not_activated() {
	new_test_ext().execute_with(|| {
		assert_eq!(SafeMode::active_until(), None);
		assert_noop!(SafeMode::extend(Origin::signed(2)), Error::<Test>::IsInactive);
	});
}

// GENERAL SUCCESS/POSITIVE TESTS ---------------------

#[test]
fn can_automatically_inactivate_after_timeout() {
	new_test_ext().execute_with(|| {
		let activated_at_block = System::block_number();
		assert_ok!(SafeMode::force_activate(ForceActivateOrigin::Weak.signed()));
		run_to(ForceActivateOrigin::Weak.duration() + activated_at_block + 1);
		SafeMode::on_initialize(System::block_number());
		assert_eq!(SafeMode::active_until(), None);
	});
}

#[test]
fn can_filter_balance_calls_when_activated() {
	new_test_ext().execute_with(|| {
		let call = RuntimeCall::Balances(pallet_balances::Call::transfer { dest: 1, value: 1 });

		assert_ok!(call.clone().dispatch(Origin::signed(0)));
		assert_ok!(SafeMode::activate(Origin::signed(0)));
		assert_err!(
			call.clone().dispatch(Origin::signed(0)),
			frame_system::Error::<Test>::CallFiltered
		);
		// TODO ^^^ consider refactor to throw a safe mode error, not generic `CallFiltered`
	});
}

// SIGNED ORIGIN CALL TESTS ---------------------

#[test]
fn can_activate_with_signed_origin() {
	new_test_ext().execute_with(|| {
		assert_ok!(SafeMode::activate(Origin::signed(0)));
		assert_eq!(
			SafeMode::active_until().unwrap(),
			System::block_number() + mock::ActivateDuration::get()
		);
		assert_eq!(Balances::reserved_balance(0), mock::ActivateStakeAmount::get());
		assert_noop!(SafeMode::activate(Origin::signed(0)), Error::<Test>::IsActive);
		// Assert the stake.
		assert_eq!(Stakes::<Test>::get(0, 1), Some(mock::ActivateStakeAmount::get()));
	});
}

#[test]
fn can_extend_with_signed_origin() {
	new_test_ext().execute_with(|| {
		assert_ok!(SafeMode::activate(Origin::signed(0)));
		assert_ok!(SafeMode::extend(Origin::signed(0)));
		assert_eq!(
			SafeMode::active_until().unwrap(),
			System::block_number() + mock::ActivateDuration::get() + mock::ExtendDuration::get()
		);
		assert_eq!(
			Balances::reserved_balance(0),
			mock::ActivateStakeAmount::get() + mock::ExtendStakeAmount::get()
		);
	});
}

#[test]
fn fails_signed_origin_when_explicit_origin_required() {
	new_test_ext().execute_with(|| {
		assert_eq!(SafeMode::active_until(), None);
		let activated_at_block = System::block_number();

		assert_err!(SafeMode::force_activate(Origin::signed(0)), DispatchError::BadOrigin);
		assert_err!(SafeMode::force_extend(Origin::signed(0)), DispatchError::BadOrigin);
		assert_err!(SafeMode::force_inactivate(Origin::signed(0)), DispatchError::BadOrigin);
		assert_err!(
			SafeMode::slash_stake(Origin::signed(0), 0, activated_at_block),
			DispatchError::BadOrigin
		);
		assert_err!(
			SafeMode::repay_stake(Origin::signed(0), 0, activated_at_block),
			DispatchError::BadOrigin
		);
	});
}

// CONFIGURED ORIGIN CALL TESTS ---------------------

#[test]
fn fails_force_inactivate_if_not_activated() {
	new_test_ext().execute_with(|| {
		assert_noop!(
			SafeMode::force_inactivate(Origin::signed(mock::DeactivateOrigin::get())),
			Error::<Test>::IsInactive
		);
		assert_noop!(
			SafeMode::force_inactivate(Origin::signed(mock::DeactivateOrigin::get())),
			Error::<Test>::IsInactive
		);
	});
}

#[test]
fn can_force_activate_with_config_origin() {
	new_test_ext().execute_with(|| {
		assert_ok!(SafeMode::force_activate(ForceActivateOrigin::Weak.signed()));
		assert_eq!(
			SafeMode::active_until().unwrap(),
			System::block_number() + ForceActivateOrigin::Weak.duration()
		);
		assert_noop!(
			SafeMode::force_activate(ForceActivateOrigin::Weak.signed()),
			Error::<Test>::IsActive
		);
		assert_eq!(Balances::reserved_balance(ForceActivateOrigin::Weak.acc()), 0);
	});
}

#[test]
fn can_force_inactivate_with_config_origin() {
	new_test_ext().execute_with(|| {
		assert_eq!(SafeMode::active_until(), None);
		assert_err!(
			SafeMode::force_inactivate(Origin::signed(mock::DeactivateOrigin::get())),
			Error::<Test>::IsInactive
		);
		assert_ok!(SafeMode::force_activate(ForceActivateOrigin::Weak.signed()));
		assert_eq!(Balances::reserved_balance(ForceActivateOrigin::Weak.acc()), 0);
		assert_ok!(SafeMode::force_inactivate(Origin::signed(mock::DeactivateOrigin::get())));
	});
}

#[test]
fn can_force_extend_with_config_origin() {
	new_test_ext().execute_with(|| {
		// Activated by `Weak` and extended by `Medium`.
		assert_ok!(SafeMode::force_activate(ForceActivateOrigin::Weak.signed()));
		assert_eq!(
			SafeMode::active_until().unwrap(),
			System::block_number() + ForceActivateOrigin::Weak.duration()
		);
		assert_ok!(SafeMode::force_extend(ForceExtendOrigin::Medium.signed()));
		assert_eq!(
			SafeMode::active_until().unwrap(),
			System::block_number() +
				ForceActivateOrigin::Weak.duration() +
				ForceExtendOrigin::Medium.duration()
		);
		assert_eq!(Balances::reserved_balance(ForceActivateOrigin::Weak.acc()), 0);
		assert_eq!(Balances::reserved_balance(mock::ExtendDuration::get()), 0);
	});
}

#[test]
fn can_repay_stake_with_config_origin() {
	new_test_ext().execute_with(|| {
		let activated_at_block = System::block_number();
		assert_ok!(SafeMode::activate(Origin::signed(0)));
		assert_err!(
			SafeMode::repay_stake(Origin::signed(mock::RepayOrigin::get()), 0, activated_at_block),
			Error::<Test>::IsActive
		);
		run_to(mock::ActivateDuration::get() + activated_at_block + 1);
		SafeMode::on_initialize(System::block_number());
		assert_ok!(SafeMode::repay_stake(
			Origin::signed(mock::RepayOrigin::get()),
			0,
			activated_at_block
		));
		// TODO: test accounting is correct
	});
}

#[test]
fn can_slash_stake_with_config_origin() {
	new_test_ext().execute_with(|| {
		let activated_at_block = System::block_number();
		assert_ok!(SafeMode::activate(Origin::signed(0)));
		assert_err!(
			SafeMode::slash_stake(Origin::signed(mock::RepayOrigin::get()), 0, activated_at_block),
			Error::<Test>::IsActive
		);
		run_to(mock::ActivateDuration::get() + activated_at_block + 1);
		SafeMode::on_initialize(System::block_number());
		assert_ok!(SafeMode::slash_stake(
			Origin::signed(mock::RepayOrigin::get()),
			0,
			activated_at_block
		));
		// TODO: test accounting is correct
	});
}

#[test]
fn fails_when_explicit_origin_required() {
	new_test_ext().execute_with(|| {
		assert_eq!(SafeMode::active_until(), None);
		let activated_at_block = System::block_number();

		assert_err!(
			SafeMode::force_extend(ForceActivateOrigin::Weak.signed()),
			DispatchError::BadOrigin
		);
		assert_err!(
			SafeMode::force_inactivate(ForceActivateOrigin::Weak.signed()),
			DispatchError::BadOrigin
		);
		assert_err!(
			SafeMode::slash_stake(ForceActivateOrigin::Weak.signed(), 0, activated_at_block),
			DispatchError::BadOrigin
		);
		assert_err!(
			SafeMode::repay_stake(ForceActivateOrigin::Weak.signed(), 0, activated_at_block),
			DispatchError::BadOrigin
		);

		assert_err!(
			SafeMode::force_activate(ForceExtendOrigin::Weak.signed()),
			DispatchError::BadOrigin
		);
		assert_err!(
			SafeMode::force_inactivate(ForceExtendOrigin::Weak.signed()),
			DispatchError::BadOrigin
		);
		assert_err!(
			SafeMode::slash_stake(ForceExtendOrigin::Weak.signed(), 0, activated_at_block),
			DispatchError::BadOrigin
		);
		assert_err!(
			SafeMode::repay_stake(ForceExtendOrigin::Weak.signed(), 0, activated_at_block),
			DispatchError::BadOrigin
		);

		assert_err!(
			SafeMode::force_activate(Origin::signed(mock::DeactivateOrigin::get())),
			DispatchError::BadOrigin
		);
		assert_err!(
			SafeMode::force_extend(Origin::signed(mock::DeactivateOrigin::get())),
			DispatchError::BadOrigin
		);
		assert_err!(
			SafeMode::slash_stake(
				Origin::signed(mock::DeactivateOrigin::get()),
				0,
				activated_at_block
			),
			DispatchError::BadOrigin
		);
		assert_err!(
			SafeMode::repay_stake(
				Origin::signed(mock::DeactivateOrigin::get()),
				0,
				activated_at_block
			),
			DispatchError::BadOrigin
		);

		assert_err!(
			SafeMode::force_activate(Origin::signed(mock::RepayOrigin::get())),
			DispatchError::BadOrigin
		);
		assert_err!(
			SafeMode::force_extend(Origin::signed(mock::RepayOrigin::get())),
			DispatchError::BadOrigin
		);
		assert_err!(
			SafeMode::force_inactivate(Origin::signed(mock::RepayOrigin::get())),
			DispatchError::BadOrigin
		);
	});
}
