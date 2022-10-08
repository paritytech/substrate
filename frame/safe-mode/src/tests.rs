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
		assert_ok!(SafeMode::force_deactivate(Origin::signed(mock::ForceDeactivateOrigin::get())));
		assert_ok!(SafeMode::release_reservation(
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
		assert_ok!(SafeMode::force_deactivate(Origin::signed(mock::ForceDeactivateOrigin::get())));
		assert_ok!(SafeMode::slash_reservation(
			Origin::signed(mock::RepayOrigin::get()),
			0,
			activated_at_block + 2
		));
	});
}

#[test]
fn fails_to_activate_if_activated() {
	new_test_ext().execute_with(|| {
		assert_ok!(SafeMode::activate(Origin::signed(0)));
		assert_noop!(SafeMode::activate(Origin::signed(2)), Error::<Test>::IsActive);
	});
}

#[test]
fn fails_to_extend_if_not_activated() {
	new_test_ext().execute_with(|| {
		assert_eq!(SafeMode::active_until(), None);
		assert_noop!(SafeMode::extend(Origin::signed(2)), Error::<Test>::IsInactive);
	});
}

#[test]
fn fails_to_release_reservations_with_wrong_block() {
	new_test_ext().execute_with(|| {
		let activated_at_block = System::block_number();
		assert_ok!(SafeMode::activate(Origin::signed(0)));
		run_to(mock::SignedActivationDuration::get() + activated_at_block + 1);

		assert_err!(
			SafeMode::release_reservation(
				Origin::signed(mock::RepayOrigin::get()),
				0,
				activated_at_block + 1
			),
			Error::<Test>::NoReservation
		);

		assert_err!(
			SafeMode::slash_reservation(
				Origin::signed(mock::RepayOrigin::get()),
				0,
				activated_at_block + 1
			),
			Error::<Test>::NoReservation
		);
	});
}

// GENERAL SUCCESS/POSITIVE TESTS ---------------------

#[test]
fn can_automatically_deactivate_after_timeout() {
	new_test_ext().execute_with(|| {
		let activated_at_block = System::block_number();
		assert_ok!(SafeMode::force_activate(ForceActivateOrigin::Weak.signed()));
		run_to((ForceActivateOrigin::Weak as BlockNumberFor<Test>) + activated_at_block + 1);

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

#[test]
fn can_repay_independent_reservations_by_block() {
	new_test_ext().execute_with(|| {
		let activated_at_block_0 = System::block_number();
		assert_ok!(SafeMode::activate(Origin::signed(0)));
		run_to(mock::SignedActivationDuration::get() + activated_at_block_0 + 1);

		let activated_at_block_1 = System::block_number();
		assert_ok!(SafeMode::activate(Origin::signed(0)));
		run_to(mock::SignedActivationDuration::get() + activated_at_block_1 + 1);

		assert_ok!(SafeMode::release_reservation(
			Origin::signed(mock::RepayOrigin::get()),
			0,
			activated_at_block_0
		));
		assert_eq!(Balances::free_balance(&0), 1234 - mock::ActivateReservationAmount::get()); // accounts set in mock genesis

		assert_ok!(SafeMode::slash_reservation(
			Origin::signed(mock::RepayOrigin::get()),
			0,
			activated_at_block_1
		));
		assert_eq!(Balances::total_balance(&0), 1234 - mock::ActivateReservationAmount::get()); // accounts set in mock genesis
	});
}

// SIGNED ORIGIN CALL TESTS ---------------------

#[test]
fn can_activate_with_signed_origin() {
	new_test_ext().execute_with(|| {
		assert_ok!(SafeMode::activate(Origin::signed(0)));
		assert_eq!(
			SafeMode::active_until().unwrap(),
			System::block_number() + mock::SignedActivationDuration::get()
		);
		assert_eq!(Balances::reserved_balance(0), mock::ActivateReservationAmount::get());
		assert_noop!(SafeMode::activate(Origin::signed(0)), Error::<Test>::IsActive);
		// Assert the stake.
		assert_eq!(Reservations::<Test>::get(0, 1), Some(mock::ActivateReservationAmount::get()));
	});
}

#[test]
fn can_extend_with_signed_origin() {
	new_test_ext().execute_with(|| {
		assert_ok!(SafeMode::activate(Origin::signed(0)));
		assert_ok!(SafeMode::extend(Origin::signed(0)));
		assert_eq!(
			SafeMode::active_until().unwrap(),
			System::block_number() +
				mock::SignedActivationDuration::get() +
				mock::SignedExtendDuration::get()
		);
		assert_eq!(
			Balances::reserved_balance(0),
			mock::ActivateReservationAmount::get() + mock::ExtendReservationAmount::get()
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
		assert_err!(SafeMode::force_deactivate(Origin::signed(0)), DispatchError::BadOrigin);
		assert_err!(
			SafeMode::slash_reservation(Origin::signed(0), 0, activated_at_block),
			DispatchError::BadOrigin
		);
		assert_err!(
			SafeMode::release_reservation(Origin::signed(0), 0, activated_at_block),
			DispatchError::BadOrigin
		);
	});
}

// CONFIGURED ORIGIN CALL TESTS ---------------------

#[test]
fn fails_force_deactivate_if_not_activated() {
	new_test_ext().execute_with(|| {
		assert_noop!(
			SafeMode::force_deactivate(Origin::signed(mock::ForceDeactivateOrigin::get())),
			Error::<Test>::IsInactive
		);
		assert_noop!(
			SafeMode::force_deactivate(Origin::signed(mock::ForceDeactivateOrigin::get())),
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
			System::block_number() + (ForceActivateOrigin::Weak  as BlockNumberFor<Test>)
		);
		assert_noop!(
			SafeMode::force_activate(ForceActivateOrigin::Weak.signed()),
			Error::<Test>::IsActive
		);
		assert_eq!(Balances::reserved_balance(ForceActivateOrigin::Weak.acc()), 0);
	});
}

#[test]
fn can_force_deactivate_with_config_origin() {
	new_test_ext().execute_with(|| {
		assert_eq!(SafeMode::active_until(), None);
		assert_err!(
			SafeMode::force_deactivate(Origin::signed(mock::ForceDeactivateOrigin::get())),
			Error::<Test>::IsInactive
		);
		assert_ok!(SafeMode::force_activate(ForceActivateOrigin::Weak.signed()));
		assert_eq!(Balances::reserved_balance(ForceActivateOrigin::Weak.acc()), 0);
		assert_ok!(SafeMode::force_deactivate(Origin::signed(mock::ForceDeactivateOrigin::get())));
	});
}

#[test]
fn can_force_extend_with_config_origin() {
	new_test_ext().execute_with(|| {
		// Activated by `Weak` and extended by `Medium`.
		assert_ok!(SafeMode::force_activate(ForceActivateOrigin::Weak.signed()));
		assert_eq!(
			SafeMode::active_until().unwrap(),
			System::block_number() + (ForceActivateOrigin::Weak as BlockNumberFor<Test>)
		);
		assert_ok!(SafeMode::force_extend(ForceExtendOrigin::Medium.signed()));
		assert_eq!(
			SafeMode::active_until().unwrap(),
			System::block_number() +
				ForceActivateOrigin::Weak as BlockNumberFor<Test> +
				ForceExtendOrigin::Medium as BlockNumberFor<Test>
		);
		assert_eq!(Balances::reserved_balance(ForceActivateOrigin::Weak.acc()), 0);
		assert_eq!(Balances::reserved_balance(mock::SignedExtendDuration::get()), 0);
	});
}

#[test]
fn can_release_reservation_with_config_origin() {
	new_test_ext().execute_with(|| {
		let activated_at_block = System::block_number();
		assert_ok!(SafeMode::activate(Origin::signed(0)));
		assert_err!(
			SafeMode::release_reservation(
				Origin::signed(mock::RepayOrigin::get()),
				0,
				activated_at_block
			),
			Error::<Test>::IsActive
		);
		run_to(mock::SignedActivationDuration::get() + activated_at_block + 1);

		assert_ok!(SafeMode::release_reservation(
			Origin::signed(mock::RepayOrigin::get()),
			0,
			activated_at_block
		));
		assert_eq!(Balances::free_balance(&0), 1234); // accounts set in mock genesis

		Balances::make_free_balance_be(&0, 1234);
		let activated_and_extended_at_block = System::block_number();
		assert_ok!(SafeMode::activate(Origin::signed(0)));
		assert_ok!(SafeMode::extend(Origin::signed(0)));
		run_to(
			mock::SignedActivationDuration::get() +
				mock::SignedExtendDuration::get() +
				activated_and_extended_at_block +
				1,
		);

		assert_ok!(SafeMode::release_reservation(
			Origin::signed(mock::RepayOrigin::get()),
			0,
			activated_and_extended_at_block
		));
		assert_eq!(Balances::free_balance(&0), 1234); // accounts set in mock genesis
	});
}

#[test]
fn can_slash_reservation_with_config_origin() {
	new_test_ext().execute_with(|| {
		let activated_at_block = System::block_number();
		assert_ok!(SafeMode::activate(Origin::signed(0)));
		assert_err!(
			SafeMode::slash_reservation(
				Origin::signed(mock::RepayOrigin::get()),
				0,
				activated_at_block
			),
			Error::<Test>::IsActive
		);
		run_to(mock::SignedActivationDuration::get() + activated_at_block + 1);

		assert_ok!(SafeMode::slash_reservation(
			Origin::signed(mock::RepayOrigin::get()),
			0,
			activated_at_block
		));
		assert_eq!(Balances::free_balance(&0), 1234 - mock::ActivateReservationAmount::get()); // accounts set in mock genesis

		Balances::make_free_balance_be(&0, 1234);
		let activated_and_extended_at_block = System::block_number();
		assert_ok!(SafeMode::activate(Origin::signed(0)));
		assert_ok!(SafeMode::extend(Origin::signed(0)));
		run_to(
			mock::SignedActivationDuration::get() +
				mock::SignedExtendDuration::get() +
				activated_and_extended_at_block +
				1,
		);

		assert_ok!(SafeMode::slash_reservation(
			Origin::signed(mock::RepayOrigin::get()),
			0,
			activated_and_extended_at_block
		));
		assert_eq!(
			Balances::free_balance(&0),
			1234 - mock::ActivateReservationAmount::get() - mock::ExtendReservationAmount::get()
		); // accounts set in mock genesis
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
			SafeMode::force_deactivate(ForceActivateOrigin::Weak.signed()),
			DispatchError::BadOrigin
		);
		assert_err!(
			SafeMode::slash_reservation(ForceActivateOrigin::Weak.signed(), 0, activated_at_block),
			DispatchError::BadOrigin
		);
		assert_err!(
			SafeMode::release_reservation(
				ForceActivateOrigin::Weak.signed(),
				0,
				activated_at_block
			),
			DispatchError::BadOrigin
		);

		assert_err!(
			SafeMode::force_activate(ForceExtendOrigin::Weak.signed()),
			DispatchError::BadOrigin
		);
		assert_err!(
			SafeMode::force_deactivate(ForceExtendOrigin::Weak.signed()),
			DispatchError::BadOrigin
		);
		assert_err!(
			SafeMode::slash_reservation(ForceExtendOrigin::Weak.signed(), 0, activated_at_block),
			DispatchError::BadOrigin
		);
		assert_err!(
			SafeMode::release_reservation(ForceExtendOrigin::Weak.signed(), 0, activated_at_block),
			DispatchError::BadOrigin
		);

		assert_err!(
			SafeMode::force_activate(Origin::signed(mock::ForceDeactivateOrigin::get())),
			DispatchError::BadOrigin
		);
		assert_err!(
			SafeMode::force_extend(Origin::signed(mock::ForceDeactivateOrigin::get())),
			DispatchError::BadOrigin
		);
		assert_err!(
			SafeMode::slash_reservation(
				Origin::signed(mock::ForceDeactivateOrigin::get()),
				0,
				activated_at_block
			),
			DispatchError::BadOrigin
		);
		assert_err!(
			SafeMode::release_reservation(
				Origin::signed(mock::ForceDeactivateOrigin::get()),
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
			SafeMode::force_deactivate(Origin::signed(mock::RepayOrigin::get())),
			DispatchError::BadOrigin
		);
	});
}
