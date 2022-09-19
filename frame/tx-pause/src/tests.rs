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

#![cfg(test)]

use super::*;
use crate::mock::{Call, *};

use frame_support::{assert_err, assert_noop, assert_ok, dispatch::Dispatchable};

// GENERAL SUCCESS/POSITIVE TESTS ---------------------

#[test]
fn can_set_arbitrary_pause() {
	new_test_ext().execute_with(|| {
		assert_ok!(TxPause::pause_call(
			Origin::signed(mock::PauseOrigin::get()),
			b"SomePallet".to_vec().try_into().unwrap(),
			b"some_function".to_vec().try_into().unwrap(),
		));
	});
}

#[test]
fn can_pause_system_call() {
	new_test_ext().execute_with(|| {
		let call = Call::System(frame_system::Call::remark { remark: vec![] });

		assert_ok!(TxPause::pause_call(
			Origin::signed(mock::PauseOrigin::get()),
			b"System".to_vec().try_into().unwrap(),
			b"remark".to_vec().try_into().unwrap(),
		));

		assert_err!(
			call.clone().dispatch(Origin::signed(0)),
			frame_system::Error::<Test>::CallFiltered
		);
	});
}

#[test]
fn can_pause_specific_call() {
	new_test_ext().execute_with(|| {
		let call_paused = Call::Balances(pallet_balances::Call::transfer { dest: 1, value: 1 });
		let call_not_paused =
			Call::Balances(pallet_balances::Call::transfer_keep_alive { dest: 1, value: 1 });

		assert_ok!(TxPause::pause_call(
			Origin::signed(mock::PauseOrigin::get()),
			b"Balances".to_vec().try_into().unwrap(),
			b"transfer".to_vec().try_into().unwrap(),
		));

		assert_err!(
			call_paused.clone().dispatch(Origin::signed(0)),
			frame_system::Error::<Test>::CallFiltered
		);
		assert_ok!(call_not_paused.clone().dispatch(Origin::signed(0)));
	});
}

#[test]
fn can_unpause_specific_call() {
	new_test_ext().execute_with(|| {
		let call_paused = Call::Balances(pallet_balances::Call::transfer { dest: 1, value: 1 });

		assert_ok!(TxPause::pause_call(
			Origin::signed(mock::PauseOrigin::get()),
			b"Balances".to_vec().try_into().unwrap(),
			b"transfer".to_vec().try_into().unwrap(),
		));
		assert_err!(
			call_paused.clone().dispatch(Origin::signed(0)),
			frame_system::Error::<Test>::CallFiltered
		);

		assert_ok!(TxPause::unpause_call(
			Origin::signed(mock::UnpauseOrigin::get()),
			b"Balances".to_vec().try_into().unwrap(),
			b"transfer".to_vec().try_into().unwrap(),
		));
		assert_ok!(call_paused.clone().dispatch(Origin::signed(0)));
	});
}

// GENERAL FAIL/NEGATIVE TESTS ---------------------

#[test]
fn fails_to_pause_self() {
	new_test_ext().execute_with(|| {
		let within_bound_name =
			(0u8..(MaxNameLen::get() - 1).try_into().unwrap()).collect::<Vec<_>>();

		assert_noop!(
			TxPause::pause_call(
				Origin::signed(mock::PauseOrigin::get()),
				b"TxPause".to_vec().try_into().unwrap(),
				within_bound_name.try_into().expect("Function name under MaxNameLen")
			),
			Error::<Test>::IsUnpausable
		);
	});
}

#[test]
fn fails_to_pause_unpausable_pallet() {
	new_test_ext().execute_with(|| {
		let within_bound_name =
			(0u8..(MaxNameLen::get() - 1).try_into().unwrap()).collect::<Vec<_>>();

		assert_noop!(
			TxPause::pause_call(
				Origin::signed(mock::PauseOrigin::get()),
				b"UnpausablePallet".to_vec().try_into().unwrap(),
				within_bound_name.try_into().expect("Function name under MaxNameLen")
			),
			Error::<Test>::IsUnpausable
		);
	});
}

#[test]
#[should_panic(expected = "Pallet name under MaxNameLen")] // TODO - this test likely redundant/unneeded, as BoundedVec is effectively what we are testing.
fn panics_with_too_long_pallet_name() {
	new_test_ext().execute_with(|| {
		let too_long_name = (0u8..(MaxNameLen::get() + 1).try_into().unwrap()).collect::<Vec<_>>();
		let within_bound_name =
			(0u8..(MaxNameLen::get() - 1).try_into().unwrap()).collect::<Vec<_>>();

		assert_noop!(
			TxPause::pause_call(
				Origin::signed(mock::PauseOrigin::get()),
				too_long_name.try_into().expect("Pallet name under MaxNameLen"),
				within_bound_name.try_into().expect("Function name under MaxNameLen")
			),
			Error::<Test>::IsUnpausable
		);
	});
}

#[test]
fn fails_to_pause_already_paused_pallet() {
	new_test_ext().execute_with(|| {
		assert_ok!(TxPause::pause_call(
			Origin::signed(mock::PauseOrigin::get()),
			b"SomePallet".to_vec().try_into().unwrap(),
			b"some_function".to_vec().try_into().unwrap(),
		));

		assert_noop!(
			TxPause::pause_call(
				Origin::signed(mock::PauseOrigin::get()),
				b"SomePallet".to_vec().try_into().unwrap(),
				b"some_function".to_vec().try_into().unwrap(),
			),
			Error::<Test>::IsPaused
		);
	});
}

#[test]
fn fails_to_unpause_not_paused_pallet() {
	new_test_ext().execute_with(|| {
		assert_noop!(
			TxPause::unpause_call(
				Origin::signed(mock::UnpauseOrigin::get()),
				b"SomePallet".to_vec().try_into().unwrap(),
				b"some_function".to_vec().try_into().unwrap(),
			),
			Error::<Test>::IsUnpaused
		);
	});
}
