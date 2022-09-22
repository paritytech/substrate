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
use crate::mock::{RuntimeCall, *};

use frame_support::{assert_err, assert_noop, assert_ok, dispatch::Dispatchable};

// GENERAL SUCCESS/POSITIVE TESTS ---------------------

#[test]
fn can_set_arbitrary_pause() {
	new_test_ext().execute_with(|| {
		assert_ok!(TxPause::pause_call(
			Origin::signed(mock::PauseOrigin::get()),
			name(b"SomePallet"),
			name(b"some_function"),
		));
	});
}

#[test]
fn can_pause_system_call() {
	new_test_ext().execute_with(|| {
		let call = RuntimeCall::System(frame_system::Call::remark { remark: vec![] });

		assert_ok!(TxPause::pause_call(
			Origin::signed(mock::PauseOrigin::get()),
			name(b"System"),
			name(b"remark"),
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
		let call_paused =
			RuntimeCall::Balances(pallet_balances::Call::transfer { dest: 1, value: 1 });
		let call_not_paused =
			RuntimeCall::Balances(pallet_balances::Call::transfer_keep_alive { dest: 1, value: 1 });

		assert_ok!(TxPause::pause_call(
			Origin::signed(mock::PauseOrigin::get()),
			name(b"Balances"),
			name(b"transfer"),
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
		let call_paused =
			RuntimeCall::Balances(pallet_balances::Call::transfer { dest: 1, value: 1 });

		assert_ok!(TxPause::pause_call(
			Origin::signed(mock::PauseOrigin::get()),
			name(b"Balances"),
			name(b"transfer"),
		));
		assert_err!(
			call_paused.clone().dispatch(Origin::signed(0)),
			frame_system::Error::<Test>::CallFiltered
		);

		assert_ok!(TxPause::unpause_call(
			Origin::signed(mock::UnpauseOrigin::get()),
			name(b"Balances"),
			name(b"transfer"),
		));
		assert_ok!(call_paused.clone().dispatch(Origin::signed(0)));
	});
}

// GENERAL FAIL/NEGATIVE TESTS ---------------------

#[test]
fn fails_to_pause_self() {
	new_test_ext().execute_with(|| {
		assert_noop!(
			TxPause::pause_call(
				Origin::signed(mock::PauseOrigin::get()),
				name(b"TxPause"),
				name(b"should_not_matter"),
			),
			Error::<Test>::IsUnpausable
		);
	});
}

#[test]
fn fails_to_pause_unpausable_pallet() {
	new_test_ext().execute_with(|| {
		assert_noop!(
			TxPause::pause_call(
				Origin::signed(mock::PauseOrigin::get()),
				name(b"UnpausablePallet"),
				name(b"should_not_matter"),
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
			name(b"SomePallet"),
			name(b"some_function"),
		));

		assert_noop!(
			TxPause::pause_call(
				Origin::signed(mock::PauseOrigin::get()),
				name(b"SomePallet"),
				name(b"some_function"),
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
				name(b"SomePallet"),
				name(b"some_function"),
			),
			Error::<Test>::IsUnpaused
		);
	});
}

fn name(bytes: &[u8]) -> BoundedVec<u8, MaxNameLen> {
	bytes.to_vec().try_into().unwrap()
}
