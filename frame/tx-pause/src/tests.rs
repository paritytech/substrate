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
fn can_pause_specific_call() {
	new_test_ext().execute_with(|| {
		assert_ok!(call_transfer(1, 1).dispatch(Origin::signed(0)));

		assert_ok!(TxPause::pause_call(
			Origin::signed(mock::PauseOrigin::get()),
			name(b"Balances"),
			name(b"transfer"),
		));

		assert_err!(
			call_transfer(2, 1).dispatch(Origin::signed(2)),
			frame_system::Error::<Test>::CallFiltered
		);
		assert_ok!(call_transfer_keep_alive(3, 1).dispatch(Origin::signed(3)));
	});
}

#[test]
fn can_unpause_specific_call() {
	new_test_ext().execute_with(|| {
		assert_ok!(TxPause::pause_call(
			Origin::signed(mock::PauseOrigin::get()),
			name(b"Balances"),
			name(b"transfer"),
		));
		assert_err!(
			call_transfer(2, 1).dispatch(Origin::signed(2)),
			frame_system::Error::<Test>::CallFiltered
		);

		assert_ok!(TxPause::unpause_call(
			Origin::signed(mock::UnpauseOrigin::get()),
			name(b"Balances"),
			name(b"transfer"),
		));
		assert_ok!(call_transfer(4, 1).dispatch(Origin::signed(0)));
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
				name(b"pause_call")
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
				name(b"DummyPallet"),
				name(b"any-call")
			),
			Error::<Test>::IsUnpausable
		);
	});
}

#[test]
fn fails_to_pause_unpausable_call() {
	new_test_ext().execute_with(|| {
		assert_noop!(
			TxPause::pause_call(
				Origin::signed(mock::PauseOrigin::get()),
				name(b"Balances"),
				name(b"transfer_keep_alive"),
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
			name(b"Balances"),
			name(b"transfer"),
		));

		assert_noop!(
			TxPause::pause_call(
				Origin::signed(mock::PauseOrigin::get()),
				name(b"Balances"),
				name(b"transfer"),
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
				name(b"Balances"),
				name(b"transfer"),
			),
			Error::<Test>::IsUnpaused
		);
	});
}

fn name(bytes: &[u8]) -> BoundedVec<u8, MaxNameLen> {
	bytes.to_vec().try_into().unwrap()
}

fn call_transfer(dest: u64, value: u64) -> RuntimeCall {
	RuntimeCall::Balances(pallet_balances::Call::transfer { dest, value })
}

fn call_transfer_keep_alive(dest: u64, value: u64) -> RuntimeCall {
	RuntimeCall::Balances(pallet_balances::Call::transfer_keep_alive { dest, value })
}
