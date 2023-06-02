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
		assert_ok!(call_transfer(1, 1).dispatch(RuntimeOrigin::signed(0)));

		assert_ok!(TxPause::pause(
			RuntimeOrigin::signed(mock::PauseOrigin::get()),
			full_name::<Test>(b"Balances", b"transfer")
		));

		assert_err!(
			call_transfer(2, 1).dispatch(RuntimeOrigin::signed(2)),
			frame_system::Error::<Test>::CallFiltered
		);
		assert_ok!(call_transfer_keep_alive(3, 1).dispatch(RuntimeOrigin::signed(3)));
	});
}

#[test]
fn can_pause_all_calls_in_pallet_except_on_whitelist() {
	new_test_ext().execute_with(|| {
		assert_ok!(call_transfer(1, 1).dispatch(RuntimeOrigin::signed(0)));

		let batch_call =
			RuntimeCall::Utility(pallet_utility::Call::batch { calls: vec![call_transfer(1, 1)] });
		assert_ok!(batch_call.clone().dispatch(RuntimeOrigin::signed(0)));

		assert_ok!(TxPause::pause(
			RuntimeOrigin::signed(mock::PauseOrigin::get()),
			full_name::<Test>(b"Utility", b"batch")
		),);

		assert_err!(
			batch_call.clone().dispatch(RuntimeOrigin::signed(0)),
			frame_system::Error::<Test>::CallFiltered
		);
	});
}

#[test]
fn can_unpause_specific_call() {
	new_test_ext().execute_with(|| {
		assert_ok!(TxPause::pause(
			RuntimeOrigin::signed(mock::PauseOrigin::get()),
			full_name::<Test>(b"Balances", b"transfer"),
		));
		assert_err!(
			call_transfer(2, 1).dispatch(RuntimeOrigin::signed(2)),
			frame_system::Error::<Test>::CallFiltered
		);

		assert_ok!(TxPause::unpause(
			RuntimeOrigin::signed(mock::UnpauseOrigin::get()),
			full_name::<Test>(b"Balances", b"transfer"),
		));
		assert_ok!(call_transfer(4, 1).dispatch(RuntimeOrigin::signed(0)));
	});
}

#[test]
fn can_filter_balance_in_batch_when_paused() {
	new_test_ext().execute_with(|| {
		let batch_call =
			RuntimeCall::Utility(pallet_utility::Call::batch { calls: vec![call_transfer(1, 1)] });

		assert_ok!(TxPause::pause(
			RuntimeOrigin::signed(mock::PauseOrigin::get()),
			full_name::<Test>(b"Balances", b"transfer"),
		));

		assert_ok!(batch_call.clone().dispatch(RuntimeOrigin::signed(0)));
		System::assert_last_event(
			pallet_utility::Event::BatchInterrupted {
				index: 0,
				error: frame_system::Error::<Test>::CallFiltered.into(),
			}
			.into(),
		);
	});
}

#[test]
fn can_filter_balance_in_proxy_when_paused() {
	new_test_ext().execute_with(|| {
		assert_ok!(TxPause::pause(
			RuntimeOrigin::signed(mock::PauseOrigin::get()),
			full_name::<Test>(b"Balances", b"transfer"),
		));

		assert_ok!(Proxy::add_proxy(RuntimeOrigin::signed(1), 2, ProxyType::JustTransfer, 0));

		assert_ok!(Proxy::proxy(RuntimeOrigin::signed(2), 1, None, Box::new(call_transfer(1, 1))));
		System::assert_last_event(
			pallet_proxy::Event::ProxyExecuted {
				result: DispatchError::from(frame_system::Error::<Test>::CallFiltered).into(),
			}
			.into(),
		);
	});
}

// GENERAL FAIL/NEGATIVE TESTS ---------------------

#[test]
fn fails_to_pause_self() {
	new_test_ext().execute_with(|| {
		assert_noop!(
			TxPause::pause(
				RuntimeOrigin::signed(mock::PauseOrigin::get()),
				full_name::<Test>(b"TxPause", b"pause"),
			),
			Error::<Test>::Unpausable
		);
	});
}

#[test]
fn fails_to_pause_unpausable_call_when_other_call_is_paused() {
	new_test_ext().execute_with(|| {
		assert_ok!(call_transfer(1, 1).dispatch(RuntimeOrigin::signed(0)));

		let batch_call =
			RuntimeCall::Utility(pallet_utility::Call::batch { calls: vec![call_transfer(1, 1)] });
		assert_ok!(batch_call.clone().dispatch(RuntimeOrigin::signed(0)));

		assert_ok!(TxPause::pause(
			RuntimeOrigin::signed(mock::PauseOrigin::get()),
			full_name::<Test>(b"Balances", b"transfer"),
		));

		assert_ok!(call_transfer_keep_alive(3, 1).dispatch(RuntimeOrigin::signed(3)));
		assert_err!(
			call_transfer(2, 1).dispatch(RuntimeOrigin::signed(0)),
			frame_system::Error::<Test>::CallFiltered
		);
	});
}

#[test]
fn fails_to_pause_unpausable_call() {
	new_test_ext().execute_with(|| {
		assert_noop!(
			TxPause::pause(
				RuntimeOrigin::signed(mock::PauseOrigin::get()),
				full_name::<Test>(b"Balances", b"transfer_keep_alive"),
			),
			Error::<Test>::Unpausable
		);
	});
}

#[test]
fn fails_to_pause_already_paused_pallet() {
	new_test_ext().execute_with(|| {
		assert_ok!(TxPause::pause(
			RuntimeOrigin::signed(mock::PauseOrigin::get()),
			full_name::<Test>(b"Balances", b"transfer"),
		));

		assert_noop!(
			TxPause::pause(
				RuntimeOrigin::signed(mock::PauseOrigin::get()),
				full_name::<Test>(b"Balances", b"transfer"),
			),
			Error::<Test>::IsPaused
		);
	});
}

#[test]
fn fails_to_unpause_not_paused_pallet() {
	new_test_ext().execute_with(|| {
		assert_noop!(
			TxPause::unpause(
				RuntimeOrigin::signed(mock::UnpauseOrigin::get()),
				full_name::<Test>(b"Balances", b"transfer_keep_alive"),
			),
			Error::<Test>::IsUnpaused
		);
	});
}

pub fn call_transfer(dest: u64, value: u64) -> RuntimeCall {
	RuntimeCall::Balances(pallet_balances::Call::transfer { dest, value })
}

pub fn call_transfer_keep_alive(dest: u64, value: u64) -> RuntimeCall {
	RuntimeCall::Balances(pallet_balances::Call::transfer_keep_alive { dest, value })
}

pub fn full_name<T: Config>(pallet_name: &[u8], call_name: &[u8]) -> RuntimeCallNameOf<T> {
	<RuntimeCallNameOf<T>>::from((
		pallet_name.to_vec().try_into().unwrap(),
		call_name.to_vec().try_into().unwrap(),
	))
}
