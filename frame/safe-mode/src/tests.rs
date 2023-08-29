// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

#![cfg(test)]

use super::*;
use crate::mock::{RuntimeCall, *};

use frame_support::{assert_err, assert_noop, assert_ok, dispatch::Dispatchable, traits::Currency};
use sp_runtime::TransactionOutcome;

/// Do something hypothetically by rolling back any changes afterwards.
///
/// Returns the original result of the closure.
macro_rules! hypothetically {
	( $e:expr ) => {
		frame_support::storage::transactional::with_transaction(
			|| -> TransactionOutcome<Result<_, sp_runtime::DispatchError>> {
				sp_runtime::TransactionOutcome::Rollback(Ok($e))
			},
		)
		.expect("Always returning Ok; qed")
	};
}

/// Assert something to be [*hypothetically*] `Ok` without actually committing it.
///
/// Reverts any storage changes made by the closure.
macro_rules! hypothetically_ok {
	($e:expr $(, $args:expr)* $(,)?) => {
		let result = hypothetically!($e);
		assert_ok!(result $(, $args)*);
	};
}

#[test]
fn fails_to_filter_calls_to_safe_mode_pallet() {
	new_test_ext().execute_with(|| {
		assert_ok!(SafeMode::enter(RuntimeOrigin::signed(0)));
		let activated_at_block = System::block_number();

		assert_err!(
			call_transfer().dispatch(RuntimeOrigin::signed(0)),
			frame_system::Error::<Test>::CallFiltered
		);

		next_block();
		assert_ok!(SafeMode::extend(RuntimeOrigin::signed(1)));
		assert_ok!(SafeMode::force_extend(signed(ForceExtendStrong::get())));
		assert_err!(
			call_transfer().dispatch(RuntimeOrigin::signed(0)),
			frame_system::Error::<Test>::CallFiltered
		);
		assert_ok!(SafeMode::force_exit(RuntimeOrigin::signed(mock::ForceExitOrigin::get())));
		assert_ok!(SafeMode::force_release_deposit(
			RuntimeOrigin::signed(mock::ForceDepositOrigin::get()),
			0,
			activated_at_block
		));

		next_block();
		assert_ok!(SafeMode::enter(RuntimeOrigin::signed(0)));
		assert_err!(
			call_transfer().dispatch(RuntimeOrigin::signed(0)),
			frame_system::Error::<Test>::CallFiltered
		);
		assert_ok!(SafeMode::force_exit(RuntimeOrigin::signed(mock::ForceExitOrigin::get())));
		assert_ok!(SafeMode::force_slash_deposit(
			RuntimeOrigin::signed(mock::ForceDepositOrigin::get()),
			0,
			activated_at_block + 2
		));
	});
}

#[test]
fn fails_to_activate_if_activated() {
	new_test_ext().execute_with(|| {
		assert_ok!(SafeMode::enter(RuntimeOrigin::signed(0)));
		assert_noop!(SafeMode::enter(RuntimeOrigin::signed(2)), Error::<Test>::Entered);
	});
}

#[test]
fn fails_to_extend_if_not_activated() {
	new_test_ext().execute_with(|| {
		assert_eq!(EnteredUntil::<Test>::get(), None);
		assert_noop!(SafeMode::extend(RuntimeOrigin::signed(2)), Error::<Test>::Exited);
	});
}

#[test]
fn fails_to_force_release_deposits_with_wrong_block() {
	new_test_ext().execute_with(|| {
		let activated_at_block = System::block_number();
		assert_ok!(SafeMode::enter(RuntimeOrigin::signed(0)));
		run_to(mock::EnterDuration::get() + activated_at_block + 1);

		assert_err!(
			SafeMode::force_release_deposit(
				RuntimeOrigin::signed(mock::ForceDepositOrigin::get()),
				0,
				activated_at_block + 1
			),
			Error::<Test>::NoDeposit
		);

		assert_err!(
			SafeMode::force_slash_deposit(
				RuntimeOrigin::signed(mock::ForceDepositOrigin::get()),
				0,
				activated_at_block + 1
			),
			Error::<Test>::NoDeposit
		);
	});
}

#[test]
fn fails_to_release_deposits_too_early() {
	new_test_ext().execute_with(|| {
		let activated_at_block = System::block_number();
		assert_ok!(SafeMode::enter(RuntimeOrigin::signed(0)));
		assert_ok!(SafeMode::force_exit(RuntimeOrigin::signed(mock::ForceExitOrigin::get())));
		assert_err!(
			SafeMode::release_deposit(RuntimeOrigin::signed(2), 0, activated_at_block),
			Error::<Test>::CannotReleaseYet
		);
		run_to(activated_at_block + mock::ReleaseDelay::get() + 1);
		assert_ok!(SafeMode::release_deposit(RuntimeOrigin::signed(2), 0, activated_at_block));
	});
}

// GENERAL SUCCESS/POSITIVE TESTS ---------------------

#[test]
fn can_automatically_deactivate_after_timeout() {
	new_test_ext().execute_with(|| {
		let activated_at_block = System::block_number();
		assert_ok!(SafeMode::force_enter(signed(ForceEnterWeak::get())));
		run_to(1 + activated_at_block + ForceEnterWeak::get());

		assert_eq!(EnteredUntil::<Test>::get(), None);
	});
}

#[test]
fn can_filter_balance_calls_when_activated() {
	new_test_ext().execute_with(|| {
		assert_ok!(call_transfer().dispatch(RuntimeOrigin::signed(0)));
		assert_ok!(SafeMode::enter(RuntimeOrigin::signed(0)));
		assert_err!(
			call_transfer().dispatch(RuntimeOrigin::signed(0)),
			frame_system::Error::<Test>::CallFiltered
		);
	});
}

#[test]
fn can_filter_balance_in_batch_when_activated() {
	new_test_ext().execute_with(|| {
		let batch_call =
			RuntimeCall::Utility(pallet_utility::Call::batch { calls: vec![call_transfer()] });

		assert_ok!(batch_call.clone().dispatch(RuntimeOrigin::signed(0)));

		assert_ok!(SafeMode::enter(RuntimeOrigin::signed(0)));

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
fn can_filter_balance_in_proxy_when_activated() {
	new_test_ext().execute_with(|| {
		assert_ok!(Proxy::add_proxy(RuntimeOrigin::signed(1), 2, ProxyType::JustTransfer, 0));

		assert_ok!(Proxy::proxy(RuntimeOrigin::signed(2), 1, None, Box::new(call_transfer())));
		System::assert_last_event(pallet_proxy::Event::ProxyExecuted { result: Ok(()) }.into());

		assert_ok!(SafeMode::force_enter(signed(ForceEnterWeak::get())));

		assert_ok!(Proxy::proxy(RuntimeOrigin::signed(2), 1, None, Box::new(call_transfer())));
		System::assert_last_event(
			pallet_proxy::Event::ProxyExecuted {
				result: DispatchError::from(frame_system::Error::<Test>::CallFiltered).into(),
			}
			.into(),
		);
	});
}

#[test]
fn can_activate() {
	new_test_ext().execute_with(|| {
		assert_ok!(SafeMode::enter(RuntimeOrigin::signed(0)));
		assert_eq!(
			EnteredUntil::<Test>::get().unwrap(),
			System::block_number() + mock::EnterDuration::get()
		);
		assert_eq!(Balances::reserved_balance(0), mock::EnterDepositAmount::get());
		assert_eq!(Notifications::get(), vec![(1, true)]);
		assert_noop!(SafeMode::enter(RuntimeOrigin::signed(0)), Error::<Test>::Entered);
		assert_eq!(Notifications::get(), vec![(1, true)]);
		// Assert the deposit.
		assert_eq!(Deposits::<Test>::get(0, 1), Some(mock::EnterDepositAmount::get()));
	});
}

#[test]
fn notify_works() {
	new_test_ext().execute_with(|| {
		assert_ok!(SafeMode::enter(RuntimeOrigin::signed(0)));
		assert_eq!(Notifications::get(), vec![(1, true)]);
		run_to(10);
		assert_eq!(Notifications::get(), vec![(1, true), (9, false)]);
		assert_ok!(SafeMode::enter(RuntimeOrigin::signed(1)));
		assert_ok!(SafeMode::extend(RuntimeOrigin::signed(2)));
		run_to(30);
		assert_eq!(Notifications::get(), vec![(1, true), (9, false), (10, true), (28, false)]);
	});
}

#[test]
fn cannot_extend() {
	new_test_ext().execute_with(|| {
		assert_ok!(SafeMode::enter(RuntimeOrigin::signed(0)));
		assert_err!(SafeMode::extend(RuntimeOrigin::signed(0)), Error::<Test>::AlreadyDeposited);
		assert_eq!(
			EnteredUntil::<Test>::get().unwrap(),
			System::block_number() + mock::EnterDuration::get()
		);
		assert_eq!(Balances::reserved_balance(0), mock::EnterDepositAmount::get());
		assert_eq!(Notifications::get(), vec![(1, true)]);
	});
}

#[test]
fn fails_signed_origin_when_explicit_origin_required() {
	new_test_ext().execute_with(|| {
		assert_eq!(EnteredUntil::<Test>::get(), None);
		let activated_at_block = System::block_number();

		assert_err!(SafeMode::force_enter(RuntimeOrigin::signed(0)), DispatchError::BadOrigin);
		assert_err!(SafeMode::force_extend(RuntimeOrigin::signed(0)), DispatchError::BadOrigin);
		assert_err!(SafeMode::force_exit(RuntimeOrigin::signed(0)), DispatchError::BadOrigin);
		assert_err!(
			SafeMode::force_slash_deposit(RuntimeOrigin::signed(0), 0, activated_at_block),
			DispatchError::BadOrigin
		);
		assert_err!(
			SafeMode::force_release_deposit(RuntimeOrigin::signed(0), 0, activated_at_block),
			DispatchError::BadOrigin
		);
	});
}

// CONFIGURED ORIGIN CALL TESTS ---------------------

#[test]
fn fails_force_deactivate_if_not_activated() {
	new_test_ext().execute_with(|| {
		assert_noop!(
			SafeMode::force_exit(RuntimeOrigin::signed(mock::ForceExitOrigin::get())),
			Error::<Test>::Exited
		);
		assert_noop!(
			SafeMode::force_exit(RuntimeOrigin::signed(mock::ForceExitOrigin::get())),
			Error::<Test>::Exited
		);
		assert!(Notifications::get().is_empty());
	});
}

#[test]
fn can_force_activate_with_config_origin() {
	new_test_ext().execute_with(|| {
		assert_ok!(SafeMode::force_enter(signed(ForceEnterStrong::get())));
		assert_eq!(Notifications::get(), vec![(1, true)]);
		assert_eq!(
			EnteredUntil::<Test>::get().unwrap(),
			System::block_number() + ForceEnterStrong::get()
		);
		assert_noop!(
			SafeMode::force_enter(signed(ForceEnterStrong::get())),
			Error::<Test>::Entered
		);
		assert_eq!(Notifications::get(), vec![(1, true)]);
	});
}

#[test]
fn can_force_deactivate_with_config_origin() {
	new_test_ext().execute_with(|| {
		assert_eq!(EnteredUntil::<Test>::get(), None);
		assert_err!(
			SafeMode::force_exit(RuntimeOrigin::signed(ForceExitOrigin::get())),
			Error::<Test>::Exited
		);
		assert_ok!(SafeMode::force_enter(signed(ForceEnterWeak::get())));
		assert_ok!(SafeMode::force_exit(RuntimeOrigin::signed(ForceExitOrigin::get())));
		assert_eq!(Notifications::get(), vec![(1, true), (1, false)]);
	});
}

#[test]
fn can_force_extend_with_config_origin() {
	new_test_ext().execute_with(|| {
		// Activated by `Weak` and extended by `Medium`.
		assert_ok!(SafeMode::force_enter(signed(ForceEnterWeak::get())));
		assert_eq!(
			EnteredUntil::<Test>::get().unwrap(),
			System::block_number() + ForceEnterWeak::get()
		);
		assert_ok!(SafeMode::force_extend(signed(ForceExtendWeak::get())));
		assert_eq!(
			EnteredUntil::<Test>::get().unwrap(),
			System::block_number() + ForceEnterWeak::get() + ForceExtendWeak::get()
		);
	});
}

#[test]
fn can_force_release_deposit_with_config_origin() {
	new_test_ext().execute_with(|| {
		let activated_at_block = System::block_number();
		assert_ok!(SafeMode::enter(RuntimeOrigin::signed(0)));
		hypothetically_ok!(SafeMode::force_release_deposit(
			RuntimeOrigin::signed(mock::ForceDepositOrigin::get()),
			0,
			activated_at_block
		),);
		run_to(mock::EnterDuration::get() + activated_at_block + 1);

		assert_ok!(SafeMode::force_release_deposit(
			RuntimeOrigin::signed(mock::ForceDepositOrigin::get()),
			0,
			activated_at_block
		));
		assert_eq!(Balances::free_balance(&0), BAL_ACC0); // accounts set in mock genesis

		Balances::make_free_balance_be(&0, BAL_ACC0);
		let activated_and_extended_at_block = System::block_number();
		assert_ok!(SafeMode::enter(RuntimeOrigin::signed(0)));
		assert_ok!(SafeMode::extend(RuntimeOrigin::signed(1)));
		run_to(
			mock::EnterDuration::get() +
				mock::ExtendDuration::get() +
				activated_and_extended_at_block +
				1,
		);

		assert_ok!(SafeMode::force_release_deposit(
			RuntimeOrigin::signed(mock::ForceDepositOrigin::get()),
			0,
			activated_and_extended_at_block
		));
		assert_eq!(Balances::free_balance(&0), BAL_ACC0); // accounts set in mock genesis
	});
}

#[test]
fn can_release_deposit_while_entered() {
	new_test_ext().execute_with(|| {
		assert_eq!(System::block_number(), 1);
		assert_ok!(SafeMode::enter(RuntimeOrigin::signed(0)));
		assert!(SafeMode::is_entered());

		assert_eq!(Balances::free_balance(&0), BAL_ACC0 - mock::EnterDepositAmount::get());

		// We could slash in the same block or any later.
		for i in 0..mock::EnterDuration::get() + 10 {
			run_to(i);
			hypothetically_ok!(SafeMode::force_release_deposit(
				RuntimeOrigin::signed(mock::ForceDepositOrigin::get()),
				0,
				1
			));
		}
		// Now once we slash once
		assert_ok!(SafeMode::force_release_deposit(
			RuntimeOrigin::signed(mock::ForceDepositOrigin::get()),
			0,
			1
		),);
		assert_eq!(Balances::free_balance(&0), BAL_ACC0);
		// ... it wont work ever again.
		assert_err!(
			SafeMode::force_release_deposit(
				RuntimeOrigin::signed(mock::ForceDepositOrigin::get()),
				0,
				1
			),
			Error::<Test>::NoDeposit
		);
	});
}

#[test]
fn can_slash_deposit_while_entered() {
	new_test_ext().execute_with(|| {
		assert_eq!(System::block_number(), 1);
		assert_ok!(SafeMode::enter(RuntimeOrigin::signed(0)));
		assert!(SafeMode::is_entered());

		// We could slash in the same block or any later.
		for i in 0..mock::EnterDuration::get() + 10 {
			run_to(i);
			hypothetically_ok!(SafeMode::force_slash_deposit(
				RuntimeOrigin::signed(mock::ForceDepositOrigin::get()),
				0,
				1
			));
		}
		// Now once we slash once
		assert_ok!(SafeMode::force_slash_deposit(
			RuntimeOrigin::signed(mock::ForceDepositOrigin::get()),
			0,
			1
		),);
		// ... it wont work ever again.
		assert_err!(
			SafeMode::force_slash_deposit(
				RuntimeOrigin::signed(mock::ForceDepositOrigin::get()),
				0,
				1
			),
			Error::<Test>::NoDeposit
		);
	});
}

#[test]
fn can_slash_deposit_from_extend_block() {
	new_test_ext().execute_with(|| {
		assert_ok!(SafeMode::enter(RuntimeOrigin::signed(0)));
		assert_ok!(SafeMode::extend(RuntimeOrigin::signed(1)));
		assert_eq!(Balances::free_balance(&0), BAL_ACC0 - mock::EnterDepositAmount::get());
		assert_eq!(Balances::free_balance(&1), BAL_ACC1 - mock::ExtendDepositAmount::get());

		assert_ok!(SafeMode::force_slash_deposit(
			RuntimeOrigin::signed(mock::ForceDepositOrigin::get()),
			0,
			1
		),);
		assert_eq!(Balances::free_balance(&0), BAL_ACC0 - mock::EnterDepositAmount::get());

		assert_ok!(SafeMode::force_slash_deposit(
			RuntimeOrigin::signed(mock::ForceDepositOrigin::get()),
			1,
			1
		),);
		assert_eq!(Balances::free_balance(&1), BAL_ACC1 - mock::ExtendDepositAmount::get());

		// But never again.
		assert_err!(
			SafeMode::force_slash_deposit(
				RuntimeOrigin::signed(mock::ForceDepositOrigin::get()),
				0,
				1
			),
			Error::<Test>::NoDeposit
		);
		assert_err!(
			SafeMode::force_slash_deposit(
				RuntimeOrigin::signed(mock::ForceDepositOrigin::get()),
				1,
				1
			),
			Error::<Test>::NoDeposit
		);
	});
}

#[test]
fn can_slash_deposit_with_config_origin() {
	new_test_ext().execute_with(|| {
		let activated_at_block = System::block_number();
		assert_ok!(SafeMode::enter(RuntimeOrigin::signed(0)));
		hypothetically_ok!(SafeMode::force_slash_deposit(
			RuntimeOrigin::signed(mock::ForceDepositOrigin::get()),
			0,
			activated_at_block
		),);
		run_to(mock::EnterDuration::get() + activated_at_block + 1);

		assert_ok!(SafeMode::force_slash_deposit(
			RuntimeOrigin::signed(mock::ForceDepositOrigin::get()),
			0,
			activated_at_block
		));
		// accounts set in mock genesis
		assert_eq!(Balances::free_balance(&0), BAL_ACC0 - mock::EnterDepositAmount::get());

		Balances::make_free_balance_be(&0, BAL_ACC0);
		let activated_and_extended_at_block = System::block_number();
		assert_ok!(SafeMode::enter(RuntimeOrigin::signed(0)));
		assert_ok!(SafeMode::extend(RuntimeOrigin::signed(1)));
		run_to(
			mock::EnterDuration::get() +
				mock::ExtendDuration::get() +
				activated_and_extended_at_block +
				1,
		);

		assert_ok!(SafeMode::force_slash_deposit(
			RuntimeOrigin::signed(mock::ForceDepositOrigin::get()),
			0,
			activated_and_extended_at_block
		));
		// accounts set in mock genesis
		assert_eq!(Balances::free_balance(&0), BAL_ACC0 - mock::EnterDepositAmount::get());
	});
}

#[test]
fn fails_when_explicit_origin_required() {
	new_test_ext().execute_with(|| {
		assert_eq!(EnteredUntil::<Test>::get(), None);
		let activated_at_block = System::block_number();

		assert_err!(SafeMode::force_extend(signed(1)), DispatchError::BadOrigin);
		assert_err!(SafeMode::force_exit(signed(1)), DispatchError::BadOrigin);
		assert_err!(
			SafeMode::force_slash_deposit(signed(1), 0, activated_at_block),
			DispatchError::BadOrigin
		);
		assert_err!(
			SafeMode::force_release_deposit(signed(1), 0, activated_at_block),
			DispatchError::BadOrigin
		);

		assert_err!(SafeMode::force_enter(signed(1)), DispatchError::BadOrigin);
		assert_err!(SafeMode::force_exit(signed(1)), DispatchError::BadOrigin);
		assert_err!(
			SafeMode::force_slash_deposit(signed(1), 0, activated_at_block),
			DispatchError::BadOrigin
		);
		assert_err!(
			SafeMode::force_release_deposit(signed(1), 0, activated_at_block),
			DispatchError::BadOrigin
		);

		assert_err!(
			SafeMode::force_enter(RuntimeOrigin::signed(mock::ForceExitOrigin::get())),
			DispatchError::BadOrigin
		);
		assert_err!(
			SafeMode::force_extend(RuntimeOrigin::signed(mock::ForceExitOrigin::get())),
			DispatchError::BadOrigin
		);
		assert_err!(
			SafeMode::force_slash_deposit(
				RuntimeOrigin::signed(mock::ForceExitOrigin::get()),
				0,
				activated_at_block
			),
			DispatchError::BadOrigin
		);
		assert_err!(
			SafeMode::force_release_deposit(
				RuntimeOrigin::signed(mock::ForceExitOrigin::get()),
				0,
				activated_at_block
			),
			DispatchError::BadOrigin
		);

		assert_err!(
			SafeMode::force_enter(RuntimeOrigin::signed(mock::ForceDepositOrigin::get())),
			DispatchError::BadOrigin
		);
		assert_err!(
			SafeMode::force_extend(RuntimeOrigin::signed(mock::ForceDepositOrigin::get())),
			DispatchError::BadOrigin
		);
		assert_err!(
			SafeMode::force_exit(RuntimeOrigin::signed(mock::ForceDepositOrigin::get())),
			DispatchError::BadOrigin
		);
	});
}

fn call_transfer() -> RuntimeCall {
	RuntimeCall::Balances(pallet_balances::Call::transfer { dest: 1, value: 1 })
}

fn signed(who: u64) -> RuntimeOrigin {
	RuntimeOrigin::signed(who)
}
