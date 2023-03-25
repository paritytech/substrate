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

/// Assert something to be [*hypothetically*] `Ok`.
macro_rules! hypothetically_ok {
	($e:expr $(, $args:expr)* $(,)?) => {
		let result = hypothetically!($e);
		assert_ok!(result $(, $args)*);
	};
}

// GENERAL FAIL/NEGATIVE TESTS ---------------------

#[test]
fn fails_to_filter_calls_to_safe_mode_pallet() {
	new_test_ext().execute_with(|| {
		assert_ok!(SafeMode::enter(RuntimeOrigin::signed(0)));
		let activated_at_block = System::block_number();

		assert_err!(
			call_transfer().dispatch(RuntimeOrigin::signed(0)),
			frame_system::Error::<Test>::CallFiltered
		);
		// TODO ^^^ consider refactor to throw a safe mode error, not generic `CallFiltered`

		next_block();
		assert_ok!(SafeMode::extend(RuntimeOrigin::signed(0)));
		assert_ok!(SafeMode::force_extend(ForceExtendOrigin::Weak.signed()));
		assert_err!(
			call_transfer().dispatch(RuntimeOrigin::signed(0)),
			frame_system::Error::<Test>::CallFiltered
		);
		assert_ok!(SafeMode::force_exit(RuntimeOrigin::signed(mock::ForceExitOrigin::get())));
		assert_ok!(SafeMode::force_release_stake(
			RuntimeOrigin::signed(mock::StakeSlashOrigin::get()),
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
		assert_ok!(SafeMode::force_slash_stake(
			RuntimeOrigin::signed(mock::StakeSlashOrigin::get()),
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
		assert_eq!(SafeMode::active_until(), None);
		assert_noop!(SafeMode::extend(RuntimeOrigin::signed(2)), Error::<Test>::Exited);
	});
}

#[test]
fn fails_to_force_release_stakes_with_wrong_block() {
	new_test_ext().execute_with(|| {
		let activated_at_block = System::block_number();
		assert_ok!(SafeMode::enter(RuntimeOrigin::signed(0)));
		run_to(mock::EnterDuration::get() + activated_at_block + 1);

		assert_err!(
			SafeMode::force_release_stake(
				RuntimeOrigin::signed(mock::StakeSlashOrigin::get()),
				0,
				activated_at_block + 1
			),
			Error::<Test>::NoStake
		);

		assert_err!(
			SafeMode::force_slash_stake(
				RuntimeOrigin::signed(mock::StakeSlashOrigin::get()),
				0,
				activated_at_block + 1
			),
			Error::<Test>::NoStake
		);
	});
}

#[test]
fn fails_to_release_stakes_too_early() {
	new_test_ext().execute_with(|| {
		let activated_at_block = System::block_number();
		assert_ok!(SafeMode::enter(RuntimeOrigin::signed(0)));
		assert_ok!(SafeMode::force_exit(RuntimeOrigin::signed(mock::ForceExitOrigin::get())));
		assert_err!(
			SafeMode::release_stake(RuntimeOrigin::signed(2), 0, activated_at_block),
			Error::<Test>::CannotReleaseYet
		);
		run_to(activated_at_block + mock::ReleaseDelay::get() + 1);
		assert_ok!(SafeMode::release_stake(RuntimeOrigin::signed(2), 0, activated_at_block));
	});
}

// GENERAL SUCCESS/POSITIVE TESTS ---------------------

#[test]
fn can_automatically_deactivate_after_timeout() {
	new_test_ext().execute_with(|| {
		let activated_at_block = System::block_number();
		assert_ok!(SafeMode::force_enter(ForceEnterOrigin::Weak.signed()));
		run_to(ForceEnterOrigin::Weak.duration() + activated_at_block + 1);

		assert_eq!(SafeMode::active_until(), None);
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
		// TODO ^^^ consider refactor to throw a safe mode error, not generic `CallFiltered`
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

		assert_ok!(SafeMode::force_enter(ForceEnterOrigin::Weak.signed()));

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
			SafeMode::active_until().unwrap(),
			System::block_number() + mock::EnterDuration::get()
		);
		assert_eq!(Balances::reserved_balance(0), mock::EnterStakeAmount::get());
		assert_noop!(SafeMode::enter(RuntimeOrigin::signed(0)), Error::<Test>::Entered);
		// Assert the stake.
		assert_eq!(Stakes::<Test>::get(0, 1), Some(mock::EnterStakeAmount::get()));
	});
}

#[test]
fn can_extend() {
	new_test_ext().execute_with(|| {
		assert_ok!(SafeMode::enter(RuntimeOrigin::signed(0)));
		assert_ok!(SafeMode::extend(RuntimeOrigin::signed(0)));
		assert_eq!(
			SafeMode::active_until().unwrap(),
			System::block_number() + mock::EnterDuration::get() + mock::ExtendDuration::get()
		);
		assert_eq!(
			Balances::reserved_balance(0),
			mock::EnterStakeAmount::get() + mock::ExtendStakeAmount::get()
		);
	});
}

#[test]
fn can_extend_twice_in_same_block() {
	new_test_ext().execute_with(|| {
		assert_ok!(SafeMode::enter(RuntimeOrigin::signed(0)));
		assert_ok!(SafeMode::extend(RuntimeOrigin::signed(0)));
		assert_ok!(SafeMode::extend(RuntimeOrigin::signed(0)));
		assert_eq!(
			SafeMode::active_until().unwrap(),
			System::block_number() + mock::EnterDuration::get() + mock::ExtendDuration::get() * 2
		);
		assert_eq!(
			Balances::reserved_balance(0),
			mock::EnterStakeAmount::get() + mock::ExtendStakeAmount::get() * 2
		);
	});
}

#[test]
fn can_release_independent_stakes_by_block() {
	new_test_ext().execute_with(|| {
		let activated_at_block_0 = System::block_number();
		assert_ok!(SafeMode::enter(RuntimeOrigin::signed(0)));

		run_to(mock::EnterDuration::get() + mock::ReleaseDelay::get() + activated_at_block_0 + 1);

		let activated_at_block_1 = System::block_number();
		assert_ok!(SafeMode::enter(RuntimeOrigin::signed(0)));

		assert_eq!(Balances::free_balance(&0), 1234 - (2 * mock::EnterStakeAmount::get())); // accounts set in mock genesis

		assert_ok!(SafeMode::force_exit(RuntimeOrigin::signed(mock::ForceExitOrigin::get())));

		assert_ok!(SafeMode::release_stake(RuntimeOrigin::signed(2), 0, activated_at_block_0));
		assert_err!(
			SafeMode::release_stake(RuntimeOrigin::signed(2), 0, activated_at_block_1),
			Error::<Test>::CannotReleaseYet
		);
		assert_eq!(Balances::free_balance(&0), 1234 - mock::EnterStakeAmount::get()); // accounts set in mock genesis

		run_to(mock::EnterDuration::get() + mock::ReleaseDelay::get() + activated_at_block_1 + 1);

		assert_ok!(SafeMode::release_stake(RuntimeOrigin::signed(2), 0, activated_at_block_1));
		assert_eq!(<Balances as FunInspect<_>>::total_balance(&0), 1234); // accounts set in mock genesis
	});
}

#[test]
fn fails_signed_origin_when_explicit_origin_required() {
	new_test_ext().execute_with(|| {
		assert_eq!(SafeMode::active_until(), None);
		let activated_at_block = System::block_number();

		assert_err!(SafeMode::force_enter(RuntimeOrigin::signed(0)), DispatchError::BadOrigin);
		assert_err!(SafeMode::force_extend(RuntimeOrigin::signed(0)), DispatchError::BadOrigin);
		assert_err!(SafeMode::force_exit(RuntimeOrigin::signed(0)), DispatchError::BadOrigin);
		assert_err!(
			SafeMode::force_slash_stake(RuntimeOrigin::signed(0), 0, activated_at_block),
			DispatchError::BadOrigin
		);
		assert_err!(
			SafeMode::force_release_stake(RuntimeOrigin::signed(0), 0, activated_at_block),
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
	});
}

#[test]
fn can_force_activate_with_config_origin() {
	new_test_ext().execute_with(|| {
		assert_ok!(SafeMode::force_enter(ForceEnterOrigin::Weak.signed()));
		assert_eq!(
			SafeMode::active_until().unwrap(),
			System::block_number() + ForceEnterOrigin::Weak.duration()
		);
		assert_noop!(
			SafeMode::force_enter(ForceEnterOrigin::Weak.signed()),
			Error::<Test>::Entered
		);
		assert_eq!(Balances::reserved_balance(ForceEnterOrigin::Weak.acc()), 0);
	});
}

#[test]
fn can_force_deactivate_with_config_origin() {
	new_test_ext().execute_with(|| {
		assert_eq!(SafeMode::active_until(), None);
		assert_err!(
			SafeMode::force_exit(RuntimeOrigin::signed(mock::ForceExitOrigin::get())),
			Error::<Test>::Exited
		);
		assert_ok!(SafeMode::force_enter(ForceEnterOrigin::Weak.signed()));
		assert_eq!(Balances::reserved_balance(ForceEnterOrigin::Weak.acc()), 0);
		assert_ok!(SafeMode::force_exit(RuntimeOrigin::signed(mock::ForceExitOrigin::get())));
	});
}

#[test]
fn can_force_extend_with_config_origin() {
	new_test_ext().execute_with(|| {
		// Activated by `Weak` and extended by `Medium`.
		assert_ok!(SafeMode::force_enter(ForceEnterOrigin::Weak.signed()));
		assert_eq!(
			SafeMode::active_until().unwrap(),
			System::block_number() + ForceEnterOrigin::Weak.duration()
		);
		assert_ok!(SafeMode::force_extend(ForceExtendOrigin::Medium.signed()));
		assert_eq!(
			SafeMode::active_until().unwrap(),
			System::block_number() +
				ForceEnterOrigin::Weak.duration() +
				ForceExtendOrigin::Medium.duration()
		);
		assert_eq!(Balances::reserved_balance(ForceEnterOrigin::Weak.acc()), 0);
		assert_eq!(Balances::reserved_balance(mock::ExtendDuration::get()), 0);
	});
}

#[test]
fn can_force_release_stake_with_config_origin() {
	new_test_ext().execute_with(|| {
		let activated_at_block = System::block_number();
		assert_ok!(SafeMode::enter(RuntimeOrigin::signed(0)));
		hypothetically_ok!(SafeMode::force_release_stake(
			RuntimeOrigin::signed(mock::StakeSlashOrigin::get()),
			0,
			activated_at_block
		),);
		run_to(mock::EnterDuration::get() + activated_at_block + 1);

		assert_ok!(SafeMode::force_release_stake(
			RuntimeOrigin::signed(mock::StakeSlashOrigin::get()),
			0,
			activated_at_block
		));
		assert_eq!(Balances::free_balance(&0), 1234); // accounts set in mock genesis

		Balances::make_free_balance_be(&0, 1234);
		let activated_and_extended_at_block = System::block_number();
		assert_ok!(SafeMode::enter(RuntimeOrigin::signed(0)));
		assert_ok!(SafeMode::extend(RuntimeOrigin::signed(0)));
		run_to(
			mock::EnterDuration::get() +
				mock::ExtendDuration::get() +
				activated_and_extended_at_block +
				1,
		);

		assert_ok!(SafeMode::force_release_stake(
			RuntimeOrigin::signed(mock::StakeSlashOrigin::get()),
			0,
			activated_and_extended_at_block
		));
		assert_eq!(Balances::free_balance(&0), 1234); // accounts set in mock genesis
	});
}

#[test]
fn can_release_stake_while_entered() {
	new_test_ext().execute_with(|| {
		assert_eq!(System::block_number(), 1);
		assert_ok!(SafeMode::enter(RuntimeOrigin::signed(0)));
		assert!(SafeMode::is_entered());

		assert_eq!(Balances::free_balance(&0), 1234 - mock::EnterStakeAmount::get());

		// We could slash in the same block or any later.
		for i in 0..mock::EnterDuration::get() + 10 {
			run_to(i);
			hypothetically_ok!(SafeMode::force_release_stake(
				RuntimeOrigin::signed(mock::StakeSlashOrigin::get()),
				0,
				1
			));
		}
		// Now once we slash once
		assert_ok!(SafeMode::force_release_stake(
			RuntimeOrigin::signed(mock::StakeSlashOrigin::get()),
			0,
			1
		),);
		assert_eq!(Balances::free_balance(&0), 1234);
		// ... it wont work ever again.
		assert_err!(
			SafeMode::force_release_stake(
				RuntimeOrigin::signed(mock::StakeSlashOrigin::get()),
				0,
				1
			),
			Error::<Test>::NoStake
		);
	});
}

#[test]
fn can_slash_stake_while_entered() {
	new_test_ext().execute_with(|| {
		assert_eq!(System::block_number(), 1);
		assert_ok!(SafeMode::enter(RuntimeOrigin::signed(0)));
		assert!(SafeMode::is_entered());

		// We could slash in the same block or any later.
		for i in 0..mock::EnterDuration::get() + 10 {
			run_to(i);
			hypothetically_ok!(SafeMode::force_slash_stake(
				RuntimeOrigin::signed(mock::StakeSlashOrigin::get()),
				0,
				1
			));
		}
		// Now once we slash once
		assert_ok!(SafeMode::force_slash_stake(
			RuntimeOrigin::signed(mock::StakeSlashOrigin::get()),
			0,
			1
		),);
		// ... it wont work ever again.
		assert_err!(
			SafeMode::force_slash_stake(RuntimeOrigin::signed(mock::StakeSlashOrigin::get()), 0, 1),
			Error::<Test>::NoStake
		);
	});
}

#[test]
fn can_slash_stake_from_extend_block() {
	new_test_ext().execute_with(|| {
		assert_ok!(SafeMode::enter(RuntimeOrigin::signed(0)));
		assert_ok!(SafeMode::extend(RuntimeOrigin::signed(0)));
		assert_eq!(
			Balances::free_balance(&0),
			1234 - mock::EnterStakeAmount::get() - mock::ExtendStakeAmount::get()
		);

		// Now once we slash once since the enter and extend are treated as one stake.
		assert_ok!(SafeMode::force_slash_stake(
			RuntimeOrigin::signed(mock::StakeSlashOrigin::get()),
			0,
			1
		),);
		assert_eq!(
			Balances::free_balance(&0),
			1234 - mock::ExtendStakeAmount::get() - mock::EnterStakeAmount::get()
		);

		// But never again.
		assert_err!(
			SafeMode::force_slash_stake(RuntimeOrigin::signed(mock::StakeSlashOrigin::get()), 0, 1),
			Error::<Test>::NoStake
		);
	});
}

#[test]
fn can_slash_stake_with_config_origin() {
	new_test_ext().execute_with(|| {
		let activated_at_block = System::block_number();
		assert_ok!(SafeMode::enter(RuntimeOrigin::signed(0)));
		hypothetically_ok!(SafeMode::force_slash_stake(
			RuntimeOrigin::signed(mock::StakeSlashOrigin::get()),
			0,
			activated_at_block
		),);
		run_to(mock::EnterDuration::get() + activated_at_block + 1);

		assert_ok!(SafeMode::force_slash_stake(
			RuntimeOrigin::signed(mock::StakeSlashOrigin::get()),
			0,
			activated_at_block
		));
		assert_eq!(Balances::free_balance(&0), 1234 - mock::EnterStakeAmount::get()); // accounts set in mock genesis

		Balances::make_free_balance_be(&0, 1234);
		let activated_and_extended_at_block = System::block_number();
		assert_ok!(SafeMode::enter(RuntimeOrigin::signed(0)));
		assert_ok!(SafeMode::extend(RuntimeOrigin::signed(0)));
		run_to(
			mock::EnterDuration::get() +
				mock::ExtendDuration::get() +
				activated_and_extended_at_block +
				1,
		);

		assert_ok!(SafeMode::force_slash_stake(
			RuntimeOrigin::signed(mock::StakeSlashOrigin::get()),
			0,
			activated_and_extended_at_block
		));
		assert_eq!(
			Balances::free_balance(&0),
			1234 - mock::EnterStakeAmount::get() - mock::ExtendStakeAmount::get()
		); // accounts set in mock genesis
	});
}

#[test]
fn fails_when_explicit_origin_required() {
	new_test_ext().execute_with(|| {
		assert_eq!(SafeMode::active_until(), None);
		let activated_at_block = System::block_number();

		assert_err!(
			SafeMode::force_extend(ForceEnterOrigin::Weak.signed()),
			DispatchError::BadOrigin
		);
		assert_err!(
			SafeMode::force_exit(ForceEnterOrigin::Weak.signed()),
			DispatchError::BadOrigin
		);
		assert_err!(
			SafeMode::force_slash_stake(ForceEnterOrigin::Weak.signed(), 0, activated_at_block),
			DispatchError::BadOrigin
		);
		assert_err!(
			SafeMode::force_release_stake(ForceEnterOrigin::Weak.signed(), 0, activated_at_block),
			DispatchError::BadOrigin
		);

		assert_err!(
			SafeMode::force_enter(ForceExtendOrigin::Weak.signed()),
			DispatchError::BadOrigin
		);
		assert_err!(
			SafeMode::force_exit(ForceExtendOrigin::Weak.signed()),
			DispatchError::BadOrigin
		);
		assert_err!(
			SafeMode::force_slash_stake(ForceExtendOrigin::Weak.signed(), 0, activated_at_block),
			DispatchError::BadOrigin
		);
		assert_err!(
			SafeMode::force_release_stake(ForceExtendOrigin::Weak.signed(), 0, activated_at_block),
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
			SafeMode::force_slash_stake(
				RuntimeOrigin::signed(mock::ForceExitOrigin::get()),
				0,
				activated_at_block
			),
			DispatchError::BadOrigin
		);
		assert_err!(
			SafeMode::force_release_stake(
				RuntimeOrigin::signed(mock::ForceExitOrigin::get()),
				0,
				activated_at_block
			),
			DispatchError::BadOrigin
		);

		assert_err!(
			SafeMode::force_enter(RuntimeOrigin::signed(mock::StakeSlashOrigin::get())),
			DispatchError::BadOrigin
		);
		assert_err!(
			SafeMode::force_extend(RuntimeOrigin::signed(mock::StakeSlashOrigin::get())),
			DispatchError::BadOrigin
		);
		assert_err!(
			SafeMode::force_exit(RuntimeOrigin::signed(mock::StakeSlashOrigin::get())),
			DispatchError::BadOrigin
		);
	});
}

fn call_transfer() -> RuntimeCall {
	RuntimeCall::Balances(pallet_balances::Call::transfer { dest: 1, value: 1 })
}
