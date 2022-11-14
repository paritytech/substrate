// This file is part of Substrate.

// Copyright (C) 2021-2022 Parity Technologies (UK) Ltd.
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

//! Tests for the module.

use super::*;
use frame_support::{assert_noop, assert_ok, assert_storage_noop};
use mock::{
	new_test_ext, run_to_block, Balances, BalancesCall, Call, Lottery, Origin, SystemCall, Test,
};
use pallet_balances::Error as BalancesError;
use sp_runtime::traits::BadOrigin;

#[test]
fn initial_state() {
	new_test_ext().execute_with(|| {
		assert_eq!(Balances::free_balance(Lottery::account_id()), 0);
		assert!(crate::Lottery::<Test>::get().is_none());
		assert_eq!(Participants::<Test>::get(&1), (0, Default::default()));
		assert_eq!(TicketsCount::<Test>::get(), 0);
		assert!(Tickets::<Test>::get(0).is_none());
	});
}

#[test]
fn basic_end_to_end_works() {
	new_test_ext().execute_with(|| {
		let price = 10;
		let length = 20;
		let delay = 5;
		let calls = vec![
			Call::Balances(BalancesCall::force_transfer { source: 0, dest: 0, value: 0 }),
			Call::Balances(BalancesCall::transfer { dest: 0, value: 0 }),
		];

		// Set calls for the lottery
		assert_ok!(Lottery::set_calls(Origin::root(), calls));

		// Start lottery, it repeats
		assert_ok!(Lottery::start_lottery(Origin::root(), price, length, delay, true));
		assert!(crate::Lottery::<Test>::get().is_some());

		assert_eq!(Balances::free_balance(&1), 100);
		let call = Box::new(Call::Balances(BalancesCall::transfer { dest: 2, value: 20 }));
		assert_ok!(Lottery::buy_ticket(Origin::signed(1), call.clone()));
		// 20 from the transfer, 10 from buying a ticket
		assert_eq!(Balances::free_balance(&1), 100 - 20 - 10);
		assert_eq!(Participants::<Test>::get(&1).1.len(), 1);
		assert_eq!(TicketsCount::<Test>::get(), 1);
		// 1 owns the 0 ticket
		assert_eq!(Tickets::<Test>::get(0), Some(1));

		// More ticket purchases
		assert_ok!(Lottery::buy_ticket(Origin::signed(2), call.clone()));
		assert_ok!(Lottery::buy_ticket(Origin::signed(3), call.clone()));
		assert_ok!(Lottery::buy_ticket(Origin::signed(4), call.clone()));
		assert_eq!(TicketsCount::<Test>::get(), 4);

		// Go to end
		run_to_block(20);
		assert_ok!(Lottery::buy_ticket(Origin::signed(5), call.clone()));
		// Ticket isn't bought
		assert_eq!(TicketsCount::<Test>::get(), 4);

		// Go to payout
		run_to_block(25);
		// User 1 wins
		assert_eq!(Balances::free_balance(&1), 70 + 40);
		// Lottery is reset and restarted
		assert_eq!(TicketsCount::<Test>::get(), 0);
		assert_eq!(LotteryIndex::<Test>::get(), 2);
		assert_eq!(
			crate::Lottery::<Test>::get().unwrap(),
			LotteryConfig { price, start: 25, length, delay, repeat: true }
		);
	});
}

/// Only the manager can stop the Lottery from repeating via `stop_repeat`.
#[test]
fn stop_repeat_works() {
	new_test_ext().execute_with(|| {
		let price = 10;
		let length = 20;
		let delay = 5;

		// Set no calls for the lottery.
		assert_ok!(Lottery::set_calls(Origin::root(), vec![]));
		// Start lottery, it repeats.
		assert_ok!(Lottery::start_lottery(Origin::root(), price, length, delay, true));

		// Non-manager fails to `stop_repeat`.
		assert_noop!(Lottery::stop_repeat(Origin::signed(1)), DispatchError::BadOrigin);
		// Manager can `stop_repeat`, even twice.
		assert_ok!(Lottery::stop_repeat(Origin::root()));
		assert_ok!(Lottery::stop_repeat(Origin::root()));

		// Lottery still exists.
		assert!(crate::Lottery::<Test>::get().is_some());
		// End and pick a winner.
		run_to_block(length + delay);

		// Lottery stays dead and does not repeat.
		assert!(crate::Lottery::<Test>::get().is_none());
		run_to_block(length + delay + 1);
		assert!(crate::Lottery::<Test>::get().is_none());
	});
}

#[test]
fn set_calls_works() {
	new_test_ext().execute_with(|| {
		assert!(!CallIndices::<Test>::exists());

		let calls = vec![
			Call::Balances(BalancesCall::force_transfer { source: 0, dest: 0, value: 0 }),
			Call::Balances(BalancesCall::transfer { dest: 0, value: 0 }),
		];

		assert_ok!(Lottery::set_calls(Origin::root(), calls));
		assert!(CallIndices::<Test>::exists());

		let too_many_calls = vec![
			Call::Balances(BalancesCall::force_transfer { source: 0, dest: 0, value: 0 }),
			Call::Balances(BalancesCall::transfer { dest: 0, value: 0 }),
			Call::System(SystemCall::remark { remark: vec![] }),
		];

		assert_noop!(
			Lottery::set_calls(Origin::root(), too_many_calls),
			Error::<Test>::TooManyCalls,
		);

		// Clear calls
		assert_ok!(Lottery::set_calls(Origin::root(), vec![]));
		assert!(CallIndices::<Test>::get().is_empty());
	});
}

#[test]
fn call_to_indices_works() {
	new_test_ext().execute_with(|| {
		let calls = vec![
			Call::Balances(BalancesCall::force_transfer { source: 0, dest: 0, value: 0 }),
			Call::Balances(BalancesCall::transfer { dest: 0, value: 0 }),
		];
		let indices = Lottery::calls_to_indices(&calls).unwrap().into_inner();
		// Only comparing the length since it is otherwise dependant on the API
		// of `BalancesCall`.
		assert_eq!(indices.len(), calls.len());

		let too_many_calls = vec![
			Call::Balances(BalancesCall::force_transfer { source: 0, dest: 0, value: 0 }),
			Call::Balances(BalancesCall::transfer { dest: 0, value: 0 }),
			Call::System(SystemCall::remark { remark: vec![] }),
		];
		assert_noop!(Lottery::calls_to_indices(&too_many_calls), Error::<Test>::TooManyCalls);
	});
}

#[test]
fn start_lottery_works() {
	new_test_ext().execute_with(|| {
		let price = 10;
		let length = 20;
		let delay = 5;

		// Setup ignores bad origin
		assert_noop!(
			Lottery::start_lottery(Origin::signed(1), price, length, delay, false),
			BadOrigin,
		);

		// All good
		assert_ok!(Lottery::start_lottery(Origin::root(), price, length, delay, false));

		// Can't open another one if lottery is already present
		assert_noop!(
			Lottery::start_lottery(Origin::root(), price, length, delay, false),
			Error::<Test>::InProgress,
		);
	});
}

#[test]
fn buy_ticket_works_as_simple_passthrough() {
	// This test checks that even if the user could not buy a ticket, that `buy_ticket` acts
	// as a simple passthrough to the real call.
	new_test_ext().execute_with(|| {
		// No lottery set up
		let call = Box::new(Call::Balances(BalancesCall::transfer { dest: 2, value: 20 }));
		// This is just a basic transfer then
		assert_ok!(Lottery::buy_ticket(Origin::signed(1), call.clone()));
		assert_eq!(Balances::free_balance(&1), 100 - 20);
		assert_eq!(TicketsCount::<Test>::get(), 0);

		// Lottery is set up, but too expensive to enter, so `do_buy_ticket` fails.
		let calls = vec![
			Call::Balances(BalancesCall::force_transfer { source: 0, dest: 0, value: 0 }),
			Call::Balances(BalancesCall::transfer { dest: 0, value: 0 }),
		];
		assert_ok!(Lottery::set_calls(Origin::root(), calls));

		// Ticket price of 60 would kill the user's account
		assert_ok!(Lottery::start_lottery(Origin::root(), 60, 10, 5, false));
		assert_ok!(Lottery::buy_ticket(Origin::signed(1), call.clone()));
		assert_eq!(Balances::free_balance(&1), 100 - 20 - 20);
		assert_eq!(TicketsCount::<Test>::get(), 0);

		// If call would fail, the whole thing still fails the same
		let fail_call = Box::new(Call::Balances(BalancesCall::transfer { dest: 2, value: 1000 }));
		assert_noop!(
			Lottery::buy_ticket(Origin::signed(1), fail_call),
			BalancesError::<Test, _>::InsufficientBalance,
		);

		let bad_origin_call =
			Box::new(Call::Balances(BalancesCall::force_transfer { source: 0, dest: 0, value: 0 }));
		assert_noop!(Lottery::buy_ticket(Origin::signed(1), bad_origin_call), BadOrigin,);

		// User can call other txs, but doesn't get a ticket
		let remark_call =
			Box::new(Call::System(SystemCall::remark { remark: b"hello, world!".to_vec() }));
		assert_ok!(Lottery::buy_ticket(Origin::signed(2), remark_call));
		assert_eq!(TicketsCount::<Test>::get(), 0);

		let successful_call =
			Box::new(Call::Balances(BalancesCall::transfer { dest: 2, value: 1 }));
		assert_ok!(Lottery::buy_ticket(Origin::signed(2), successful_call));
		assert_eq!(TicketsCount::<Test>::get(), 1);
	});
}

#[test]
fn buy_ticket_works() {
	new_test_ext().execute_with(|| {
		// Set calls for the lottery.
		let calls = vec![
			Call::System(SystemCall::remark { remark: vec![] }),
			Call::Balances(BalancesCall::transfer { dest: 0, value: 0 }),
		];
		assert_ok!(Lottery::set_calls(Origin::root(), calls));

		// Can't buy ticket before start
		let call = Box::new(Call::Balances(BalancesCall::transfer { dest: 2, value: 1 }));
		assert_ok!(Lottery::buy_ticket(Origin::signed(1), call.clone()));
		assert_eq!(TicketsCount::<Test>::get(), 0);

		// Start lottery
		assert_ok!(Lottery::start_lottery(Origin::root(), 1, 20, 5, false));

		// Go to start, buy ticket for transfer
		run_to_block(5);
		assert_ok!(Lottery::buy_ticket(Origin::signed(1), call));
		assert_eq!(TicketsCount::<Test>::get(), 1);

		// Can't buy another of the same ticket (even if call is slightly changed)
		let call = Box::new(Call::Balances(BalancesCall::transfer { dest: 3, value: 30 }));
		assert_ok!(Lottery::buy_ticket(Origin::signed(1), call));
		assert_eq!(TicketsCount::<Test>::get(), 1);

		// Buy ticket for remark
		let call = Box::new(Call::System(SystemCall::remark { remark: b"hello, world!".to_vec() }));
		assert_ok!(Lottery::buy_ticket(Origin::signed(1), call.clone()));
		assert_eq!(TicketsCount::<Test>::get(), 2);

		// Go to end, can't buy tickets anymore
		run_to_block(20);
		assert_ok!(Lottery::buy_ticket(Origin::signed(2), call.clone()));
		assert_eq!(TicketsCount::<Test>::get(), 2);

		// Go to payout, can't buy tickets when there is no lottery open
		run_to_block(25);
		assert_ok!(Lottery::buy_ticket(Origin::signed(2), call.clone()));
		assert_eq!(TicketsCount::<Test>::get(), 0);
		assert_eq!(LotteryIndex::<Test>::get(), 1);
	});
}

/// Test that `do_buy_ticket` returns an `AlreadyParticipating` error.
/// Errors of `do_buy_ticket` are ignored by `buy_ticket`, therefore this white-box test.
#[test]
fn do_buy_ticket_already_participating() {
	new_test_ext().execute_with(|| {
		let calls = vec![Call::Balances(BalancesCall::transfer { dest: 0, value: 0 })];
		assert_ok!(Lottery::set_calls(Origin::root(), calls.clone()));
		assert_ok!(Lottery::start_lottery(Origin::root(), 1, 10, 10, false));

		// Buying once works.
		assert_ok!(Lottery::do_buy_ticket(&1, &calls[0]));
		// Buying the same ticket again fails.
		assert_noop!(Lottery::do_buy_ticket(&1, &calls[0]), Error::<Test>::AlreadyParticipating);
	});
}

/// `buy_ticket` is a storage noop when called with the same ticket again.
#[test]
fn buy_ticket_already_participating() {
	new_test_ext().execute_with(|| {
		let calls = vec![Call::Balances(BalancesCall::transfer { dest: 0, value: 0 })];
		assert_ok!(Lottery::set_calls(Origin::root(), calls.clone()));
		assert_ok!(Lottery::start_lottery(Origin::root(), 1, 10, 10, false));

		// Buying once works.
		let call = Box::new(calls[0].clone());
		assert_ok!(Lottery::buy_ticket(Origin::signed(1), call.clone()));

		// Buying the same ticket again returns Ok, but changes nothing.
		assert_storage_noop!(Lottery::buy_ticket(Origin::signed(1), call).unwrap());

		// Exactly one ticket exists.
		assert_eq!(TicketsCount::<Test>::get(), 1);
	});
}

/// `buy_ticket` is a storage noop when called with insufficient balance.
#[test]
fn buy_ticket_insufficient_balance() {
	new_test_ext().execute_with(|| {
		let calls = vec![Call::Balances(BalancesCall::transfer { dest: 0, value: 0 })];
		assert_ok!(Lottery::set_calls(Origin::root(), calls.clone()));
		// Price set to 100.
		assert_ok!(Lottery::start_lottery(Origin::root(), 100, 10, 10, false));
		let call = Box::new(calls[0].clone());

		// Buying a ticket returns Ok, but changes nothing.
		assert_storage_noop!(Lottery::buy_ticket(Origin::signed(1), call).unwrap());
		assert!(TicketsCount::<Test>::get().is_zero());
	});
}

#[test]
fn do_buy_ticket_insufficient_balance() {
	new_test_ext().execute_with(|| {
		let calls = vec![Call::Balances(BalancesCall::transfer { dest: 0, value: 0 })];
		assert_ok!(Lottery::set_calls(Origin::root(), calls.clone()));
		// Price set to 101.
		assert_ok!(Lottery::start_lottery(Origin::root(), 101, 10, 10, false));

		// Buying fails with InsufficientBalance.
		assert_noop!(
			Lottery::do_buy_ticket(&1, &calls[0]),
			BalancesError::<Test, _>::InsufficientBalance
		);
		assert!(TicketsCount::<Test>::get().is_zero());
	});
}

#[test]
fn do_buy_ticket_keep_alive() {
	new_test_ext().execute_with(|| {
		let calls = vec![Call::Balances(BalancesCall::transfer { dest: 0, value: 0 })];
		assert_ok!(Lottery::set_calls(Origin::root(), calls.clone()));
		// Price set to 100.
		assert_ok!(Lottery::start_lottery(Origin::root(), 100, 10, 10, false));

		// Buying fails with KeepAlive.
		assert_noop!(Lottery::do_buy_ticket(&1, &calls[0]), BalancesError::<Test, _>::KeepAlive);
		assert!(TicketsCount::<Test>::get().is_zero());
	});
}

/// The lottery handles the case that no one participated.
#[test]
fn no_participants_works() {
	new_test_ext().execute_with(|| {
		let length = 20;
		let delay = 5;

		// Set no calls for the lottery.
		assert_ok!(Lottery::set_calls(Origin::root(), vec![]));
		// Start lottery.
		assert_ok!(Lottery::start_lottery(Origin::root(), 10, length, delay, false));

		// End the lottery, no one wins.
		run_to_block(length + delay);
	});
}

#[test]
fn start_lottery_will_create_account() {
	new_test_ext().execute_with(|| {
		let price = 10;
		let length = 20;
		let delay = 5;

		assert_eq!(Balances::total_balance(&Lottery::account_id()), 0);
		assert_ok!(Lottery::start_lottery(Origin::root(), price, length, delay, false));
		assert_eq!(Balances::total_balance(&Lottery::account_id()), 1);
	});
}

#[test]
fn choose_ticket_trivial_cases() {
	new_test_ext().execute_with(|| {
		assert!(Lottery::choose_ticket(0).is_none());
		assert_eq!(Lottery::choose_ticket(1).unwrap(), 0);
	});
}

#[test]
fn choose_account_one_participant() {
	new_test_ext().execute_with(|| {
		let calls = vec![Call::Balances(BalancesCall::transfer { dest: 0, value: 0 })];
		assert_ok!(Lottery::set_calls(Origin::root(), calls.clone()));
		assert_ok!(Lottery::start_lottery(Origin::root(), 10, 10, 10, false));
		let call = Box::new(calls[0].clone());

		// Buy one ticket with account 1.
		assert_ok!(Lottery::buy_ticket(Origin::signed(1), call));
		// Account 1 is always the winner.
		assert_eq!(Lottery::choose_account().unwrap(), 1);
	});
}
