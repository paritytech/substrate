// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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
use mock::{
	Lottery, Balances, Test, Origin, Call, BalancesCall,
	new_test_ext, run_to_block
};
use sp_runtime::traits::{BadOrigin};
use frame_support::{
	assert_noop, assert_ok,
	traits::{Currency},
};

#[test]
fn initial_state() {
	new_test_ext().execute_with(|| {
		assert_eq!(Balances::free_balance(Lottery::account_id()), 1);
		assert!(crate::Lottery::<Test>::get().is_none());
		assert_eq!(Participants::<Test>::get(&1), vec![]);
		assert_eq!(TicketsCount::get(), 0);
		assert!(Tickets::<Test>::get(0).is_none());
	});
}

#[test]
fn basic_end_to_end_works() {
	new_test_ext().execute_with(|| {
		let price = 10;
		let start = 5;
		let end = 20;
		let payout = 25;
		let calls = vec![Call::Balances(BalancesCall::transfer(0, 0))];

		// Setup Lottery
		assert_ok!(Lottery::setup_lottery(Origin::root(), price, start, end, payout, calls.clone()));
		assert!(crate::Lottery::<Test>::get().is_some());

		// Go to start
		run_to_block(5);

		assert_eq!(Balances::free_balance(&1), 100);
		let call = Call::Balances(BalancesCall::transfer(2, 20));
		assert_ok!(Lottery::buy_ticket(Origin::signed(1), call.clone()));
		// 20 from the transfer, 10 from buying a ticket
		assert_eq!(Balances::free_balance(&1), 100 - 20 - 10);
		assert_eq!(Participants::<Test>::get(&1).len(), 1);
		assert_eq!(TicketsCount::get(), 1);
		// 1 owns the 0 ticket
		assert_eq!(Tickets::<Test>::get(0), Some(1));

		// More ticket purchases
		assert_ok!(Lottery::buy_ticket(Origin::signed(2), call.clone()));
		assert_ok!(Lottery::buy_ticket(Origin::signed(3), call.clone()));
		assert_ok!(Lottery::buy_ticket(Origin::signed(4), call.clone()));
		assert_eq!(TicketsCount::get(), 4);

		// Go to end
		run_to_block(20);
		assert_ok!(Lottery::buy_ticket(Origin::signed(5), call.clone()));
		// Ticket isn't bought
		assert_eq!(TicketsCount::get(), 4);

		// Go to payout
		run_to_block(25);
		// Lottery is reset
		assert!(crate::Lottery::<Test>::get().is_none());
		assert_eq!(Participants::<Test>::get(&1), vec![]);
		assert_eq!(TicketsCount::get(), 0);
		assert!(Tickets::<Test>::get(0).is_none());
		// User 1 wins
		assert_eq!(Balances::free_balance(&1), 70 + 40);
	});
}

#[test]
fn setup_lottery_works() {
	new_test_ext().execute_with(|| {
		let price = 10;
		let start = 5;
		let end = 20;
		let payout = 25;
		let calls = vec![Call::Balances(BalancesCall::transfer(0, 0))];
		let too_many_calls = vec![Call::Balances(BalancesCall::transfer(0, 0)); 10];

		// Setup ignores bad origin
		assert_noop!(
			Lottery::setup_lottery(Origin::signed(1), price, start, end, payout, calls.clone()),
			BadOrigin,
		);
		// Too many calls
		assert_noop!(
			Lottery::setup_lottery(Origin::root(), price, start, end, payout, too_many_calls),
			Error::<Test>::TooManyCalls,
		);

		// All good
		assert_ok!(Lottery::setup_lottery(Origin::root(), price, start, end, payout, calls.clone()));

		// Can't open another one if lottery is already present
		assert_noop!(
			Lottery::setup_lottery(Origin::root(), price, start, end, payout, calls),
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
		let call = Call::Balances(BalancesCall::transfer(2, 20));
	});
}
