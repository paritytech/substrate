// This file is part of Substrate.

// Copyright (C) 2017-2020 Parity Technologies (UK) Ltd.
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

//! The tests for the public proposal queue.

use super::*;

#[test]
fn backing_for_should_work() {
	new_test_ext().execute_with(|| {
		assert_ok!(propose_set_balance_and_note(1, 2, 2));
		assert_ok!(propose_set_balance_and_note(1, 4, 4));
		assert_ok!(propose_set_balance_and_note(1, 3, 3));
		assert_eq!(Democracy::backing_for(0), Some(2));
		assert_eq!(Democracy::backing_for(1), Some(4));
		assert_eq!(Democracy::backing_for(2), Some(3));
	});
}

#[test]
fn deposit_for_proposals_should_be_taken() {
	new_test_ext().execute_with(|| {
		assert_ok!(propose_set_balance_and_note(1, 2, 5));
		assert_ok!(Democracy::second(Origin::signed(2), 0, u32::max_value()));
		assert_ok!(Democracy::second(Origin::signed(5), 0, u32::max_value()));
		assert_ok!(Democracy::second(Origin::signed(5), 0, u32::max_value()));
		assert_ok!(Democracy::second(Origin::signed(5), 0, u32::max_value()));
		assert_eq!(Balances::free_balance(1), 5);
		assert_eq!(Balances::free_balance(2), 15);
		assert_eq!(Balances::free_balance(5), 35);
	});
}

#[test]
fn deposit_for_proposals_should_be_returned() {
	new_test_ext().execute_with(|| {
		assert_ok!(propose_set_balance_and_note(1, 2, 5));
		assert_ok!(Democracy::second(Origin::signed(2), 0, u32::max_value()));
		assert_ok!(Democracy::second(Origin::signed(5), 0, u32::max_value()));
		assert_ok!(Democracy::second(Origin::signed(5), 0, u32::max_value()));
		assert_ok!(Democracy::second(Origin::signed(5), 0, u32::max_value()));
		fast_forward_to(3);
		assert_eq!(Balances::free_balance(1), 10);
		assert_eq!(Balances::free_balance(2), 20);
		assert_eq!(Balances::free_balance(5), 50);
	});
}

#[test]
fn proposal_with_deposit_below_minimum_should_not_work() {
	new_test_ext().execute_with(|| {
		assert_noop!(propose_set_balance(1, 2, 0), Error::<Test>::ValueLow);
	});
}

#[test]
fn poor_proposer_should_not_work() {
	new_test_ext().execute_with(|| {
		assert_noop!(propose_set_balance(1, 2, 11), BalancesError::<Test, _>::InsufficientBalance);
	});
}

#[test]
fn poor_seconder_should_not_work() {
	new_test_ext().execute_with(|| {
		assert_ok!(propose_set_balance_and_note(2, 2, 11));
		assert_noop!(
			Democracy::second(Origin::signed(1), 0, u32::max_value()),
			BalancesError::<Test, _>::InsufficientBalance
		);
	});
}

#[test]
fn invalid_seconds_upper_bound_should_not_work() {
	new_test_ext().execute_with(|| {
		assert_ok!(propose_set_balance_and_note(1, 2, 5));
		assert_noop!(
			Democracy::second(Origin::signed(2), 0, 0),
			Error::<Test>::WrongUpperBound
		);
	});
}

#[test]
fn cancel_proposal_should_work() {
	new_test_ext().execute_with(|| {
		System::set_block_number(0);
		assert_ok!(propose_set_balance_and_note(1, 2, 2));
		assert_ok!(propose_set_balance_and_note(1, 4, 4));
		assert_noop!(Democracy::cancel_proposal(Origin::signed(1), 0), BadOrigin);
		assert_ok!(Democracy::cancel_proposal(Origin::root(), 0));
		assert_eq!(Democracy::backing_for(0), None);
		assert_eq!(Democracy::backing_for(1), Some(4));
	});
}

#[test]
fn blacklisting_should_work() {
	new_test_ext().execute_with(|| {
		System::set_block_number(0);
		let hash = set_balance_proposal_hash(2);

		assert_ok!(propose_set_balance_and_note(1, 2, 2));
		assert_ok!(propose_set_balance_and_note(1, 4, 4));

		assert_noop!(Democracy::blacklist(Origin::signed(1), hash.clone(), None), BadOrigin);
		assert_ok!(Democracy::blacklist(Origin::root(), hash, None));

		assert_eq!(Democracy::backing_for(0), None);
		assert_eq!(Democracy::backing_for(1), Some(4));

		assert_noop!(propose_set_balance_and_note(1, 2, 2), Error::<Test>::ProposalBlacklisted);

		fast_forward_to(2);

		let hash = set_balance_proposal_hash(4);
		assert!(Democracy::referendum_status(0).is_ok());
		assert_ok!(Democracy::blacklist(Origin::root(), hash, Some(0)));
		assert!(Democracy::referendum_status(0).is_err());
	});
}

#[test]
fn runners_up_should_come_after() {
	new_test_ext().execute_with(|| {
		System::set_block_number(0);
		assert_ok!(propose_set_balance_and_note(1, 2, 2));
		assert_ok!(propose_set_balance_and_note(1, 4, 4));
		assert_ok!(propose_set_balance_and_note(1, 3, 3));
		fast_forward_to(2);
		assert_ok!(Democracy::vote(Origin::signed(1), 0, aye(1)));
		fast_forward_to(4);
		assert_ok!(Democracy::vote(Origin::signed(1), 1, aye(1)));
		fast_forward_to(6);
		assert_ok!(Democracy::vote(Origin::signed(1), 2, aye(1)));
	});
}
