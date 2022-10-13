// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
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

//! The tests for functionality concerning locking and lock-voting.

use super::*;

fn aye(x: u8, balance: u64) -> AccountVote<u64> {
	AccountVote::Standard {
		vote: Vote { aye: true, conviction: Conviction::try_from(x).unwrap() },
		balance,
	}
}

fn nay(x: u8, balance: u64) -> AccountVote<u64> {
	AccountVote::Standard {
		vote: Vote { aye: false, conviction: Conviction::try_from(x).unwrap() },
		balance,
	}
}

fn the_lock(amount: u64) -> BalanceLock<u64> {
	BalanceLock { id: DEMOCRACY_ID, amount, reasons: pallet_balances::Reasons::Misc }
}

#[test]
fn lock_voting_should_work() {
	new_test_ext().execute_with(|| {
		System::set_block_number(0);
		let r = Democracy::inject_referendum(
			2,
			set_balance_proposal_hash_and_note(2),
			VoteThreshold::SuperMajorityApprove,
			0,
		);
		assert_ok!(Democracy::vote(Origin::signed(1), r, nay(5, 10)));
		assert_ok!(Democracy::vote(Origin::signed(2), r, aye(4, 20)));
		assert_ok!(Democracy::vote(Origin::signed(3), r, aye(3, 30)));
		assert_ok!(Democracy::vote(Origin::signed(4), r, aye(2, 40)));
		assert_ok!(Democracy::vote(Origin::signed(5), r, nay(1, 50)));
		assert_eq!(tally(r), Tally { ayes: 250, nays: 100, turnout: 150 });

		// All balances are currently locked.
		for i in 1..=5 {
			assert_eq!(Balances::locks(i), vec![the_lock(i * 10)]);
		}

		fast_forward_to(2);

		// Referendum passed; 1 and 5 didn't get their way and can now reap and unlock.
		assert_ok!(Democracy::remove_vote(Origin::signed(1), r));
		assert_ok!(Democracy::unlock(Origin::signed(1), 1));
		// Anyone can reap and unlock anyone else's in this context.
		assert_ok!(Democracy::remove_other_vote(Origin::signed(2), 5, r));
		assert_ok!(Democracy::unlock(Origin::signed(2), 5));

		// 2, 3, 4 got their way with the vote, so they cannot be reaped by others.
		assert_noop!(
			Democracy::remove_other_vote(Origin::signed(1), 2, r),
			Error::<Test>::NoPermission
		);
		// However, they can be unvoted by the owner, though it will make no difference to the lock.
		assert_ok!(Democracy::remove_vote(Origin::signed(2), r));
		assert_ok!(Democracy::unlock(Origin::signed(2), 2));

		assert_eq!(Balances::locks(1), vec![]);
		assert_eq!(Balances::locks(2), vec![the_lock(20)]);
		assert_eq!(Balances::locks(3), vec![the_lock(30)]);
		assert_eq!(Balances::locks(4), vec![the_lock(40)]);
		assert_eq!(Balances::locks(5), vec![]);
		assert_eq!(Balances::free_balance(42), 2);

		fast_forward_to(7);
		// No change yet...
		assert_noop!(
			Democracy::remove_other_vote(Origin::signed(1), 4, r),
			Error::<Test>::NoPermission
		);
		assert_ok!(Democracy::unlock(Origin::signed(1), 4));
		assert_eq!(Balances::locks(4), vec![the_lock(40)]);
		fast_forward_to(8);
		// 4 should now be able to reap and unlock
		assert_ok!(Democracy::remove_other_vote(Origin::signed(1), 4, r));
		assert_ok!(Democracy::unlock(Origin::signed(1), 4));
		assert_eq!(Balances::locks(4), vec![]);

		fast_forward_to(13);
		assert_noop!(
			Democracy::remove_other_vote(Origin::signed(1), 3, r),
			Error::<Test>::NoPermission
		);
		assert_ok!(Democracy::unlock(Origin::signed(1), 3));
		assert_eq!(Balances::locks(3), vec![the_lock(30)]);
		fast_forward_to(14);
		assert_ok!(Democracy::remove_other_vote(Origin::signed(1), 3, r));
		assert_ok!(Democracy::unlock(Origin::signed(1), 3));
		assert_eq!(Balances::locks(3), vec![]);

		// 2 doesn't need to reap_vote here because it was already done before.
		fast_forward_to(25);
		assert_ok!(Democracy::unlock(Origin::signed(1), 2));
		assert_eq!(Balances::locks(2), vec![the_lock(20)]);
		fast_forward_to(26);
		assert_ok!(Democracy::unlock(Origin::signed(1), 2));
		assert_eq!(Balances::locks(2), vec![]);
	});
}

#[test]
fn no_locks_without_conviction_should_work() {
	new_test_ext().execute_with(|| {
		System::set_block_number(0);
		let r = Democracy::inject_referendum(
			2,
			set_balance_proposal_hash_and_note(2),
			VoteThreshold::SuperMajorityApprove,
			0,
		);
		assert_ok!(Democracy::vote(Origin::signed(1), r, aye(0, 10)));

		fast_forward_to(2);

		assert_eq!(Balances::free_balance(42), 2);
		assert_ok!(Democracy::remove_other_vote(Origin::signed(2), 1, r));
		assert_ok!(Democracy::unlock(Origin::signed(2), 1));
		assert_eq!(Balances::locks(1), vec![]);
	});
}

#[test]
fn lock_voting_should_work_with_delegation() {
	new_test_ext().execute_with(|| {
		let r = Democracy::inject_referendum(
			2,
			set_balance_proposal_hash_and_note(2),
			VoteThreshold::SuperMajorityApprove,
			0,
		);
		assert_ok!(Democracy::vote(Origin::signed(1), r, nay(5, 10)));
		assert_ok!(Democracy::vote(Origin::signed(2), r, aye(4, 20)));
		assert_ok!(Democracy::vote(Origin::signed(3), r, aye(3, 30)));
		assert_ok!(Democracy::delegate(Origin::signed(4), 2, Conviction::Locked2x, 40));
		assert_ok!(Democracy::vote(Origin::signed(5), r, nay(1, 50)));

		assert_eq!(tally(r), Tally { ayes: 250, nays: 100, turnout: 150 });

		next_block();
		next_block();

		assert_eq!(Balances::free_balance(42), 2);
	});
}

fn setup_three_referenda() -> (u32, u32, u32) {
	System::set_block_number(0);
	let r1 = Democracy::inject_referendum(
		2,
		set_balance_proposal_hash_and_note(2),
		VoteThreshold::SimpleMajority,
		0,
	);
	assert_ok!(Democracy::vote(Origin::signed(5), r1, aye(4, 10)));

	let r2 = Democracy::inject_referendum(
		2,
		set_balance_proposal_hash_and_note(2),
		VoteThreshold::SimpleMajority,
		0,
	);
	assert_ok!(Democracy::vote(Origin::signed(5), r2, aye(3, 20)));

	let r3 = Democracy::inject_referendum(
		2,
		set_balance_proposal_hash_and_note(2),
		VoteThreshold::SimpleMajority,
		0,
	);
	assert_ok!(Democracy::vote(Origin::signed(5), r3, aye(2, 50)));

	fast_forward_to(2);

	(r1, r2, r3)
}

#[test]
fn prior_lockvotes_should_be_enforced() {
	new_test_ext().execute_with(|| {
		let r = setup_three_referenda();
		// r.0 locked 10 until 2 + 8 * 3 = #26
		// r.1 locked 20 until 2 + 4 * 3 = #14
		// r.2 locked 50 until 2 + 2 * 3 = #8

		fast_forward_to(7);
		assert_noop!(
			Democracy::remove_other_vote(Origin::signed(1), 5, r.2),
			Error::<Test>::NoPermission
		);
		assert_ok!(Democracy::unlock(Origin::signed(5), 5));
		assert_eq!(Balances::locks(5), vec![the_lock(50)]);
		fast_forward_to(8);
		assert_ok!(Democracy::remove_other_vote(Origin::signed(1), 5, r.2));
		assert_ok!(Democracy::unlock(Origin::signed(5), 5));
		assert_eq!(Balances::locks(5), vec![the_lock(20)]);
		fast_forward_to(13);
		assert_noop!(
			Democracy::remove_other_vote(Origin::signed(1), 5, r.1),
			Error::<Test>::NoPermission
		);
		assert_ok!(Democracy::unlock(Origin::signed(5), 5));
		assert_eq!(Balances::locks(5), vec![the_lock(20)]);
		fast_forward_to(14);
		assert_ok!(Democracy::remove_other_vote(Origin::signed(1), 5, r.1));
		assert_ok!(Democracy::unlock(Origin::signed(5), 5));
		assert_eq!(Balances::locks(5), vec![the_lock(10)]);
		fast_forward_to(25);
		assert_noop!(
			Democracy::remove_other_vote(Origin::signed(1), 5, r.0),
			Error::<Test>::NoPermission
		);
		assert_ok!(Democracy::unlock(Origin::signed(5), 5));
		assert_eq!(Balances::locks(5), vec![the_lock(10)]);
		fast_forward_to(26);
		assert_ok!(Democracy::remove_other_vote(Origin::signed(1), 5, r.0));
		assert_ok!(Democracy::unlock(Origin::signed(5), 5));
		assert_eq!(Balances::locks(5), vec![]);
	});
}

#[test]
fn single_consolidation_of_lockvotes_should_work_as_before() {
	new_test_ext().execute_with(|| {
		let r = setup_three_referenda();
		// r.0 locked 10 until 2 + 8 * 3 = #26
		// r.1 locked 20 until 2 + 4 * 3 = #14
		// r.2 locked 50 until 2 + 2 * 3 = #8

		fast_forward_to(7);
		assert_ok!(Democracy::remove_vote(Origin::signed(5), r.2));
		assert_ok!(Democracy::unlock(Origin::signed(5), 5));
		assert_eq!(Balances::locks(5), vec![the_lock(50)]);
		fast_forward_to(8);
		assert_ok!(Democracy::unlock(Origin::signed(5), 5));
		assert_eq!(Balances::locks(5), vec![the_lock(20)]);

		fast_forward_to(13);
		assert_ok!(Democracy::remove_vote(Origin::signed(5), r.1));
		assert_ok!(Democracy::unlock(Origin::signed(5), 5));
		assert_eq!(Balances::locks(5), vec![the_lock(20)]);
		fast_forward_to(14);
		assert_ok!(Democracy::unlock(Origin::signed(5), 5));
		assert_eq!(Balances::locks(5), vec![the_lock(10)]);

		fast_forward_to(25);
		assert_ok!(Democracy::remove_vote(Origin::signed(5), r.0));
		assert_ok!(Democracy::unlock(Origin::signed(5), 5));
		assert_eq!(Balances::locks(5), vec![the_lock(10)]);
		fast_forward_to(26);
		assert_ok!(Democracy::unlock(Origin::signed(5), 5));
		assert_eq!(Balances::locks(5), vec![]);
	});
}

#[test]
fn multi_consolidation_of_lockvotes_should_be_conservative() {
	new_test_ext().execute_with(|| {
		let r = setup_three_referenda();
		// r.0 locked 10 until 2 + 8 * 3 = #26
		// r.1 locked 20 until 2 + 4 * 3 = #14
		// r.2 locked 50 until 2 + 2 * 3 = #8

		assert_ok!(Democracy::remove_vote(Origin::signed(5), r.2));
		assert_ok!(Democracy::remove_vote(Origin::signed(5), r.1));
		assert_ok!(Democracy::remove_vote(Origin::signed(5), r.0));

		fast_forward_to(8);
		assert_ok!(Democracy::unlock(Origin::signed(5), 5));
		assert!(Balances::locks(5)[0].amount >= 20);

		fast_forward_to(14);
		assert_ok!(Democracy::unlock(Origin::signed(5), 5));
		assert!(Balances::locks(5)[0].amount >= 10);

		fast_forward_to(26);
		assert_ok!(Democracy::unlock(Origin::signed(5), 5));
		assert_eq!(Balances::locks(5), vec![]);
	});
}

#[test]
fn locks_should_persist_from_voting_to_delegation() {
	new_test_ext().execute_with(|| {
		System::set_block_number(0);
		let r = Democracy::inject_referendum(
			2,
			set_balance_proposal_hash_and_note(2),
			VoteThreshold::SimpleMajority,
			0,
		);
		assert_ok!(Democracy::vote(Origin::signed(5), r, aye(4, 10)));
		fast_forward_to(2);
		assert_ok!(Democracy::remove_vote(Origin::signed(5), r));
		// locked 10 until #26.

		assert_ok!(Democracy::delegate(Origin::signed(5), 1, Conviction::Locked3x, 20));
		// locked 20.
		assert!(Balances::locks(5)[0].amount == 20);

		assert_ok!(Democracy::undelegate(Origin::signed(5)));
		// locked 20 until #14

		fast_forward_to(13);
		assert_ok!(Democracy::unlock(Origin::signed(5), 5));
		assert!(Balances::locks(5)[0].amount == 20);

		fast_forward_to(14);
		assert_ok!(Democracy::unlock(Origin::signed(5), 5));
		assert!(Balances::locks(5)[0].amount >= 10);

		fast_forward_to(25);
		assert_ok!(Democracy::unlock(Origin::signed(5), 5));
		assert!(Balances::locks(5)[0].amount >= 10);

		fast_forward_to(26);
		assert_ok!(Democracy::unlock(Origin::signed(5), 5));
		assert_eq!(Balances::locks(5), vec![]);
	});
}

#[test]
fn locks_should_persist_from_delegation_to_voting() {
	new_test_ext().execute_with(|| {
		System::set_block_number(0);
		assert_ok!(Democracy::delegate(Origin::signed(5), 1, Conviction::Locked5x, 5));
		assert_ok!(Democracy::undelegate(Origin::signed(5)));
		// locked 5 until 16 * 3 = #48

		let r = setup_three_referenda();
		// r.0 locked 10 until 2 + 8 * 3 = #26
		// r.1 locked 20 until 2 + 4 * 3 = #14
		// r.2 locked 50 until 2 + 2 * 3 = #8

		assert_ok!(Democracy::remove_vote(Origin::signed(5), r.2));
		assert_ok!(Democracy::remove_vote(Origin::signed(5), r.1));
		assert_ok!(Democracy::remove_vote(Origin::signed(5), r.0));

		fast_forward_to(8);
		assert_ok!(Democracy::unlock(Origin::signed(5), 5));
		assert!(Balances::locks(5)[0].amount >= 20);

		fast_forward_to(14);
		assert_ok!(Democracy::unlock(Origin::signed(5), 5));
		assert!(Balances::locks(5)[0].amount >= 10);

		fast_forward_to(26);
		assert_ok!(Democracy::unlock(Origin::signed(5), 5));
		assert!(Balances::locks(5)[0].amount >= 5);

		fast_forward_to(48);
		assert_ok!(Democracy::unlock(Origin::signed(5), 5));
		assert_eq!(Balances::locks(5), vec![]);
	});
}
