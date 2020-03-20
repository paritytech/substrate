// Copyright 2017-2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! The tests for functionality concerning locking and lock-voting.

use super::*;
use std::convert::TryFrom;

fn aye(x: u8, balance: u64) -> AccountVote<u64> {
	AccountVote::Standard {
		vote: Vote { aye: true, conviction: Conviction::try_from(x).unwrap() },
		balance
	}
}

fn nay(x: u8, balance: u64) -> AccountVote<u64> {
	AccountVote::Standard {
		vote: Vote { aye: false, conviction: Conviction::try_from(x).unwrap() },
		balance
	}
}

fn the_lock(amount: u64) -> BalanceLock<u64> {
	BalanceLock {
		id: DEMOCRACY_ID,
		amount,
		reasons: pallet_balances::Reasons::Misc,
	}
}

#[test]
fn lock_voting_should_work() {
	new_test_ext().execute_with(|| {
		System::set_block_number(0);
		let r = Democracy::inject_referendum(
			2,
			set_balance_proposal_hash_and_note(2),
			VoteThreshold::SuperMajorityApprove,
			0
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
		assert_noop!(Democracy::remove_other_vote(Origin::signed(1), 2, r), Error::<Test>::NoPermission);
		// However, they can be unvoted by the owner, though it will make no difference to the lock.
		assert_ok!(Democracy::remove_vote(Origin::signed(2), r));
		assert_ok!(Democracy::unlock(Origin::signed(2), 2));

		assert_eq!(Balances::locks(1), vec![]);
		assert_eq!(Balances::locks(2), vec![the_lock(20)]);
		assert_eq!(Balances::locks(3), vec![the_lock(30)]);
		assert_eq!(Balances::locks(4), vec![the_lock(40)]);
		assert_eq!(Balances::locks(5), vec![]);
		assert_eq!(Balances::free_balance(42), 2);


		fast_forward_to(5);
		// No change yet...
		assert_noop!(Democracy::remove_other_vote(Origin::signed(1), 4, r), Error::<Test>::NoPermission);
		assert_ok!(Democracy::unlock(Origin::signed(1), 4));
		assert_eq!(Balances::locks(4), vec![the_lock(40)]);
		fast_forward_to(6);
		// 4 should now be able to reap and unlock
		assert_ok!(Democracy::remove_other_vote(Origin::signed(1), 4, r));
		assert_ok!(Democracy::unlock(Origin::signed(1), 4));
		assert_eq!(Balances::locks(4), vec![]);

		fast_forward_to(9);
		assert_noop!(Democracy::remove_other_vote(Origin::signed(1), 3, r), Error::<Test>::NoPermission);
		assert_ok!(Democracy::unlock(Origin::signed(1), 3));
		assert_eq!(Balances::locks(3), vec![the_lock(30)]);
		fast_forward_to(10);
		assert_ok!(Democracy::remove_other_vote(Origin::signed(1), 3, r));
		assert_ok!(Democracy::unlock(Origin::signed(1), 3));
		assert_eq!(Balances::locks(3), vec![]);

		// 2 doesn't need to reap_vote here because it was already done before.
		fast_forward_to(17);
		assert_ok!(Democracy::unlock(Origin::signed(1), 2));
		assert_eq!(Balances::locks(2), vec![the_lock(20)]);
		fast_forward_to(18);
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
		System::set_block_number(1);
		let r = Democracy::inject_referendum(
			2,
			set_balance_proposal_hash_and_note(2),
			VoteThreshold::SuperMajorityApprove,
			0
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
