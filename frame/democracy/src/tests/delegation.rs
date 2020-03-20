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

//! The tests for functionality concerning delegation.

use super::*;

#[test]
fn single_proposal_should_work_with_delegation() {
	new_test_ext().execute_with(|| {
		System::set_block_number(0);

		assert_ok!(propose_set_balance_and_note(1, 2, 1));

		fast_forward_to(2);

		// Delegate first vote.
		assert_ok!(Democracy::delegate(Origin::signed(2), 1, Conviction::None, 20));
		let r = 0;
		assert_ok!(Democracy::vote(Origin::signed(1), r, aye(1)));
		assert_eq!(tally(r), Tally { ayes: 3, nays: 0, turnout: 30 });

		// Delegate a second vote.
		assert_ok!(Democracy::delegate(Origin::signed(3), 1, Conviction::None, 30));
		assert_eq!(tally(r), Tally { ayes: 6, nays: 0, turnout: 60 });

		// Reduce first vote.
		assert_ok!(Democracy::delegate(Origin::signed(2), 1, Conviction::None, 10));
		assert_eq!(tally(r), Tally { ayes: 5, nays: 0, turnout: 50 });

		// Second vote delegates to first; we don't do tiered delegation, so it doesn't get used.
		assert_ok!(Democracy::delegate(Origin::signed(3), 2, Conviction::None, 30));
		assert_eq!(tally(r), Tally { ayes: 2, nays: 0, turnout: 20 });

		// Main voter cancels their vote
		assert_ok!(Democracy::remove_vote(Origin::signed(1), r));
		assert_eq!(tally(r), Tally { ayes: 0, nays: 0, turnout: 0 });

		// First delegator delegates half funds with conviction; nothing changes yet.
		assert_ok!(Democracy::delegate(Origin::signed(2), 1, Conviction::Locked1x, 10));
		assert_eq!(tally(r), Tally { ayes: 0, nays: 0, turnout: 0 });

		// Main voter reinstates their vote
		assert_ok!(Democracy::vote(Origin::signed(1), r, aye(1)));
		assert_eq!(tally(r), Tally { ayes: 11, nays: 0, turnout: 20 });
	});
}

#[test]
fn self_delegation_not_allowed() {
	new_test_ext().execute_with(|| {
		assert_noop!(
			Democracy::delegate(Origin::signed(1), 1, Conviction::None, 10),
			Error::<Test>::Nonsense,
		);
	});
}

#[test]
fn cyclic_delegation_should_unwind() {
	new_test_ext().execute_with(|| {
		System::set_block_number(0);

		assert_ok!(propose_set_balance_and_note(1, 2, 1));

		fast_forward_to(2);

		// Check behavior with cycle.
		assert_ok!(Democracy::delegate(Origin::signed(2), 1, Conviction::None, 20));
		assert_ok!(Democracy::delegate(Origin::signed(3), 2, Conviction::None, 30));
		assert_ok!(Democracy::delegate(Origin::signed(1), 3, Conviction::None, 10));
		let r = 0;
		assert_ok!(Democracy::undelegate(Origin::signed(3)));
		assert_ok!(Democracy::vote(Origin::signed(3), r, aye(3)));
		assert_ok!(Democracy::undelegate(Origin::signed(1)));
		assert_ok!(Democracy::vote(Origin::signed(1), r, nay(1)));

		// Delegated vote is counted.
		assert_eq!(tally(r), Tally { ayes: 3, nays: 3, turnout: 60 });
	});
}

#[test]
fn single_proposal_should_work_with_vote_and_delegation() {
	// If transactor already voted, delegated vote is overwritten.
	new_test_ext().execute_with(|| {
		System::set_block_number(0);

		assert_ok!(propose_set_balance_and_note(1, 2, 1));

		fast_forward_to(2);

		let r = 0;
		assert_ok!(Democracy::vote(Origin::signed(1), r, aye(1)));
		assert_ok!(Democracy::vote(Origin::signed(2), r, nay(2)));
		assert_eq!(tally(r), Tally { ayes: 1, nays: 2, turnout: 30 });

		// Delegate vote.
		assert_ok!(Democracy::remove_vote(Origin::signed(2), r));
		assert_ok!(Democracy::delegate(Origin::signed(2), 1, Conviction::None, 20));
		// Delegated vote replaces the explicit vote.
		assert_eq!(tally(r), Tally { ayes: 3, nays: 0, turnout: 30 });
	});
}

#[test]
fn single_proposal_should_work_with_undelegation() {
	new_test_ext().execute_with(|| {
		System::set_block_number(0);

		assert_ok!(propose_set_balance_and_note(1, 2, 1));

		// Delegate and undelegate vote.
		assert_ok!(Democracy::delegate(Origin::signed(2), 1, Conviction::None, 20));
		assert_ok!(Democracy::undelegate(Origin::signed(2)));

		fast_forward_to(2);
		let r = 0;
		assert_ok!(Democracy::vote(Origin::signed(1), r, aye(1)));

		// Delegated vote is not counted.
		assert_eq!(tally(r), Tally { ayes: 1, nays: 0, turnout: 10 });
	});
}

#[test]
fn single_proposal_should_work_with_delegation_and_vote() {
	// If transactor voted, delegated vote is overwritten.
	new_test_ext().execute_with(|| {
		let r = begin_referendum();
		// Delegate, undelegate and vote.
		assert_ok!(Democracy::vote(Origin::signed(1), r, aye(1)));
		assert_ok!(Democracy::delegate(Origin::signed(2), 1, Conviction::None, 20));
		assert_eq!(tally(r), Tally { ayes: 3, nays: 0, turnout: 30 });
		assert_ok!(Democracy::undelegate(Origin::signed(2)));
		assert_ok!(Democracy::vote(Origin::signed(2), r, aye(2)));
		// Delegated vote is not counted.
		assert_eq!(tally(r), Tally { ayes: 3, nays: 0, turnout: 30 });
	});
}

#[test]
fn conviction_should_be_honored_in_delegation() {
	// If transactor voted, delegated vote is overwritten.
	new_test_ext().execute_with(|| {
		let r = begin_referendum();
		// Delegate, undelegate and vote.
		assert_ok!(Democracy::delegate(Origin::signed(2), 1, Conviction::Locked6x, 20));
		assert_ok!(Democracy::vote(Origin::signed(1), r, aye(1)));
		// Delegated vote is huge.
		assert_eq!(tally(r), Tally { ayes: 121, nays: 0, turnout: 30 });
	});
}

#[test]
fn split_vote_delegation_should_be_ignored() {
	// If transactor voted, delegated vote is overwritten.
	new_test_ext().execute_with(|| {
		let r = begin_referendum();
		assert_ok!(Democracy::delegate(Origin::signed(2), 1, Conviction::Locked6x, 20));
		assert_ok!(Democracy::vote(Origin::signed(1), r, AccountVote::Split { aye: 10, nay: 0 }));
		// Delegated vote is huge.
		assert_eq!(tally(r), Tally { ayes: 1, nays: 0, turnout: 10 });
	});
}
