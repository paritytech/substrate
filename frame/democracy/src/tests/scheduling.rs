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

//! The tests for functionality concerning normal starting, ending and enacting of referenda.

use super::*;

#[test]
fn simple_passing_should_work() {
	new_test_ext().execute_with(|| {
		let r = Democracy::inject_referendum(
			2,
			set_balance_proposal_hash_and_note(2),
			VoteThreshold::SuperMajorityApprove,
			0
		);
		assert_ok!(Democracy::vote(Origin::signed(1), r, aye(1)));
		assert_eq!(tally(r), Tally { ayes: 1, nays: 0, turnout: 10 });
		next_block();
		next_block();
		assert_eq!(Balances::free_balance(42), 2);
	});
}

#[test]
fn simple_failing_should_work() {
	new_test_ext().execute_with(|| {
		let r = Democracy::inject_referendum(
			2,
			set_balance_proposal_hash_and_note(2),
			VoteThreshold::SuperMajorityApprove,
			0
		);
		assert_ok!(Democracy::vote(Origin::signed(1), r, nay(1)));
		assert_eq!(tally(r), Tally { ayes: 0, nays: 1, turnout: 10 });

		next_block();
		next_block();

		assert_eq!(Balances::free_balance(42), 0);
	});
}

#[test]
fn ooo_inject_referendums_should_work() {
	new_test_ext().execute_with(|| {
		let r1 = Democracy::inject_referendum(
			3,
			set_balance_proposal_hash_and_note(3),
			VoteThreshold::SuperMajorityApprove,
			0
		);
		let r2 = Democracy::inject_referendum(
			2,
			set_balance_proposal_hash_and_note(2),
			VoteThreshold::SuperMajorityApprove,
			0
		);

		assert_ok!(Democracy::vote(Origin::signed(1), r2, aye(1)));
		assert_eq!(tally(r2), Tally { ayes: 1, nays: 0, turnout: 10 });

		next_block();
		assert_eq!(Balances::free_balance(42), 2);

		assert_ok!(Democracy::vote(Origin::signed(1), r1, aye(1)));
		assert_eq!(tally(r1), Tally { ayes: 1, nays: 0, turnout: 10 });

		next_block();
		assert_eq!(Balances::free_balance(42), 3);
	});
}

#[test]
fn delayed_enactment_should_work() {
	new_test_ext().execute_with(|| {
		let r = Democracy::inject_referendum(
			2,
			set_balance_proposal_hash_and_note(2),
			VoteThreshold::SuperMajorityApprove,
			1
		);
		assert_ok!(Democracy::vote(Origin::signed(1), r, aye(1)));
		assert_ok!(Democracy::vote(Origin::signed(2), r, aye(2)));
		assert_ok!(Democracy::vote(Origin::signed(3), r, aye(3)));
		assert_ok!(Democracy::vote(Origin::signed(4), r, aye(4)));
		assert_ok!(Democracy::vote(Origin::signed(5), r, aye(5)));
		assert_ok!(Democracy::vote(Origin::signed(6), r, aye(6)));

		assert_eq!(tally(r), Tally { ayes: 21, nays: 0, turnout: 210 });

		next_block();
		assert_eq!(Balances::free_balance(42), 0);

		next_block();
		assert_eq!(Balances::free_balance(42), 2);
	});
}
