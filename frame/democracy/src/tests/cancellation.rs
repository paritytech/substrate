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

//! The tests for cancelation functionality.

use super::*;

#[test]
fn cancel_referendum_should_work() {
	new_test_ext().execute_with(|| {
		let r = Democracy::inject_referendum(
			2,
			set_balance_proposal_hash_and_note(2),
			VoteThreshold::SuperMajorityApprove,
			0
		);
		assert_ok!(Democracy::vote(Origin::signed(1), r, aye(1)));
		assert_ok!(Democracy::cancel_referendum(Origin::ROOT, r.into()));

		next_block();
		next_block();

		assert_eq!(Balances::free_balance(42), 0);
	});
}

#[test]
fn cancel_queued_should_work() {
	new_test_ext().execute_with(|| {
		System::set_block_number(0);
		assert_ok!(propose_set_balance_and_note(1, 2, 1));

		// start of 2 => next referendum scheduled.
		fast_forward_to(2);

		assert_ok!(Democracy::vote(Origin::signed(1), 0, aye(1)));

		fast_forward_to(4);

		assert!(pallet_scheduler::Agenda::<Test>::get(6)[0].is_some());

		assert_noop!(Democracy::cancel_queued(Origin::ROOT, 1), Error::<Test>::ProposalMissing);
		assert_ok!(Democracy::cancel_queued(Origin::ROOT, 0));
		assert!(pallet_scheduler::Agenda::<Test>::get(6)[0].is_none());
	});
}

#[test]
fn emergency_cancel_should_work() {
	new_test_ext().execute_with(|| {
		System::set_block_number(0);
		let r = Democracy::inject_referendum(
			2,
			set_balance_proposal_hash_and_note(2),
			VoteThreshold::SuperMajorityApprove,
			2
		);
		assert!(Democracy::referendum_status(r).is_ok());

		assert_noop!(Democracy::emergency_cancel(Origin::signed(3), r), BadOrigin);
		assert_ok!(Democracy::emergency_cancel(Origin::signed(4), r));
		assert!(Democracy::referendum_info(r).is_none());

		// some time later...

		let r = Democracy::inject_referendum(
			2,
			set_balance_proposal_hash_and_note(2),
			VoteThreshold::SuperMajorityApprove,
			2
		);
		assert!(Democracy::referendum_status(r).is_ok());
		assert_noop!(
			Democracy::emergency_cancel(Origin::signed(4), r),
			Error::<Test>::AlreadyCanceled,
		);
	});
}
