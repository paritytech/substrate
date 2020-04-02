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

//! The preimage tests.

use super::*;

#[test]
fn missing_preimage_should_fail() {
	new_test_ext().execute_with(|| {
		let r = Democracy::inject_referendum(
			2,
			set_balance_proposal_hash(2),
			VoteThreshold::SuperMajorityApprove,
			0
		);
		assert_ok!(Democracy::vote(Origin::signed(1), r, aye(1)));

		next_block();
		next_block();

		assert_eq!(Balances::free_balance(42), 0);
	});
}

#[test]
fn preimage_deposit_should_be_required_and_returned() {
	new_test_ext().execute_with(|| {
		// fee of 100 is too much.
		PREIMAGE_BYTE_DEPOSIT.with(|v| *v.borrow_mut() = 100);
		assert_noop!(
				Democracy::note_preimage(Origin::signed(6), vec![0; 500]),
				BalancesError::<Test, _>::InsufficientBalance,
			);
		// fee of 1 is reasonable.
		PREIMAGE_BYTE_DEPOSIT.with(|v| *v.borrow_mut() = 1);
		let r = Democracy::inject_referendum(
			2,
			set_balance_proposal_hash_and_note(2),
			VoteThreshold::SuperMajorityApprove,
			0
		);
		assert_ok!(Democracy::vote(Origin::signed(1), r, aye(1)));

		assert_eq!(Balances::reserved_balance(6), 12);

		next_block();
		next_block();

		assert_eq!(Balances::reserved_balance(6), 0);
		assert_eq!(Balances::free_balance(6), 60);
		assert_eq!(Balances::free_balance(42), 2);
	});
}

#[test]
fn preimage_deposit_should_be_reapable_earlier_by_owner() {
	new_test_ext().execute_with(|| {
		PREIMAGE_BYTE_DEPOSIT.with(|v| *v.borrow_mut() = 1);
		assert_ok!(Democracy::note_preimage(Origin::signed(6), set_balance_proposal(2)));

		assert_eq!(Balances::reserved_balance(6), 12);

		next_block();
		assert_noop!(
				Democracy::reap_preimage(Origin::signed(6), set_balance_proposal_hash(2)),
				Error::<Test>::TooEarly
			);
		next_block();
		assert_ok!(Democracy::reap_preimage(Origin::signed(6), set_balance_proposal_hash(2)));

		assert_eq!(Balances::free_balance(6), 60);
		assert_eq!(Balances::reserved_balance(6), 0);
	});
}

#[test]
fn preimage_deposit_should_be_reapable() {
	new_test_ext().execute_with(|| {
		assert_noop!(
				Democracy::reap_preimage(Origin::signed(5), set_balance_proposal_hash(2)),
				Error::<Test>::PreimageMissing
			);

		PREIMAGE_BYTE_DEPOSIT.with(|v| *v.borrow_mut() = 1);
		assert_ok!(Democracy::note_preimage(Origin::signed(6), set_balance_proposal(2)));
		assert_eq!(Balances::reserved_balance(6), 12);

		next_block();
		next_block();
		next_block();
		assert_noop!(
				Democracy::reap_preimage(Origin::signed(5), set_balance_proposal_hash(2)),
				Error::<Test>::TooEarly
			);

		next_block();
		assert_ok!(Democracy::reap_preimage(Origin::signed(5), set_balance_proposal_hash(2)));
		assert_eq!(Balances::reserved_balance(6), 0);
		assert_eq!(Balances::free_balance(6), 48);
		assert_eq!(Balances::free_balance(5), 62);
	});
}

#[test]
fn noting_imminent_preimage_for_free_should_work() {
	new_test_ext().execute_with(|| {
		PREIMAGE_BYTE_DEPOSIT.with(|v| *v.borrow_mut() = 1);

		let r = Democracy::inject_referendum(
			2,
			set_balance_proposal_hash(2),
			VoteThreshold::SuperMajorityApprove,
			1
		);
		assert_ok!(Democracy::vote(Origin::signed(1), r, aye(1)));

		assert_noop!(
				Democracy::note_imminent_preimage(Origin::signed(7), set_balance_proposal(2)),
				Error::<Test>::NotImminent
			);

		next_block();

		// Now we're in the dispatch queue it's all good.
		assert_ok!(Democracy::note_imminent_preimage(Origin::signed(7), set_balance_proposal(2)));

		next_block();

		assert_eq!(Balances::free_balance(42), 2);
	});
}

#[test]
fn reaping_imminent_preimage_should_fail() {
	new_test_ext().execute_with(|| {
		let h = set_balance_proposal_hash_and_note(2);
		let r = Democracy::inject_referendum(3, h, VoteThreshold::SuperMajorityApprove, 1);
		assert_ok!(Democracy::vote(Origin::signed(1), r, aye(1)));
		next_block();
		next_block();
		assert_noop!(Democracy::reap_preimage(Origin::signed(6), h), Error::<Test>::Imminent);
	});
}
