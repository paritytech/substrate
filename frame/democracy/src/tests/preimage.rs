// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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

//! The preimage tests.

use super::*;

#[test]
fn missing_preimage_should_fail() {
	new_test_ext().execute_with(|| {
		let r = Democracy::inject_referendum(
			2,
			set_balance_proposal_hash(2),
			VoteThreshold::SuperMajorityApprove,
			0,
		);
		assert_ok!(Democracy::vote(Origin::signed(1), r, aye(1)));

		next_block();
		next_block();

		assert_eq!(Balances::free_balance(42), 0);
	});
}

#[test]
fn preimage_deposit_should_be_required_and_returned() {
	new_test_ext_execute_with_cond(|operational| {
		// fee of 100 is too much.
		PREIMAGE_BYTE_DEPOSIT.with(|v| *v.borrow_mut() = 100);
		assert_noop!(
			if operational {
				Democracy::note_preimage_operational(Origin::signed(6), vec![0; 500])
			} else {
				Democracy::note_preimage(Origin::signed(6), vec![0; 500])
			},
			BalancesError::<Test, _>::InsufficientBalance,
		);
		// fee of 1 is reasonable.
		PREIMAGE_BYTE_DEPOSIT.with(|v| *v.borrow_mut() = 1);
		let r = Democracy::inject_referendum(
			2,
			set_balance_proposal_hash_and_note(2),
			VoteThreshold::SuperMajorityApprove,
			0,
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
	new_test_ext_execute_with_cond(|operational| {
		PREIMAGE_BYTE_DEPOSIT.with(|v| *v.borrow_mut() = 1);
		assert_ok!(if operational {
			Democracy::note_preimage_operational(Origin::signed(6), set_balance_proposal(2))
		} else {
			Democracy::note_preimage(Origin::signed(6), set_balance_proposal(2))
		});

		assert_eq!(Balances::reserved_balance(6), 12);

		next_block();
		assert_noop!(
			Democracy::reap_preimage(Origin::signed(6), set_balance_proposal_hash(2), u32::MAX),
			Error::<Test>::TooEarly
		);
		next_block();
		assert_ok!(Democracy::reap_preimage(
			Origin::signed(6),
			set_balance_proposal_hash(2),
			u32::MAX
		));

		assert_eq!(Balances::free_balance(6), 60);
		assert_eq!(Balances::reserved_balance(6), 0);
	});
}

#[test]
fn preimage_deposit_should_be_reapable() {
	new_test_ext_execute_with_cond(|operational| {
		assert_noop!(
			Democracy::reap_preimage(Origin::signed(5), set_balance_proposal_hash(2), u32::MAX),
			Error::<Test>::PreimageMissing
		);

		PREIMAGE_BYTE_DEPOSIT.with(|v| *v.borrow_mut() = 1);
		assert_ok!(if operational {
			Democracy::note_preimage_operational(Origin::signed(6), set_balance_proposal(2))
		} else {
			Democracy::note_preimage(Origin::signed(6), set_balance_proposal(2))
		});
		assert_eq!(Balances::reserved_balance(6), 12);

		next_block();
		next_block();
		next_block();
		assert_noop!(
			Democracy::reap_preimage(Origin::signed(5), set_balance_proposal_hash(2), u32::MAX),
			Error::<Test>::TooEarly
		);

		next_block();
		assert_ok!(Democracy::reap_preimage(
			Origin::signed(5),
			set_balance_proposal_hash(2),
			u32::MAX
		));
		assert_eq!(Balances::reserved_balance(6), 0);
		assert_eq!(Balances::free_balance(6), 48);
		assert_eq!(Balances::free_balance(5), 62);
	});
}

#[test]
fn noting_imminent_preimage_for_free_should_work() {
	new_test_ext_execute_with_cond(|operational| {
		PREIMAGE_BYTE_DEPOSIT.with(|v| *v.borrow_mut() = 1);

		let r = Democracy::inject_referendum(
			2,
			set_balance_proposal_hash(2),
			VoteThreshold::SuperMajorityApprove,
			1,
		);
		assert_ok!(Democracy::vote(Origin::signed(1), r, aye(1)));

		assert_noop!(
			if operational {
				Democracy::note_imminent_preimage_operational(
					Origin::signed(6),
					set_balance_proposal(2),
				)
			} else {
				Democracy::note_imminent_preimage(Origin::signed(6), set_balance_proposal(2))
			},
			Error::<Test>::NotImminent
		);

		next_block();

		// Now we're in the dispatch queue it's all good.
		assert_ok!(Democracy::note_imminent_preimage(Origin::signed(6), set_balance_proposal(2)));

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
		assert_noop!(
			Democracy::reap_preimage(Origin::signed(6), h, u32::MAX),
			Error::<Test>::Imminent
		);
	});
}

#[test]
fn note_imminent_preimage_can_only_be_successful_once() {
	new_test_ext().execute_with(|| {
		PREIMAGE_BYTE_DEPOSIT.with(|v| *v.borrow_mut() = 1);

		let r = Democracy::inject_referendum(
			2,
			set_balance_proposal_hash(2),
			VoteThreshold::SuperMajorityApprove,
			1,
		);
		assert_ok!(Democracy::vote(Origin::signed(1), r, aye(1)));
		next_block();

		// First time works
		assert_ok!(Democracy::note_imminent_preimage(Origin::signed(6), set_balance_proposal(2)));

		// Second time fails
		assert_noop!(
			Democracy::note_imminent_preimage(Origin::signed(6), set_balance_proposal(2)),
			Error::<Test>::DuplicatePreimage
		);

		// Fails from any user
		assert_noop!(
			Democracy::note_imminent_preimage(Origin::signed(5), set_balance_proposal(2)),
			Error::<Test>::DuplicatePreimage
		);
	});
}
