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

//! The tests for normal voting functionality.

use super::*;

#[test]
fn overvoting_should_fail() {
	new_test_ext().execute_with(|| {
		let r = begin_referendum();
		assert_noop!(Democracy::vote(Origin::signed(1), r, aye(2)), Error::<Test>::InsufficientFunds);
	});
}

#[test]
fn split_voting_should_work() {
	new_test_ext().execute_with(|| {
		let r = begin_referendum();
		let v = AccountVote::Split { aye: 40, nay: 20 };
		assert_noop!(Democracy::vote(Origin::signed(5), r, v), Error::<Test>::InsufficientFunds);
		let v = AccountVote::Split { aye: 30, nay: 20 };
		assert_ok!(Democracy::vote(Origin::signed(5), r, v));

		assert_eq!(tally(r), Tally { ayes: 3, nays: 2, turnout: 50 });
	});
}

#[test]
fn split_vote_cancellation_should_work() {
	new_test_ext().execute_with(|| {
		let r = begin_referendum();
		let v = AccountVote::Split { aye: 30, nay: 20 };
		assert_ok!(Democracy::vote(Origin::signed(5), r, v));
		assert_ok!(Democracy::remove_vote(Origin::signed(5), r));
		assert_eq!(tally(r), Tally { ayes: 0, nays: 0, turnout: 0 });
		assert_ok!(Democracy::unlock(Origin::signed(5), 5));
		assert_eq!(Balances::locks(5), vec![]);
	});
}

#[test]
fn single_proposal_should_work() {
	new_test_ext().execute_with(|| {
		System::set_block_number(0);
		assert_ok!(propose_set_balance_and_note(1, 2, 1));
		let r = 0;
		assert!(Democracy::referendum_info(r).is_none());

		// start of 2 => next referendum scheduled.
		fast_forward_to(2);
		assert_ok!(Democracy::vote(Origin::signed(1), r, aye(1)));

		assert_eq!(Democracy::referendum_count(), 1);
		assert_eq!(
			Democracy::referendum_status(0),
			Ok(ReferendumStatus {
				end: 4,
				proposal_hash: set_balance_proposal_hash_and_note(2),
				threshold: VoteThreshold::SuperMajorityApprove,
				delay: 2,
				tally: Tally { ayes: 1, nays: 0, turnout: 10 },
			})
		);

		fast_forward_to(3);

		// referendum still running
		assert!(Democracy::referendum_status(0).is_ok());

		// referendum runs during 2 and 3, ends @ start of 4.
		fast_forward_to(4);

		assert!(Democracy::referendum_status(0).is_err());
		assert!(pallet_scheduler::Agenda::<Test>::get(6)[0].is_some());

		// referendum passes and wait another two blocks for enactment.
		fast_forward_to(6);

		assert_eq!(Balances::free_balance(42), 2);
	});
}

#[test]
fn controversial_voting_should_work() {
	new_test_ext().execute_with(|| {
		let r = Democracy::inject_referendum(
			2,
			set_balance_proposal_hash_and_note(2),
			VoteThreshold::SuperMajorityApprove,
			0
		);

		assert_ok!(Democracy::vote(Origin::signed(1), r, big_aye(1)));
		assert_ok!(Democracy::vote(Origin::signed(2), r, big_nay(2)));
		assert_ok!(Democracy::vote(Origin::signed(3), r, big_nay(3)));
		assert_ok!(Democracy::vote(Origin::signed(4), r, big_aye(4)));
		assert_ok!(Democracy::vote(Origin::signed(5), r, big_nay(5)));
		assert_ok!(Democracy::vote(Origin::signed(6), r, big_aye(6)));

		assert_eq!(tally(r), Tally { ayes: 110, nays: 100, turnout: 210 });

		next_block();
		next_block();

		assert_eq!(Balances::free_balance(42), 2);
	});
}

#[test]
fn controversial_low_turnout_voting_should_work() {
	new_test_ext().execute_with(|| {
		let r = Democracy::inject_referendum(
			2,
			set_balance_proposal_hash_and_note(2),
			VoteThreshold::SuperMajorityApprove,
			0
		);
		assert_ok!(Democracy::vote(Origin::signed(5), r, big_nay(5)));
		assert_ok!(Democracy::vote(Origin::signed(6), r, big_aye(6)));

		assert_eq!(tally(r), Tally { ayes: 60, nays: 50, turnout: 110 });

		next_block();
		next_block();

		assert_eq!(Balances::free_balance(42), 0);
	});
}

#[test]
fn passing_low_turnout_voting_should_work() {
	new_test_ext().execute_with(|| {
		assert_eq!(Balances::free_balance(42), 0);
		assert_eq!(Balances::total_issuance(), 210);

		let r = Democracy::inject_referendum(
			2,
			set_balance_proposal_hash_and_note(2),
			VoteThreshold::SuperMajorityApprove,
			0
		);
		assert_ok!(Democracy::vote(Origin::signed(4), r, big_aye(4)));
		assert_ok!(Democracy::vote(Origin::signed(5), r, big_nay(5)));
		assert_ok!(Democracy::vote(Origin::signed(6), r, big_aye(6)));
		assert_eq!(tally(r), Tally { ayes: 100, nays: 50, turnout: 150 });

		next_block();
		next_block();
		assert_eq!(Balances::free_balance(42), 2);
	});
}

#[test]
fn first_free_should_work() {
	new_test_ext().execute_with(|| {

		const PROP_ACC_ID: u64 = 6;
		const VOTER1_ACC_ID: u64 = 5;
		const WHO_ACC_ID_42: u64 = 42;
		const DBG_THIS_FILE: &str = file!();

		System::set_block_number(0);

		let dbg_current_line = line!();
		println!("@[{:#?}::{:#?}]::**Test-Start**",
						DBG_THIS_FILE,
						dbg_current_line );

		let dbg_current_line = line!();
		println!("@[{:#?}::{:#?}]::Bal of(acc-{:#?}={:#?} | acc-{:#?}={:#?})",
						DBG_THIS_FILE,
						dbg_current_line,
						PROP_ACC_ID,
						Balances::free_balance(PROP_ACC_ID),
						WHO_ACC_ID_42,
						Balances::free_balance(WHO_ACC_ID_42));

		let dbg_current_line = line!();
		println!("@[{:#?}::{:#?}]::Bal of(acc-{:#?}={:#?} | acc-{:#?}={:#?})",
						DBG_THIS_FILE,
						dbg_current_line,
						VOTER1_ACC_ID,
						Balances::free_balance(VOTER1_ACC_ID),
						WHO_ACC_ID_42,
						Balances::free_balance(WHO_ACC_ID_42));

		let dbg_current_line = line!();
		println!("@[{:#?}::{:#?}]::**Democracy::propose({:#?})**",
						DBG_THIS_FILE,
						dbg_current_line,
						PROP_ACC_ID );

		assert_ok!(propose_set_balance_and_note(PROP_ACC_ID, 5, 10));
		let dbg_current_line = line!();
		println!("@[{:#?}::{:#?}]::Bal of(acc-{:#?}={:#?} | acc-{:#?}={:#?})",
						DBG_THIS_FILE,
						dbg_current_line,
						PROP_ACC_ID,
						Balances::free_balance(PROP_ACC_ID),
						WHO_ACC_ID_42,
						Balances::free_balance(WHO_ACC_ID_42));

		let r = 0;
		assert!(Democracy::referendum_info(r).is_none());

		// start of 2 => next referendum scheduled.
		fast_forward_to(2);

		// referendum still running
		assert!(Democracy::referendum_status(r).is_ok());

		let dbg_current_line = line!();
		println!("@[{:#?}::{:#?}]::**Democracy::vote({:#?})**",
						DBG_THIS_FILE,
						dbg_current_line,
						PROP_ACC_ID );

		assert_ok!(Democracy::vote(Origin::signed(PROP_ACC_ID), r, aye(PROP_ACC_ID)));

		let dbg_current_line = line!();
		println!("@[{:#?}::{:#?}]::Bal of(acc-{:#?}={:#?} | acc-{:#?}={:#?})",
						DBG_THIS_FILE,
						dbg_current_line,
						PROP_ACC_ID,
						Balances::free_balance(PROP_ACC_ID),
						WHO_ACC_ID_42,
						Balances::free_balance(WHO_ACC_ID_42));

		let dbg_current_line = line!();
		println!("@[{:#?}::{:#?}]::Bal of(acc-{:#?}={:#?} | acc-{:#?}={:#?})",
						DBG_THIS_FILE,
						dbg_current_line,
						VOTER1_ACC_ID,
						Balances::free_balance(VOTER1_ACC_ID),
						WHO_ACC_ID_42,
						Balances::free_balance(WHO_ACC_ID_42));

		let dbg_current_line = line!();
		println!("@[{:#?}::{:#?}]::**Democracy::vote({:#?})**",
						DBG_THIS_FILE,
						dbg_current_line,
						VOTER1_ACC_ID );

		assert_ok!(Democracy::vote(Origin::signed(VOTER1_ACC_ID), r, aye(VOTER1_ACC_ID)));

		let dbg_current_line = line!();
		println!("@[{:#?}::{:#?}]::Bal of(acc-{:#?}={:#?} | acc-{:#?}={:#?})",
						DBG_THIS_FILE,
						dbg_current_line,
						PROP_ACC_ID,
						Balances::free_balance(PROP_ACC_ID),
						WHO_ACC_ID_42,
						Balances::free_balance(WHO_ACC_ID_42));

		let dbg_current_line = line!();
		println!("@[{:#?}::{:#?}]::Bal of(acc-{:#?}={:#?} | acc-{:#?}={:#?})",
						DBG_THIS_FILE,
						dbg_current_line,
						VOTER1_ACC_ID,
						Balances::free_balance(VOTER1_ACC_ID),
						WHO_ACC_ID_42,
						Balances::free_balance(WHO_ACC_ID_42));

		let dbg_current_line = line!();
		println!("@[{:#?}::{:#?}]::**Democracy::referendum_status**",
						DBG_THIS_FILE,
						dbg_current_line );

		assert_eq!(Democracy::referendum_count(), 1);
		assert_eq!(
			Democracy::referendum_status(0),
			Ok(ReferendumStatus {
				end: 4,
				proposal_hash: set_balance_proposal_hash_and_note(5),
				threshold: VoteThreshold::SuperMajorityApprove,
				delay: 2,
				tally: Tally { ayes: 11, nays: 0, turnout: 110 },
			})
		);

		let dbg_current_line = line!();
		println!("@[{:#?}::{:#?}]::**Democracy::vote({:#?})**",
						DBG_THIS_FILE,
						dbg_current_line,
						PROP_ACC_ID );

		assert_ok!(Democracy::vote(Origin::signed(PROP_ACC_ID), r, aye(PROP_ACC_ID)));

		let dbg_current_line = line!();
		println!("@[{:#?}::{:#?}]::**Democracy::vote({:#?})**",
						DBG_THIS_FILE,
						dbg_current_line,
						VOTER1_ACC_ID );

		assert_ok!(Democracy::vote(Origin::signed(VOTER1_ACC_ID), r, aye(VOTER1_ACC_ID)));

		fast_forward_to(3);

		assert_eq!(
			Democracy::referendum_status(r),
			Ok(ReferendumStatus {
				end: 4,
				proposal_hash: set_balance_proposal_hash_and_note(5),
				threshold: VoteThreshold::SuperMajorityApprove,
				delay: 2,
				tally: Tally { ayes: 11, nays: 0, turnout: 110 },
			})
		);

		// referendum still running
		assert!(Democracy::referendum_status(r).is_ok());

		// referendum runs during 2 and 3, ends @ start of 4.
		fast_forward_to(4);

		assert!(Democracy::referendum_status(r).is_err());
		assert!(pallet_scheduler::Agenda::<Test>::get(6)[0].is_some());

		// referendum passes and wait another two blocks for enactment.
		fast_forward_to(6);

		assert_eq!(Balances::free_balance(42), 5);

		let dbg_current_line = line!();
		println!("@[{:#?}::{:#?}]::**referendum-0-Test-Exit**",
						DBG_THIS_FILE,
						dbg_current_line );

		let dbg_current_line = line!();
		println!("@[{:#?}::{:#?}]::Bal of(acc-{:#?}={:#?} | acc-{:#?}={:#?})",
						DBG_THIS_FILE,
						dbg_current_line,
						PROP_ACC_ID,
						Balances::free_balance(PROP_ACC_ID),
						WHO_ACC_ID_42,
						Balances::free_balance(WHO_ACC_ID_42));

		let dbg_current_line = line!();
		println!("@[{:#?}::{:#?}]::Bal of(acc-{:#?}={:#?} | acc-{:#?}={:#?})",
						DBG_THIS_FILE,
						dbg_current_line,
						VOTER1_ACC_ID,
						Balances::free_balance(VOTER1_ACC_ID),
						WHO_ACC_ID_42,
						Balances::free_balance(WHO_ACC_ID_42));


		//============= referendum-1(Start) ====================================

		/*
		const REF1_PROP_ACC_ID: u64 = 4;

		let dbg_current_line = line!();
		println!("@[{:#?}::{:#?}]::**referendum-1-Start**",
						DBG_THIS_FILE,
						dbg_current_line );

		let dbg_current_line = line!();
		println!("@[{:#?}::{:#?}]::**Democracy::propose({:#?})**",
						DBG_THIS_FILE,
						dbg_current_line,
						REF1_PROP_ACC_ID );

		assert_ok!(propose_set_balance_and_note(REF1_PROP_ACC_ID, 4, 10));
		let dbg_current_line = line!();
		println!("@[{:#?}::{:#?}]::Bal of(acc-{:#?}={:#?} | acc-{:#?}={:#?})",
						DBG_THIS_FILE,
						dbg_current_line,
						REF1_PROP_ACC_ID,
						Balances::free_balance(REF1_PROP_ACC_ID),
						WHO_ACC_ID_42,
						Balances::free_balance(WHO_ACC_ID_42));

		let r = 1;
		assert!(Democracy::referendum_info(r).is_none());

		// start of 2 => next referendum scheduled.
		fast_forward_to(2);

		let dbg_current_line = line!();
		println!("@[{:#?}::{:#?}]::**Democracy::vote({:#?})**",
						DBG_THIS_FILE,
						dbg_current_line,
						VOTER1_ACC_ID );

		assert!(Democracy::referendum_status(r).is_ok());

		assert_ok!(Democracy::vote(Origin::signed(VOTER1_ACC_ID), r, aye(VOTER1_ACC_ID)));

		fast_forward_to(3);

		assert_eq!(
			Democracy::referendum_status(r),
			Ok(ReferendumStatus {
				end: 4,
				proposal_hash: set_balance_proposal_hash_and_note(5),
				threshold: VoteThreshold::SuperMajorityApprove,
				delay: 2,
				tally: Tally { ayes: 11, nays: 0, turnout: 110 },
			})
		);

		// referendum still running
		assert!(Democracy::referendum_status(r).is_ok());

		// referendum runs during 2 and 3, ends @ start of 4.
		fast_forward_to(4);

		assert!(Democracy::referendum_status(r).is_err());
		*/
	});
}
