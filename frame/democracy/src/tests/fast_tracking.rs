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

//! The tests for fast-tracking functionality.

use super::*;

#[test]
fn fast_track_referendum_works() {
	new_test_ext().execute_with(|| {
		System::set_block_number(0);
		let h = set_balance_proposal_hash_and_note(2);
		assert_noop!(
			Democracy::fast_track(RuntimeOrigin::signed(5), h, 3, 2),
			Error::<Test>::ProposalMissing
		);
		assert_ok!(Democracy::external_propose_majority(
			RuntimeOrigin::signed(3),
			set_balance_proposal_hash_and_note(2)
		));
		assert_noop!(Democracy::fast_track(RuntimeOrigin::signed(1), h, 3, 2), BadOrigin);
		assert_ok!(Democracy::fast_track(RuntimeOrigin::signed(5), h, 2, 0));
		assert_eq!(
			Democracy::referendum_status(0),
			Ok(ReferendumStatus {
				end: 2,
				proposal_hash: set_balance_proposal_hash_and_note(2),
				threshold: VoteThreshold::SimpleMajority,
				delay: 0,
				tally: Tally { ayes: 0, nays: 0, turnout: 0 },
			})
		);
	});
}

#[test]
fn instant_referendum_works() {
	new_test_ext().execute_with(|| {
		System::set_block_number(0);
		let h = set_balance_proposal_hash_and_note(2);
		assert_noop!(
			Democracy::fast_track(RuntimeOrigin::signed(5), h, 3, 2),
			Error::<Test>::ProposalMissing
		);
		assert_ok!(Democracy::external_propose_majority(
			RuntimeOrigin::signed(3),
			set_balance_proposal_hash_and_note(2)
		));
		assert_noop!(Democracy::fast_track(RuntimeOrigin::signed(1), h, 3, 2), BadOrigin);
		assert_noop!(Democracy::fast_track(RuntimeOrigin::signed(5), h, 1, 0), BadOrigin);
		assert_noop!(
			Democracy::fast_track(RuntimeOrigin::signed(6), h, 1, 0),
			Error::<Test>::InstantNotAllowed
		);
		INSTANT_ALLOWED.with(|v| *v.borrow_mut() = true);
		assert_noop!(
			Democracy::fast_track(RuntimeOrigin::signed(6), h, 0, 0),
			Error::<Test>::VotingPeriodLow
		);
		assert_ok!(Democracy::fast_track(RuntimeOrigin::signed(6), h, 1, 0));
		assert_eq!(
			Democracy::referendum_status(0),
			Ok(ReferendumStatus {
				end: 1,
				proposal_hash: set_balance_proposal_hash_and_note(2),
				threshold: VoteThreshold::SimpleMajority,
				delay: 0,
				tally: Tally { ayes: 0, nays: 0, turnout: 0 },
			})
		);
	});
}

#[test]
fn instant_next_block_referendum_backed() {
	new_test_ext().execute_with(|| {
		// arrange
		let start_block_number = 10;
		let majority_origin_id = 3;
		let instant_origin_id = 6;
		let voting_period = 1;
		let proposal_hash = set_balance_proposal_hash_and_note(2);
		let delay = 2; // has no effect on test

		// init
		System::set_block_number(start_block_number);
		InstantAllowed::set(true);

		// propose with majority origin
		assert_ok!(Democracy::external_propose_majority(
			RuntimeOrigin::signed(majority_origin_id),
			proposal_hash
		));

		// fast track with instant origin and voting period pointing to the next block
		assert_ok!(Democracy::fast_track(
			RuntimeOrigin::signed(instant_origin_id),
			proposal_hash,
			voting_period,
			delay
		));

		// fetch the status of the only referendum at index 0
		assert_eq!(
			Democracy::referendum_status(0),
			Ok(ReferendumStatus {
				end: start_block_number + voting_period,
				proposal_hash,
				threshold: VoteThreshold::SimpleMajority,
				delay,
				tally: Tally { ayes: 0, nays: 0, turnout: 0 },
			})
		);

		// referendum expected to be baked with the start of the next block
		next_block();

		// assert no active referendums
		assert_noop!(Democracy::referendum_status(0), Error::<Test>::ReferendumInvalid);
		// the only referendum in the storage is finished and not approved
		assert_eq!(
			ReferendumInfoOf::<Test>::get(0).unwrap(),
			ReferendumInfo::Finished { approved: false, end: start_block_number + voting_period }
		);
	});
}

#[test]
fn fast_track_referendum_fails_when_no_simple_majority() {
	new_test_ext().execute_with(|| {
		System::set_block_number(0);
		let h = set_balance_proposal_hash_and_note(2);
		assert_ok!(Democracy::external_propose(
			RuntimeOrigin::signed(2),
			set_balance_proposal_hash_and_note(2)
		));
		assert_noop!(
			Democracy::fast_track(RuntimeOrigin::signed(5), h, 3, 2),
			Error::<Test>::NotSimpleMajority
		);
	});
}
