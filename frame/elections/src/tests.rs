// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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

//! Tests for election module.

#![cfg(test)]

use crate::mock::*;
use crate::*;

use frame_support::{assert_ok, assert_err, assert_noop};

#[test]
fn params_should_work() {
	ExtBuilder::default().build().execute_with(|| {
		assert_eq!(Elections::next_vote_from(1), 4);
		assert_eq!(Elections::next_vote_from(4), 4);
		assert_eq!(Elections::next_vote_from(5), 8);
		assert_eq!(Elections::vote_index(), 0);
		assert_eq!(Elections::presentation_duration(), 2);
		assert_eq!(Elections::term_duration(), 5);
		assert_eq!(Elections::desired_seats(), 2);

		assert_eq!(Elections::members(), vec![]);
		assert_eq!(Elections::next_tally(), Some(4));
		assert_eq!(Elections::presentation_active(), false);
		assert_eq!(Elections::next_finalize(), None);

		assert_eq!(Elections::candidates(), Vec::<u64>::new());
		assert_eq!(Elections::is_a_candidate(&1), false);
		assert_eq!(Elections::candidate_reg_info(1), None);

		assert_eq!(Elections::voters(0), Vec::<Option<u64>>::new());
		assert_eq!(Elections::voter_info(1), None);
		assert_eq!(Elections::all_approvals_of(&1), vec![]);
	});
}

#[test]
fn chunking_bool_to_flag_should_work() {
	ExtBuilder::default().build().execute_with(|| {
		assert_eq!(Elections::bool_to_flag(vec![]), vec![]);
		assert_eq!(Elections::bool_to_flag(vec![false]), vec![0]);
		assert_eq!(Elections::bool_to_flag(vec![true]), vec![1]);
		assert_eq!(Elections::bool_to_flag(vec![true, true, true, true]), vec![15]);
		assert_eq!(Elections::bool_to_flag(vec![true, true, true, true, true]), vec![15 + 16]);

		let set_1 = vec![
				true, false, false, false, // 0x1
				false, true, true, true, // 0xE
		];
		assert_eq!(
			Elections::bool_to_flag(set_1.clone()),
			vec![0x00_00_00_E1_u32]
		);
		assert_eq!(
			Elections::flag_to_bool(vec![0x00_00_00_E1_u32]),
			set_1
		);

		let set_2 = vec![
				false, false, false, true, // 0x8
				false, true, false, true, // 0xA
		];
		assert_eq!(
			Elections::bool_to_flag(set_2.clone()),
			vec![0x00_00_00_A8_u32]
		);
		assert_eq!(
			Elections::flag_to_bool(vec![0x00_00_00_A8_u32]),
			set_2
		);

		let mut rhs = (0..100/APPROVAL_FLAG_LEN).map(|_| 0xFFFFFFFF_u32).collect::<Vec<u32>>();
		// NOTE: this might be need change based on `APPROVAL_FLAG_LEN`.
		rhs.extend(vec![0x00_00_00_0F]);
		assert_eq!(
			Elections::bool_to_flag((0..100).map(|_| true).collect()),
			rhs
		)
	})
}

#[test]
fn chunking_voter_set_growth_should_work() {
	ExtBuilder::default().build().execute_with(|| {
		assert_ok!(Elections::submit_candidacy(Origin::signed(2), 0));

		// create 65. 64 (set0) + 1 (set1)
		(1..=63).for_each(|i| vote(i, 0));
		assert_eq!(Elections::next_nonfull_voter_set(), 0);
		vote(64, 0);
		assert_eq!(Elections::next_nonfull_voter_set(), 1);
		vote(65, 0);

		let set1 = Elections::voters(0);
		let set2 = Elections::voters(1);

		assert_eq!(set1.len(), 64);
		assert_eq!(set2.len(), 1);

		assert_eq!(set1[0], Some(1));
		assert_eq!(set1[10], Some(11));
		assert_eq!(set2[0], Some(65));
	})
}

#[test]
fn chunking_voter_set_reclaim_should_work() {
	ExtBuilder::default().build().execute_with(|| {
		assert_ok!(Elections::submit_candidacy(Origin::signed(2), 0));

		(1..=129).for_each(|i| vote(i, 0));
		assert_eq!(Elections::next_nonfull_voter_set(), 2);

		assert_ok!(Elections::retract_voter(Origin::signed(11), 10));

		assert_ok!(Elections::retract_voter(Origin::signed(66), 65));
		assert_ok!(Elections::retract_voter(Origin::signed(67), 66));

		// length does not show it but holes do exist.
		assert_eq!(Elections::voters(0).len(), 64);
		assert_eq!(Elections::voters(1).len(), 64);
		assert_eq!(Elections::voters(2).len(), 1);

		assert_eq!(Elections::voters(0)[10], None);
		assert_eq!(Elections::voters(1)[1], None);
		assert_eq!(Elections::voters(1)[2], None);
		// Next set with capacity is 2.
		assert_eq!(Elections::next_nonfull_voter_set(), 2);

		// But we can fill a hole.
		vote_at(130, 0, 10);

		// Nothing added to set 2. A hole was filled.
		assert_eq!(Elections::voters(0).len(), 64);
		assert_eq!(Elections::voters(1).len(), 64);
		assert_eq!(Elections::voters(2).len(), 1);

		// and the next two (scheduled) to the second set.
		assert_eq!(Elections::next_nonfull_voter_set(), 2);
	})
}

#[test]
fn chunking_approvals_set_growth_should_work() {
	ExtBuilder::default().build().execute_with(|| {
		// create candidates and voters.
		(1..=250).for_each(|i| create_candidate(i, (i-1) as u32));
		(1..=250).for_each(|i| vote(i, i as usize));

		// all approvals of should return the exact expected vector.
		assert_eq!(
			Elections::all_approvals_of(&180),
			(0..180).map(|_| true).collect::<Vec<bool>>()
		);
		assert_eq!(
			Elections::all_approvals_of(&32),
			(0..32).map(|_| true).collect::<Vec<bool>>()
		);
		assert_eq!(
			Elections::all_approvals_of(&8),
			(0..8).map(|_| true).collect::<Vec<bool>>()
		);
		assert_eq!(
			Elections::all_approvals_of(&64),
			(0..64).map(|_| true).collect::<Vec<bool>>()
		);
		assert_eq!(
			Elections::all_approvals_of(&65),
			(0..65).map(|_| true).collect::<Vec<bool>>()
		);
		assert_eq!(
			Elections::all_approvals_of(&63),
			(0..63).map(|_| true).collect::<Vec<bool>>()
		);

		// NOTE: assuming that APPROVAL_SET_SIZE is more or less small-ish. Might fail otherwise.
		let full_sets = (180 / APPROVAL_FLAG_LEN) / APPROVAL_SET_SIZE;
		let left_over = (180 / APPROVAL_FLAG_LEN) / APPROVAL_SET_SIZE;
		let rem = 180 % APPROVAL_FLAG_LEN;

		// grab and check the last full set, if it exists.
		if full_sets > 0 {
			assert_eq!(
				Elections::approvals_of((180, (full_sets-1) as SetIndex )),
				Elections::bool_to_flag(
					(0..APPROVAL_SET_SIZE * APPROVAL_FLAG_LEN)
					.map(|_| true).collect::<Vec<bool>>()
				)
			);
		}

		// grab and check the last, half-empty, set.
		if left_over > 0 {
			assert_eq!(
				Elections::approvals_of((180, full_sets as SetIndex)),
				Elections::bool_to_flag(
					(0..left_over * APPROVAL_FLAG_LEN + rem)
					.map(|_| true).collect::<Vec<bool>>()
				)
			);
		}
	})
}

#[test]
fn chunking_cell_status_works() {
	ExtBuilder::default().build().execute_with(|| {
		assert_ok!(Elections::submit_candidacy(Origin::signed(2), 0));

		(1..=63).for_each(|i| vote(i, 0));

		assert_ok!(Elections::retract_voter(Origin::signed(11), 10));
		assert_ok!(Elections::retract_voter(Origin::signed(21), 20));

		assert_eq!(Elections::cell_status(0, 10), CellStatus::Hole);
		assert_eq!(Elections::cell_status(0, 0), CellStatus::Occupied);
		assert_eq!(Elections::cell_status(0, 20), CellStatus::Hole);
		assert_eq!(Elections::cell_status(0, 63), CellStatus::Head);
		assert_eq!(Elections::cell_status(1, 0), CellStatus::Head);
		assert_eq!(Elections::cell_status(1, 10), CellStatus::Head);
	})
}

#[test]
fn chunking_voter_index_does_not_take_holes_into_account() {
	ExtBuilder::default().build().execute_with(|| {
		assert_ok!(Elections::submit_candidacy(Origin::signed(2), 0));

		// create 65. 64 (set0) + 1 (set1)
		(1..=65).for_each(|i| vote(i, 0));

		// account 65 has global index 65.
		assert_eq!(Elections::voter_at(64).unwrap(), 65);

		assert_ok!(Elections::retract_voter(Origin::signed(1), 0));
		assert_ok!(Elections::retract_voter(Origin::signed(2), 1));

		// still the same. These holes are in some other set.
		assert_eq!(Elections::voter_at(64).unwrap(), 65);
		// proof: can submit a new approval with the old index.
		assert_noop!(
			Elections::set_approvals(Origin::signed(65), vec![], 0, 64 - 2, 10),
			Error::<Test>::InvalidVoterIndex,
		);
		assert_ok!(Elections::set_approvals(Origin::signed(65), vec![], 0, 64, 10));
	})
}

#[test]
fn chunking_approval_storage_should_work() {
	ExtBuilder::default().build().execute_with(|| {
		assert_ok!(Elections::submit_candidacy(Origin::signed(2), 0));
		assert_ok!(Elections::submit_candidacy(Origin::signed(3), 1));

		assert_ok!(Elections::set_approvals(Origin::signed(2), vec![true, false], 0, 0, 20));
		assert_ok!(Elections::set_approvals(Origin::signed(3), vec![false, false], 0, 0, 30));
		assert_ok!(Elections::set_approvals(Origin::signed(4), vec![], 0, 0, 40));

		assert_eq!(Elections::all_approvals_of(&2), vec![true]);
		// NOTE: these two are stored in mem differently though.
		assert_eq!(Elections::all_approvals_of(&3), vec![]);
		assert_eq!(Elections::all_approvals_of(&4), vec![]);

		assert_eq!(Elections::approvals_of((3, 0)), vec![0]);
		assert_eq!(Elections::approvals_of((4, 0)), vec![]);
	});
}

#[test]
fn voting_initial_set_approvals_ignores_voter_index() {
	ExtBuilder::default().build().execute_with(|| {
		assert_ok!(Elections::submit_candidacy(Origin::signed(2), 0));

		// Last argument is essentially irrelevant. You might get or miss a tip.
		assert_ok!(Elections::set_approvals(Origin::signed(3), vec![], 0, 0, 30));
		assert_ok!(Elections::set_approvals(Origin::signed(4), vec![], 0, 5, 40));
		assert_ok!(Elections::set_approvals(Origin::signed(5), vec![], 0, 100, 50));

		// indices are more or less ignored. all is pushed.
		assert_eq!(voter_ids(), vec![3, 4, 5]);
	})
}
#[test]
fn voting_bad_approval_index_slashes_voters_and_bond_reduces_stake() {
	ExtBuilder::default().voting_fee(5).voter_bond(2).build().execute_with(|| {
		assert_ok!(Elections::submit_candidacy(Origin::signed(2), 0));

		(1..=63).for_each(|i| vote(i, 0));
		assert_eq!(balances(&1), (13, 2));
		assert_eq!(balances(&10), (18, 2));
		assert_eq!(balances(&60), (18, 2));

		// still no fee
		vote(64, 0);
		assert_eq!(balances(&64), (18, 2));
		assert_eq!(
			Elections::voter_info(&64).unwrap(),
			VoterInfo { last_win: 0, last_active: 0, stake: 20, pot:0 }
		);

		assert_eq!(Elections::next_nonfull_voter_set(), 1);

		// now we charge the next voter.
		vote(65, 0);
		assert_eq!(balances(&65), (13, 2));
		assert_eq!(
			Elections::voter_info(&65).unwrap(),
			VoterInfo { last_win: 0, last_active: 0, stake: 15, pot:0 }
		);
	});
}

#[test]
fn voting_subsequent_set_approvals_checks_voter_index() {
	ExtBuilder::default().build().execute_with(|| {
		assert_ok!(Elections::submit_candidacy(Origin::signed(2), 0));

		assert_ok!(Elections::set_approvals(Origin::signed(3), vec![], 0, 0, 30));
		assert_ok!(Elections::set_approvals(Origin::signed(4), vec![], 0, 5, 40));
		assert_ok!(Elections::set_approvals(Origin::signed(5), vec![], 0, 100, 50));

		// invalid index
		assert_noop!(
			Elections::set_approvals(Origin::signed(4), vec![true], 0, 5, 40),
			Error::<Test>::InvalidVoterIndex,
		);
		// wrong index
		assert_noop!(
			Elections::set_approvals(Origin::signed(4), vec![true], 0, 0, 40),
			Error::<Test>::InvalidVoterIndex,
		);
		// correct
		assert_ok!(Elections::set_approvals(Origin::signed(4), vec![true], 0, 1, 40));
	})
}

#[test]
fn voting_cannot_lock_less_than_limit() {
	ExtBuilder::default().build().execute_with(|| {
		assert_ok!(Elections::submit_candidacy(Origin::signed(2), 0));

		assert_noop!(
			Elections::set_approvals(Origin::signed(3), vec![], 0, 0, 4),
			Error::<Test>::InsufficientLockedValue,
		);
		assert_ok!(Elections::set_approvals(Origin::signed(3), vec![], 0, 0, 5));
	});
}

#[test]
fn voting_locking_more_than_total_balance_is_moot() {
	ExtBuilder::default().voter_bond(2).build().execute_with(|| {
		assert_ok!(Elections::submit_candidacy(Origin::signed(2), 0));

		assert_eq!(balances(&3), (30, 0));
		assert_ok!(Elections::set_approvals(Origin::signed(3), vec![], 0, 0, 35));

		assert_eq!(balances(&3), (28, 2));
		assert_eq!(
			Elections::voter_info(&3).unwrap(),
			VoterInfo { last_win: 0, last_active: 0, stake: 30, pot:0 }
		);
	});
}

#[test]
fn voting_locking_stake_and_reserving_bond_works() {
	ExtBuilder::default().voter_bond(2).build().execute_with(|| {
		assert_ok!(Elections::submit_candidacy(Origin::signed(5), 0));

		assert_eq!(balances(&2), (20, 0));
		assert_eq!(locks(&2), vec![]);
		assert_ok!(Elections::set_approvals(Origin::signed(2), vec![], 0, 0, 15));
		assert_eq!(balances(&2), (18, 2));
		assert_eq!(locks(&2), vec![15]);

		// deposit a bit more.
		let _ = Balances::make_free_balance_be(&2, 100);

		// change vote
		assert_ok!(Elections::set_approvals(Origin::signed(2), vec![true], 0, 0, 70));
		assert_eq!(balances(&2), (100, 2));
		assert_eq!(locks(&2), vec![70]);

		assert_ok!(Elections::retract_voter(Origin::signed(2), 0));

		assert_eq!(balances(&2), (102, 0));
		assert_eq!(locks(&2), vec![]);
	});
}

#[test]
fn voting_without_any_candidate_count_should_not_work() {
	ExtBuilder::default().build().execute_with(|| {
		assert_eq!(Elections::candidates().len(), 0);

		assert_noop!(
			Elections::set_approvals(Origin::signed(4), vec![], 0, 0, 40),
			Error::<Test>::ZeroCandidates,
		);
	});
}

#[test]
fn voting_setting_an_approval_vote_count_more_than_candidate_count_should_not_work() {
	ExtBuilder::default().build().execute_with(|| {
		assert_ok!(Elections::submit_candidacy(Origin::signed(5), 0));
		assert_eq!(Elections::candidates().len(), 1);

		assert_noop!(
			Elections::set_approvals(Origin::signed(4),vec![true, true], 0, 0, 40),
			Error::<Test>::TooManyVotes,
		);
	});
}

#[test]
fn voting_resubmitting_approvals_should_work() {
	ExtBuilder::default().build().execute_with(|| {
		assert_ok!(Elections::submit_candidacy(Origin::signed(5), 0));
		assert_ok!(Elections::set_approvals(Origin::signed(4), vec![true], 0, 0, 40));

		assert_eq!(Elections::all_approvals_of(&4), vec![true]);

		assert_ok!(Elections::submit_candidacy(Origin::signed(2), 1));
		assert_ok!(Elections::submit_candidacy(Origin::signed(3), 2));
		assert_eq!(Elections::candidates().len(), 3);
		assert_ok!(Elections::set_approvals(Origin::signed(4), vec![true, false, true], 0, 0, 40));

		assert_eq!(Elections::all_approvals_of(&4), vec![true, false, true]);
	});
}

#[test]
fn voting_retracting_voter_should_work() {
	ExtBuilder::default().build().execute_with(|| {
		assert_ok!(Elections::submit_candidacy(Origin::signed(5), 0));
		assert_eq!(Elections::candidates().len(), 1);

		assert_ok!(Elections::set_approvals(Origin::signed(1), vec![true], 0, 0, 10));
		assert_ok!(Elections::set_approvals(Origin::signed(2), vec![true], 0, 1, 20));
		assert_ok!(Elections::set_approvals(Origin::signed(3), vec![true], 0, 2, 30));
		assert_ok!(Elections::set_approvals(Origin::signed(4), vec![true], 0, 3, 40));

		assert_eq!(voter_ids(), vec![1, 2, 3, 4]);
		assert_eq!(Elections::all_approvals_of(&1), vec![true]);
		assert_eq!(Elections::all_approvals_of(&2), vec![true]);
		assert_eq!(Elections::all_approvals_of(&3), vec![true]);
		assert_eq!(Elections::all_approvals_of(&4), vec![true]);

		assert_ok!(Elections::retract_voter(Origin::signed(1), 0));

		assert_eq!(voter_ids(), vec![0, 2, 3, 4]);
		assert_eq!(Elections::all_approvals_of(&1), Vec::<bool>::new());
		assert_eq!(Elections::all_approvals_of(&2), vec![true]);
		assert_eq!(Elections::all_approvals_of(&3), vec![true]);
		assert_eq!(Elections::all_approvals_of(&4), vec![true]);

		assert_ok!(Elections::retract_voter(Origin::signed(2), 1));

		assert_eq!(voter_ids(), vec![0, 0, 3, 4]);
		assert_eq!(Elections::all_approvals_of(&1), Vec::<bool>::new());
		assert_eq!(Elections::all_approvals_of(&2), Vec::<bool>::new());
		assert_eq!(Elections::all_approvals_of(&3), vec![true]);
		assert_eq!(Elections::all_approvals_of(&4), vec![true]);

		assert_ok!(Elections::retract_voter(Origin::signed(3), 2));

		assert_eq!(voter_ids(), vec![0, 0, 0, 4]);
		assert_eq!(Elections::all_approvals_of(&1), Vec::<bool>::new());
		assert_eq!(Elections::all_approvals_of(&2), Vec::<bool>::new());
		assert_eq!(Elections::all_approvals_of(&3), Vec::<bool>::new());
		assert_eq!(Elections::all_approvals_of(&4), vec![true]);
	});
}

#[test]
fn voting_invalid_retraction_index_should_not_work() {
	ExtBuilder::default().build().execute_with(|| {
		assert_ok!(Elections::submit_candidacy(Origin::signed(3), 0));

		assert_ok!(Elections::set_approvals(Origin::signed(1), vec![true], 0, 0, 10));
		assert_ok!(Elections::set_approvals(Origin::signed(2), vec![true], 0, 0, 20));
		assert_eq!(voter_ids(), vec![1, 2]);
		assert_noop!(Elections::retract_voter(Origin::signed(1), 1), Error::<Test>::InvalidRetractionIndex);
	});
}

#[test]
fn voting_overflow_retraction_index_should_not_work() {
	ExtBuilder::default().build().execute_with(|| {
		assert_ok!(Elections::submit_candidacy(Origin::signed(3), 0));

		assert_ok!(Elections::set_approvals(Origin::signed(1), vec![true], 0, 0, 10));
		assert_noop!(Elections::retract_voter(Origin::signed(1), 1), Error::<Test>::InvalidRetractionIndex);
	});
}

#[test]
fn voting_non_voter_retraction_should_not_work() {
	ExtBuilder::default().build().execute_with(|| {
		assert_ok!(Elections::submit_candidacy(Origin::signed(3), 0));

		assert_ok!(Elections::set_approvals(Origin::signed(1), vec![true], 0, 0, 10));
		assert_noop!(Elections::retract_voter(Origin::signed(2), 0), Error::<Test>::RetractNonVoter);
	});
}

#[test]
fn retracting_inactive_voter_should_work() {
	ExtBuilder::default().build().execute_with(|| {
		System::set_block_number(4);
		assert_ok!(Elections::submit_candidacy(Origin::signed(2), 0));
		assert_ok!(Elections::set_approvals(Origin::signed(2), vec![true], 0, 0, 20));
		assert_ok!(Elections::end_block(System::block_number()));

		System::set_block_number(6);
		assert_ok!(Elections::present_winner(Origin::signed(4), 2, 20, 0));
		assert_ok!(Elections::end_block(System::block_number()));

		System::set_block_number(8);
		assert_ok!(Elections::submit_candidacy(Origin::signed(5), 0));
		assert_ok!(Elections::set_approvals(Origin::signed(5), vec![true], 1, 0, 50));
		assert_ok!(Elections::end_block(System::block_number()));

		System::set_block_number(10);
		assert_ok!(Elections::present_winner(Origin::signed(4), 5, 50, 1));
		assert_ok!(Elections::end_block(System::block_number()));

		assert_ok!(Elections::reap_inactive_voter(Origin::signed(5),
			(voter_ids().iter().position(|&i| i == 5).unwrap() as u32).into(),
			2, (voter_ids().iter().position(|&i| i == 2).unwrap() as u32).into(),
			2
		));

		assert_eq!(voter_ids(), vec![0, 5]);
		assert_eq!(Elections::all_approvals_of(&2).len(), 0);
		assert_eq!(Balances::total_balance(&2), 20);
		assert_eq!(Balances::total_balance(&5), 50);
	});
}

#[test]
fn retracting_inactive_voter_with_other_candidates_in_slots_should_work() {
	ExtBuilder::default().voter_bond(2).build().execute_with(|| {
		System::set_block_number(4);
		assert_ok!(Elections::submit_candidacy(Origin::signed(2), 0));
		assert_ok!(Elections::set_approvals(Origin::signed(2), vec![true], 0, 0, 20));
		assert_ok!(Elections::end_block(System::block_number()));

		System::set_block_number(6);
		assert_ok!(Elections::present_winner(Origin::signed(4), 2, 20, 0));
		assert_ok!(Elections::end_block(System::block_number()));

		System::set_block_number(8);
		assert_ok!(Elections::submit_candidacy(Origin::signed(5), 0));
		assert_ok!(Elections::set_approvals(Origin::signed(5), vec![true], 1, 0, 50));
		assert_ok!(Elections::end_block(System::block_number()));

		System::set_block_number(10);
		assert_ok!(Elections::present_winner(Origin::signed(4), 5, 50, 1));
		assert_ok!(Elections::end_block(System::block_number()));

		System::set_block_number(11);
		assert_ok!(Elections::submit_candidacy(Origin::signed(1), 0));

		assert_ok!(Elections::reap_inactive_voter(Origin::signed(5),
			(voter_ids().iter().position(|&i| i == 5).unwrap() as u32).into(),
			2, (voter_ids().iter().position(|&i| i == 2).unwrap() as u32).into(),
			2
		));

		assert_eq!(voter_ids(), vec![0, 5]);
		assert_eq!(Elections::all_approvals_of(&2).len(), 0);
	});
}

#[test]
fn retracting_inactive_voter_with_bad_reporter_index_should_not_work() {
	ExtBuilder::default().build().execute_with(|| {
		System::set_block_number(4);
		assert_ok!(Elections::submit_candidacy(Origin::signed(2), 0));
		assert_ok!(Elections::set_approvals(Origin::signed(2), vec![true], 0, 0, 20));
		assert_ok!(Elections::end_block(System::block_number()));

		System::set_block_number(6);
		assert_ok!(Elections::present_winner(Origin::signed(4), 2, 20, 0));
		assert_ok!(Elections::end_block(System::block_number()));

		System::set_block_number(8);
		assert_ok!(Elections::submit_candidacy(Origin::signed(5), 0));
		assert_ok!(Elections::set_approvals(Origin::signed(5), vec![true], 1, 0, 50));
		assert_ok!(Elections::end_block(System::block_number()));

		System::set_block_number(10);
		assert_ok!(Elections::present_winner(Origin::signed(4), 5, 50, 1));
		assert_ok!(Elections::end_block(System::block_number()));

		assert_noop!(Elections::reap_inactive_voter(Origin::signed(2),
			42,
			2, (voter_ids().iter().position(|&i| i == 2).unwrap() as u32).into(),
			2
		), Error::<Test>::InvalidReporterIndex);
	});
}

#[test]
fn retracting_inactive_voter_with_bad_target_index_should_not_work() {
	ExtBuilder::default().build().execute_with(|| {
		System::set_block_number(4);
		assert_ok!(Elections::submit_candidacy(Origin::signed(2), 0));
		assert_ok!(Elections::set_approvals(Origin::signed(2), vec![true], 0, 0, 20));
		assert_ok!(Elections::end_block(System::block_number()));

		System::set_block_number(6);
		assert_ok!(Elections::present_winner(Origin::signed(4), 2, 20, 0));
		assert_ok!(Elections::end_block(System::block_number()));

		System::set_block_number(8);
		assert_ok!(Elections::submit_candidacy(Origin::signed(5), 0));
		assert_ok!(Elections::set_approvals(Origin::signed(5), vec![true], 1, 0, 50));
		assert_ok!(Elections::end_block(System::block_number()));

		System::set_block_number(10);
		assert_ok!(Elections::present_winner(Origin::signed(4), 5, 50, 1));
		assert_ok!(Elections::end_block(System::block_number()));

		assert_noop!(Elections::reap_inactive_voter(Origin::signed(2),
			(voter_ids().iter().position(|&i| i == 2).unwrap() as u32).into(),
			2, 42,
			2
		), Error::<Test>::InvalidTargetIndex);
	});
}

#[test]
fn retracting_active_voter_should_slash_reporter() {
	ExtBuilder::default().build().execute_with(|| {
		System::set_block_number(4);
		assert_ok!(Elections::submit_candidacy(Origin::signed(2), 0));
		assert_ok!(Elections::submit_candidacy(Origin::signed(3), 1));
		assert_ok!(Elections::submit_candidacy(Origin::signed(4), 2));
		assert_ok!(Elections::submit_candidacy(Origin::signed(5), 3));
		assert_ok!(Elections::set_approvals(Origin::signed(2), vec![true, false, false, false], 0, 0, 20));
		assert_ok!(Elections::set_approvals(Origin::signed(3), vec![false, true, false, false], 0, 0, 30));
		assert_ok!(Elections::set_approvals(Origin::signed(4), vec![false, false, true, false], 0, 0, 40));
		assert_ok!(Elections::set_approvals(Origin::signed(5), vec![false, false, false, true], 0, 0, 50));
		assert_ok!(Elections::end_block(System::block_number()));

		System::set_block_number(6);
		assert_ok!(Elections::present_winner(Origin::signed(4), 2, 20, 0));
		assert_ok!(Elections::present_winner(Origin::signed(4), 3, 30, 0));
		assert_ok!(Elections::present_winner(Origin::signed(4), 4, 40, 0));
		assert_ok!(Elections::present_winner(Origin::signed(4), 5, 50, 0));
		assert_ok!(Elections::end_block(System::block_number()));

		System::set_block_number(8);
		assert_ok!(Elections::set_desired_seats(Origin::ROOT, 3));
		assert_ok!(Elections::end_block(System::block_number()));

		System::set_block_number(10);
		assert_ok!(Elections::present_winner(Origin::signed(4), 2, 20 + Elections::get_offset(20, 1), 1));
		assert_ok!(Elections::present_winner(Origin::signed(4), 3, 30 + Elections::get_offset(30, 1), 1));
		assert_ok!(Elections::end_block(System::block_number()));

		assert_eq!(Elections::vote_index(), 2);
		assert_eq!(<Test as Trait>::InactiveGracePeriod::get(), 1);
		assert_eq!(<Test as Trait>::VotingPeriod::get(), 4);
		assert_eq!(Elections::voter_info(4), Some(VoterInfo { last_win: 1, last_active: 0, stake: 40, pot: 0 }));

		assert_ok!(Elections::reap_inactive_voter(Origin::signed(4),
			(voter_ids().iter().position(|&i| i == 4).unwrap() as u32).into(),
			2,
			(voter_ids().iter().position(|&i| i == 2).unwrap() as u32).into(),
			2
		));

		assert_eq!(voter_ids(), vec![2, 3, 0, 5]);
		assert_eq!(Elections::all_approvals_of(&4).len(), 0);
		assert_eq!(Balances::total_balance(&4), 40);
	});
}

#[test]
fn retracting_inactive_voter_by_nonvoter_should_not_work() {
	ExtBuilder::default().build().execute_with(|| {
		System::set_block_number(4);
		assert_ok!(Elections::submit_candidacy(Origin::signed(2), 0));
		assert_ok!(Elections::set_approvals(Origin::signed(2), vec![true], 0, 0, 20));
		assert_ok!(Elections::end_block(System::block_number()));

		System::set_block_number(6);
		assert_ok!(Elections::present_winner(Origin::signed(4), 2, 20, 0));
		assert_ok!(Elections::end_block(System::block_number()));

		System::set_block_number(8);
		assert_ok!(Elections::submit_candidacy(Origin::signed(5), 0));
		assert_ok!(Elections::set_approvals(Origin::signed(5), vec![true], 1, 0, 50));
		assert_ok!(Elections::end_block(System::block_number()));

		System::set_block_number(10);
		assert_ok!(Elections::present_winner(Origin::signed(4), 5, 50, 1));
		assert_ok!(Elections::end_block(System::block_number()));

		assert_noop!(Elections::reap_inactive_voter(Origin::signed(4),
			0,
			2, (voter_ids().iter().position(|&i| i == 2).unwrap() as u32).into(),
			2
		), Error::<Test>::NotVoter);
	});
}

#[test]
fn candidacy_simple_candidate_submission_should_work() {
	ExtBuilder::default().build().execute_with(|| {
		assert_eq!(Elections::candidates(), Vec::<u64>::new());
		assert_eq!(Elections::candidate_reg_info(1), None);
		assert_eq!(Elections::candidate_reg_info(2), None);
		assert_eq!(Elections::is_a_candidate(&1), false);
		assert_eq!(Elections::is_a_candidate(&2), false);

		assert_ok!(Elections::submit_candidacy(Origin::signed(1), 0));
		assert_eq!(Elections::candidates(), vec![1]);
		assert_eq!(Elections::candidate_reg_info(1), Some((0, 0)));
		assert_eq!(Elections::candidate_reg_info(2), None);
		assert_eq!(Elections::is_a_candidate(&1), true);
		assert_eq!(Elections::is_a_candidate(&2), false);

		assert_ok!(Elections::submit_candidacy(Origin::signed(2), 1));
		assert_eq!(Elections::candidates(), vec![1, 2]);
		assert_eq!(Elections::candidate_reg_info(1), Some((0, 0)));
		assert_eq!(Elections::candidate_reg_info(2), Some((0, 1)));
		assert_eq!(Elections::is_a_candidate(&1), true);
		assert_eq!(Elections::is_a_candidate(&2), true);
	});
}

#[test]
fn candidacy_submission_using_free_slot_should_work() {
	let mut t = new_test_ext_with_candidate_holes();

	t.execute_with(|| {
		assert_eq!(Elections::candidates(), vec![0, 0, 1]);

		assert_ok!(Elections::submit_candidacy(Origin::signed(2), 1));
		assert_eq!(Elections::candidates(), vec![0, 2, 1]);

		assert_ok!(Elections::submit_candidacy(Origin::signed(3), 0));
		assert_eq!(Elections::candidates(), vec![3, 2, 1]);
	});
}

#[test]
fn candidacy_submission_using_alternative_free_slot_should_work() {
	let mut t = new_test_ext_with_candidate_holes();

	t.execute_with(|| {
		assert_eq!(Elections::candidates(), vec![0, 0, 1]);

		assert_ok!(Elections::submit_candidacy(Origin::signed(2), 0));
		assert_eq!(Elections::candidates(), vec![2, 0, 1]);

		assert_ok!(Elections::submit_candidacy(Origin::signed(3), 1));
		assert_eq!(Elections::candidates(), vec![2, 3, 1]);
	});
}

#[test]
fn candidacy_submission_not_using_free_slot_should_not_work() {
	let mut t = new_test_ext_with_candidate_holes();

	t.execute_with(|| {
		assert_noop!(
			Elections::submit_candidacy(Origin::signed(4), 3),
			Error::<Test>::InvalidCandidateSlot
		);
	});
}

#[test]
fn candidacy_bad_candidate_slot_submission_should_not_work() {
	ExtBuilder::default().build().execute_with(|| {
		assert_eq!(Elections::candidates(), Vec::<u64>::new());
		assert_noop!(
			Elections::submit_candidacy(Origin::signed(1), 1),
			Error::<Test>::InvalidCandidateSlot
		);
	});
}

#[test]
fn candidacy_non_free_candidate_slot_submission_should_not_work() {
	ExtBuilder::default().build().execute_with(|| {
		assert_eq!(Elections::candidates(), Vec::<u64>::new());
		assert_ok!(Elections::submit_candidacy(Origin::signed(1), 0));
		assert_eq!(Elections::candidates(), vec![1]);
		assert_noop!(
			Elections::submit_candidacy(Origin::signed(2), 0),
			Error::<Test>::InvalidCandidateSlot
		);
	});
}

#[test]
fn candidacy_dupe_candidate_submission_should_not_work() {
	ExtBuilder::default().build().execute_with(|| {
		assert_eq!(Elections::candidates(), Vec::<u64>::new());
		assert_ok!(Elections::submit_candidacy(Origin::signed(1), 0));
		assert_eq!(Elections::candidates(), vec![1]);
		assert_noop!(
			Elections::submit_candidacy(Origin::signed(1), 1),
			Error::<Test>::DuplicatedCandidate,
		);
	});
}

#[test]
fn candidacy_poor_candidate_submission_should_not_work() {
	ExtBuilder::default().build().execute_with(|| {
		assert_eq!(Elections::candidates(), Vec::<u64>::new());
		assert_noop!(
			Elections::submit_candidacy(Origin::signed(7), 0),
			Error::<Test>::InsufficientCandidateFunds,
		);
	});
}

#[test]
fn election_voting_should_work() {
	ExtBuilder::default().build().execute_with(|| {
		assert_ok!(Elections::submit_candidacy(Origin::signed(5), 0));

		assert_ok!(Elections::set_approvals(Origin::signed(1), vec![true], 0, 0, 10));
		assert_ok!(Elections::set_approvals(Origin::signed(4), vec![true], 0, 1, 40));

		assert_eq!(Elections::all_approvals_of(&1), vec![true]);
		assert_eq!(Elections::all_approvals_of(&4), vec![true]);
		assert_eq!(voter_ids(), vec![1, 4]);

		assert_ok!(Elections::submit_candidacy(Origin::signed(2), 1));
		assert_ok!(Elections::submit_candidacy(Origin::signed(3), 2));

		assert_ok!(Elections::set_approvals(Origin::signed(2), vec![false, true, true], 0, 2, 20));
		assert_ok!(Elections::set_approvals(Origin::signed(3), vec![false, true, true], 0, 3, 30));

		assert_eq!(Elections::all_approvals_of(&1), vec![true]);
		assert_eq!(Elections::all_approvals_of(&4), vec![true]);
		assert_eq!(Elections::all_approvals_of(&2), vec![false, true, true]);
		assert_eq!(Elections::all_approvals_of(&3), vec![false, true, true]);

		assert_eq!(voter_ids(), vec![1, 4, 2, 3]);
	});
}

#[test]
fn election_proxy_voting_should_work() {
	ExtBuilder::default().build().execute_with(|| {
		assert_ok!(Elections::submit_candidacy(Origin::signed(5), 0));

		<Proxy<Test>>::insert(11, 1);
		<Proxy<Test>>::insert(12, 2);
		<Proxy<Test>>::insert(13, 3);
		<Proxy<Test>>::insert(14, 4);
		assert_ok!(
			Elections::proxy_set_approvals(Origin::signed(11), vec![true], 0, 0, 10)
		);
		assert_ok!(
			Elections::proxy_set_approvals(Origin::signed(14), vec![true], 0, 1, 40)
		);

		assert_eq!(Elections::all_approvals_of(&1), vec![true]);
		assert_eq!(Elections::all_approvals_of(&4), vec![true]);
		assert_eq!(voter_ids(), vec![1, 4]);

		assert_ok!(Elections::submit_candidacy(Origin::signed(2), 1));
		assert_ok!(Elections::submit_candidacy(Origin::signed(3), 2));

		assert_ok!(
			Elections::proxy_set_approvals(Origin::signed(12), vec![false, true], 0, 2, 20)
		);
		assert_ok!(
			Elections::proxy_set_approvals(Origin::signed(13), vec![false, true], 0, 3, 30)
		);

		assert_eq!(Elections::all_approvals_of(&1), vec![true]);
		assert_eq!(Elections::all_approvals_of(&4), vec![true]);
		assert_eq!(Elections::all_approvals_of(&2), vec![false, true]);
		assert_eq!(Elections::all_approvals_of(&3), vec![false, true]);

		assert_eq!(voter_ids(), vec![1, 4, 2, 3]);
	});
}

#[test]
fn election_simple_tally_should_work() {
	ExtBuilder::default().build().execute_with(|| {
		System::set_block_number(4);
		assert!(!Elections::presentation_active());

		assert_ok!(Elections::submit_candidacy(Origin::signed(2), 0));
		assert_ok!(Elections::submit_candidacy(Origin::signed(5), 1));
		assert_ok!(Elections::set_approvals(Origin::signed(2), vec![true], 0, 0, 20));
		assert_ok!(Elections::set_approvals(Origin::signed(5), vec![false, true], 0, 0, 50));
		assert_eq!(voter_ids(), vec![2, 5]);
		assert_eq!(Elections::all_approvals_of(&2), vec![true]);
		assert_eq!(Elections::all_approvals_of(&5), vec![false, true]);
		assert_ok!(Elections::end_block(System::block_number()));

		System::set_block_number(6);
		assert!(Elections::presentation_active());
		assert_eq!(Elections::present_winner(Origin::signed(4), 2, 20, 0), Ok(()));
		assert_eq!(Elections::present_winner(Origin::signed(4), 5, 50, 0), Ok(()));
		assert_eq!(Elections::leaderboard(), Some(vec![(0, 0), (0, 0), (20, 2), (50, 5)]));
		assert_ok!(Elections::end_block(System::block_number()));

		assert!(!Elections::presentation_active());
		assert_eq!(Elections::members(), vec![(5, 11), (2, 11)]);

		assert!(!Elections::is_a_candidate(&2));
		assert!(!Elections::is_a_candidate(&5));
		assert_eq!(Elections::vote_index(), 1);
		assert_eq!(
			Elections::voter_info(2),
			Some(VoterInfo { last_win: 1, last_active: 0, stake: 20, pot: 0 })
		);
		assert_eq!(
			Elections::voter_info(5),
			Some(VoterInfo { last_win: 1, last_active: 0, stake: 50, pot: 0 })
		);
	});
}

#[test]
fn election_seats_should_be_released() {
	ExtBuilder::default().build().execute_with(|| {
		System::set_block_number(4);
		assert_ok!(Elections::submit_candidacy(Origin::signed(2), 0));
		assert_ok!(Elections::submit_candidacy(Origin::signed(5), 1));
		assert_ok!(Elections::set_approvals(Origin::signed(2), vec![true, false], 0, 0, 20));
		assert_ok!(Elections::set_approvals(Origin::signed(5), vec![false, true], 0, 0, 50));
		assert_ok!(Elections::end_block(System::block_number()));

		System::set_block_number(6);
		assert!(Elections::presentation_active());
		assert_eq!(Elections::present_winner(Origin::signed(4), 2, 20, 0), Ok(()));
		assert_eq!(Elections::present_winner(Origin::signed(4), 5, 50, 0), Ok(()));
		assert_eq!(Elections::leaderboard(), Some(vec![(0, 0), (0, 0), (20, 2), (50, 5)]));
		assert_ok!(Elections::end_block(System::block_number()));

		assert_eq!(Elections::members(), vec![(5, 11), (2, 11)]);
		let mut current = System::block_number();
		let free_block;
		loop {
			current += 1;
			System::set_block_number(current);
			assert_ok!(Elections::end_block(System::block_number()));
			if Elections::members().len() == 0 {
				free_block = current;
				break;
			}
		}
		// 11 + 2 which is the next voting period.
		assert_eq!(free_block, 14);
	});
}

#[test]
fn election_presentations_with_zero_staked_deposit_should_not_work() {
	ExtBuilder::default().build().execute_with(|| {
		System::set_block_number(4);
		assert_ok!(Elections::submit_candidacy(Origin::signed(2), 0));
		assert_ok!(Elections::set_approvals(Origin::signed(2), vec![true], 0, 0, 20));
		assert_ok!(Elections::end_block(System::block_number()));

		System::set_block_number(6);
		assert_noop!(
			Elections::present_winner(Origin::signed(4), 2, 0, 0),
			Error::<Test>::ZeroDeposit,
		);
	});
}

#[test]
fn election_double_presentations_should_be_punished() {
	ExtBuilder::default().build().execute_with(|| {
		assert!(Balances::can_slash(&4, 10));

		System::set_block_number(4);
		assert_ok!(Elections::submit_candidacy(Origin::signed(2), 0));
		assert_ok!(Elections::submit_candidacy(Origin::signed(5), 1));
		assert_ok!(Elections::set_approvals(Origin::signed(2), vec![true, false], 0, 0, 20));
		assert_ok!(Elections::set_approvals(Origin::signed(5), vec![false, true], 0, 0, 50));
		assert_ok!(Elections::end_block(System::block_number()));

		System::set_block_number(6);
		assert_ok!(Elections::present_winner(Origin::signed(4), 2, 20, 0));
		assert_ok!(Elections::present_winner(Origin::signed(4), 5, 50, 0));
		assert_eq!(
			Elections::present_winner(Origin::signed(4), 5, 50, 0),
			Err(Error::<Test>::DuplicatedPresentation.into()),
		);
		assert_ok!(Elections::end_block(System::block_number()));

		assert_eq!(Elections::members(), vec![(5, 11), (2, 11)]);
		assert_eq!(Balances::total_balance(&4), 38);
	});
}

#[test]
fn election_presenting_for_double_election_should_not_work() {
	ExtBuilder::default().build().execute_with(|| {
		System::set_block_number(4);
		assert_eq!(Elections::submit_candidacy(Origin::signed(2), 0), Ok(()));
		assert_ok!(Elections::set_approvals(Origin::signed(2), vec![true], 0, 0, 20));
		assert_ok!(Elections::end_block(System::block_number()));

		System::set_block_number(6);
		assert_ok!(Elections::present_winner(Origin::signed(4), 2, 20, 0));
		assert_ok!(Elections::end_block(System::block_number()));

		System::set_block_number(8);
		// NOTE: This is now mandatory to disable the lock
		assert_ok!(Elections::retract_voter(Origin::signed(2), 0));
		assert_eq!(Elections::submit_candidacy(Origin::signed(2), 0), Ok(()));
		assert_ok!(Elections::set_approvals(Origin::signed(2), vec![true], 1, 0, 20));
		assert_ok!(Elections::end_block(System::block_number()));

		System::set_block_number(10);
		assert_noop!(
			Elections::present_winner(Origin::signed(4), 2, 20, 1),
			Error::<Test>::DuplicatedCandidate,
		);
	});
}

#[test]
fn election_presenting_loser_should_not_work() {
	ExtBuilder::default().build().execute_with(|| {
		System::set_block_number(4);
		assert_ok!(Elections::submit_candidacy(Origin::signed(1), 0));
		assert_ok!(Elections::set_approvals(Origin::signed(6), vec![true], 0, 0, 60));
		assert_ok!(Elections::submit_candidacy(Origin::signed(2), 1));
		assert_ok!(Elections::set_approvals(Origin::signed(2), vec![false, true], 0, 0, 20));
		assert_ok!(Elections::submit_candidacy(Origin::signed(3), 2));
		assert_ok!(Elections::set_approvals(Origin::signed(3), vec![false, false, true], 0, 0, 30));
		assert_ok!(Elections::submit_candidacy(Origin::signed(4), 3));
		assert_ok!(Elections::set_approvals(Origin::signed(4), vec![false, false, false, true], 0, 0, 40));
		assert_ok!(Elections::submit_candidacy(Origin::signed(5), 4));
		assert_ok!(Elections::set_approvals(Origin::signed(5), vec![false, false, false, false, true], 0, 0, 50));
		assert_ok!(Elections::end_block(System::block_number()));

		System::set_block_number(6);
		assert_ok!(Elections::present_winner(Origin::signed(4), 1, 60, 0));
		assert_ok!(Elections::present_winner(Origin::signed(4), 3, 30, 0));
		assert_ok!(Elections::present_winner(Origin::signed(4), 4, 40, 0));
		assert_ok!(Elections::present_winner(Origin::signed(4), 5, 50, 0));

		assert_eq!(Elections::leaderboard(), Some(vec![
			(30, 3),
			(40, 4),
			(50, 5),
			(60, 1)
		]));

		assert_noop!(Elections::present_winner(Origin::signed(4), 2, 20, 0), Error::<Test>::UnworthyCandidate);
	});
}

#[test]
fn election_presenting_loser_first_should_not_matter() {
	ExtBuilder::default().build().execute_with(|| {
		System::set_block_number(4);
		assert_ok!(Elections::submit_candidacy(Origin::signed(1), 0));
		assert_ok!(Elections::set_approvals(Origin::signed(6), vec![true], 0, 0, 60));
		assert_ok!(Elections::submit_candidacy(Origin::signed(2), 1));
		assert_ok!(Elections::set_approvals(Origin::signed(2), vec![false, true], 0, 0, 20));
		assert_ok!(Elections::submit_candidacy(Origin::signed(3), 2));
		assert_ok!(Elections::set_approvals(Origin::signed(3), vec![false, false, true], 0, 0, 30));
		assert_ok!(Elections::submit_candidacy(Origin::signed(4), 3));
		assert_ok!(Elections::set_approvals(Origin::signed(4), vec![false, false, false, true], 0, 0, 40));
		assert_ok!(Elections::submit_candidacy(Origin::signed(5), 4));
		assert_ok!(Elections::set_approvals(Origin::signed(5), vec![false, false, false, false, true], 0, 0, 50));
		assert_ok!(Elections::end_block(System::block_number()));

		System::set_block_number(6);
		assert_ok!(Elections::present_winner(Origin::signed(4), 2, 20, 0));
		assert_ok!(Elections::present_winner(Origin::signed(4), 1, 60, 0));
		assert_ok!(Elections::present_winner(Origin::signed(4), 3, 30, 0));
		assert_ok!(Elections::present_winner(Origin::signed(4), 4, 40, 0));
		assert_ok!(Elections::present_winner(Origin::signed(4), 5, 50, 0));

		assert_eq!(Elections::leaderboard(), Some(vec![
			(30, 3),
			(40, 4),
			(50, 5),
			(60, 1)
		]));
	});
}

#[test]
fn election_present_outside_of_presentation_period_should_not_work() {
	ExtBuilder::default().build().execute_with(|| {
		System::set_block_number(4);
		assert!(!Elections::presentation_active());
		assert_noop!(
			Elections::present_winner(Origin::signed(5), 5, 1, 0),
			Error::<Test>::NotPresentationPeriod,
		);
	});
}

#[test]
fn election_present_with_invalid_vote_index_should_not_work() {
	ExtBuilder::default().build().execute_with(|| {
		System::set_block_number(4);
		assert_ok!(Elections::submit_candidacy(Origin::signed(2), 0));
		assert_ok!(Elections::submit_candidacy(Origin::signed(5), 1));
		assert_ok!(Elections::set_approvals(Origin::signed(2), vec![true, false], 0, 0, 20));
		assert_ok!(Elections::set_approvals(Origin::signed(5), vec![false, true], 0, 0, 50));
		assert_ok!(Elections::end_block(System::block_number()));

		System::set_block_number(6);
		assert_noop!(Elections::present_winner(Origin::signed(4), 2, 20, 1), Error::<Test>::InvalidVoteIndex);
	});
}

#[test]
fn election_present_when_presenter_is_poor_should_not_work() {
	let test_present = |p| {
		ExtBuilder::default()
			.voting_fee(5)
			.voter_bond(2)
			.bad_presentation_punishment(p)
			.build()
			.execute_with(|| {
				System::set_block_number(4);
				let _ = Balances::make_free_balance_be(&1, 15);
				assert!(!Elections::presentation_active());

 				// -3
				assert_ok!(Elections::submit_candidacy(Origin::signed(1), 0));
				assert_eq!(Balances::free_balance(1), 12);
 				// -2 -5
				assert_ok!(Elections::set_approvals(Origin::signed(1), vec![true], 0, 0, 15));
				assert_ok!(Elections::end_block(System::block_number()));

				System::set_block_number(6);
				assert_eq!(Balances::free_balance(1), 5);
				assert_eq!(Balances::reserved_balance(1), 5);
				if p > 5 {
					assert_noop!(Elections::present_winner(
						Origin::signed(1), 1, 10, 0),
						Error::<Test>::InsufficientPresenterFunds,
					);
				} else {
					assert_ok!(Elections::present_winner(Origin::signed(1), 1, 10, 0));
				}
			});
	};
	test_present(4);
	test_present(6);
}

#[test]
fn election_invalid_present_tally_should_slash() {
	ExtBuilder::default().build().execute_with(|| {
		System::set_block_number(4);
		assert!(!Elections::presentation_active());
		assert_eq!(Balances::total_balance(&4), 40);

		assert_ok!(Elections::submit_candidacy(Origin::signed(2), 0));
		assert_ok!(Elections::submit_candidacy(Origin::signed(5), 1));
		assert_ok!(Elections::set_approvals(Origin::signed(2), vec![true, false], 0, 0, 20));
		assert_ok!(Elections::set_approvals(Origin::signed(5), vec![false, true], 0, 0, 50));
		assert_ok!(Elections::end_block(System::block_number()));

		System::set_block_number(6);
		assert_err!(Elections::present_winner(Origin::signed(4), 2, 80, 0), Error::<Test>::IncorrectTotal);

		assert_eq!(Balances::total_balance(&4), 38);
	});
}

#[test]
fn election_runners_up_should_be_kept() {
	ExtBuilder::default().build().execute_with(|| {
		System::set_block_number(4);
		assert!(!Elections::presentation_active());

		assert_ok!(Elections::submit_candidacy(Origin::signed(1), 0));
		assert_ok!(Elections::set_approvals(Origin::signed(6), vec![true], 0, 0, 60));
		assert_ok!(Elections::submit_candidacy(Origin::signed(2), 1));
		assert_ok!(Elections::set_approvals(Origin::signed(2), vec![false, true], 0, 0, 20));
		assert_ok!(Elections::submit_candidacy(Origin::signed(3), 2));
		assert_ok!(Elections::set_approvals(Origin::signed(3), vec![false, false, true], 0, 0, 30));
		assert_ok!(Elections::submit_candidacy(Origin::signed(4), 3));
		assert_ok!(Elections::set_approvals(Origin::signed(4), vec![false, false, false, true], 0, 0, 40));
		assert_ok!(Elections::submit_candidacy(Origin::signed(5), 4));
		assert_ok!(Elections::set_approvals(Origin::signed(5), vec![false, false, false, false, true], 0, 0, 50));

		assert_ok!(Elections::end_block(System::block_number()));

		System::set_block_number(6);
		assert!(Elections::presentation_active());
		assert_ok!(Elections::present_winner(Origin::signed(4), 1, 60, 0));
		// leaderboard length is the empty seats plus the carry count (i.e. 5 + 2), where those
		// to be carried are the lowest and stored in lowest indices
		assert_eq!(Elections::leaderboard(), Some(vec![
			(0, 0),
			(0, 0),
			(0, 0),
			(60, 1)
		]));
		assert_ok!(Elections::present_winner(Origin::signed(4), 3, 30, 0));
		assert_ok!(Elections::present_winner(Origin::signed(4), 4, 40, 0));
		assert_ok!(Elections::present_winner(Origin::signed(4), 5, 50, 0));
		assert_eq!(Elections::leaderboard(), Some(vec![
			(30, 3),
			(40, 4),
			(50, 5),
			(60, 1)
		]));

		assert_ok!(Elections::end_block(System::block_number()));

		assert!(!Elections::presentation_active());
		assert_eq!(Elections::members(), vec![(1, 11), (5, 11)]);

		assert!(!Elections::is_a_candidate(&1));
		assert!(!Elections::is_a_candidate(&5));
		assert!(!Elections::is_a_candidate(&2));
		assert!(Elections::is_a_candidate(&3));
		assert!(Elections::is_a_candidate(&4));
		assert_eq!(Elections::vote_index(), 1);
		assert_eq!(Elections::voter_info(2), Some(VoterInfo { last_win: 0, last_active: 0, stake: 20, pot: 0 }));
		assert_eq!(Elections::voter_info(3), Some(VoterInfo { last_win: 0, last_active: 0, stake: 30, pot: 0 }));
		assert_eq!(Elections::voter_info(4), Some(VoterInfo { last_win: 0, last_active: 0, stake: 40, pot: 0 }));
		assert_eq!(Elections::voter_info(5), Some(VoterInfo { last_win: 1, last_active: 0, stake: 50, pot: 0 }));
		assert_eq!(Elections::voter_info(6), Some(VoterInfo { last_win: 1, last_active: 0, stake: 60, pot: 0 }));
		assert_eq!(Elections::candidate_reg_info(3), Some((0, 2)));
		assert_eq!(Elections::candidate_reg_info(4), Some((0, 3)));
	});
}

#[test]
fn election_second_tally_should_use_runners_up() {
	ExtBuilder::default().build().execute_with(|| {
		System::set_block_number(4);
		assert_ok!(Elections::submit_candidacy(Origin::signed(1), 0));
		assert_ok!(Elections::set_approvals(Origin::signed(6), vec![true], 0, 0, 60));
		assert_ok!(Elections::submit_candidacy(Origin::signed(2), 1));
		assert_ok!(Elections::set_approvals(Origin::signed(2), vec![false, true], 0, 0, 20));
		assert_ok!(Elections::submit_candidacy(Origin::signed(3), 2));
		assert_ok!(Elections::set_approvals(Origin::signed(3), vec![false, false, true], 0, 0, 30));
		assert_ok!(Elections::submit_candidacy(Origin::signed(4), 3));
		assert_ok!(Elections::set_approvals(Origin::signed(4), vec![false, false, false, true], 0, 0, 40));
		assert_ok!(Elections::submit_candidacy(Origin::signed(5), 4));
		assert_ok!(Elections::set_approvals(Origin::signed(5), vec![false, false, false, false, true], 0, 0, 50));
		assert_ok!(Elections::end_block(System::block_number()));

		System::set_block_number(6);
		assert_ok!(Elections::present_winner(Origin::signed(4), 1, 60, 0));
		assert_ok!(Elections::present_winner(Origin::signed(4), 3, 30, 0));
		assert_ok!(Elections::present_winner(Origin::signed(4), 4, 40, 0));
		assert_ok!(Elections::present_winner(Origin::signed(4), 5, 50, 0));
		assert_ok!(Elections::end_block(System::block_number()));

		System::set_block_number(8);
		assert_ok!(Elections::set_approvals(Origin::signed(6), vec![false, false, true, false], 1, 0, 60));
		assert_ok!(Elections::set_desired_seats(Origin::ROOT, 3));
		assert_ok!(Elections::end_block(System::block_number()));

		System::set_block_number(10);
		assert_ok!(Elections::present_winner(Origin::signed(4), 3, 30 + Elections::get_offset(30, 1) + 60, 1));
		assert_ok!(Elections::present_winner(Origin::signed(4), 4, 40 + Elections::get_offset(40, 1), 1));
		assert_ok!(Elections::end_block(System::block_number()));

		assert!(!Elections::presentation_active());
		assert_eq!(Elections::members(), vec![(1, 11), (5, 11), (3, 15)]);

		assert!(!Elections::is_a_candidate(&1));
		assert!(!Elections::is_a_candidate(&2));
		assert!(!Elections::is_a_candidate(&3));
		assert!(!Elections::is_a_candidate(&5));
		assert!(Elections::is_a_candidate(&4));
		assert_eq!(Elections::vote_index(), 2);
		assert_eq!(Elections::voter_info(2), Some( VoterInfo { last_win: 0, last_active: 0, stake: 20, pot: 0}));
		assert_eq!(Elections::voter_info(3), Some( VoterInfo { last_win: 2, last_active: 0, stake: 30, pot: 0}));
		assert_eq!(Elections::voter_info(4), Some( VoterInfo { last_win: 0, last_active: 0, stake: 40, pot: 0}));
		assert_eq!(Elections::voter_info(5), Some( VoterInfo { last_win: 1, last_active: 0, stake: 50, pot: 0}));
		assert_eq!(
			Elections::voter_info(6),
			Some(VoterInfo { last_win: 2, last_active: 1, stake: 60, pot: 0})
		);

		assert_eq!(Elections::candidate_reg_info(4), Some((0, 3)));
	});
}

#[test]
fn election_loser_candidates_bond_gets_slashed() {
	ExtBuilder::default().desired_seats(1).build().execute_with(|| {
		System::set_block_number(4);
		assert!(!Elections::presentation_active());

		assert_ok!(Elections::submit_candidacy(Origin::signed(1), 0));
		assert_ok!(Elections::submit_candidacy(Origin::signed(2), 1));
		assert_ok!(Elections::submit_candidacy(Origin::signed(3), 2));
		assert_ok!(Elections::submit_candidacy(Origin::signed(4), 3));

		assert_eq!(balances(&2), (17, 3));

		assert_ok!(Elections::set_approvals(Origin::signed(5), vec![true], 0, 0, 50));
		assert_ok!(
			Elections::set_approvals(Origin::signed(1), vec![false, true, true, true], 0, 0, 10)
		);

		assert_ok!(Elections::end_block(System::block_number()));

		System::set_block_number(6);
		assert!(Elections::presentation_active());
		assert_eq!(Elections::present_winner(Origin::signed(4), 4, 10, 0), Ok(()));
		assert_eq!(Elections::present_winner(Origin::signed(3), 3, 10, 0), Ok(()));
		assert_eq!(Elections::present_winner(Origin::signed(2), 2, 10, 0), Ok(()));
		assert_eq!(Elections::present_winner(Origin::signed(1), 1, 50, 0), Ok(()));


		// winner + carry
		assert_eq!(Elections::leaderboard(), Some(vec![(10, 3), (10, 4), (50, 1)]));
		assert_ok!(Elections::end_block(System::block_number()));
		assert!(!Elections::presentation_active());
		assert_eq!(Elections::members(), vec![(1, 11)]);

		// account 2 is not a runner up or in leaderboard.
		assert_eq!(balances(&2), (17, 0));
	});
}

#[test]
fn pot_accumulating_weight_and_decaying_should_work() {
	ExtBuilder::default().balance_factor(10).build().execute_with(|| {
		System::set_block_number(4);
		assert!(!Elections::presentation_active());

		assert_ok!(Elections::submit_candidacy(Origin::signed(6), 0));
		assert_ok!(Elections::submit_candidacy(Origin::signed(5), 1));
		assert_ok!(Elections::submit_candidacy(Origin::signed(1), 2));

		assert_ok!(
			Elections::set_approvals(Origin::signed(6), vec![true, false, false], 0, 0, 600)
		);
		assert_ok!(
			Elections::set_approvals(Origin::signed(5), vec![false, true, false], 0, 0, 500)
		);
		assert_ok!(
			Elections::set_approvals(Origin::signed(1), vec![false, false, true], 0, 0, 100)
		);

		assert_ok!(Elections::end_block(System::block_number()));

		System::set_block_number(6);
		assert!(Elections::presentation_active());

		assert_eq!(Elections::present_winner(Origin::signed(6), 6, 600, 0), Ok(()));
		assert_eq!(Elections::present_winner(Origin::signed(5), 5, 500, 0), Ok(()));
		assert_eq!(Elections::present_winner(Origin::signed(1), 1, 100, 0), Ok(()));
		assert_eq!(Elections::leaderboard(), Some(vec![(0, 0), (100, 1), (500, 5), (600, 6)]));
		assert_ok!(Elections::end_block(System::block_number()));

		assert_eq!(Elections::members(), vec![(6, 11), (5, 11)]);
		assert_eq!(
			Elections::voter_info(6).unwrap(),
			VoterInfo { last_win: 1, last_active: 0, stake: 600, pot: 0},
		);
		assert_eq!(
			Elections::voter_info(5).unwrap(),
			VoterInfo { last_win: 1, last_active: 0, stake: 500, pot: 0},
		);
		assert_eq!(
			Elections::voter_info(1).unwrap(),
			VoterInfo { last_win: 0, last_active: 0, stake: 100, pot: 0},
		);

		System::set_block_number(12);
		// retract needed to unlock approval funds => submit candidacy again.
		assert_ok!(Elections::retract_voter(Origin::signed(6), 0));
		assert_ok!(Elections::retract_voter(Origin::signed(5), 1));
		assert_ok!(Elections::submit_candidacy(Origin::signed(6), 0));
		assert_ok!(Elections::submit_candidacy(Origin::signed(5), 1));
		assert_ok!(
			Elections::set_approvals(Origin::signed(6), vec![true, false, false], 1, 0, 600)
		);
		assert_ok!(
			Elections::set_approvals(Origin::signed(5), vec![false, true, false], 1, 1, 500)
		);
		assert_ok!(Elections::end_block(System::block_number()));

		System::set_block_number(14);
		assert!(Elections::presentation_active());
		assert_eq!(Elections::present_winner(Origin::signed(6), 6, 600, 1), Ok(()));
		assert_eq!(Elections::present_winner(Origin::signed(5), 5, 500, 1), Ok(()));
		assert_eq!(Elections::present_winner(Origin::signed(1), 1, 100 + Elections::get_offset(100, 1), 1), Ok(()));
		assert_eq!(Elections::leaderboard(), Some(vec![(0, 0), (100 + 96, 1), (500, 5), (600, 6)]));
		assert_ok!(Elections::end_block(System::block_number()));

		assert_eq!(Elections::members(), vec![(6, 19), (5, 19)]);
		assert_eq!(
			Elections::voter_info(6).unwrap(),
			VoterInfo { last_win: 2, last_active: 1, stake: 600, pot:0 }
		);
		assert_eq!(Elections::voter_info(5).unwrap(), VoterInfo { last_win: 2, last_active: 1, stake: 500, pot:0 });
		assert_eq!(Elections::voter_info(1).unwrap(), VoterInfo { last_win: 0, last_active: 0, stake: 100, pot:0 });

		System::set_block_number(20);
		assert_ok!(Elections::retract_voter(Origin::signed(6), 0));
		assert_ok!(Elections::retract_voter(Origin::signed(5), 1));
		assert_ok!(Elections::submit_candidacy(Origin::signed(6), 0));
		assert_ok!(Elections::submit_candidacy(Origin::signed(5), 1));
		assert_ok!(Elections::set_approvals(Origin::signed(6), vec![true, false, false], 2, 0, 600));
		assert_ok!(Elections::set_approvals(Origin::signed(5), vec![false, true, false], 2, 1, 500));
		assert_ok!(Elections::end_block(System::block_number()));

		System::set_block_number(22);
		assert!(Elections::presentation_active());
		assert_eq!(Elections::present_winner(Origin::signed(6), 6, 600, 2), Ok(()));
		assert_eq!(Elections::present_winner(Origin::signed(5), 5, 500, 2), Ok(()));
		assert_eq!(Elections::present_winner(Origin::signed(1), 1, 100 + Elections::get_offset(100, 2), 2), Ok(()));
		assert_eq!(Elections::leaderboard(), Some(vec![(0, 0), (100 + 96 + 93, 1), (500, 5), (600, 6)]));
		assert_ok!(Elections::end_block(System::block_number()));

		assert_eq!(Elections::members(), vec![(6, 27), (5, 27)]);
		assert_eq!(
			Elections::voter_info(6).unwrap(),
			VoterInfo { last_win: 3, last_active: 2, stake: 600, pot: 0}
		);
		assert_eq!(Elections::voter_info(5).unwrap(), VoterInfo { last_win: 3, last_active: 2, stake: 500, pot: 0});
		assert_eq!(Elections::voter_info(1).unwrap(), VoterInfo { last_win: 0, last_active: 0, stake: 100, pot: 0});


		System::set_block_number(28);
		assert_ok!(Elections::retract_voter(Origin::signed(6), 0));
		assert_ok!(Elections::retract_voter(Origin::signed(5), 1));
		assert_ok!(Elections::submit_candidacy(Origin::signed(6), 0));
		assert_ok!(Elections::submit_candidacy(Origin::signed(5), 1));
		assert_ok!(Elections::set_approvals(Origin::signed(6), vec![true, false, false], 3, 0, 600));
		assert_ok!(Elections::set_approvals(Origin::signed(5), vec![false, true, false], 3, 1, 500));
		assert_ok!(Elections::end_block(System::block_number()));

		System::set_block_number(30);
		assert!(Elections::presentation_active());
		assert_eq!(Elections::present_winner(Origin::signed(6), 6, 600, 3), Ok(()));
		assert_eq!(Elections::present_winner(Origin::signed(5), 5, 500, 3), Ok(()));
		assert_eq!(Elections::present_winner(Origin::signed(1), 1, 100 + Elections::get_offset(100, 3), 3), Ok(()));
		assert_eq!(Elections::leaderboard(), Some(vec![(0, 0), (100 + 96 + 93 + 90, 1), (500, 5), (600, 6)]));
		assert_ok!(Elections::end_block(System::block_number()));

		assert_eq!(Elections::members(), vec![(6, 35), (5, 35)]);
		assert_eq!(
			Elections::voter_info(6).unwrap(),
			VoterInfo { last_win: 4, last_active: 3, stake: 600, pot: 0}
		);
		assert_eq!(Elections::voter_info(5).unwrap(), VoterInfo { last_win: 4, last_active: 3, stake: 500, pot: 0});
		assert_eq!(Elections::voter_info(1).unwrap(), VoterInfo { last_win: 0, last_active: 0, stake: 100, pot: 0});
	})
}

#[test]
fn pot_winning_resets_accumulated_pot() {
	ExtBuilder::default().balance_factor(10).build().execute_with(|| {
		System::set_block_number(4);
		assert!(!Elections::presentation_active());

		assert_ok!(Elections::submit_candidacy(Origin::signed(6), 0));
		assert_ok!(Elections::submit_candidacy(Origin::signed(4), 1));
		assert_ok!(Elections::submit_candidacy(Origin::signed(3), 2));
		assert_ok!(Elections::submit_candidacy(Origin::signed(2), 3));

		assert_ok!(Elections::set_approvals(Origin::signed(6), vec![true, false, false, false], 0, 0, 600));
		assert_ok!(Elections::set_approvals(Origin::signed(4), vec![false, true, false, false], 0, 1, 400));
		assert_ok!(Elections::set_approvals(Origin::signed(3), vec![false, false, true, true], 0, 2, 300));
		assert_ok!(Elections::end_block(System::block_number()));

		System::set_block_number(6);
		assert!(Elections::presentation_active());
		assert_eq!(Elections::present_winner(Origin::signed(6), 6, 600, 0), Ok(()));
		assert_eq!(Elections::present_winner(Origin::signed(4), 4, 400, 0), Ok(()));
		assert_eq!(Elections::present_winner(Origin::signed(3), 3, 300, 0), Ok(()));
		assert_eq!(Elections::present_winner(Origin::signed(2), 2, 300, 0), Ok(()));
		assert_eq!(Elections::leaderboard(), Some(vec![(300, 2), (300, 3), (400, 4), (600, 6)]));
		assert_ok!(Elections::end_block(System::block_number()));

		assert_eq!(Elections::members(), vec![(6, 11), (4, 11)]);

		System::set_block_number(12);
		assert_ok!(Elections::retract_voter(Origin::signed(6), 0));
		assert_ok!(Elections::retract_voter(Origin::signed(4), 1));
		assert_ok!(Elections::submit_candidacy(Origin::signed(6), 0));
		assert_ok!(Elections::submit_candidacy(Origin::signed(4), 1));
		assert_ok!(Elections::set_approvals(Origin::signed(6), vec![true, false, false, false], 1, 0, 600));
		assert_ok!(Elections::set_approvals(Origin::signed(4), vec![false, true, false, false], 1, 1, 400));
		assert_ok!(Elections::end_block(System::block_number()));

		System::set_block_number(14);
		assert!(Elections::presentation_active());
		assert_eq!(Elections::present_winner(Origin::signed(6), 6, 600, 1), Ok(()));
		assert_eq!(Elections::present_winner(Origin::signed(4), 4, 400, 1), Ok(()));
		assert_eq!(Elections::present_winner(Origin::signed(3), 3, 300 + Elections::get_offset(300, 1), 1), Ok(()));
		assert_eq!(Elections::present_winner(Origin::signed(2), 2, 300 + Elections::get_offset(300, 1), 1), Ok(()));
		assert_eq!(Elections::leaderboard(), Some(vec![(400, 4), (588, 2), (588, 3), (600, 6)]));
		assert_ok!(Elections::end_block(System::block_number()));

		assert_eq!(Elections::members(), vec![(6, 19), (3, 19)]);

		System::set_block_number(20);
		assert_ok!(Elections::end_block(System::block_number()));

		System::set_block_number(22);
		// 2 will not get re-elected with 300 + 288, instead just 300.
		// because one of 3's candidates (3) won in previous round
		// 4 on the other hand will get extra weight since it was unlucky.
		assert_eq!(Elections::present_winner(Origin::signed(3), 2, 300, 2), Ok(()));
		assert_eq!(Elections::present_winner(Origin::signed(4), 4, 400 + Elections::get_offset(400, 1), 2), Ok(()));
		assert_ok!(Elections::end_block(System::block_number()));

		assert_eq!(Elections::members(), vec![(4, 27), (2, 27)]);
	})
}

#[test]
fn pot_resubmitting_approvals_stores_pot() {
	ExtBuilder::default()
		.voter_bond(0)
		.voting_fee(0)
		.balance_factor(10)
		.build()
		.execute_with(|| {
			System::set_block_number(4);
			assert!(!Elections::presentation_active());

			assert_ok!(Elections::submit_candidacy(Origin::signed(6), 0));
			assert_ok!(Elections::submit_candidacy(Origin::signed(5), 1));
			assert_ok!(Elections::submit_candidacy(Origin::signed(1), 2));

			assert_ok!(
				Elections::set_approvals(Origin::signed(6), vec![true, false, false], 0, 0, 600),
			);
			assert_ok!(
				Elections::set_approvals(Origin::signed(5), vec![false, true, false], 0, 1, 500),
			);
			assert_ok!(
				Elections::set_approvals(Origin::signed(1), vec![false, false, true], 0, 2, 100),
			);

			assert_ok!(Elections::end_block(System::block_number()));

			System::set_block_number(6);
			assert!(Elections::presentation_active());

			assert_eq!(Elections::present_winner(Origin::signed(6), 6, 600, 0), Ok(()));
			assert_eq!(Elections::present_winner(Origin::signed(5), 5, 500, 0), Ok(()));
			assert_eq!(Elections::present_winner(Origin::signed(1), 1, 100, 0), Ok(()));
			assert_eq!(Elections::leaderboard(), Some(vec![(0, 0), (100, 1), (500, 5), (600, 6)]));
			assert_ok!(Elections::end_block(System::block_number()));

			assert_eq!(Elections::members(), vec![(6, 11), (5, 11)]);

			System::set_block_number(12);
			assert_ok!(Elections::retract_voter(Origin::signed(6), 0));
			assert_ok!(Elections::retract_voter(Origin::signed(5), 1));
			assert_ok!(Elections::submit_candidacy(Origin::signed(6), 0));
			assert_ok!(Elections::submit_candidacy(Origin::signed(5), 1));
			assert_ok!(
				Elections::set_approvals(Origin::signed(6), vec![true, false, false], 1, 0, 600),
			);
			assert_ok!(
				Elections::set_approvals(Origin::signed(5), vec![false, true, false], 1, 1, 500),
			);
			// give 1 some new high balance
			let _ = Balances::make_free_balance_be(&1, 997);
			assert_ok!(
				Elections::set_approvals(Origin::signed(1), vec![false, false, true], 1, 2, 1000),
			);
			assert_eq!(Elections::voter_info(1).unwrap(),
				VoterInfo {
					stake: 1000, // 997 + 3 which is candidacy bond.
					pot: Elections::get_offset(100, 1),
					last_active: 1,
					last_win: 1,
				}
			);
			assert_ok!(Elections::end_block(System::block_number()));

			assert_eq!(Elections::members(), vec![(6, 11), (5, 11)]);

			System::set_block_number(14);
			assert!(Elections::presentation_active());
			assert_eq!(Elections::present_winner(Origin::signed(6), 6, 600, 1), Ok(()));
			assert_eq!(Elections::present_winner(Origin::signed(5), 5, 500, 1), Ok(()));
			assert_eq!(
				Elections::present_winner(Origin::signed(1), 1, 1000 + 96 /* pot */, 1),
				Ok(()),
			);
			assert_eq!(Elections::leaderboard(), Some(vec![(0, 0), (500, 5), (600, 6), (1096, 1)]));
			assert_ok!(Elections::end_block(System::block_number()));

			assert_eq!(Elections::members(), vec![(1, 19), (6, 19)]);
		})
}

#[test]
fn pot_get_offset_should_work() {
	ExtBuilder::default().build().execute_with(|| {
		assert_eq!(Elections::get_offset(100, 0), 0);
		assert_eq!(Elections::get_offset(100, 1), 96);
		assert_eq!(Elections::get_offset(100, 2), 96 + 93);
		assert_eq!(Elections::get_offset(100, 3), 96 + 93 + 90);
		assert_eq!(Elections::get_offset(100, 4), 96 + 93 + 90 + 87);
		// limit
		assert_eq!(Elections::get_offset(100, 1000), 100 * 24);

		assert_eq!(Elections::get_offset(50_000_000_000, 0), 0);
		assert_eq!(Elections::get_offset(50_000_000_000, 1), 48_000_000_000);
		assert_eq!(Elections::get_offset(50_000_000_000, 2), 48_000_000_000 + 46_080_000_000);
		assert_eq!(Elections::get_offset(50_000_000_000, 3), 48_000_000_000 + 46_080_000_000 + 44_236_800_000);
		assert_eq!(
			Elections::get_offset(50_000_000_000, 4),
			48_000_000_000 + 46_080_000_000 + 44_236_800_000 + 42_467_328_000
		);
		// limit
		assert_eq!(Elections::get_offset(50_000_000_000, 1000), 50_000_000_000 * 24);
	})
}

#[test]
fn pot_get_offset_with_zero_decay() {
	ExtBuilder::default().decay_ratio(0).build().execute_with(|| {
		assert_eq!(Elections::get_offset(100, 0), 0);
		assert_eq!(Elections::get_offset(100, 1), 0);
		assert_eq!(Elections::get_offset(100, 2), 0);
		assert_eq!(Elections::get_offset(100, 3), 0);
		// limit
		assert_eq!(Elections::get_offset(100, 1000), 0);
	})
}
