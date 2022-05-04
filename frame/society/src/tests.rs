// This file is part of Substrate.

// Copyright (C) 2020-2022 Parity Technologies (UK) Ltd.
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

//! Tests for the module.

use super::*;
use mock::*;

use frame_support::{assert_noop, assert_ok};
use sp_core::blake2_256;
use sp_runtime::traits::BadOrigin;

fn next_voting() {
	if let Period::Voting { more, .. } = Society::period() {
		run_to_block(System::block_number() + more);
	}
}

fn conclude_intake(allow_resignation: bool, judge_intake: Option<bool>) {
	next_voting();
	let round = RoundCount::<Test>::get();
	for (who, candidacy) in Candidates::<Test>::iter() {
		if candidacy.tally.clear_approval() {
			assert_ok!(Society::claim_membership(Origin::signed(who)));
			assert_noop!(Society::claim_membership(Origin::signed(who)), Error::<Test>::NotCandidate);
			continue
		}
		if candidacy.tally.clear_rejection() && allow_resignation {
			assert_noop!(Society::claim_membership(Origin::signed(who)), Error::<Test>::NotApproved);
			assert_ok!(Society::resign_candidacy(Origin::signed(who)));
			continue
		}
		if let (Some(founder), Some(approve)) = (Founder::<Test>::get(), judge_intake) {
			if !candidacy.tally.clear_approval() && !approve {
				// can be rejected by founder
				assert_ok!(Society::kick_candidate(Origin::signed(founder), who));
				continue
			}
			if !candidacy.tally.clear_rejection() && approve {
				// can be rejected by founder
				assert_ok!(Society::bestow_membership(Origin::signed(founder), who));
				continue
			}
		}
		if candidacy.tally.clear_rejection() && round > candidacy.round + 1 {
			assert_noop!(Society::claim_membership(Origin::signed(who)), Error::<Test>::NotApproved);
			assert_ok!(Society::drop_candidate(Origin::signed(0), who));
			assert_noop!(Society::drop_candidate(Origin::signed(0), who), Error::<Test>::NotCandidate);
			continue
		}
		if !candidacy.skeptic_struck {
			assert_ok!(Society::punish_skeptic(Origin::signed(who)));
		}
	}
}

fn next_intake() {
	let claim_period: u64 = <Test as Config>::ClaimPeriod::get();
	match Society::period() {
		Period::Voting { more, .. } => run_to_block(System::block_number() + more + claim_period),
		Period::Claim { more, .. } => run_to_block(System::block_number() + more),
	}
}

fn place_members(members: impl AsRef<[u128]>) {
	for who in members.as_ref() {
		assert_ok!(Society::insert_member(who, 0));
	}
}

fn members() -> Vec<u128> {
	let mut r = Members::<Test>::iter_keys().collect::<Vec<_>>();
	r.sort();
	r
}

fn candidacies() -> Vec<(u128, Candidacy<u128, u64>)> {
	let mut r = Candidates::<Test>::iter().collect::<Vec<_>>();
	r.sort_by_key(|x| x.0);
	r
}

fn candidates() -> Vec<u128> {
	let mut r = Candidates::<Test>::iter_keys().collect::<Vec<_>>();
	r.sort();
	r
}

#[test]
fn founding_works() {
	EnvBuilder::new().founded(false).execute(|| {
		// Not set up initially.
		assert_eq!(Founder::<Test>::get(), None);
		assert_eq!(Parameters::<Test>::get(), None);
		assert_eq!(Pot::<Test>::get(), 0);
		// Account 1 is set as the founder origin
		// Account 5 cannot start a society
		assert_noop!(Society::found_society(Origin::signed(5), 20, 100, 10, 2, 25, vec![]), BadOrigin);
		// Account 1 can start a society, where 10 is the founding member
		assert_ok!(Society::found_society(Origin::signed(1), 10, 100, 10, 2, 25, b"be cool".to_vec()));
		// Society members only include 10
		assert_eq!(members(), vec![10]);
		// 10 is the head of the society
		assert_eq!(Head::<Test>::get(), Some(10));
		// ...and also the founder
		assert_eq!(Founder::<Test>::get(), Some(10));
		// 100 members max
		assert_eq!(Parameters::<Test>::get().unwrap().max_members, 100);
		// rules are correct
		assert_eq!(Rules::<Test>::get(), Some(blake2_256(b"be cool").into()));
		// Pot grows after first rotation period
		next_intake();
		assert_eq!(Pot::<Test>::get(), 1000);
		// Cannot start another society
		assert_noop!(
			Society::found_society(Origin::signed(1), 20, 100, 10, 2, 25, vec![]),
			Error::<Test>::AlreadyFounded
		);
	});
}

#[test]
fn unfounding_works() {
	EnvBuilder::new().founded(false).execute(|| {
		// Account 1 sets the founder...
		assert_ok!(Society::found_society(Origin::signed(1), 10, 100, 10, 2, 25, vec![]));
		// Account 2 cannot unfound it as it's not the founder.
		assert_noop!(Society::dissolve(Origin::signed(2)), Error::<Test>::NotFounder);
		// Account 10 can, though.
		assert_ok!(Society::dissolve(Origin::signed(10)));

		// 1 sets the founder to 20 this time
		assert_ok!(Society::found_society(Origin::signed(1), 20, 100, 10, 2, 25, vec![]));
		// Bring in a new member...
		assert_ok!(Society::bid(Origin::signed(10), 0));
		next_intake();
		assert_ok!(Society::vote(Origin::signed(20), 10, true));
		conclude_intake(true, None);

		// Unfounding won't work now, even though it's from 20.
		assert_noop!(Society::dissolve(Origin::signed(20)), Error::<Test>::NotHead);
	});
}

#[test]
fn basic_new_member_works() {
	EnvBuilder::new().execute(|| {
		assert_eq!(Balances::free_balance(20), 50);
		// Bid causes Candidate Deposit to be reserved.
		assert_ok!(Society::bid(Origin::signed(20), 0));
		assert_eq!(Balances::free_balance(20), 25);
		assert_eq!(Balances::reserved_balance(20), 25);
		// Rotate period every 4 blocks
		next_intake();
		// 20 is now a candidate
		assert_eq!(candidacies(), vec![(20, candidacy(1, 0, BidKind::Deposit(25), 0, 0))]);
		// 10 (a member) can vote for the candidate
		assert_ok!(Society::vote(Origin::signed(10), 20, true));
		conclude_intake(true, None);
		// Rotate period every 4 blocks
		next_intake();
		// 20 is now a member of the society
		assert_eq!(members(), vec![10, 20]);
		// Reserved balance is returned
		assert_eq!(Balances::free_balance(20), 50);
		assert_eq!(Balances::reserved_balance(20), 0);
	});
}

#[test]
fn bidding_works() {
	EnvBuilder::new().execute(|| {
		// Users make bids of various amounts
		assert_ok!(Society::bid(Origin::signed(60), 1900));
		assert_ok!(Society::bid(Origin::signed(50), 500));
		assert_ok!(Society::bid(Origin::signed(40), 400));
		assert_ok!(Society::bid(Origin::signed(30), 300));
		// Rotate period
		next_intake();
		// Pot is 1000 after "PeriodSpend"
		assert_eq!(Pot::<Test>::get(), 1000);
		assert_eq!(Balances::free_balance(Society::account_id()), 10_000);
		// Choose smallest bidding users whose total is less than pot
		assert_eq!(
			candidacies(),
			vec![
				(30, candidacy(1, 300, BidKind::Deposit(25), 0, 0)),
				(40, candidacy(1, 400, BidKind::Deposit(25), 0, 0)),
			]
		);
		// A member votes for these candidates to join the society
		assert_ok!(Society::vote(Origin::signed(10), 30, true));
		assert_ok!(Society::vote(Origin::signed(10), 40, true));
		conclude_intake(true, None);
		next_intake();
		// Candidates become members after a period rotation
		assert_eq!(members(), vec![10, 30, 40]);
		// Pot is increased by 1000, but pays out 700 to the members
		assert_eq!(Balances::free_balance(Society::account_id()), 9_300);
		assert_eq!(Pot::<Test>::get(), 1_300);
		// Left over from the original bids is 50 who satisfies the condition of bid less than pot.
		assert_eq!(candidacies(), vec![(50, candidacy(2, 500, BidKind::Deposit(25), 0, 0))]);
		// 40, now a member, can vote for 50
		assert_ok!(Society::vote(Origin::signed(40), 50, true));
		conclude_intake(true, None);
		run_to_block(12);
		// 50 is now a member
		assert_eq!(members(), vec![10, 30, 40, 50]);
		// Pot is increased by 1000, and 500 is paid out. Total payout so far is 1200.
		assert_eq!(Pot::<Test>::get(), 1_800);
		assert_eq!(Balances::free_balance(Society::account_id()), 8_800);
		// No more candidates satisfy the requirements
		assert_eq!(candidacies(), vec![]);
		assert_ok!(Society::defender_vote(Origin::signed(10), true)); // Keep defender around
		// Next period
		run_to_block(16);
		// Same members
		assert_eq!(members(), vec![10, 30, 40, 50]);
		// Pot is increased by 1000 again
		assert_eq!(Pot::<Test>::get(), 2_800);
		// No payouts
		assert_eq!(Balances::free_balance(Society::account_id()), 8_800);
		// Candidate 60 now qualifies based on the increased pot size.
		assert_eq!(candidacies(), vec![(60, candidacy(4, 1900, BidKind::Deposit(25), 0, 0))]);
		// Candidate 60 is voted in.
		assert_ok!(Society::vote(Origin::signed(50), 60, true));
		conclude_intake(true, None);
		run_to_block(20);
		// 60 joins as a member
		assert_eq!(members(), vec![10, 30, 40, 50, 60]);
		// Pay them
		assert_eq!(Pot::<Test>::get(), 1_900);
		assert_eq!(Balances::free_balance(Society::account_id()), 6_900);
	});
}

#[test]
fn unbidding_works() {
	EnvBuilder::new().execute(|| {
		// 20 and 30 make bids
		assert_ok!(Society::bid(Origin::signed(20), 1000));
		assert_ok!(Society::bid(Origin::signed(30), 0));
		// Balances are reserved
		assert_eq!(Balances::free_balance(30), 25);
		assert_eq!(Balances::reserved_balance(30), 25);
		// Can unbid themselves with the right position
		assert_ok!(Society::unbid(Origin::signed(30)));
		assert_noop!(Society::unbid(Origin::signed(30)), Error::<Test>::NotBidder);
		// Balance is returned
		assert_eq!(Balances::free_balance(30), 50);
		assert_eq!(Balances::reserved_balance(30), 0);
		// 20 wins candidacy
		next_intake();
		assert_eq!(candidacies(), vec![(20, candidacy(1, 1000, BidKind::Deposit(25), 0, 0))]);
	});
}

#[test]
fn payout_works() {
	EnvBuilder::new().execute(|| {
		// Original balance of 50
		assert_eq!(Balances::free_balance(20), 50);
		assert_ok!(Society::bid(Origin::signed(20), 1000));
		next_intake();
		assert_ok!(Society::vote(Origin::signed(10), 20, true));
		conclude_intake(true, None);
		// payout not ready
		assert_noop!(Society::payout(Origin::signed(20)), Error::<Test>::NoPayout);
		next_intake();
		// payout should be here
		assert_ok!(Society::payout(Origin::signed(20)));
		assert_eq!(Balances::free_balance(20), 1050);
	});
}

#[test]
fn non_voting_skeptic_is_punished() {
	EnvBuilder::new().execute(|| {
		assert_eq!(Members::<Test>::get(10).unwrap().strikes, 0);
		assert_ok!(Society::bid(Origin::signed(20), 0));
		next_intake();
		assert_eq!(candidacies(), vec![(20, candidacy(1, 0, BidKind::Deposit(25), 0, 0))]);
		conclude_intake(true, None);
		next_intake();
		assert_eq!(members(), vec![10]);
		assert_eq!(Members::<Test>::get(10).unwrap().strikes, 1);
	});
}

#[test]
fn rejecting_skeptic_on_approved_is_punished() {
	EnvBuilder::new().execute(|| {
		place_members([20, 30]);
		assert_ok!(Society::bid(Origin::signed(40), 0));
		next_intake();
		let skeptic = Skeptic::<Test>::get().unwrap();
		for &i in &[10, 20, 30][..] {
			assert_ok!(Society::vote(Origin::signed(i), 40, i != skeptic));
		}
		conclude_intake(true, None);
		assert_eq!(Members::<Test>::get(10).unwrap().strikes, 0);
		run_to_block(12);
		assert_eq!(members(), vec![10, 20, 30, 40]);
		assert_eq!(Members::<Test>::get(skeptic).unwrap().strikes, 1);
	});
}

#[test]
fn basic_new_member_reject_works() {
	EnvBuilder::new().execute(|| {
		// Starting Balance
		assert_eq!(Balances::free_balance(20), 50);
		// 20 makes a bid
		assert_ok!(Society::bid(Origin::signed(20), 0));
		assert_eq!(Balances::free_balance(20), 25);
		assert_eq!(Balances::reserved_balance(20), 25);
		// Rotation Period
		next_intake();
		assert_eq!(candidacies(), vec![(20, candidacy(1, 0, BidKind::Deposit(25), 0, 0))]);
		// We say no
		assert_ok!(Society::vote(Origin::signed(10), 20, false));
		conclude_intake(true, None);
		next_intake();
		// User is not added as member
		assert_eq!(members(), vec![10]);
		// User is rejected.
		assert_eq!(candidacies(), vec![]);
		assert_eq!(Bids::<Test>::get(), vec![]);
	});
}

#[test]
fn slash_payout_works() {
	EnvBuilder::new().execute(|| {
		assert_eq!(Balances::free_balance(20), 50);
		assert_ok!(Society::bid(Origin::signed(20), 1000));
		next_intake();
		assert_ok!(Society::vote(Origin::signed(10), 20, true));
		conclude_intake(true, None);
		// payout in queue
		assert_eq!(Payouts::<Test>::get(20), PayoutRecord { paid: 0, payouts: vec![(8, 1000)].try_into().unwrap() });
		assert_noop!(Society::payout(Origin::signed(20)), Error::<Test>::NoPayout);
		// slash payout
		assert_eq!(Society::slash_payout(&20, 500), 500);
		assert_eq!(Payouts::<Test>::get(20), PayoutRecord { paid: 0, payouts: vec![(8, 500)].try_into().unwrap() });
		run_to_block(8);
		// payout should be here, but 500 less
		assert_ok!(Society::payout(Origin::signed(20)));
		assert_eq!(Balances::free_balance(20), 550);
		assert_eq!(Payouts::<Test>::get(20), PayoutRecord { paid: 500, payouts: Default::default() });
	});
}

#[test]
fn slash_payout_multi_works() {
	EnvBuilder::new().execute(|| {
		assert_eq!(Balances::free_balance(20), 50);
		place_members([20]);
		// create a few payouts
		Society::bump_payout(&20, 5, 100);
		Society::bump_payout(&20, 10, 100);
		Society::bump_payout(&20, 15, 100);
		Society::bump_payout(&20, 20, 100);
		// payouts in queue
		assert_eq!(Payouts::<Test>::get(20), PayoutRecord { paid: 0, payouts: vec![(5, 100), (10, 100), (15, 100), (20, 100)].try_into().unwrap() });
		// slash payout
		assert_eq!(Society::slash_payout(&20, 250), 250);
		assert_eq!(Payouts::<Test>::get(20), PayoutRecord { paid: 0, payouts: vec![(15, 50), (20, 100)].try_into().unwrap() });
		// slash again
		assert_eq!(Society::slash_payout(&20, 50), 50);
		assert_eq!(Payouts::<Test>::get(20), PayoutRecord { paid: 0, payouts: vec![(20, 100)].try_into().unwrap() });
	});
}

#[test]
fn suspended_member_life_cycle_works() {
	EnvBuilder::new().execute(|| {
		// Add 20 to members, who is not the head and can be suspended/removed.
		place_members([20]);
		assert_eq!(members(), vec![10, 20]);
		assert_eq!(Members::<Test>::get(20).unwrap().strikes, 0);
		assert!(!SuspendedMembers::<Test>::contains_key(20));

		// Let's suspend account 20 by giving them 2 strikes by not voting
		assert_ok!(Society::bid(Origin::signed(30), 0));
		assert_ok!(Society::bid(Origin::signed(40), 1));
		next_intake();
		conclude_intake(false, None);


		// 2 strikes are accumulated, and 20 is suspended :(
		assert!(SuspendedMembers::<Test>::contains_key(20));
		assert_eq!(members(), vec![10]);

		// Suspended members cannot get payout
		Society::bump_payout(&20, 10, 100);
		assert_noop!(Society::payout(Origin::signed(20)), Error::<Test>::NotMember);

		// Normal people cannot make judgement
		assert_noop!(Society::judge_suspended_member(Origin::signed(20), 20, true), Error::<Test>::NotFounder);

		// Suspension judgment origin can judge thee
		// Suspension judgement origin forgives the suspended member
		assert_ok!(Society::judge_suspended_member(Origin::signed(10), 20, true));
		assert!(!SuspendedMembers::<Test>::contains_key(20));
		assert_eq!(members(), vec![10, 20]);

		// Let's suspend them again, directly
		Society::suspend_member(&20);
		assert!(SuspendedMembers::<Test>::contains_key(20));
		// Suspension judgement origin does not forgive the suspended member
		assert_ok!(Society::judge_suspended_member(Origin::signed(10), 20, false));
		// Cleaned up
		assert!(!SuspendedMembers::<Test>::contains_key(20));
		assert_eq!(members(), vec![10]);
		assert_eq!(Payouts::<Test>::get(20), PayoutRecord { paid: 0, payouts: vec![].try_into().unwrap() });
	});
}

#[test]
fn suspended_candidate_rejected_works() {
	EnvBuilder::new().execute(|| {
		place_members([20, 30]);
		// 40, 50, 60, 70, 80 make bids
		for &x in &[40u128, 50, 60, 70] {
			assert_ok!(Society::bid(Origin::signed(x), 10));
			assert_eq!(Balances::free_balance(x), 25);
			assert_eq!(Balances::reserved_balance(x), 25);
		}

		// Rotation Period
		next_intake();
		assert_eq!(candidacies(), vec![
			(40, candidacy(1, 10, BidKind::Deposit(25), 0, 0)),
			(50, candidacy(1, 10, BidKind::Deposit(25), 0, 0)),
			(60, candidacy(1, 10, BidKind::Deposit(25), 0, 0)),
			(70, candidacy(1, 10, BidKind::Deposit(25), 0, 0)),
		]);

		// Split vote over all.
		for &x in &[40, 50, 60, 70] {
			assert_ok!(Society::vote(Origin::signed(20), x, false));
			assert_ok!(Society::vote(Origin::signed(30), x, true));
		}

		// Voting continues, as no canidate is clearly accepted yet and the founder chooses not to
		// act.
		conclude_intake(false, None);
		assert_eq!(members(), vec![10, 20, 30]);
		assert_eq!(candidates(), vec![40, 50, 60, 70]);

		// 40 gets approved after founder weighs in giving it a clear approval.
		// but the founder's rejection of 60 doesn't do much for now.
		assert_ok!(Society::vote(Origin::signed(10), 40, true));
		assert_ok!(Society::vote(Origin::signed(10), 60, false));
		conclude_intake(false, None);
		assert_eq!(members(), vec![10, 20, 30, 40]);
		assert_eq!(candidates(), vec![50, 60, 70]);
		assert_eq!(Balances::free_balance(40), 50);
		assert_eq!(Balances::reserved_balance(40), 0);
		assert_eq!(Balances::free_balance(Society::account_id()), 9990);

		// Founder manually bestows membership on 50 and and kicks 70.
		assert_ok!(Society::bestow_membership(Origin::signed(10), 50));
		assert_eq!(members(), vec![10, 20, 30, 40, 50]);
		assert_eq!(candidates(), vec![60, 70]);
		assert_eq!(Balances::free_balance(50), 50);
		assert_eq!(Balances::reserved_balance(50), 0);
		assert_eq!(Balances::free_balance(Society::account_id()), 9980);

		assert_ok!(Society::kick_candidate(Origin::signed(10), 70));
		assert_eq!(members(), vec![10, 20, 30, 40, 50]);
		assert_eq!(candidates(), vec![60]);
		assert_eq!(Balances::free_balance(70), 25);
		assert_eq!(Balances::reserved_balance(70), 0);
		assert_eq!(Balances::free_balance(Society::account_id()), 10005);

		// Next round doesn't make much difference.
		next_intake();
		conclude_intake(false, None);
		assert_eq!(members(), vec![10, 20, 30, 40, 50]);
		assert_eq!(candidates(), vec![60]);
		assert_eq!(Balances::free_balance(Society::account_id()), 10005);

		// But after two rounds, the clearly rejected 60 gets dropped and slashed.
		next_intake();
		conclude_intake(false, None);
		assert_eq!(members(), vec![10, 20, 30, 40, 50]);
		assert_eq!(candidates(), vec![]);
		assert_eq!(Balances::free_balance(60), 25);
		assert_eq!(Balances::reserved_balance(60), 0);
		assert_eq!(Balances::free_balance(Society::account_id()), 10030);
	});
}

/*
#[test]
fn vouch_works() {
	EnvBuilder::new().execute(|| {
		// 10 is the only member
		assert_eq!(members(), vec![10]);
		// A non-member cannot vouch
		assert_noop!(Society::vouch(Origin::signed(1), 20, 1000, 100), Error::<Test>::NotMember);
		// A member can though
		assert_ok!(Society::vouch(Origin::signed(10), 20, 1000, 100));
		assert_eq!(<Vouching<Test>>::get(10), Some(VouchingStatus::Vouching));
		// A member cannot vouch twice at the same time
		assert_noop!(
			Society::vouch(Origin::signed(10), 30, 100, 0),
			Error::<Test>::AlreadyVouching
		);
		// Vouching creates the right kind of bid
		assert_eq!(<Bids<Test>>::get(), vec![(20, candidacy(1, 1000, BidKind::Vouch(10,, 0, 0) 100))]);
		// Vouched user can become candidate
		next_intake();
		assert_eq!(candidacies(), vec![(20, candidacy(1, 1000, BidKind::Vouch(10,, 0, 0) 100))]);
		// Vote yes
		assert_ok!(Society::vote(Origin::signed(10), 20, true));
		// Vouched user can win
		next_intake();
		assert_eq!(members(), vec![10, 20]);
		// Voucher wins a portion of the payment
		assert_eq!(Payouts::<Test>::get(10), PayoutRecord { paid: 0, payouts: vec![(9, 100)].try_into().unwrap() });
		// Vouched user wins the rest
		assert_eq!(Payouts::<Test>::get(20), PayoutRecord { paid: 0, payouts: vec![(9, 900)].try_into().unwrap() });
		// 10 is no longer vouching
		assert_eq!(<Vouching<Test>>::get(10), None);
	});
}

#[test]
fn voucher_cannot_win_more_than_bid() {
	EnvBuilder::new().execute(|| {
		// 10 is the only member
		assert_eq!(members(), vec![10]);
		// 10 vouches, but asks for more than the bid
		assert_ok!(Society::vouch(Origin::signed(10), 20, 100, 1000));
		// Vouching creates the right kind of bid
		assert_eq!(<Bids<Test>>::get(), vec![(20, candidacy(1, 100, BidKind::Vouch(10,, 0, 0) 1000))]);
		// Vouched user can become candidate
		next_intake();
		assert_eq!(candidacies(), vec![(20, candidacy(1, 100, BidKind::Vouch(10,, 0, 0) 1000))]);
		// Vote yes
		assert_ok!(Society::vote(Origin::signed(10), 20, true));
		// Vouched user can win
		next_intake();
		assert_eq!(members(), vec![10, 20]);
		// Voucher wins as much as the bid
		assert_eq!(Payouts::<Test>::get(10), PayoutRecord { paid: 0, payouts: vec![(9, 100)].try_into().unwrap() });
		// Vouched user gets nothing
		assert_eq!(Payouts::<Test>::get(20), PayoutRecord { paid: 0, payouts: vec![].try_into().unwrap() });
	});
}

#[test]
fn unvouch_works() {
	EnvBuilder::new().execute(|| {
		// 10 is the only member
		assert_eq!(members(), vec![10]);
		// 10 vouches for 20
		assert_ok!(Society::vouch(Origin::signed(10), 20, 100, 0));
		// 20 has a bid
		assert_eq!(<Bids<Test>>::get(), vec![(20, candidacy(1, 100, BidKind::Vouch(10,, 0, 0) 0))]);
		// 10 is vouched
		assert_eq!(<Vouching<Test>>::get(10), Some(VouchingStatus::Vouching));
		// To unvouch, you must know the right bid position
		assert_noop!(Society::unvouch(Origin::signed(10), 2), Error::<Test>::BadPosition);
		// 10 can unvouch with the right position
		assert_ok!(Society::unvouch(Origin::signed(10), 0));
		// 20 no longer has a bid
		assert_eq!(<Bids<Test>>::get(), vec![]);
		// 10 is no longer vouching
		assert_eq!(<Vouching<Test>>::get(10), None);

		// Cannot unvouch after they become candidate
		assert_ok!(Society::vouch(Origin::signed(10), 20, 100, 0));
		next_intake();
		assert_eq!(candidacies(), vec![(20, candidacy(1, 100, BidKind::Vouch(10,, 0, 0) 0))]);
		assert_noop!(Society::unvouch(Origin::signed(10), 0), Error::<Test>::BadPosition);
		// 10 is still vouching until candidate is approved or rejected
		assert_eq!(<Vouching<Test>>::get(10), Some(VouchingStatus::Vouching));
		next_intake();
		// In this case candidate is denied and suspended
		assert!(Society::suspended_candidate(&20).is_some());
		assert_eq!(members(), vec![10]);
		// User is stuck vouching until judgement origin resolves suspended candidate
		assert_eq!(<Vouching<Test, _>>::get(10), Some(VouchingStatus::Vouching));
		// Judge denies candidate
		assert_ok!(Society::judge_suspended_candidate(Origin::signed(2), 20, Judgement::Reject));
		// 10 is banned from vouching
		assert_eq!(<Vouching<Test, _>>::get(10), Some(VouchingStatus::Banned));
		assert_eq!(members(), vec![10]);

		// 10 cannot vouch again
		assert_noop!(
			Society::vouch(Origin::signed(10), 30, 100, 0),
			Error::<Test>::AlreadyVouching
		);
		// 10 cannot unvouch either, so they are banned forever.
		assert_noop!(Society::unvouch(Origin::signed(10), 0), Error::<Test>::NotVouching);
	});
}

#[test]
fn unbid_vouch_works() {
	EnvBuilder::new().execute(|| {
		// 10 is the only member
		assert_eq!(members(), vec![10]);
		// 10 vouches for 20
		assert_ok!(Society::vouch(Origin::signed(10), 20, 100, 0));
		// 20 has a bid
		assert_eq!(<Bids<Test>>::get(), vec![(20, candidacy(1, 100, BidKind::Vouch(10,, 0, 0) 0))]);
		// 10 is vouched
		assert_eq!(<Vouching<Test>>::get(10), Some(VouchingStatus::Vouching));
		// 20 doesn't want to be a member and can unbid themselves.
		assert_ok!(Society::unbid(Origin::signed(20)));
		// Everything is cleaned up
		assert_eq!(<Vouching<Test>>::get(10), None);
		assert_eq!(<Bids<Test>>::get(), vec![]);
	});
}

#[test]
fn founder_and_head_cannot_be_removed() {
	EnvBuilder::new().execute(|| {
		// 10 is the only member, founder, and head
		assert_eq!(members(), vec![10]);
		assert_eq!(Founder::<Test>::get(), Some(10));
		assert_eq!(Head::<Test>::get(), Some(10));
		// 10 can still accumulate strikes
		assert_ok!(Society::bid(Origin::signed(20), 0));
		next_intake();
		assert_eq!(Members::<Test>::get(10).unwrap().strikes, 1);
		assert_ok!(Society::bid(Origin::signed(30), 0));
		run_to_block(16);
		assert_eq!(Members::<Test>::get(10).unwrap().strikes, 2);
		// Awkwardly they can obtain more than MAX_STRIKES...
		assert_ok!(Society::bid(Origin::signed(40), 0));
		run_to_block(24);
		assert_eq!(Members::<Test>::get(10).unwrap().strikes, 3);

		// Replace the head
		assert_ok!(Society::bid(Origin::signed(50), 0));
		run_to_block(28);
		assert_ok!(Society::vote(Origin::signed(10), 50, true));
		assert_ok!(Society::defender_vote(Origin::signed(10), true)); // Keep defender around
		run_to_block(32);
		assert_eq!(members(), vec![10, 50]);
		assert_eq!(Head::<Test>::get(), Some(50));
		// Founder is unchanged
		assert_eq!(Founder::<Test>::get(), Some(10));

		// 50 can still accumulate strikes
		assert_ok!(Society::bid(Origin::signed(60), 0));
		run_to_block(40);
		assert_eq!(Members::<Test>::get(50).unwrap().strikes, 1);
		assert_ok!(Society::bid(Origin::signed(70), 0));
		run_to_block(48);
		assert_eq!(Members::<Test>::get(50).unwrap().strikes, 2);

		// Replace the head
		assert_ok!(Society::bid(Origin::signed(80), 0));
		run_to_block(52);
		assert_ok!(Society::vote(Origin::signed(10), 80, true));
		assert_ok!(Society::vote(Origin::signed(50), 80, true));
		assert_ok!(Society::defender_vote(Origin::signed(10), true)); // Keep defender around
		run_to_block(56);
		assert_eq!(members(), vec![10, 50, 80]);
		assert_eq!(Head::<Test>::get(), Some(80));
		assert_eq!(Founder::<Test>::get(), Some(10));

		// 50 can now be suspended for strikes
		assert_ok!(Society::bid(Origin::signed(90), 0));
		run_to_block(60);
		// The candidate is rejected, so voting approve will give a strike
		assert_ok!(Society::vote(Origin::signed(50), 90, true));
		run_to_block(64);
		assert_eq!(Members::<Test>::get(50).unwrap().strikes, 0);
		assert_eq!(SuspendedMembers::<Test>::contains_key(50), true);
		assert_eq!(members(), vec![10, 80]);
	});
}

#[test]
fn challenges_work() {
	EnvBuilder::new().execute(|| {
		// Add some members
		assert_ok!(Society::add_member(&20));
		assert_ok!(Society::add_member(&30));
		assert_ok!(Society::add_member(&40));
		// Votes are empty
		assert_eq!(<DefenderVotes<Test>>::get(10), None);
		assert_eq!(<DefenderVotes<Test>>::get(20), None);
		assert_eq!(<DefenderVotes<Test>>::get(30), None);
		assert_eq!(<DefenderVotes<Test>>::get(40), None);
		// Check starting point
		assert_eq!(members(), vec![10, 20, 30, 40]);
		assert_eq!(Society::defender(), None);
		// 20 will be challenged during the challenge rotation
		next_intake();
		assert_eq!(Society::defender(), Some(30));
		// They can always free vote for themselves
		assert_ok!(Society::defender_vote(Origin::signed(30), true));
		// If no one else votes, nothing happens
		run_to_block(16);
		assert_eq!(members(), vec![10, 20, 30, 40]);
		// New challenge period
		assert_eq!(Society::defender(), Some(30));
		// Non-member cannot challenge
		assert_noop!(Society::defender_vote(Origin::signed(1), true), Error::<Test>::NotMember);
		// 3 people say accept, 1 reject
		assert_ok!(Society::defender_vote(Origin::signed(10), true));
		assert_ok!(Society::defender_vote(Origin::signed(20), true));
		assert_ok!(Society::defender_vote(Origin::signed(30), true));
		assert_ok!(Society::defender_vote(Origin::signed(40), false));
		run_to_block(24);
		// 20 survives
		assert_eq!(members(), vec![10, 20, 30, 40]);
		// Votes are reset
		assert_eq!(<DefenderVotes<Test>>::get(10), None);
		assert_eq!(<DefenderVotes<Test>>::get(20), None);
		assert_eq!(<DefenderVotes<Test>>::get(30), None);
		assert_eq!(<DefenderVotes<Test>>::get(40), None);
		// One more time
		assert_eq!(Society::defender(), Some(30));
		// 2 people say accept, 2 reject
		assert_ok!(Society::defender_vote(Origin::signed(10), true));
		assert_ok!(Society::defender_vote(Origin::signed(20), true));
		assert_ok!(Society::defender_vote(Origin::signed(30), false));
		assert_ok!(Society::defender_vote(Origin::signed(40), false));
		run_to_block(32);
		// 20 is suspended
		assert_eq!(members(), vec![10, 20, 40]);
		assert_eq!(Society::suspended_member(30), true);
		// New defender is chosen
		assert_eq!(Society::defender(), Some(20));
		// Votes are reset
		assert_eq!(<DefenderVotes<Test>>::get(10), None);
		assert_eq!(<DefenderVotes<Test>>::get(20), None);
		assert_eq!(<DefenderVotes<Test>>::get(30), None);
		assert_eq!(<DefenderVotes<Test>>::get(40), None);
	});
}

#[test]
fn bad_vote_slash_works() {
	EnvBuilder::new().execute(|| {
		// Add some members
		assert_ok!(Society::add_member(&20));
		assert_ok!(Society::add_member(&30));
		assert_ok!(Society::add_member(&40));
		// Create some payouts
		Society::bump_payout(&10, 5, 100);
		Society::bump_payout(&20, 5, 100);
		Society::bump_payout(&30, 5, 100);
		Society::bump_payout(&40, 5, 100);
		// Check starting point
		assert_eq!(members(), vec![10, 20, 30, 40]);
		assert_eq!(Payouts::<Test>::get(10), PayoutRecord { paid: 0, payouts: vec![(5, 100)].try_into().unwrap() });
		assert_eq!(Payouts::<Test>::get(20), PayoutRecord { paid: 0, payouts: vec![(5, 100)].try_into().unwrap() });
		assert_eq!(Payouts::<Test>::get(30), PayoutRecord { paid: 0, payouts: vec![(5, 100)].try_into().unwrap() });
		assert_eq!(Payouts::<Test>::get(40), PayoutRecord { paid: 0, payouts: vec![(5, 100)].try_into().unwrap() });
		// Create a new bid
		assert_ok!(Society::bid(Origin::signed(50), 1000));
		next_intake();
		assert_ok!(Society::vote(Origin::signed(10), 50, false));
		assert_ok!(Society::vote(Origin::signed(20), 50, true));
		assert_ok!(Society::vote(Origin::signed(30), 50, false));
		assert_ok!(Society::vote(Origin::signed(40), 50, false));
		next_intake();
		// Wrong voter gained a strike
		assert_eq!(<Strikes<Test>>::get(10), 0);
		assert_eq!(<Strikes<Test>>::get(20), 1);
		assert_eq!(<Strikes<Test>>::get(30), 0);
		assert_eq!(<Strikes<Test>>::get(40), 0);
		// Their payout is slashed, a random person is rewarded
		assert_eq!(Payouts::<Test>::get(10), PayoutRecord { paid: 0, payouts: vec![(5, 100), (9, 2)].try_into().unwrap() });
		assert_eq!(Payouts::<Test>::get(20), PayoutRecord { paid: 0, payouts: vec![(5, 98)].try_into().unwrap() });
		assert_eq!(Payouts::<Test>::get(30), PayoutRecord { paid: 0, payouts: vec![(5, 100)].try_into().unwrap() });
		assert_eq!(Payouts::<Test>::get(40), PayoutRecord { paid: 0, payouts: vec![(5, 100)].try_into().unwrap() });
	});
}

#[test]
fn user_cannot_bid_twice() {
	EnvBuilder::new().execute(|| {
		// Cannot bid twice
		assert_ok!(Society::bid(Origin::signed(20), 100));
		assert_noop!(Society::bid(Origin::signed(20), 100), Error::<Test>::AlreadyBid);
		// Cannot bid when vouched
		assert_ok!(Society::vouch(Origin::signed(10), 30, 100, 100));
		assert_noop!(Society::bid(Origin::signed(30), 100), Error::<Test>::AlreadyBid);
		// Cannot vouch when already bid
		assert_ok!(Society::add_member(&50));
		assert_noop!(
			Society::vouch(Origin::signed(50), 20, 100, 100),
			Error::<Test>::AlreadyBid
		);
	});
}

#[test]
fn vouching_handles_removed_member_with_bid() {
	EnvBuilder::new().execute(|| {
		// Add a member
		assert_ok!(Society::add_member(&20));
		// Have that member vouch for a user
		assert_ok!(Society::vouch(Origin::signed(20), 30, 1000, 100));
		// That user is now a bid and the member is vouching
		assert_eq!(<Bids<Test>>::get(), vec![(30, candidacy(1, 1000, BidKind::Vouch(20,, 0, 0) 100))]);
		assert_eq!(<Vouching<Test>>::get(20), Some(VouchingStatus::Vouching));
		// Suspend that member
		Society::suspend_member(&20);
		assert_eq!(SuspendedMembers::<Test>::contains_key(20), true);
		// Nothing changes yet
		assert_eq!(<Bids<Test>>::get(), vec![(30, candidacy(1, 1000, BidKind::Vouch(20,, 0, 0) 100))]);
		assert_eq!(<Vouching<Test>>::get(20), Some(VouchingStatus::Vouching));
		// Remove member
		assert_ok!(Society::judge_suspended_member(Origin::signed(2), 20, false));
		// Bid is removed, vouching status is removed
		assert_eq!(<Bids<Test>>::get(), vec![]);
		assert_eq!(<Vouching<Test>>::get(20), None);
	});
}

#[test]
fn vouching_handles_removed_member_with_candidate() {
	EnvBuilder::new().execute(|| {
		// Add a member
		assert_ok!(Society::add_member(&20));
		// Have that member vouch for a user
		assert_ok!(Society::vouch(Origin::signed(20), 30, 1000, 100));
		// That user is now a bid and the member is vouching
		assert_eq!(<Bids<Test>>::get(), vec![(30, candidacy(1, 1000, BidKind::Vouch(20,, 0, 0) 100))]);
		assert_eq!(<Vouching<Test>>::get(20), Some(VouchingStatus::Vouching));
		// Make that bid a candidate
		next_intake();
		assert_eq!(candidacies(), vec![(30, candidacy(1, 1000, BidKind::Vouch(20,, 0, 0) 100))]);
		// Suspend that member
		Society::suspend_member(&20);
		assert_eq!(SuspendedMembers::<Test>::contains_key(20), true);
		// Nothing changes yet
		assert_eq!(candidacies(), vec![(30, candidacy(1, 1000, BidKind::Vouch(20,, 0, 0) 100))]);
		assert_eq!(<Vouching<Test>>::get(20), Some(VouchingStatus::Vouching));
		// Remove member
		assert_ok!(Society::judge_suspended_member(Origin::signed(2), 20, false));
		// Vouching status is removed, but candidate is still in the queue
		assert_eq!(<Vouching<Test>>::get(20), None);
		assert_eq!(candidacies(), vec![(30, candidacy(1, 1000, BidKind::Vouch(20,, 0, 0) 100))]);
		// Candidate wins
		assert_ok!(Society::vote(Origin::signed(10), 30, true));
		next_intake();
		assert_eq!(members(), vec![10, 30]);
		// Payout does not go to removed member
		assert_eq!(Payouts::<Test>::get(20), PayoutRecord { paid: 0, payouts: vec![].try_into().unwrap() });
		assert_eq!(Payouts::<Test>::get(30), PayoutRecord { paid: 0, payouts: vec![(9, 1000)].try_into().unwrap() });
	});
}

#[test]
fn votes_are_working() {
	EnvBuilder::new().execute(|| {
		// Users make bids of various amounts
		assert_ok!(Society::bid(Origin::signed(50), 500));
		assert_ok!(Society::bid(Origin::signed(40), 400));
		assert_ok!(Society::bid(Origin::signed(30), 300));
		// Rotate period
		next_intake();
		// A member votes for these candidates to join the society
		assert_ok!(Society::vote(Origin::signed(10), 30, true));
		assert_ok!(Society::vote(Origin::signed(10), 40, true));
		// You cannot vote for a non-candidate
		assert_noop!(Society::vote(Origin::signed(10), 50, true), Error::<Test>::NotCandidate);
		// Votes are stored
		assert_eq!(<Votes<Test>>::get(30, 10), Some(Vote::Approve));
		assert_eq!(<Votes<Test>>::get(40, 10), Some(Vote::Approve));
		assert_eq!(<Votes<Test>>::get(50, 10), None);
		next_intake();
		// Candidates become members after a period rotation
		assert_eq!(members(), vec![10, 30, 40]);
		// Votes are cleaned up
		assert_eq!(<Votes<Test>>::get(30, 10), None);
		assert_eq!(<Votes<Test>>::get(40, 10), None);
	});
}

#[test]
fn max_limits_work() {
	EnvBuilder::new().with_pot(100000).execute(|| {
		// Max bids is 1000, when extra bids come in, it pops the larger ones off the stack.
		// Try to put 1010 users into the bid pool
		for i in (100..1110).rev() {
			// Give them some funds
			let _ = Balances::make_free_balance_be(&(i as u128), 1000);
			assert_ok!(Society::bid(Origin::signed(i as u128), i));
		}
		let bids = <Bids<Test>>::get();
		// Length is 1000
		assert_eq!(bids.len(), 1000);
		// First bid is smallest number (100)
		assert_eq!(bids[0], (100, candidacy(1, 100, BidKind::Deposit(25), 0, 0)));
		// Last bid is smallest number + 99 (1099)
		assert_eq!(bids[999], (1099, candidacy(1, 1099, BidKind::Deposit(25), 0, 0)));
		// Rotate period
		next_intake();
		// Max of 10 candidates
		assert_eq!(candidates().len(), 10);
		// Fill up membership, max 100, we will do just 95
		for i in 2000..2095 {
			assert_ok!(Society::add_member(&(i as u128)));
		}
		// Remember there was 1 original member, so 96 total
		assert_eq!(members().len(), 96);
		// Rotate period
		next_intake();
		// Only of 4 candidates possible now
		assert_eq!(candidates().len(), 4);
		// Fill up members with suspended candidates from the first rotation
		for i in 100..104 {
			assert_ok!(Society::judge_suspended_candidate(
				Origin::signed(2),
				i,
				Judgement::Approve
			));
		}
		assert_eq!(members().len(), 100);
		// Can't add any more members
		assert_noop!(Society::add_member(&98), Error::<Test>::MaxMembers);
		// However, a fringe scenario allows for in-progress candidates to increase the membership
		// pool, but it has no real after-effects.
		for i in members().iter() {
			assert_ok!(Society::vote(Origin::signed(*i), 110, true));
			assert_ok!(Society::vote(Origin::signed(*i), 111, true));
			assert_ok!(Society::vote(Origin::signed(*i), 112, true));
		}
		// Rotate period
		run_to_block(12);
		// Members length is over 100, no problem...
		assert_eq!(members().len(), 103);
		// No candidates because full
		assert_eq!(candidates().len(), 0);
		// Increase member limit
		assert_ok!(Society::set_max_members(Origin::root(), 200));
		// Rotate period
		run_to_block(16);
		// Candidates are back!
		assert_eq!(candidates().len(), 10);
	});
}

#[test]
fn zero_bid_works() {
	// This tests:
	// * Only one zero bid is selected.
	// * That zero bid is placed as head when accepted.
	EnvBuilder::new().execute(|| {
		// Users make bids of various amounts
		assert_ok!(Society::bid(Origin::signed(60), 400));
		assert_ok!(Society::bid(Origin::signed(50), 300));
		assert_ok!(Society::bid(Origin::signed(30), 0));
		assert_ok!(Society::bid(Origin::signed(20), 0));
		assert_ok!(Society::bid(Origin::signed(40), 0));

		// Rotate period
		next_intake();
		// Pot is 1000 after "PeriodSpend"
		assert_eq!(Pot::<Test>::get(), 1000);
		assert_eq!(Balances::free_balance(Society::account_id()), 10_000);
		// Choose smallest bidding users whose total is less than pot, with only one zero bid.
		assert_eq!(
			candidates(),
			vec![
				(30, candidacy(1, 0, BidKind::Deposit(25), 0, 0)),
				(50, candidacy(1, 300, BidKind::Deposit(25), 0, 0)),
				(60, candidacy(1, 400, BidKind::Deposit(25), 0, 0)),
			]
		);
		assert_eq!(
			<Bids<Test>>::get(),
			vec![(20, candidacy(1, 0, BidKind::Deposit(25), 0, 0)), (40, candidacy(1, 0, BidKind::Deposit(25), 0, 0)),]
		);
		// A member votes for these candidates to join the society
		assert_ok!(Society::vote(Origin::signed(10), 30, true));
		assert_ok!(Society::vote(Origin::signed(10), 50, true));
		assert_ok!(Society::vote(Origin::signed(10), 60, true));
		next_intake();
		// Candidates become members after a period rotation
		assert_eq!(members(), vec![10, 30, 50, 60]);
		// The zero bid is selected as head
		assert_eq!(Head::<Test>::get(), Some(30));
	});
}

#[test]
fn bids_ordered_correctly() {
	// This tests that bids with the same value are placed in the list ordered
	// with bidders who bid first earlier on the list.
	EnvBuilder::new().execute(|| {
		for i in 0..5 {
			for j in 0..5 {
				// Give them some funds
				let _ = Balances::make_free_balance_be(&(100 + (i * 5 + j) as u128), 1000);
				assert_ok!(Society::bid(Origin::signed(100 + (i * 5 + j) as u128), j));
			}
		}

		let mut final_list = Vec::new();

		for j in 0..5 {
			for i in 0..5 {
				final_list.push((100 +candidacy(j1, ,  (i * 5 + j), 0, 0) as u128, BidKind::Deposit(25)));
			}
		}

		assert_eq!(<Bids<Test>>::get(), final_list);
	});
}
*/