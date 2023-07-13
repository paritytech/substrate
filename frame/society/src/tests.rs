// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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
use migrations::old;
use mock::*;

use frame_support::{assert_noop, assert_ok};
use sp_core::blake2_256;
use sp_runtime::traits::BadOrigin;
use BidKind::*;
use VouchingStatus::*;

use RuntimeOrigin as Origin;

#[test]
fn migration_works() {
	EnvBuilder::new().founded(false).execute(|| {
		use old::Vote::*;

		// Initialise the old storage items.
		Founder::<Test>::put(10);
		Head::<Test>::put(30);
		old::Members::<Test, ()>::put(vec![10, 20, 30]);
		old::Vouching::<Test, ()>::insert(30, Vouching);
		old::Vouching::<Test, ()>::insert(40, Banned);
		old::Strikes::<Test, ()>::insert(20, 1);
		old::Strikes::<Test, ()>::insert(30, 2);
		old::Strikes::<Test, ()>::insert(40, 5);
		old::Payouts::<Test, ()>::insert(20, vec![(1, 1)]);
		old::Payouts::<Test, ()>::insert(
			30,
			(0..=<Test as Config>::MaxPayouts::get())
				.map(|i| (i as u64, i as u64))
				.collect::<Vec<_>>(),
		);
		old::SuspendedMembers::<Test, ()>::insert(40, true);

		old::Defender::<Test, ()>::put(20);
		old::DefenderVotes::<Test, ()>::insert(10, Approve);
		old::DefenderVotes::<Test, ()>::insert(20, Approve);
		old::DefenderVotes::<Test, ()>::insert(30, Reject);

		old::SuspendedCandidates::<Test, ()>::insert(50, (10, Deposit(100)));

		old::Candidates::<Test, ()>::put(vec![
			Bid { who: 60, kind: Deposit(100), value: 200 },
			Bid { who: 70, kind: Vouch(30, 30), value: 100 },
		]);
		old::Votes::<Test, ()>::insert(60, 10, Approve);
		old::Votes::<Test, ()>::insert(70, 10, Reject);
		old::Votes::<Test, ()>::insert(70, 20, Approve);
		old::Votes::<Test, ()>::insert(70, 30, Approve);

		let bids = (0..=<Test as Config>::MaxBids::get())
			.map(|i| Bid {
				who: 100u128 + i as u128,
				kind: Deposit(20u64 + i as u64),
				value: 10u64 + i as u64,
			})
			.collect::<Vec<_>>();
		old::Bids::<Test, ()>::put(bids);

		migrations::from_original::<Test, ()>(&mut [][..]).expect("migration failed");
		migrations::assert_internal_consistency::<Test, ()>();

		assert_eq!(
			membership(),
			vec![
				(10, MemberRecord { rank: 0, strikes: 0, vouching: None, index: 0 }),
				(20, MemberRecord { rank: 0, strikes: 1, vouching: None, index: 1 }),
				(30, MemberRecord { rank: 0, strikes: 2, vouching: Some(Vouching), index: 2 }),
			]
		);
		assert_eq!(Payouts::<Test>::get(10), PayoutRecord::default());
		let payouts = vec![(1, 1)].try_into().unwrap();
		assert_eq!(Payouts::<Test>::get(20), PayoutRecord { paid: 0, payouts });
		let payouts = (0..<Test as Config>::MaxPayouts::get())
			.map(|i| (i as u64, i as u64))
			.collect::<Vec<_>>()
			.try_into()
			.unwrap();
		assert_eq!(Payouts::<Test>::get(30), PayoutRecord { paid: 0, payouts });
		assert_eq!(
			SuspendedMembers::<Test>::iter().collect::<Vec<_>>(),
			vec![(40, MemberRecord { rank: 0, strikes: 5, vouching: Some(Banned), index: 0 }),]
		);
		let bids: BoundedVec<_, <Test as Config>::MaxBids> = (0..<Test as Config>::MaxBids::get())
			.map(|i| Bid {
				who: 100u128 + i as u128,
				kind: Deposit(20u64 + i as u64),
				value: 10u64 + i as u64,
			})
			.collect::<Vec<_>>()
			.try_into()
			.unwrap();
		assert_eq!(Bids::<Test>::get(), bids);
		assert_eq!(RoundCount::<Test, ()>::get(), 0);
		assert_eq!(
			candidacies(),
			vec![
				(
					60,
					Candidacy {
						round: 0,
						kind: Deposit(100),
						bid: 200,
						tally: Tally { approvals: 1, rejections: 0 },
						skeptic_struck: false,
					}
				),
				(
					70,
					Candidacy {
						round: 0,
						kind: Vouch(30, 30),
						bid: 100,
						tally: Tally { approvals: 2, rejections: 1 },
						skeptic_struck: false,
					}
				),
			]
		);
		assert_eq!(Votes::<Test>::get(60, 10), Some(Vote { approve: true, weight: 1 }));
		assert_eq!(Votes::<Test>::get(70, 10), Some(Vote { approve: false, weight: 1 }));
		assert_eq!(Votes::<Test>::get(70, 20), Some(Vote { approve: true, weight: 1 }));
		assert_eq!(Votes::<Test>::get(70, 30), Some(Vote { approve: true, weight: 1 }));
	});
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
		assert_noop!(
			Society::found_society(Origin::signed(5), 20, 100, 10, 2, 25, vec![]),
			BadOrigin
		);
		// Account 1 can start a society, where 10 is the founding member
		assert_ok!(Society::found_society(
			Origin::signed(1),
			10,
			100,
			10,
			2,
			25,
			b"be cool".to_vec()
		));
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
		assert_ok!(Society::bid(RuntimeOrigin::signed(20), 0));
		assert_eq!(Balances::free_balance(20), 25);
		assert_eq!(Balances::reserved_balance(20), 25);
		// Rotate period every 4 blocks
		next_intake();
		// 20 is now a candidate
		assert_eq!(candidacies(), vec![(20, candidacy(1, 0, Deposit(25), 0, 0))]);
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
		assert_ok!(Society::bid(RuntimeOrigin::signed(60), 1900));
		assert_ok!(Society::bid(RuntimeOrigin::signed(50), 500));
		assert_ok!(Society::bid(RuntimeOrigin::signed(40), 400));
		assert_ok!(Society::bid(RuntimeOrigin::signed(30), 300));
		// Rotate period
		next_intake();
		// Pot is 1000 after "PeriodSpend"
		assert_eq!(Pot::<Test>::get(), 1000);
		assert_eq!(Balances::free_balance(Society::account_id()), 10_000);
		// Choose smallest bidding users whose total is less than pot
		assert_eq!(
			candidacies(),
			vec![
				(30, candidacy(1, 300, Deposit(25), 0, 0)),
				(40, candidacy(1, 400, Deposit(25), 0, 0)),
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
		assert_eq!(candidacies(), vec![(50, candidacy(2, 500, Deposit(25), 0, 0))]);
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
		assert_eq!(candidacies(), vec![(60, candidacy(4, 1900, Deposit(25), 0, 0))]);
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
		assert_ok!(Society::bid(RuntimeOrigin::signed(20), 1000));
		assert_ok!(Society::bid(RuntimeOrigin::signed(30), 0));
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
		assert_eq!(candidacies(), vec![(20, candidacy(1, 1000, Deposit(25), 0, 0))]);
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
		assert_ok!(Society::payout(RuntimeOrigin::signed(20)));
		assert_eq!(Balances::free_balance(20), 1050);
	});
}

#[test]
fn non_voting_skeptic_is_punished() {
	EnvBuilder::new().execute(|| {
		assert_eq!(Members::<Test>::get(10).unwrap().strikes, 0);
		assert_ok!(Society::bid(Origin::signed(20), 0));
		next_intake();
		assert_eq!(candidacies(), vec![(20, candidacy(1, 0, Deposit(25), 0, 0))]);
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
		assert_ok!(Society::bid(RuntimeOrigin::signed(20), 0));
		assert_eq!(Balances::free_balance(20), 25);
		assert_eq!(Balances::reserved_balance(20), 25);
		// Rotation Period
		next_intake();
		assert_eq!(candidacies(), vec![(20, candidacy(1, 0, Deposit(25), 0, 0))]);
		// We say no
		assert_ok!(Society::vote(Origin::signed(10), 20, false));
		conclude_intake(true, None);
		next_intake();
		// User is not added as member
		assert_eq!(members(), vec![10]);
		// User is rejected.
		assert_eq!(candidacies(), vec![]);
		assert_eq!(Bids::<Test>::get().into_inner(), vec![]);
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
		assert_eq!(
			Payouts::<Test>::get(20),
			PayoutRecord { paid: 0, payouts: vec![(8, 1000)].try_into().unwrap() }
		);
		assert_noop!(Society::payout(Origin::signed(20)), Error::<Test>::NoPayout);
		// slash payout
		assert_eq!(Society::slash_payout(&20, 500), 500);
		assert_eq!(
			Payouts::<Test>::get(20),
			PayoutRecord { paid: 0, payouts: vec![(8, 500)].try_into().unwrap() }
		);
		run_to_block(8);
		// payout should be here, but 500 less
		assert_ok!(Society::payout(RuntimeOrigin::signed(20)));
		assert_eq!(Balances::free_balance(20), 550);
		assert_eq!(
			Payouts::<Test>::get(20),
			PayoutRecord { paid: 500, payouts: Default::default() }
		);
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
		assert_eq!(
			Payouts::<Test>::get(20),
			PayoutRecord {
				paid: 0,
				payouts: vec![(5, 100), (10, 100), (15, 100), (20, 100)].try_into().unwrap()
			}
		);
		// slash payout
		assert_eq!(Society::slash_payout(&20, 250), 250);
		assert_eq!(
			Payouts::<Test>::get(20),
			PayoutRecord { paid: 0, payouts: vec![(15, 50), (20, 100)].try_into().unwrap() }
		);
		// slash again
		assert_eq!(Society::slash_payout(&20, 50), 50);
		assert_eq!(
			Payouts::<Test>::get(20),
			PayoutRecord { paid: 0, payouts: vec![(20, 100)].try_into().unwrap() }
		);
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
		assert_noop!(
			Society::judge_suspended_member(Origin::signed(20), 20, true),
			Error::<Test>::NotFounder
		);

		// Suspension judgment origin can judge thee
		// Suspension judgement origin forgives the suspended member
		assert_ok!(Society::judge_suspended_member(Origin::signed(10), 20, true));
		assert!(!SuspendedMembers::<Test>::contains_key(20));
		assert_eq!(members(), vec![10, 20]);

		// Let's suspend them again, directly
		assert_ok!(Society::suspend_member(&20));
		assert!(SuspendedMembers::<Test>::contains_key(20));
		// Suspension judgement origin does not forgive the suspended member
		assert_ok!(Society::judge_suspended_member(Origin::signed(10), 20, false));
		// Cleaned up
		assert!(!SuspendedMembers::<Test>::contains_key(20));
		assert_eq!(members(), vec![10]);
		assert_eq!(
			Payouts::<Test>::get(20),
			PayoutRecord { paid: 0, payouts: vec![].try_into().unwrap() }
		);
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
		assert_eq!(
			candidacies(),
			vec![
				(40, candidacy(1, 10, Deposit(25), 0, 0)),
				(50, candidacy(1, 10, Deposit(25), 0, 0)),
				(60, candidacy(1, 10, Deposit(25), 0, 0)),
				(70, candidacy(1, 10, Deposit(25), 0, 0)),
			]
		);

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

		assert_eq!(Balances::free_balance(70), 25);
		assert_eq!(Balances::reserved_balance(70), 25);

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

#[test]
fn unpaid_vouch_works() {
	EnvBuilder::new().execute(|| {
		// 10 is the only member
		assert_eq!(members(), vec![10]);
		// A non-member cannot vouch
		assert_noop!(Society::vouch(Origin::signed(1), 20, 1000, 100), Error::<Test>::NotMember);
		// A member can though
		assert_ok!(Society::vouch(Origin::signed(10), 20, 1000, 100));
		assert_eq!(Members::<Test>::get(10).unwrap().vouching, Some(VouchingStatus::Vouching));
		// A member cannot vouch twice at the same time
		assert_noop!(
			Society::vouch(Origin::signed(10), 30, 100, 0),
			Error::<Test>::AlreadyVouching
		);
		// Vouching creates the right kind of bid
		assert_eq!(Bids::<Test>::get().into_inner(), vec![bid(20, Vouch(10, 100), 1000)]);
		// Vouched user can become candidate
		next_intake();
		assert_eq!(candidacies(), vec![(20, candidacy(1, 1000, Vouch(10, 100), 0, 0))]);
		// Vote yes
		assert_ok!(Society::vote(RuntimeOrigin::signed(10), 20, true));
		// Vouched user can win
		conclude_intake(true, None);
		assert_eq!(members(), vec![10, 20]);
		// Vouched user gets whatever remains after the voucher's reservation.
		assert_eq!(
			Payouts::<Test>::get(20),
			PayoutRecord { paid: 0, payouts: vec![(8, 900)].try_into().unwrap() }
		);
		// 10 is no longer vouching
		assert_eq!(Members::<Test>::get(10).unwrap().vouching, None);
	});
}

#[test]
fn paid_vouch_works() {
	EnvBuilder::new().execute(|| {
		place_members([20]);
		assert_eq!(members(), vec![10, 20]);

		assert_ok!(Society::vouch(Origin::signed(20), 30, 1000, 100));
		assert_eq!(Members::<Test>::get(20).unwrap().vouching, Some(VouchingStatus::Vouching));
		assert_eq!(Bids::<Test>::get().into_inner(), vec![bid(30, Vouch(20, 100), 1000)]);

		next_intake();
		assert_eq!(candidacies(), vec![(30, candidacy(1, 1000, Vouch(20, 100), 0, 0))]);
		assert_ok!(Society::vote(Origin::signed(20), 30, true));
		conclude_intake(true, None);

		assert_eq!(members(), vec![10, 20, 30]);
		// Voucher wins a portion of the payment
		assert_eq!(
			Payouts::<Test>::get(20),
			PayoutRecord { paid: 0, payouts: vec![(8, 100)].try_into().unwrap() }
		);
		// Vouched user wins the rest
		assert_eq!(
			Payouts::<Test>::get(30),
			PayoutRecord { paid: 0, payouts: vec![(8, 900)].try_into().unwrap() }
		);
		// 20 is no longer vouching
		assert_eq!(Members::<Test>::get(20).unwrap().vouching, None);
	});
}

#[test]
fn voucher_cannot_win_more_than_bid() {
	EnvBuilder::new().execute(|| {
		place_members([20]);
		// 20 vouches, but asks for more than the bid
		assert_ok!(Society::vouch(Origin::signed(20), 30, 100, 1000));
		// Vouching creates the right kind of bid
		assert_eq!(Bids::<Test>::get().into_inner(), vec![bid(30, Vouch(20, 1000), 100)]);
		// Vouched user can become candidate
		next_intake();
		assert_eq!(candidacies(), vec![(30, candidacy(1, 100, Vouch(20, 1000), 0, 0))]);
		// Vote yes
		assert_ok!(Society::vote(Origin::signed(20), 30, true));
		// Vouched user can win
		conclude_intake(true, None);
		assert_eq!(members(), vec![10, 20, 30]);
		// Voucher wins as much as the bid
		assert_eq!(
			Payouts::<Test>::get(20),
			PayoutRecord { paid: 0, payouts: vec![(8, 100)].try_into().unwrap() }
		);
		// Vouched user gets nothing
		assert_eq!(
			Payouts::<Test>::get(30),
			PayoutRecord { paid: 0, payouts: vec![].try_into().unwrap() }
		);
	});
}

#[test]
fn unvouch_works() {
	EnvBuilder::new().execute(|| {
		// 10 is the only member
		assert_eq!(members(), vec![10]);
		// 10 vouches for 20
		assert_ok!(Society::vouch(RuntimeOrigin::signed(10), 20, 100, 0));
		// 20 has a bid
		assert_eq!(Bids::<Test>::get().into_inner(), vec![bid(20, Vouch(10, 0), 100)]);
		// 10 is vouched
		assert_eq!(Members::<Test>::get(10).unwrap().vouching, Some(VouchingStatus::Vouching));
		// 10 can unvouch
		assert_ok!(Society::unvouch(Origin::signed(10)));
		// 20 no longer has a bid
		assert_eq!(Bids::<Test>::get().into_inner(), vec![]);
		// 10 is no longer vouching
		assert_eq!(Members::<Test>::get(10).unwrap().vouching, None);

		// Cannot unvouch after they become candidate
		assert_ok!(Society::vouch(Origin::signed(10), 20, 100, 0));
		next_intake();
		assert_eq!(candidacies(), vec![(20, candidacy(1, 100, Vouch(10, 0), 0, 0))]);
		assert_noop!(Society::unvouch(Origin::signed(10)), Error::<Test>::NotVouchingOnBidder);

		// 10 is still vouching until candidate is approved or rejected
		assert_eq!(Members::<Test>::get(10).unwrap().vouching, Some(VouchingStatus::Vouching));
		// Voucher inexplicably votes against their pick.
		assert_ok!(Society::vote(Origin::signed(10), 20, false));
		// But their pick doesn't resign (yet).
		conclude_intake(false, None);
		// Voting still happening and voucher cannot unvouch.
		assert_eq!(candidacies(), vec![(20, candidacy(1, 100, Vouch(10, 0), 0, 1))]);
		assert_eq!(Members::<Test>::get(10).unwrap().vouching, Some(VouchingStatus::Vouching));

		// Candidate gives in and resigns.
		conclude_intake(true, None);
		// Vouxher (10) is banned from vouching.
		assert_eq!(Members::<Test>::get(10).unwrap().vouching, Some(VouchingStatus::Banned));
		assert_eq!(members(), vec![10]);

		// 10 cannot vouch again
		assert_noop!(
			Society::vouch(Origin::signed(10), 30, 100, 0),
			Error::<Test>::AlreadyVouching
		);
		// 10 cannot unvouch either, so they are banned forever.
		assert_noop!(Society::unvouch(Origin::signed(10)), Error::<Test>::NotVouchingOnBidder);
	});
}

#[test]
fn unbid_vouch_works() {
	EnvBuilder::new().execute(|| {
		// 10 is the only member
		assert_eq!(members(), vec![10]);
		// 10 vouches for 20
		assert_ok!(Society::vouch(RuntimeOrigin::signed(10), 20, 100, 0));
		// 20 has a bid
		assert_eq!(Bids::<Test>::get().into_inner(), vec![bid(20, Vouch(10, 0), 100)]);
		// 10 is vouched
		assert_eq!(Members::<Test>::get(10).unwrap().vouching, Some(VouchingStatus::Vouching));
		// 20 doesn't want to be a member and can unbid themselves.
		assert_ok!(Society::unbid(Origin::signed(20)));
		// Everything is cleaned up
		assert_eq!(Members::<Test>::get(10).unwrap().vouching, None);
		assert_eq!(Bids::<Test>::get().into_inner(), vec![]);
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
		conclude_intake(false, None);
		assert_eq!(Members::<Test>::get(10).unwrap().strikes, 1);
		assert_ok!(Society::bid(Origin::signed(30), 0));
		next_intake();
		conclude_intake(false, None);
		assert_eq!(Members::<Test>::get(10).unwrap().strikes, 2);
		// Awkwardly they can obtain more than MAX_STRIKES...
		assert_ok!(Society::bid(Origin::signed(40), 0));
		next_intake();
		conclude_intake(false, None);
		assert_eq!(Members::<Test>::get(10).unwrap().strikes, 3);

		// Replace the head
		assert_ok!(Society::bid(Origin::signed(50), 0));
		next_intake();
		assert_ok!(Society::vote(Origin::signed(10), 50, true));
		conclude_intake(false, None);
		assert_eq!(members(), vec![10, 50]);
		assert_eq!(Head::<Test>::get(), Some(10));
		next_intake();
		assert_eq!(Head::<Test>::get(), Some(50));
		// Founder is unchanged
		assert_eq!(Founder::<Test>::get(), Some(10));

		// 50 can still accumulate strikes
		assert_ok!(Society::bid(Origin::signed(60), 0));
		next_intake();
		// Force 50 to be Skeptic so it gets a strike.
		Skeptic::<Test>::put(50);
		conclude_intake(false, None);
		assert_eq!(Members::<Test>::get(50).unwrap().strikes, 1);
		assert_ok!(Society::bid(Origin::signed(70), 0));
		next_intake();
		// Force 50 to be Skeptic so it gets a strike.
		Skeptic::<Test>::put(50);
		conclude_intake(false, None);
		assert_eq!(Members::<Test>::get(50).unwrap().strikes, 2);

		// Replace the head
		assert_ok!(Society::bid(Origin::signed(80), 0));
		next_intake();
		assert_ok!(Society::vote(Origin::signed(10), 80, true));
		assert_ok!(Society::vote(Origin::signed(50), 80, true));
		conclude_intake(false, None);
		next_intake();
		assert_eq!(members(), vec![10, 50, 80]);
		assert_eq!(Head::<Test>::get(), Some(80));
		assert_eq!(Founder::<Test>::get(), Some(10));

		// 50 can now be suspended for strikes
		assert_ok!(Society::bid(Origin::signed(90), 0));
		next_intake();
		// Force 50 to be Skeptic and get it a strike.
		Skeptic::<Test>::put(50);
		conclude_intake(false, None);
		next_intake();
		assert_eq!(
			SuspendedMembers::<Test>::get(50),
			Some(MemberRecord { rank: 0, strikes: 3, vouching: None, index: 1 })
		);
		assert_eq!(members(), vec![10, 80]);
	});
}

#[test]
fn challenges_work() {
	EnvBuilder::new().execute(|| {
		// Add some members
		place_members([20, 30, 40]);
		// Votes are empty
		assert_eq!(DefenderVotes::<Test>::get(0, 10), None);
		assert_eq!(DefenderVotes::<Test>::get(0, 20), None);
		assert_eq!(DefenderVotes::<Test>::get(0, 30), None);
		assert_eq!(DefenderVotes::<Test>::get(0, 40), None);
		// Check starting point
		assert_eq!(members(), vec![10, 20, 30, 40]);
		assert_eq!(Defending::<Test>::get(), None);

		// 30 will be challenged during the challenge rotation
		next_challenge();
		assert_eq!(Defending::<Test>::get().unwrap().0, 30);
		// They can always free vote for themselves
		assert_ok!(Society::defender_vote(Origin::signed(30), true));

		// If no one else votes, nothing happens
		next_challenge();
		assert_eq!(members(), vec![10, 20, 30, 40]);
		// Reset votes for last challenge
		assert_ok!(Society::cleanup_challenge(Origin::signed(0), 0, 10));
		// New challenge period
		assert_eq!(Defending::<Test>::get().unwrap().0, 30);
		// Non-member cannot vote
		assert_noop!(Society::defender_vote(Origin::signed(1), true), Error::<Test>::NotMember);
		// 3 people say accept, 1 reject
		assert_ok!(Society::defender_vote(Origin::signed(10), true));
		assert_ok!(Society::defender_vote(Origin::signed(20), true));
		assert_ok!(Society::defender_vote(Origin::signed(30), true));
		assert_ok!(Society::defender_vote(Origin::signed(40), false));

		next_challenge();
		// 30 survives
		assert_eq!(members(), vec![10, 20, 30, 40]);
		// Reset votes for last challenge
		assert_ok!(Society::cleanup_challenge(Origin::signed(0), 1, 10));
		// Votes are reset
		assert_eq!(DefenderVotes::<Test>::get(0, 10), None);
		assert_eq!(DefenderVotes::<Test>::get(0, 20), None);
		assert_eq!(DefenderVotes::<Test>::get(0, 30), None);
		assert_eq!(DefenderVotes::<Test>::get(0, 40), None);

		// One more time
		assert_eq!(Defending::<Test>::get().unwrap().0, 30);
		// 2 people say accept, 2 reject
		assert_ok!(Society::defender_vote(Origin::signed(10), true));
		assert_ok!(Society::defender_vote(Origin::signed(20), true));
		assert_ok!(Society::defender_vote(Origin::signed(30), false));
		assert_ok!(Society::defender_vote(Origin::signed(40), false));

		next_challenge();
		// 30 is suspended
		assert_eq!(members(), vec![10, 20, 40]);
		assert_eq!(
			SuspendedMembers::<Test>::get(30),
			Some(MemberRecord { rank: 0, strikes: 0, vouching: None, index: 2 })
		);
		// Reset votes for last challenge
		assert_ok!(Society::cleanup_challenge(Origin::signed(0), 2, 10));
		// New defender is chosen
		assert_eq!(Defending::<Test>::get().unwrap().0, 20);
		// Votes are reset
		assert_eq!(DefenderVotes::<Test>::get(0, 10), None);
		assert_eq!(DefenderVotes::<Test>::get(0, 20), None);
		assert_eq!(DefenderVotes::<Test>::get(0, 30), None);
		assert_eq!(DefenderVotes::<Test>::get(0, 40), None);
	});
}

#[test]
fn bad_vote_slash_works() {
	EnvBuilder::new().execute(|| {
		// Add some members
		place_members([20, 30, 40, 50]);
		assert_eq!(members(), vec![10, 20, 30, 40, 50]);
		// Create some payouts
		Society::bump_payout(&20, 5, 100);
		Society::bump_payout(&30, 5, 100);
		Society::bump_payout(&40, 5, 100);
		Society::bump_payout(&50, 5, 100);
		// Check starting point
		assert_eq!(
			Payouts::<Test>::get(20),
			PayoutRecord { paid: 0, payouts: vec![(5, 100)].try_into().unwrap() }
		);
		assert_eq!(
			Payouts::<Test>::get(30),
			PayoutRecord { paid: 0, payouts: vec![(5, 100)].try_into().unwrap() }
		);
		assert_eq!(
			Payouts::<Test>::get(40),
			PayoutRecord { paid: 0, payouts: vec![(5, 100)].try_into().unwrap() }
		);
		assert_eq!(
			Payouts::<Test>::get(50),
			PayoutRecord { paid: 0, payouts: vec![(5, 100)].try_into().unwrap() }
		);
		// Create a new bid
		assert_ok!(Society::bid(Origin::signed(60), 1000));
		next_intake();
		// Force 20 to be the skeptic, and make it vote against the settled majority.
		Skeptic::<Test>::put(20);
		assert_ok!(Society::vote(Origin::signed(20), 60, true));
		assert_ok!(Society::vote(Origin::signed(30), 60, false));
		assert_ok!(Society::vote(Origin::signed(40), 60, false));
		assert_ok!(Society::vote(Origin::signed(50), 60, false));
		conclude_intake(false, None);
		// Wrong voter gained a strike
		assert_eq!(Members::<Test>::get(20).unwrap().strikes, 1);
		assert_eq!(Members::<Test>::get(30).unwrap().strikes, 0);
		assert_eq!(Members::<Test>::get(40).unwrap().strikes, 0);
		assert_eq!(Members::<Test>::get(50).unwrap().strikes, 0);
		// Their payout is slashed, a random person is rewarded
		assert_eq!(
			Payouts::<Test>::get(20),
			PayoutRecord { paid: 0, payouts: vec![(5, 50)].try_into().unwrap() }
		);
		assert_eq!(
			Payouts::<Test>::get(30),
			PayoutRecord { paid: 0, payouts: vec![(5, 100)].try_into().unwrap() }
		);
		assert_eq!(
			Payouts::<Test>::get(40),
			PayoutRecord { paid: 0, payouts: vec![(5, 100)].try_into().unwrap() }
		);
		assert_eq!(
			Payouts::<Test>::get(50),
			PayoutRecord { paid: 0, payouts: vec![(5, 100)].try_into().unwrap() }
		);
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
		place_members([50]);
		assert_noop!(Society::vouch(Origin::signed(50), 20, 100, 100), Error::<Test>::AlreadyBid);
	});
}

#[test]
fn vouching_handles_removed_member_with_bid() {
	EnvBuilder::new().execute(|| {
		// Add a member
		place_members([20]);
		// Have that member vouch for a user
		assert_ok!(Society::vouch(RuntimeOrigin::signed(20), 30, 1000, 100));
		// That user is now a bid and the member is vouching
		assert_eq!(Bids::<Test>::get().into_inner(), vec![bid(30, Vouch(20, 100), 1000)]);
		assert_eq!(Members::<Test>::get(20).unwrap().vouching, Some(VouchingStatus::Vouching));
		// Suspend that member
		assert_ok!(Society::suspend_member(&20));
		// Bid is removed, vouching status is removed
		let r = MemberRecord { rank: 0, strikes: 0, vouching: None, index: 1 };
		assert_eq!(SuspendedMembers::<Test>::get(20), Some(r));
		assert_eq!(Bids::<Test>::get().into_inner(), vec![]);
		assert_eq!(Members::<Test>::get(20), None);
	});
}

#[test]
fn vouching_handles_removed_member_with_candidate() {
	EnvBuilder::new().execute(|| {
		// Add a member
		place_members([20]);
		// Have that member vouch for a user
		assert_ok!(Society::vouch(RuntimeOrigin::signed(20), 30, 1000, 100));
		// That user is now a bid and the member is vouching
		assert_eq!(Bids::<Test>::get().into_inner(), vec![bid(30, Vouch(20, 100), 1000)]);
		assert_eq!(Members::<Test>::get(20).unwrap().vouching, Some(VouchingStatus::Vouching));

		// Make that bid a candidate
		next_intake();
		assert_eq!(candidacies(), vec![(30, candidacy(1, 1000, Vouch(20, 100), 0, 0))]);
		// Suspend that member
		assert_ok!(Society::suspend_member(&20));
		assert_eq!(SuspendedMembers::<Test>::contains_key(20), true);

		// Nothing changes yet in the candidacy, though the member now forgets.
		assert_eq!(candidacies(), vec![(30, candidacy(1, 1000, Vouch(20, 100), 0, 0))]);

		// Candidate wins
		assert_ok!(Society::vote(Origin::signed(10), 30, true));
		conclude_intake(false, None);
		assert_eq!(members(), vec![10, 30]);
		// Payout does not go to removed member
		assert_eq!(
			Payouts::<Test>::get(20),
			PayoutRecord { paid: 0, payouts: vec![].try_into().unwrap() }
		);
		assert_eq!(
			Payouts::<Test>::get(30),
			PayoutRecord { paid: 0, payouts: vec![(8, 1000)].try_into().unwrap() }
		);
	});
}

#[test]
fn votes_are_working() {
	EnvBuilder::new().execute(|| {
		place_members([20]);
		// Users make bids of various amounts
		assert_ok!(Society::bid(RuntimeOrigin::signed(50), 500));
		assert_ok!(Society::bid(RuntimeOrigin::signed(40), 400));
		assert_ok!(Society::bid(RuntimeOrigin::signed(30), 300));
		// Rotate period
		next_intake();
		// A member votes for these candidates to join the society
		assert_ok!(Society::vote(Origin::signed(10), 30, true));
		assert_ok!(Society::vote(Origin::signed(20), 30, true));
		assert_ok!(Society::vote(Origin::signed(10), 40, true));
		// You cannot vote for a non-candidate
		assert_noop!(Society::vote(Origin::signed(10), 50, true), Error::<Test>::NotCandidate);
		// Votes are stored
		assert_eq!(Votes::<Test>::get(30, 10), Some(Vote { approve: true, weight: 4 }));
		assert_eq!(Votes::<Test>::get(30, 20), Some(Vote { approve: true, weight: 1 }));
		assert_eq!(Votes::<Test>::get(40, 10), Some(Vote { approve: true, weight: 4 }));
		assert_eq!(Votes::<Test>::get(50, 10), None);
		conclude_intake(false, None);
		// Cleanup the candidacy
		assert_ok!(Society::cleanup_candidacy(Origin::signed(0), 30, 10));
		assert_ok!(Society::cleanup_candidacy(Origin::signed(0), 40, 10));
		// Candidates become members after a period rotation
		assert_eq!(members(), vec![10, 20, 30, 40]);
		// Votes are cleaned up
		assert_eq!(Votes::<Test>::get(30, 10), None);
		assert_eq!(Votes::<Test>::get(30, 20), None);
		assert_eq!(Votes::<Test>::get(40, 10), None);
	});
}

#[test]
fn max_bids_work() {
	EnvBuilder::new().execute(|| {
		// Max bids is 1000, when extra bids come in, it pops the larger ones off the stack.
		// Try to put 1010 users into the bid pool
		for i in (0..=10).rev() {
			// Give them some funds and bid
			let _ = Balances::make_free_balance_be(&((i + 100) as u128), 1000);
			assert_ok!(Society::bid(Origin::signed((i + 100) as u128), i));
		}
		let bids = Bids::<Test>::get();
		// Length is 1000
		assert_eq!(bids.len(), 10);
		// First bid is smallest number (100)
		assert_eq!(bids[0], bid(100, Deposit(25), 0));
		// Last bid is smallest number + 99 (1099)
		assert_eq!(bids[9], bid(109, Deposit(25), 9));
	});
}

#[test]
fn candidates_are_limited_by_membership_size() {
	EnvBuilder::new().execute(|| {
		// Fill up some membership
		place_members([1, 2, 3, 4, 5, 6, 7, 8]);
		// One place left from 10
		assert_eq!(members().len(), 9);

		assert_ok!(Society::bid(Origin::signed(20), 0));
		assert_ok!(Society::bid(Origin::signed(30), 1));
		next_intake();
		assert_eq!(candidates().len(), 1);
	});
}

#[test]
fn candidates_are_limited_by_maximum() {
	EnvBuilder::new().execute(|| {
		// Nine places left from 10
		assert_eq!(members().len(), 1);

		// Nine bids
		for i in (1..=9).rev() {
			// Give them some funds and bid
			let _ = Balances::make_free_balance_be(&((i + 100) as u128), 1000);
			assert_ok!(Society::bid(Origin::signed((i + 100) as u128), i));
		}
		next_intake();

		// Still only 8 candidates.
		assert_eq!(candidates().len(), 8);
	});
}

#[test]
fn too_many_candidates_cannot_overflow_membership() {
	EnvBuilder::new().execute(|| {
		// One place left
		place_members([1, 2, 3, 4, 5, 6, 7, 8]);
		assert_ok!(Society::bid(Origin::signed(20), 0));
		assert_ok!(Society::bid(Origin::signed(30), 1));
		next_intake();
		// Candidate says a candidate.
		next_intake();
		// Another candidate taken.
		// Both approved.
		assert_ok!(Society::vote(Origin::signed(10), 20, true));
		assert_ok!(Society::vote(Origin::signed(10), 30, true));
		next_voting();
		assert_ok!(Society::claim_membership(Origin::signed(20)));
		assert_noop!(Society::claim_membership(Origin::signed(30)), Error::<Test>::MaxMembers);

		// Maximum members.
		assert_eq!(members().len(), 10);
		// Still 1 candidate.
		assert_eq!(candidates().len(), 1);

		// Increase max-members and the candidate can get in.
		assert_ok!(Society::set_parameters(Origin::signed(10), 11, 8, 3, 25));
		assert_ok!(Society::claim_membership(Origin::signed(30)));
	});
}

#[test]
fn zero_bid_works() {
	// This tests:
	// * Only one zero bid is selected.
	// * That zero bid is placed as head when accepted.
	EnvBuilder::new().execute(|| {
		// Users make bids of various amounts
		assert_ok!(Society::bid(RuntimeOrigin::signed(60), 400));
		assert_ok!(Society::bid(RuntimeOrigin::signed(50), 300));
		assert_ok!(Society::bid(RuntimeOrigin::signed(30), 0));
		assert_ok!(Society::bid(RuntimeOrigin::signed(20), 0));
		assert_ok!(Society::bid(RuntimeOrigin::signed(40), 0));

		// Rotate period
		next_intake();
		// Pot is 1000 after "PeriodSpend"
		assert_eq!(Pot::<Test>::get(), 1000);
		assert_eq!(Balances::free_balance(Society::account_id()), 10_000);
		// Choose smallest bidding users whose total is less than pot, with only one zero bid.
		assert_eq!(
			candidacies(),
			vec![
				(30, candidacy(1, 0, Deposit(25), 0, 0)),
				(50, candidacy(1, 300, Deposit(25), 0, 0)),
				(60, candidacy(1, 400, Deposit(25), 0, 0)),
			]
		);
		assert_eq!(Bids::<Test>::get(), vec![bid(20, Deposit(25), 0), bid(40, Deposit(25), 0),],);
		// A member votes for these candidates to join the society
		assert_ok!(Society::vote(Origin::signed(10), 30, true));
		assert_ok!(Society::vote(Origin::signed(10), 50, true));
		assert_ok!(Society::vote(Origin::signed(10), 60, true));
		conclude_intake(false, None);
		// Candidates become members after a period rotation
		assert_eq!(members(), vec![10, 30, 50, 60]);
		next_intake();
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
				let who = 100 + (i * 5 + j) as u128;
				let _ = Balances::make_free_balance_be(&who, 1000);
				assert_ok!(Society::bid(Origin::signed(who), j));
			}
		}

		let mut final_list = Vec::new();

		for j in 0..5 {
			for i in 0..5 {
				final_list.push(bid(100 + (i * 5 + j) as u128, Deposit(25), j));
			}
		}
		let max_bids: u32 = <Test as Config>::MaxBids::get();
		final_list.truncate(max_bids as usize);
		assert_eq!(Bids::<Test>::get(), final_list);
	});
}

#[test]
fn waive_repay_works() {
	EnvBuilder::new().execute(|| {
		place_members([20, 30]);
		Society::bump_payout(&20, 5, 100);
		assert_eq!(
			Payouts::<Test>::get(20),
			PayoutRecord { paid: 0, payouts: vec![(5, 100)].try_into().unwrap() }
		);
		assert_eq!(Members::<Test>::get(20).unwrap().rank, 0);
		assert_ok!(Society::waive_repay(Origin::signed(20), 100));
		assert_eq!(
			Payouts::<Test>::get(20),
			PayoutRecord { paid: 0, payouts: vec![].try_into().unwrap() }
		);
		assert_eq!(Members::<Test>::get(10).unwrap().rank, 1);
		assert_eq!(Balances::free_balance(20), 50);
	});
}

#[test]
fn punish_skeptic_works() {
	EnvBuilder::new().execute(|| {
		place_members([20]);
		assert_ok!(Society::bid(Origin::signed(30), 0));
		next_intake();
		// Force 20 to be Skeptic so it gets a strike.
		Skeptic::<Test>::put(20);
		next_voting();
		// 30 decides to punish the skeptic (20).
		assert_ok!(Society::punish_skeptic(Origin::signed(30)));
		// 20 gets 1 strike.
		assert_eq!(Members::<Test>::get(20).unwrap().strikes, 1);
		let candidacy = Candidates::<Test>::get(&30).unwrap();
		// 30 candidacy has changed.
		assert_eq!(candidacy.skeptic_struck, true);
	});
}

#[test]
fn resign_candidacy_works() {
	EnvBuilder::new().execute(|| {
		assert_ok!(Society::bid(Origin::signed(30), 45));
		next_intake();
		assert_eq!(candidates(), vec![30]);
		assert_ok!(Society::resign_candidacy(Origin::signed(30)));
		// 30 candidacy has gone.
		assert_eq!(candidates(), vec![]);
	});
}

#[test]
fn drop_candidate_works() {
	EnvBuilder::new().execute(|| {
		place_members([20, 30]);
		assert_ok!(Society::bid(Origin::signed(40), 45));
		next_intake();
		assert_eq!(candidates(), vec![40]);
		assert_ok!(Society::vote(Origin::signed(10), 40, false));
		assert_ok!(Society::vote(Origin::signed(20), 40, false));
		assert_ok!(Society::vote(Origin::signed(30), 40, false));
		run_to_block(12);
		assert_ok!(Society::drop_candidate(Origin::signed(50), 40));
		// 40 candidacy has gone.
		assert_eq!(candidates(), vec![]);
	});
}
