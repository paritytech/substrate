// Copyright 2019 Parity Technologies (UK) Ltd.
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

//! Tests for the module.

use super::*;
use mock::*;

use support::{assert_ok, assert_noop};

#[test]
fn founding_works() {
	EnvBuilder::new().with_members(vec![]).execute(|| {
		// Account 1 is set as the founder origin
		// Account 5 cannot start a society
		assert_noop!(Society::found(Origin::signed(5), 20), "Invalid origin");
		// Account 1 can start a society, where 10 is the founding member
		assert_ok!(Society::found(Origin::signed(1), 10));
		// Society members only include 10
		assert_eq!(Society::members(), vec![10]);
		// 10 is the head of the society
		assert_eq!(Society::head(), Some(10));
		// Cannot start another society
		assert_noop!(Society::found(Origin::signed(1), 20), "already founded");
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
		run_to_block(4);
		// 20 is now a candidate
		assert_eq!(Society::candidates(), vec![(0, 20, BidKind::Deposit(25))]);
		// 10 (a member) can vote for the candidate
		assert_ok!(Society::vote(Origin::signed(10), 20, true));
		// Rotate period every 4 blocks
		run_to_block(8);
		// 20 is now a member of the society
		assert_eq!(Society::members(), vec![10, 20]);
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
		run_to_block(4);
		// Pot is 1000 after "PeriodSpend"
		assert_eq!(Society::pot(), 1000);
		assert_eq!(Balances::free_balance(Society::account_id()), 10_000);
		// Choose smallest bidding users whose total is less than pot
		assert_eq!(Society::candidates(), vec![
			(300, 30, BidKind::Deposit(25)),
			(400, 40, BidKind::Deposit(25)),
		]);
		// A member votes for these candidates to join the society
		assert_ok!(Society::vote(Origin::signed(10), 30, true));
		assert_ok!(Society::vote(Origin::signed(10), 40, true));
		run_to_block(8);
		// Candidates become members after a period rotation
		assert_eq!(Society::members(), vec![10, 30, 40]);
		// Pot is increased by 1000, but pays out 700 to the members
		assert_eq!(Balances::free_balance(Society::account_id()), 9_300);
		assert_eq!(Society::pot(), 1_300);
		// Left over from the original bids is 50 who satisfies the condition of bid less than pot.
		assert_eq!(Society::candidates(), vec![ (500, 50, BidKind::Deposit(25)) ]);
		// 40, now a member, can vote for 50
		assert_ok!(Society::vote(Origin::signed(40), 50, true));
		run_to_block(12);
		// 50 is now a member
		assert_eq!(Society::members(), vec![10, 30, 40, 50]);
		// Pot is increased by 1000, and 500 is paid out. Total payout so far is 1200.
		assert_eq!(Society::pot(), 1_800);
		assert_eq!(Balances::free_balance(Society::account_id()), 8_800);
		// No more candidates satisfy the requirements
		assert_eq!(Society::candidates(), vec![]);
		// Next period
		run_to_block(16);
		// Same members
		assert_eq!(Society::members(), vec![10, 30, 40, 50]);
		// Pot is increased by 1000 again
		assert_eq!(Society::pot(), 2_800);
		// No payouts
		assert_eq!(Balances::free_balance(Society::account_id()), 8_800);
		// Candidate 60 now qualifies based on the increased pot size.
		assert_eq!(Society::candidates(), vec![ (1900, 60, BidKind::Deposit(25)) ]);
		// Candidate 60 is voted in.
		assert_ok!(Society::vote(Origin::signed(50), 60, true));
		run_to_block(20);
		// 60 joins as a member
		assert_eq!(Society::members(), vec![10, 30, 40, 50, 60]);
		// Pay them
		assert_eq!(Society::pot(), 1_900);
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
		// Must know right position to unbid + cannot unbid someone else
		assert_noop!(Society::unbid(Origin::signed(30), 1), "bad position");
		// Can unbid themselves with the right position
		assert_ok!(Society::unbid(Origin::signed(30), 0));
		// Balance is returned
		assert_eq!(Balances::free_balance(30), 50);
		assert_eq!(Balances::reserved_balance(30), 0);
		// 20 wins candidacy
		run_to_block(4);
		assert_eq!(Society::candidates(), vec![ (1000, 20, BidKind::Deposit(25)) ]);
	});
}

#[test]
fn payout_works() {
	EnvBuilder::new().execute(|| {
		// Original balance of 50
		assert_eq!(Balances::free_balance(20), 50);
		assert_ok!(Society::bid(Origin::signed(20), 1000));
		run_to_block(4);
		assert_ok!(Society::vote(Origin::signed(10), 20, true));
		run_to_block(8);
		// payout not ready
		assert_noop!(Society::payout(Origin::signed(20)), "nothing to payout");
		run_to_block(9);
		// payout should be here
		assert_ok!(Society::payout(Origin::signed(20)));
		assert_eq!(Balances::free_balance(20), 1050);
	});
}

#[test]
fn basic_new_member_skeptic_works() {
	EnvBuilder::new().execute(|| {
		assert_eq!(Strikes::<Test>::get(10), 0);
		assert_ok!(Society::bid(Origin::signed(20), 0));
		run_to_block(4);
		assert_eq!(Society::candidates(), vec![(0, 20, BidKind::Deposit(25))]);
		run_to_block(8);
		assert_eq!(Society::members(), vec![10]);
		assert_eq!(Strikes::<Test>::get(10), 1);
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
		run_to_block(4);
		assert_eq!(Society::candidates(), vec![(0, 20, BidKind::Deposit(25))]);
		// We say no
		assert_ok!(Society::vote(Origin::signed(10), 20, false));
		run_to_block(8);
		// User is not added as member
		assert_eq!(Society::members(), vec![10]);
		// User is suspended
		assert_eq!(Society::candidates(), vec![]);
		assert_eq!(Society::suspended_candidate(20).is_some(), true);
	});
}

#[test]
fn slash_payout_works() {
	EnvBuilder::new().execute(|| {
		assert_eq!(Balances::free_balance(20), 50);
		assert_ok!(Society::bid(Origin::signed(20), 1000));
		run_to_block(4);
		assert_ok!(Society::vote(Origin::signed(10), 20, true));
		run_to_block(8);
		// payout in queue
		assert_eq!(Payouts::<Test>::get(20), vec![(9, 1000)]);
		assert_noop!(Society::payout(Origin::signed(20)), "nothing to payout");
		// slash payout
		assert_eq!(Society::slash_payout(&20, 500), 500);
		assert_eq!(Payouts::<Test>::get(20), vec![(9, 500)]);
		run_to_block(9);
		// payout should be here, but 500 less
		assert_ok!(Society::payout(Origin::signed(20)));
		assert_eq!(Balances::free_balance(20), 550);
	});
}

#[test]
fn slash_payout_multi_works() {
	EnvBuilder::new().execute(|| {
		assert_eq!(Balances::free_balance(20), 50);
		// create a few payouts
		Society::bump_payout(&20, 5, 100);
		Society::bump_payout(&20, 10, 100);
		Society::bump_payout(&20, 15, 100);
		Society::bump_payout(&20, 20, 100);
		// payouts in queue
		assert_eq!(Payouts::<Test>::get(20), vec![(5, 100), (10, 100), (15, 100), (20, 100)]);
		// slash payout
		assert_eq!(Society::slash_payout(&20, 250), 250);
		assert_eq!(Payouts::<Test>::get(20), vec![(15, 50), (20, 100)]);
		// slash again
		assert_eq!(Society::slash_payout(&20, 50), 50);
		assert_eq!(Payouts::<Test>::get(20), vec![(20, 100)]);
	});
}

#[test]
fn suspended_member_lifecycle_works() {
	EnvBuilder::new().execute(|| {
		// Add 20 to members, who is not the head and can be suspended/removed.
		assert_ok!(Society::add_member(&20));
		assert_eq!(<Members<Test>>::get(), vec![10, 20]);
		assert_eq!(Strikes::<Test>::get(20), 0);
		assert_eq!(<SuspendedMembers<Test>>::get(20), None);

		// Let's suspend account 20 by giving them 2 strikes by not voting
		assert_ok!(Society::bid(Origin::signed(30), 0));
		run_to_block(8);
		assert_eq!(Strikes::<Test>::get(20), 1);
		assert_ok!(Society::bid(Origin::signed(40), 0));
		run_to_block(16);

		// Strike 2 is accumulated, and 20 is suspended :(
		assert_eq!(<SuspendedMembers<Test>>::get(20), Some(()));
		assert_eq!(<Members<Test>>::get(), vec![10]);

		// Suspended members cannot get payout
		Society::bump_payout(&20, 10, 100);
		assert_noop!(Society::payout(Origin::signed(20)), "account is suspended");
		
		// Normal people cannot make judgement
		assert_noop!(Society::judge_suspended_member(Origin::signed(20), 20, true), "Invalid origin");

		// Suspension judgment origin can judge thee
		// Suspension judgement origin forgives the suspended member
		assert_ok!(Society::judge_suspended_member(Origin::signed(2), 20, true));
		assert_eq!(<SuspendedMembers<Test>>::get(20), None);
		assert_eq!(<Members<Test>>::get(), vec![10, 20]);

		// Let's suspend them again, directly
		Society::suspend_member(&20);
		assert_eq!(<SuspendedMembers<Test>>::get(20), Some(()));
		// Suspension judgement origin does not forgive the suspended member
		assert_ok!(Society::judge_suspended_member(Origin::signed(2), 20, false));
		// Cleaned up
		assert_eq!(<SuspendedMembers<Test>>::get(20), None);
		assert_eq!(<Members<Test>>::get(), vec![10]);
		assert_eq!(<Payouts<Test>>::get(20), vec![]);
	});
}

#[test]
fn suspended_candidate_rejected_works() {
	EnvBuilder::new().execute(|| {
		// Starting Balance
		assert_eq!(Balances::free_balance(20), 50);
		assert_eq!(Balances::free_balance(Society::account_id()), 10000);
		// 20 makes a bid
		assert_ok!(Society::bid(Origin::signed(20), 0));
		assert_eq!(Balances::free_balance(20), 25);
		assert_eq!(Balances::reserved_balance(20), 25);
		// Rotation Period
		run_to_block(4);
		assert_eq!(Society::candidates(), vec![(0, 20, BidKind::Deposit(25))]);
		// We say no
		assert_ok!(Society::vote(Origin::signed(10), 20, false));
		run_to_block(8);
		// User is not added as member
		assert_eq!(Society::members(), vec![10]);
		// User is suspended
		assert_eq!(Society::candidates(), vec![]);
		assert_eq!(Society::suspended_candidate(20).is_some(), true);

		// Normal user cannot make judgement on suspended candidate
		assert_noop!(Society::judge_suspended_candidate(Origin::signed(20), 20, Judgement::Approve), "Invalid origin");

		// Suspension judgement origin makes no direct judgement
		assert_ok!(Society::judge_suspended_candidate(Origin::signed(2), 20, Judgement::Rebid));
		// They are placed back in bid pool, repeat suspension process
		// Rotation Period
		run_to_block(12);
		assert_eq!(Society::candidates(), vec![(0, 20, BidKind::Deposit(25))]);
		// We say no
		assert_ok!(Society::vote(Origin::signed(10), 20, false));
		run_to_block(16);
		// User is not added as member
		assert_eq!(Society::members(), vec![10]);
		// User is suspended
		assert_eq!(Society::candidates(), vec![]);
		assert_eq!(Society::suspended_candidate(20).is_some(), true);

		// Suspension judgement origin rejects the candidate
		assert_ok!(Society::judge_suspended_candidate(Origin::signed(2), 20, Judgement::Reject));
		// User is slashed
		assert_eq!(Balances::free_balance(20), 25);
		assert_eq!(Balances::reserved_balance(20), 0);
		// Funds are deposited to society account
		assert_eq!(Balances::free_balance(Society::account_id()), 10025);
		// Cleaned up
		assert_eq!(Society::candidates(), vec![]);
		assert_eq!(<SuspendedCandidates<Test>>::get(20), None);
	});
}

#[test]
fn vouch_works() {
	EnvBuilder::new().execute(|| {
		// 10 is the only member
		assert_eq!(Society::members(), vec![10]);
		// A non-member cannot vouch
		assert_noop!(Society::vouch(Origin::signed(1), 20, 1000, 100), "not a member");
		// A member can though
		assert_ok!(Society::vouch(Origin::signed(10), 20, 1000, 100));
		assert_eq!(<Vouching<Test>>::get(), vec![10]);
		// A member cannot vouch twice at the same time
		assert_noop!(Society::vouch(Origin::signed(10), 30, 100, 0), "already vouching");
		// Vouching creates the right kind of bid
		assert_eq!(<Bids<Test>>::get(), vec![(1000, 20, BidKind::Vouch(10, 100))]);
		// Vouched user can become candidate
		run_to_block(4);
		assert_eq!(Society::candidates(), vec![(1000, 20, BidKind::Vouch(10, 100))]);
		// Vote yes
		assert_ok!(Society::vote(Origin::signed(10), 20, true));
		// Vouched user can win
		run_to_block(8);
		assert_eq!(Society::members(), vec![10, 20]);
		// Voucher wins a portion of the payment
		assert_eq!(<Payouts<Test>>::get(10), vec![(9, 100)]);
		// Vouched user wins the rest
		assert_eq!(<Payouts<Test>>::get(20), vec![(9, 900)]);
		// 10 is no longer vouching
		assert_eq!(<Vouching<Test>>::get(), vec![]);
	});
}

#[test]
fn voucher_cannot_win_more_than_bid() {
	EnvBuilder::new().execute(|| {
		// 10 is the only member
		assert_eq!(Society::members(), vec![10]);
		// 10 vouches, but asks for more than the bid
		assert_ok!(Society::vouch(Origin::signed(10), 20, 100, 1000));
		// Vouching creates the right kind of bid
		assert_eq!(<Bids<Test>>::get(), vec![(100, 20, BidKind::Vouch(10, 1000))]);
		// Vouched user can become candidate
		run_to_block(4);
		assert_eq!(Society::candidates(), vec![(100, 20, BidKind::Vouch(10, 1000))]);
		// Vote yes
		assert_ok!(Society::vote(Origin::signed(10), 20, true));
		// Vouched user can win
		run_to_block(8);
		assert_eq!(Society::members(), vec![10, 20]);
		// Voucher wins as much as the bid
		assert_eq!(<Payouts<Test>>::get(10), vec![(9, 100)]);
		// Vouched user gets nothing
		assert_eq!(<Payouts<Test>>::get(20), vec![]);
	});
}

#[test]
fn unvouch_works() {
	EnvBuilder::new().execute(|| {
		// 10 is the only member
		assert_eq!(Society::members(), vec![10]);
		// 10 vouches for 20
		assert_ok!(Society::vouch(Origin::signed(10), 20, 100, 0));
		// 20 has a bid
		assert_eq!(<Bids<Test>>::get(), vec![(100, 20, BidKind::Vouch(10, 0))]);
		// 10 is vouched
		assert_eq!(<Vouching<Test>>::get(), vec![10]);
		// To unvouch, you must know the right bid position
		assert_noop!(Society::unvouch(Origin::signed(10), 2), "bad position");
		// 10 can unvouch with the right position
		assert_ok!(Society::unvouch(Origin::signed(10), 0));
		// 20 no longer has a bid
		assert_eq!(<Bids<Test>>::get(), vec![]);
		// 10 is no longer vouching
		assert_eq!(<Vouching<Test>>::get(), vec![]);

		// Cannot unvouch after they become candidate
		assert_ok!(Society::vouch(Origin::signed(10), 20, 100, 0));
		run_to_block(4);
		assert_eq!(Society::candidates(), vec![(100, 20, BidKind::Vouch(10, 0))]);
		assert_noop!(Society::unvouch(Origin::signed(10), 0), "bad position");
		// 10 is still vouching until candidate is approved or rejected
		assert_eq!(<Vouching<Test>>::get(), vec![10]);
		run_to_block(8);
		// In this case member is denied and suspended
		assert!(Society::suspended_candidate(&20).is_some());
		assert_eq!(Society::members(), vec![10]);
		// User is stuck vouching until judgement origin resolves suspended candidate
		assert_eq!(<Vouching<Test>>::get(), vec![10]);
		// Judge denies candidate
		assert_ok!(Society::judge_suspended_candidate(Origin::signed(2), 20, Judgement::Reject));
		// 10 is finally unvouched
		assert_eq!(<Vouching<Test>>::get(), vec![]);
		assert_eq!(Society::members(), vec![10]);
	});
}

#[test]
fn unbid_vouch_works() {
	EnvBuilder::new().execute(|| {
		// 10 is the only member
		assert_eq!(Society::members(), vec![10]);
		// 10 vouches for 20
		assert_ok!(Society::vouch(Origin::signed(10), 20, 100, 0));
		// 20 has a bid
		assert_eq!(<Bids<Test>>::get(), vec![(100, 20, BidKind::Vouch(10, 0))]);
		// 10 is vouched
		assert_eq!(<Vouching<Test>>::get(), vec![10]);
		// 20 doesn't want to be a member and can unbid themselves.
		assert_ok!(Society::unbid(Origin::signed(20), 0));
		// Everything is cleaned up
		assert_eq!(<Vouching<Test>>::get(), vec![]);
		assert_eq!(<Bids<Test>>::get(), vec![]);
	});
}

#[test]
fn head_cannot_be_removed() {
	EnvBuilder::new().execute(|| {
		// 10 is the only member and head
		assert_eq!(Society::members(), vec![10]);
		assert_eq!(Society::head(), Some(10));
		// 10 can still accumulate strikes
		assert_ok!(Society::bid(Origin::signed(20), 0));
		run_to_block(8);
		assert_eq!(Strikes::<Test>::get(10), 1);
		assert_ok!(Society::bid(Origin::signed(30), 0));
		run_to_block(16);
		assert_eq!(Strikes::<Test>::get(10), 2);
		// Awkwardly they can obtain more than MAX_STRIKES...
		// TODO: Check if this is okay behavior
		assert_ok!(Society::vouch(Origin::signed(10), 40, 0, 0));
		run_to_block(24);
		assert_eq!(Strikes::<Test>::get(10), 3);

		// Replace the head
		assert_ok!(Society::bid(Origin::signed(50), 0));
		run_to_block(28);
		assert_ok!(Society::vote(Origin::signed(10), 50, true));
		run_to_block(32);
		assert_eq!(Society::members(), vec![10, 50]);
		assert_eq!(Society::head(), Some(50));

		// 10 can now be suspended for strikes
		assert_ok!(Society::judge_suspended_candidate(Origin::signed(2), 40, Judgement::Reject));
		assert_eq!(Strikes::<Test>::get(10), 0);
		assert_eq!(<SuspendedMembers<Test>>::get(10), Some(()));
		assert_eq!(Society::members(), vec![50]);
	});
}

#[test]
fn challenges_work() {
	EnvBuilder::new().execute(|| {
		// Add some members
		assert_ok!(Society::add_member(&20));
		assert_ok!(Society::add_member(&30));
		assert_ok!(Society::add_member(&40));
		// Check starting point
		assert_eq!(Society::members(), vec![10, 20, 30, 40]);
		assert_eq!(Society::defender(), None);
		// 20 will be challenged during the challenge rotation
		run_to_block(8);
		assert_eq!(Society::defender(), Some(20));
		// If no one votes, nothing happens
		run_to_block(16);
		assert_eq!(Society::members(), vec![10, 20, 30, 40]);
		// New challenge period
		assert_eq!(Society::defender(), Some(20));
		// Non-member cannot challenge
		assert_noop!(Society::defender_vote(Origin::signed(1), true), "not a member");
		// 2 people say accept, 2 reject
		assert_ok!(Society::defender_vote(Origin::signed(10), true));
		assert_ok!(Society::defender_vote(Origin::signed(20), true));
		assert_ok!(Society::defender_vote(Origin::signed(30), false));
		assert_ok!(Society::defender_vote(Origin::signed(40), false));
		run_to_block(24);
		// 20 survives
		assert_eq!(Society::members(), vec![10, 20, 30, 40]);
		// One more time
		assert_eq!(Society::defender(), Some(20));
		// 3 people reject
		assert_ok!(Society::defender_vote(Origin::signed(10), false));
		assert_ok!(Society::defender_vote(Origin::signed(20), true));
		assert_ok!(Society::defender_vote(Origin::signed(30), false));
		assert_ok!(Society::defender_vote(Origin::signed(40), false));
		run_to_block(32);
		// 20 is suspended
		assert_eq!(Society::members(), vec![10, 30, 40]);
		assert_eq!(Society::suspended_member(20), Some(()));
		// New defender is chosen
		assert_eq!(Society::defender(), Some(40));
	});
}
