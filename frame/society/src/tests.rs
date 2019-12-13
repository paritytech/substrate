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
		// Account 1 is set as the founder origin and can start a society
		// This allows the module to bootstrap on an already running chain

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
		assert_ok!(Society::bid(Origin::signed(20), 1000));
		assert_ok!(Society::bid(Origin::signed(30), 0));
		assert_eq!(Balances::free_balance(30), 25);

		assert_noop!(Society::unbid(Origin::signed(30), 1), "bad position");
		assert_ok!(Society::unbid(Origin::signed(30), 0));
		assert_eq!(Balances::free_balance(30), 50);

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
		assert_ok!(Society::bid(Origin::signed(20), 0));
		run_to_block(4);
		assert_eq!(Society::candidates(), vec![(0, 20, BidKind::Deposit(25))]);
		assert_ok!(Society::vote(Origin::signed(10), 20, false));
		run_to_block(8);
		assert_eq!(Society::members(), vec![10]);
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
		assert_eq!(Society::slash_payout(&20, 500), (9, 500));
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
		assert_eq!(Society::slash_payout(&20, 250), (15, 250));
		assert_eq!(Payouts::<Test>::get(20), vec![(15, 50), (20, 100)]);
		// slash again
		assert_eq!(Society::slash_payout(&20, 50), (20, 50));
		assert_eq!(Payouts::<Test>::get(20), vec![(20, 100)]);
	});
}

#[test]
fn suspended_member_lifecycle_works() {
	EnvBuilder::new().execute(|| {
		assert_eq!(Strikes::<Test>::get(10), 0);
		assert_eq!(<SuspendedMembers<Test>>::get(10), None);

		// Let's suspend account 10 by giving them 2 strikes by not voting
		assert_ok!(Society::bid(Origin::signed(20), 0));
		run_to_block(8);
		assert_eq!(Strikes::<Test>::get(10), 1);
		assert_ok!(Society::bid(Origin::signed(20), 0));
		run_to_block(16);

		// Strike 2 is accumulated, and 10 is suspended :(
		assert_eq!(<SuspendedMembers<Test>>::get(10), Some(16));
		assert_eq!(<Members<Test>>::get(), vec![]);

		// Suspended members cannot get payout
		Society::bump_payout(&10, 10, 100);
		assert_noop!(Society::payout(Origin::signed(10)), "account is suspended");

		// Move 10 blocks to the future
		run_to_block(26);
		
		// Normal people cannot make judgement
		assert_noop!(Society::judge_suspended_member(Origin::signed(10), 10, true), "Invalid origin");

		// Founder origin can judge thee
		// Founder forgives the suspended member
		assert_ok!(Society::judge_suspended_member(Origin::signed(1), 10, true));
		assert_eq!(<SuspendedMembers<Test>>::get(10), None);
		assert_eq!(<Members<Test>>::get(), vec![10]);
		// Suspended member has increased payout time due to suspension period
		assert_eq!(<Payouts<Test>>::get(10), vec![(20, 100)]);

		// Let's suspend them again, directly
		Society::suspend_member(&10);
		assert_eq!(<SuspendedMembers<Test>>::get(10), Some(26));
		// Founder does not forgive the suspended member
		assert_ok!(Society::judge_suspended_member(Origin::signed(1), 10, false));
		// Cleaned up
		assert_eq!(<SuspendedMembers<Test>>::get(10), None);
		assert_eq!(<Members<Test>>::get(), vec![]);
		assert_eq!(<Payouts<Test>>::get(10), vec![]);
	});
}
