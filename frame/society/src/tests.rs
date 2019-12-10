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
		assert_noop!(Society::found(Origin::signed(5), 20), "Invalid origin");
		assert_ok!(Society::found(Origin::signed(1), 10));
		assert_eq!(Society::members(), vec![10]);
		assert_eq!(Society::head(), Some(10));
		assert_noop!(Society::found(Origin::signed(1), 20), "already founded");
	});
}

#[test]
fn basic_new_member_works() {
	EnvBuilder::new().execute(|| {
		assert_ok!(Society::bid(Origin::signed(20), 0));
		run_to_block(4);
		assert_eq!(Society::candidates(), vec![(0, 20, BidKind::Deposit(25))]);
		assert_ok!(Society::vote(Origin::signed(10), 20, true));
		run_to_block(8);
		assert_eq!(Society::members(), vec![10, 20]);
	});
}

#[test]
fn bidding_works() {
	EnvBuilder::new().execute(|| {
		assert_ok!(Society::bid(Origin::signed(60), 1900));
		assert_ok!(Society::bid(Origin::signed(50), 500));
		assert_ok!(Society::bid(Origin::signed(40), 400));
		assert_ok!(Society::bid(Origin::signed(30), 300));
		run_to_block(4);
		assert_eq!(Society::candidates(), vec![
			(300, 30, BidKind::Deposit(25)),
			(400, 40, BidKind::Deposit(25)),
		]);
		assert_eq!(Balances::free_balance(Society::account_id()), 10_000);
		assert_eq!(Society::pot(), 1_000);

		assert_ok!(Society::vote(Origin::signed(10), 30, true));
		assert_ok!(Society::vote(Origin::signed(10), 40, true));
		run_to_block(8);
		assert_eq!(Society::members(), vec![10, 30, 40]);
		assert_eq!(Society::candidates(), vec![ (500, 50, BidKind::Deposit(25)) ]);
		assert_eq!(Balances::free_balance(Society::account_id()), 9_300);
		assert_eq!(Society::pot(), 1_300);

		assert_ok!(Society::vote(Origin::signed(40), 50, true));  // the last is chosen as decider
		run_to_block(12);
		assert_eq!(Society::members(), vec![10, 30, 40, 50]);
		assert_eq!(Society::candidates(), vec![]);
		assert_eq!(Balances::free_balance(Society::account_id()), 8_800);
		assert_eq!(Society::pot(), 1_800);

		run_to_block(16);
		assert_eq!(Society::members(), vec![10, 30, 40, 50]);
		assert_eq!(Society::candidates(), vec![ (1900, 60, BidKind::Deposit(25)) ]);
		assert_eq!(Balances::free_balance(Society::account_id()), 8_800);
		assert_eq!(Society::pot(), 2_800);

		assert_ok!(Society::vote(Origin::signed(50), 60, true));
		run_to_block(20);
		assert_eq!(Society::members(), vec![10, 30, 40, 50, 60]);
		assert_eq!(Balances::free_balance(Society::account_id()), 6_900);
		assert_eq!(Society::pot(), 1_900);
	});
}

#[test]
fn unbidding_works() {
	EnvBuilder::new().execute(|| {
		assert_ok!(Society::bid(Origin::signed(10), 1000));
		assert_ok!(Society::bid(Origin::signed(20), 0));
		assert_eq!(Balances::free_balance(20), 25);

		assert_noop!(Society::unbid(Origin::signed(20), 1), "bad position");
		assert_ok!(Society::unbid(Origin::signed(20), 0));
		assert_eq!(Balances::free_balance(20), 50);

		run_to_block(4);
		assert_eq!(Society::candidates(), vec![ (1000, 10, BidKind::Deposit(25)) ]);
	});
}

#[test]
fn basic_new_member_skeptic_works() {
	EnvBuilder::new().execute(|| {
		assert_ok!(Society::bid(Origin::signed(20), 0));
		run_to_block(4);
		assert_eq!(Society::candidates(), vec![(0, 20, BidKind::Deposit(25))]);
		run_to_block(8);
		assert_eq!(Society::members(), vec![10]);
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
