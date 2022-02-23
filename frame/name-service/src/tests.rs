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

//! Tests for the module.

#![cfg(test)]

use super::{mock::*, *};
use frame_support::{
	assert_noop, assert_ok,
	error::BadOrigin,
	traits::{Currency, OnFinalize, OnInitialize},
};
use sp_core::blake2_256;

use sp_runtime::MultiAddress;

fn run_to_block(n: u64) {
	while System::block_number() < n {
		NameService::on_finalize(System::block_number());
		System::set_block_number(System::block_number() + 1);
		NameService::on_initialize(System::block_number());
	}
}

#[test]
fn basic_setup_works() {
	new_test_ext().execute_with(|| {
		assert_eq!(Balances::free_balance(&1), 100);
		assert_eq!(Balances::free_balance(&2), 200);
	});
}

#[test]
fn end_to_end_should_work() {
	new_test_ext().execute_with(|| {
		// This is the name we will bid on.
		let name = b"shawntabrizi";
		let name_hash = blake2_256(name);

		// Name is totally available.
		assert!(!Registration::<Test>::contains_key(name_hash));
		assert!(!Lookup::<Test>::contains_key(name_hash));

		// User 1 can make an initial bid.
		assert_ok!(NameService::bid(Origin::signed(1), name_hash, 5));
		assert_eq!(Balances::free_balance(&1), 95);

		// User 2 can be outbid.
		run_to_block(9);
		assert_ok!(NameService::bid(Origin::signed(2), name_hash, 10));
		assert_eq!(Balances::free_balance(&1), 100);
		assert_eq!(Balances::free_balance(&2), 190);

		// User 2 can win bid. (others cant bid anymore)
		run_to_block(19);
		assert_noop!(NameService::bid(Origin::signed(1), name_hash, 15), Error::<Test>::InvalidBid);

		// User 2 can claim bid. 2 ^ 2 = 4 * 10 = 40 total cost
		assert_ok!(NameService::claim(Origin::signed(2), name_hash, 2));
		assert_eq!(Balances::free_balance(&2), 160);

		// User 2 can assign their name
		assert_ok!(NameService::assign(Origin::signed(2), name_hash, Some(2)));

		// Name is totally taken.
		assert!(Registration::<Test>::contains_key(name_hash));
		assert_eq!(Lookup::<Test>::get(name_hash), Some(2));

		// Name can be used instead of AccountId
		// TODO assert_ok!(Balances::transfer(Origin::signed(1), MultiAddress::Address32(name_hash),
		// 40));
		assert_ok!(Balances::transfer(Origin::signed(1), 2, 40));
		assert_eq!(Balances::free_balance(&2), 200);

		// Name can expire
		run_to_block(219);
		assert_ok!(NameService::free(Origin::signed(1), name_hash));

		// Name can be bid for again.
		assert_ok!(NameService::bid(Origin::signed(1), name_hash, 5));
	});
}

#[test]
fn set_name_works() {
	new_test_ext().execute_with(|| {
		// Test data
		let name = b"shawntabrizi";
		let name_hash = blake2_256(name);

		// name setting by manager works correctly
		let status = NameStatus::Owned { who: 1, expiration: None };
		assert_ok!(NameService::set_name(Origin::signed(100), name_hash.clone(), status.clone()));

		let stored_data = Registration::<Test>::get(&name_hash);
		assert_eq!(stored_data, status);

		// non manager call should fail
		assert_noop!(NameService::set_name(Origin::signed(1), name_hash, status), BadOrigin);
	})
}

#[test]
fn bid_works() {
	new_test_ext().execute_with(|| {
		// Test data
		let name = b"shawntabrizi";
		let name_hash = blake2_256(name);

		// call with less than MinBid should fail
		assert_noop!(
			NameService::bid(
				Origin::signed(1),
				name_hash,
				<mock::Test as Config>::MinBid::get() - 1
			),
			Error::<Test>::InvalidBid
		);

		// create bid works correctly
		assert_ok!(NameService::bid(Origin::signed(1), name_hash, 5));
		let stored_data = Registration::<Test>::get(&name_hash);
		assert_eq!(
			stored_data,
			NameStatus::Bidding {
				who: 1,
				bid_end: <mock::Test as Config>::BiddingPeriod::get(),
				amount: 5
			}
		);
		assert_eq!(Balances::free_balance(&1), 95);

		// another bid at same price should fail
		assert_noop!(NameService::bid(Origin::signed(2), name_hash, 5), Error::<Test>::InvalidBid);

		// previous bidder should be able to raise bid
		run_to_block(2);
		assert_ok!(NameService::bid(Origin::signed(1), name_hash, 10));
		let stored_data = Registration::<Test>::get(&name_hash);
		assert_eq!(
			stored_data,
			NameStatus::Bidding {
				who: 1,
				bid_end: <mock::Test as Config>::BiddingPeriod::get() + 2,
				amount: 10
			}
		);
		assert_eq!(Balances::free_balance(&1), 90);

		// another user can outbid current bidder
		assert_ok!(NameService::bid(Origin::signed(2), name_hash, 20));
		let stored_data = Registration::<Test>::get(&name_hash);
		assert_eq!(
			stored_data,
			NameStatus::Bidding {
				who: 2,
				bid_end: <mock::Test as Config>::BiddingPeriod::get() + 2,
				amount: 20
			}
		);
		assert_eq!(Balances::free_balance(&1), 100);
		assert_eq!(Balances::free_balance(&2), 180);

		// cannot bid on expired item
		run_to_block(12);
		assert_noop!(NameService::bid(Origin::signed(2), name_hash, 25), Error::<Test>::InvalidBid);
	})
}

#[test]
fn claim_works() {
	new_test_ext().execute_with(|| {
		// Test data
		let name = b"shawntabrizi";
		let name_hash = blake2_256(name);

		// claim to non existent name should fail
		assert_noop!(
			NameService::claim(Origin::signed(1), name_hash, 1),
			Error::<Test>::InvalidClaim
		);

		// setup a bid to claim
		assert_ok!(NameService::bid(Origin::signed(1), name_hash, 10));

		// claim before bid expiry should fail
		assert_noop!(
			NameService::claim(Origin::signed(1), name_hash, 1),
			Error::<Test>::NotExpired
		);

		run_to_block(<mock::Test as Config>::BiddingPeriod::get());

		// cannot invoke with less than one period
		assert_noop!(
			NameService::claim(Origin::signed(1), name_hash, 0),
			Error::<Test>::InvalidClaim
		);

		// call by not current bidder should fail
		assert_noop!(NameService::claim(Origin::signed(2), name_hash, 1), Error::<Test>::NotBidder);

		// claim by successful bidder should pass
		assert_ok!(NameService::claim(Origin::signed(1), name_hash, 2));
		assert_eq!(Balances::free_balance(&1), 60);
		// ensure reserves have been slashed
		assert_eq!(Balances::total_balance(&1), 60);

		let stored_data = Registration::<Test>::get(&name_hash);
		assert_eq!(
			stored_data,
			NameStatus::Owned {
				who: 1,
				expiration: Some(
					<mock::Test as Config>::OwnershipPeriod::get() * 2 +
						<mock::Test as Config>::BiddingPeriod::get()
				),
			}
		);

		// call to previously claimed name should fail
		assert_noop!(
			NameService::claim(Origin::signed(1), name_hash, 1),
			Error::<Test>::InvalidClaim
		);
	});
}

#[test]
fn free_works() {
	new_test_ext().execute_with(|| {
		// Test data
		let name = b"shawntabrizi";
		let name_hash = blake2_256(name);

		// free non existent name should fail
		assert_noop!(
			NameService::free(Origin::signed(1), name_hash),
			Error::<Test>::AlreadyAvailable
		);

		// setup a bid to free
		assert_ok!(NameService::bid(Origin::signed(1), name_hash, 10));

		// free a name in bidding period should fail
		assert_noop!(NameService::free(Origin::signed(2), name_hash), Error::<Test>::NotExpired);

		// free should wait for claim period
		run_to_block(<mock::Test as Config>::BiddingPeriod::get());
		assert_noop!(NameService::free(Origin::signed(2), name_hash), Error::<Test>::NotExpired);

		// call after (bid_end+bidding+claim+1) period should pass
		let ideal_block = <mock::Test as Config>::BiddingPeriod::get()
			.saturating_add(<mock::Test as Config>::ClaimPeriod::get());
		run_to_block(ideal_block.saturating_add(11));
		assert_ok!(NameService::free(Origin::signed(1), name_hash));

		let stored_data = Registration::<Test>::get(&name_hash);
		assert_eq!(stored_data, NameStatus::default());

		// original bidder reserve balance is slashed
		assert_eq!(Balances::free_balance(&1), 90);
		assert_eq!(Balances::reserved_balance(&1), 0);

		// setup a claimed name to free
		assert_ok!(NameService::bid(Origin::signed(2), name_hash, 10));
		run_to_block(100);
		assert_ok!(NameService::claim(Origin::signed(2), name_hash, 1));

		// only current owner should be able to free non expired name
		assert_noop!(NameService::free(Origin::signed(1), name_hash), Error::<Test>::NotExpired);
		assert_ok!(NameService::free(Origin::signed(2), name_hash));
		let stored_data = Registration::<Test>::get(&name_hash);
		assert_eq!(stored_data, NameStatus::default());
	});
}

#[test]
fn assign_works() {
	new_test_ext().execute_with(|| {
		// Test data
		let name = b"shawntabrizi";
		let name_hash = blake2_256(name);

		// setup a claimed name to assign
		assert_ok!(NameService::bid(Origin::signed(1), name_hash, 10));
		run_to_block(<mock::Test as Config>::BiddingPeriod::get());
		assert_ok!(NameService::claim(Origin::signed(1), name_hash, 1));

		// non owner calls should fail
		assert_noop!(
			NameService::assign(Origin::signed(2), name_hash, Some(4)),
			Error::<Test>::NotOwner
		);

		// owner can assign accountID
		assert_ok!(NameService::assign(Origin::signed(1), name_hash, Some(4)));
		assert_eq!(Lookup::<Test>::get(&name_hash), Some(4));

		// owner can unassign accountId
		assert_ok!(NameService::assign(Origin::signed(1), name_hash, None));
		assert_eq!(Lookup::<Test>::get(&name_hash), None);
	});
}

#[test]
fn unassign_works() {
	new_test_ext().execute_with(|| {
		// Test data
		let name_hash = blake2_256(b"shawntabrizi");

		// setup an assigned name to test
		assert_ok!(NameService::bid(Origin::signed(1), name_hash, 10));
		run_to_block(<mock::Test as Config>::BiddingPeriod::get());
		assert_ok!(NameService::claim(Origin::signed(1), name_hash, 1));
		assert_ok!(NameService::assign(Origin::signed(1), name_hash, Some(1)));

		// non assigned account call should fail
		assert_noop!(
			NameService::unassign(Origin::signed(2), name_hash),
			Error::<Test>::NotAssigned
		);

		// assigned account call should pass
		assert_ok!(NameService::unassign(Origin::signed(1), name_hash));
		assert_eq!(Lookup::<Test>::get(&name_hash), None);
	});
}

#[test]
fn make_permanent_works() {
	new_test_ext().execute_with(|| {
		// Test data
		let name_hash = blake2_256(b"shawntabrizi");

		// setup an assigned name to test
		assert_ok!(NameService::bid(Origin::signed(1), name_hash, 10));
		run_to_block(<mock::Test as Config>::BiddingPeriod::get());
		assert_ok!(NameService::claim(Origin::signed(1), name_hash, 1));

		// call from non permeance account should fail
		assert_noop!(NameService::make_permanent(Origin::signed(1), name_hash), BadOrigin);

		// call from permeance accout should pass
		assert_ok!(NameService::make_permanent(Origin::signed(200), name_hash));
		let stored_data = Registration::<Test>::get(&name_hash);
		assert_eq!(stored_data, NameStatus::Owned { who: 1, expiration: None });
	});
}

#[test]
fn extend_ownership_works() {
	new_test_ext().execute_with(|| {
		// Test data
		let name_hash = blake2_256(b"shawntabrizi");

		// call with non claimed name should fail
		assert_noop!(
			NameService::extend_ownership(Origin::signed(1), name_hash),
			Error::<Test>::UnexpectedState
		);

		// setup an assigned name to test
		assert_ok!(NameService::bid(Origin::signed(1), name_hash, 10));
		run_to_block(<mock::Test as Config>::BiddingPeriod::get());
		assert_ok!(NameService::claim(Origin::signed(1), name_hash, 1));

		// call to extend ownership should pass
		assert_ok!(NameService::extend_ownership(Origin::signed(2), name_hash));
		// balance of caller should reduce by the extension fee
		assert_eq!(Balances::free_balance(&2), 200 - 5);

		let stored_data = Registration::<Test>::get(&name_hash);
		assert_eq!(stored_data, NameStatus::Owned { who: 1, expiration: Some(210) });
	});
}
