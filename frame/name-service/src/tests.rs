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

use super::*;
use super::mock::*;
use sp_core::blake2_256;
use frame_support::{
	assert_ok, assert_noop,
	traits::{OnInitialize, OnFinalize}
};
use pallet_balances::Error as BalancesError;

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
		assert_ok!(Balances::transfer(Origin::signed(1), MultiAddress::Address32(name_hash), 40));
		assert_eq!(Balances::free_balance(&2), 200);

		// Name can expire
		run_to_block(219);
		assert_ok!(NameService::free(Origin::signed(1), name_hash));

		// Name can be bid for again.
		assert_ok!(NameService::bid(Origin::signed(1), name_hash, 5));
	});
}
