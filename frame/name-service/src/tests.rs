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
use codec::Encode;
use frame_support::{
	assert_noop, assert_ok,
	traits::{OnFinalize, OnInitialize},
};
use sp_core::blake2_256;

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
fn commit_works() {
	new_test_ext().execute_with(|| {
		let sender = 1;
		let registrant = 2;
		let secret = 3u64;
		let commitment_hash = ("alice", secret).using_encoded(blake2_256);

		assert_eq!(Balances::free_balance(&1), 100);

		assert_ok!(NameService::commit(Origin::signed(sender), registrant, commitment_hash));

		assert_eq!(Balances::free_balance(&1), 90);

		assert!(Commitments::<Test>::contains_key(commitment_hash));

		System::assert_last_event(
			NameServiceEvent::Committed { sender, who: registrant, hash: commitment_hash }.into(),
		);
	});
}

#[test]
fn commit_handles_errors() {
	new_test_ext().execute_with(|| {
		let sender = 1;
		let registrant = 2;
		let secret = 3u64;
		let commitment_hash = ("alice", secret).using_encoded(blake2_256);

		assert_eq!(Balances::free_balance(&1), 100);

		assert_ok!(NameService::commit(Origin::signed(sender), registrant, commitment_hash));
		// The same commitment cant be put twice
		assert_noop!(
			NameService::commit(Origin::signed(sender), registrant, commitment_hash),
			Error::<Test>::AlreadyCommitted
		);

		let commitment_hash = ("new", secret).using_encoded(blake2_256);
		// 1337 should have no balance
		assert_noop!(
			NameService::commit(Origin::signed(1337), registrant, commitment_hash),
			BalancesError::InsufficientBalance,
		);
	});
}
