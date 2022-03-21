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
		let secret = 3_u64;
		let name = "alice".as_bytes().to_vec();
		let commitment_hash = (name, secret).using_encoded(blake2_256);

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
		let secret = 3_u64;
		let name = "alice".as_bytes().to_vec();
		let commitment_hash = (name, secret).using_encoded(blake2_256);

		assert_eq!(Balances::free_balance(&1), 100);

		assert_ok!(NameService::commit(Origin::signed(sender), registrant, commitment_hash));

		// The same commitment cant be put twice.
		assert_noop!(
			NameService::commit(Origin::signed(sender), registrant, commitment_hash),
			Error::<Test>::AlreadyCommitted
		);

		let commitment_hash = ("new", secret).using_encoded(blake2_256);
		// 1337 should have no balance.
		assert_noop!(
			NameService::commit(Origin::signed(1337), registrant, commitment_hash),
			BalancesError::InsufficientBalance,
		);
	});
}

#[test]
fn reveal_works() {
	new_test_ext().execute_with(|| {
		let sender = 1;
		let registrant = 2;
		let secret = 3_u64;
		let name = "alice".as_bytes().to_vec();
		let encoded_bytes = (&name, secret).encode();
		let commitment_hash = blake2_256(&encoded_bytes);
		let periods = 10;
		let name_hash = sp_io::hashing::blake2_256(&name);

		assert_eq!(Balances::free_balance(&1), 100);
		assert_ok!(NameService::commit(Origin::signed(sender), registrant, commitment_hash));

		run_to_block(12);

		assert_ok!(NameService::reveal(Origin::signed(sender), name, secret, periods));
		assert!(Registrations::<Test>::contains_key(name_hash));

		let registration = Registrations::<Test>::get(name_hash).unwrap();

		// expiry = current block number + (periods * blocks_per_registration_period)
		// 12 + (10 * 1000)
		assert_eq!(registration.expiry, 10012_u64);

		// ensure correct balance is deducated from sender
		// commit deposit + registration fee + length fee + name deposit
		// 10 + 1 + 10 + 1 = 22
		// commitment deposit returned
		// 22 - 1 = 21
		// deduct from initial deposit
		// 100 - 21 = 79
		assert_eq!(Balances::free_balance(&1), 79);

		// println!("{:?}", sp_core::hexdisplay::HexDisplay::from(&encoded_bytes));
		// println!("{:?}", sp_core::hexdisplay::HexDisplay::from(&commitment_hash));
	});
}

#[test]
fn reveal_existing_registration_deposit_returned() {
	new_test_ext().execute_with(|| {
		let name = "alice".as_bytes().to_vec();
		let periods = 1;

		// inital registrant
		let sender_1 = 1;
		let registrant_1 = 1;
		let secret_1 = 3_u64;
		let commitment_hash_1 = blake2_256(&(&name, secret_1).encode());

		// second registrant
		let sender_2 = 2;
		let registrant_2 = 2;
		let secret_2 = 6_u64;
		let commitment_hash_2 = blake2_256(&(&name, secret_2).encode());

		// initial registration
		assert_eq!(Balances::free_balance(&1), 100);
		assert_eq!(Balances::free_balance(&2), 200);

		assert_ok!(NameService::commit(Origin::signed(sender_1), registrant_1, commitment_hash_1));
		run_to_block(12);
		assert_ok!(NameService::reveal(Origin::signed(sender_1), name.clone(), secret_1, periods));

		assert_eq!(Balances::free_balance(&1), 97);
		// run until expiry
		run_to_block(10013);

		// second registration
		assert_ok!(NameService::commit(Origin::signed(sender_2), registrant_2, commitment_hash_2));
		run_to_block(10024);
		assert_ok!(NameService::reveal(Origin::signed(sender_2), name.clone(), secret_2, periods));

		// deposit returned to initial registrant
		// Note registration + length fee permanently lost. commit and name deposit returned.
		assert_eq!(Balances::free_balance(&1), 98);
	});
}

#[test]
fn reveal_ensure_active_registration_not_registered_again() {
	new_test_ext().execute_with(|| {
		let name = "alice".as_bytes().to_vec();
		let name_hash = sp_io::hashing::blake2_256(&name);
		let periods = 1;

		// inital registrant
		let sender_1 = 1;
		let registrant_1 = 1;
		let secret_1 = 3_u64;
		let commitment_hash_1 = blake2_256(&(&name, secret_1).encode());

		// second registrant
		let sender_2 = 2;
		let registrant_2 = 2;
		let secret_2 = 6_u64;
		let commitment_hash_2 = blake2_256(&(&name, secret_2).encode());

		// initial registration
		assert_eq!(Balances::free_balance(&1), 100);
		assert_eq!(Balances::free_balance(&2), 200);

		assert_ok!(NameService::commit(Origin::signed(sender_1), registrant_1, commitment_hash_1));
		run_to_block(12);
		assert_ok!(NameService::reveal(Origin::signed(sender_1), name.clone(), secret_1, periods));

		run_to_block(50);

		assert_ok!(NameService::commit(Origin::signed(sender_2), registrant_2, commitment_hash_2));
		run_to_block(61);

		// TODO: currently returns OK(()) even if not available. Change this?
		assert_ok!(NameService::reveal(Origin::signed(sender_2), name.clone(), secret_2, periods));

		// initial registrant should still be registrant of `Registration`.
		assert_eq!(Registrations::<Test>::get(name_hash).unwrap().registrant, sender_1);
	});
}

#[test]
fn reveal_handle_errors() {
	new_test_ext().execute_with(|| {
		let sender = 1;
		let registrant = 2;
		let secret = 3u64;
		let periods = 10;

		let name = "alice".as_bytes().to_vec();
		let commitment_hash = blake2_256(&(&name, secret).encode());

		assert_eq!(Balances::free_balance(&1), 100);

		// Commitment not yet stored.
		assert_noop!(
			NameService::reveal(Origin::signed(sender), name.clone(), secret, periods),
			Error::<Test>::CommitmentNotFound
		);
		assert_ok!(NameService::commit(Origin::signed(sender), registrant, commitment_hash));

		run_to_block(2);

		// Reveal is too early.
		assert_noop!(
			NameService::reveal(Origin::signed(sender), name.clone(), secret, periods),
			Error::<Test>::TooEarlyToReveal
		);

		// Cannot reveal if balance is too low.
		let name = "bob".as_bytes().to_vec();
		let commitment_hash = blake2_256(&(&name, secret).encode());
		assert_ok!(NameService::commit(Origin::signed(sender), registrant, commitment_hash));
		run_to_block(13);

		// drain 1's balance to existential
		assert_ok!(Balances::transfer(Origin::signed(1), 0, 79));
		assert_eq!(Balances::free_balance(1), 1);

		assert_noop!(
			NameService::reveal(Origin::signed(1337), name.clone(), secret, periods),
			BalancesError::InsufficientBalance,
		);
	});
}
