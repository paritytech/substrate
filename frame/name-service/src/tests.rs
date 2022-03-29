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
	traits::{Get, OnFinalize, OnInitialize},
};
// use sp_runtime::traits::One;
use sp_io::hashing::blake2_256;

fn add_blocks(n: u64) {
	let current_block = System::block_number();
	run_to_block(n + current_block);
}

fn run_to_block(n: u64) {
	let current_block = System::block_number();
	assert!(n > current_block);
	while System::block_number() < n {
		NameService::on_finalize(System::block_number());
		System::set_block_number(System::block_number() + 1);
		NameService::on_initialize(System::block_number());
	}
}

// Common name and name hash used as the scenario setup.
fn alice_register_bob_scenario_name_and_hash() -> ([u8; 32], Vec<u8>) {
	let name = "alice".as_bytes().to_vec();
	(sp_io::hashing::blake2_256(&name), name)
}

/* Basic registration setup scenario.
 * Used for tests where an existing registration is required.
 * Logic in this scenario are tested within `commit` and `reveal` tests.
 * Alice: 1
 * Bob: 2
 * Secret: 3_u64
 * Name: alice
 * Length: 10
 * Finishes at block 12
 */
fn alice_register_bob_senario_setup() -> (Vec<u8>, [u8; 32]) {
	let sender = 1;
	let owner = 2;
	let secret = 3_u64;
	let (name_hash, name) = alice_register_bob_scenario_name_and_hash();
	let commitment_hash = (name.clone(), secret).using_encoded(blake2_256);
	let length = 10;

	let min_commitment: u64 = <Test as crate::Config>::MinCommitmentAge::get();

	assert_eq!(Balances::free_balance(&sender), 100);
	assert_eq!(Balances::free_balance(&owner), 200);
	assert_ok!(NameService::commit(Origin::signed(sender), owner, commitment_hash));
	add_blocks(min_commitment + 1);
	assert_ok!(NameService::reveal(Origin::signed(sender), name.clone(), secret, length));
	assert_eq!(Balances::free_balance(&sender), 89);
	assert_eq!(Balances::free_balance(&owner), 200);
	(name, name_hash)
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
		let owner = 2;
		let secret = 3_u64;
		let name = "alice".as_bytes().to_vec();
		let commitment_hash = (name, secret).using_encoded(blake2_256);

		assert_eq!(Balances::free_balance(&1), 100);
		assert_ok!(NameService::commit(Origin::signed(sender), owner, commitment_hash));
		assert_eq!(Balances::free_balance(&1), 90);
		assert!(Commitments::<Test>::contains_key(commitment_hash));

		let commitment = Commitments::<Test>::get(commitment_hash).unwrap();

		assert_eq!(commitment.owner, owner);
		assert_eq!(commitment.when, 1);
		assert_eq!(commitment.deposit, 10);

		System::assert_last_event(
			NameServiceEvent::Committed { depositor: sender, owner, hash: commitment_hash }.into(),
		);
	});
}

#[test]
fn commit_handles_errors() {
	new_test_ext().execute_with(|| {
		let sender = 1;
		let owner = 2;
		let secret = 3_u64;
		let name = "alice".as_bytes().to_vec();
		let commitment_hash = (name, secret).using_encoded(blake2_256);

		assert_eq!(Balances::free_balance(&1), 100);
		assert_ok!(NameService::commit(Origin::signed(sender), owner, commitment_hash));

		// The same commitment cant be put twice.
		assert_noop!(
			NameService::commit(Origin::signed(sender), owner, commitment_hash),
			Error::<Test>::AlreadyCommitted
		);

		let commitment_hash = ("new", secret).using_encoded(blake2_256);
		// 1337 should have no balance.
		assert_noop!(
			NameService::commit(Origin::signed(1337), owner, commitment_hash),
			BalancesError::InsufficientBalance,
		);
	});
}

#[test]
fn reveal_works() {
	new_test_ext().execute_with(|| {
		let sender = 1;
		let owner = 2;
		let secret = 3_u64;
		let name = "alice".as_bytes().to_vec();
		let encoded_bytes = (&name, secret).encode();
		let commitment_hash = blake2_256(&encoded_bytes);
		let length = 10;
		let name_hash = sp_io::hashing::blake2_256(&name);
		let min_commitment: u64 = <Test as crate::Config>::MinCommitmentAge::get();

		assert_eq!(Balances::free_balance(&1), 100);
		assert_ok!(NameService::commit(Origin::signed(sender), owner, commitment_hash));

		add_blocks(min_commitment + 1);

		assert_ok!(NameService::reveal(Origin::signed(sender), name, secret, length));
		assert!(Registrations::<Test>::contains_key(name_hash));
		assert!(!Commitments::<Test>::contains_key(commitment_hash));

		let registration = Registrations::<Test>::get(name_hash).unwrap();

		assert_eq!(registration.owner, owner);
		assert_eq!(registration.deposit, None);

		// expiry = current block number + length
		// 12 + (10)
		assert_eq!(registration.expiry.unwrap(), 22);

		// ensure correct balance is deducated from sender
		// commit deposit + registration fee + length fee
		// 10 + 1 + 10  = 21
		// commitment deposit returned
		// 21 - 10 = 11
		// deduct from initial deposit
		// 100 - 11 = 89
		assert_eq!(Balances::free_balance(&1), 89);

		// println!("{:?}", sp_core::hexdisplay::HexDisplay::from(&encoded_bytes));
		// println!("{:?}", sp_core::hexdisplay::HexDisplay::from(&commitment_hash));
	});
}

#[test]
fn reveal_handles_errors() {
	new_test_ext().execute_with(|| {
		let sender = 1;
		let owner = 2;
		let secret = 3u64;
		let length = 10;
		let name = "alice".as_bytes().to_vec();
		let commitment_hash = blake2_256(&(&name, secret).encode());
		let min_commitment: u64 = <Test as crate::Config>::MinCommitmentAge::get();

		assert_eq!(Balances::free_balance(&1), 100);

		// Commitment not yet stored.
		assert_noop!(
			NameService::reveal(Origin::signed(sender), name.clone(), secret, length),
			Error::<Test>::CommitmentNotFound
		);

		assert_ok!(NameService::commit(Origin::signed(sender), owner, commitment_hash));
		let commitment = Commitments::<Test>::get(commitment_hash).unwrap();
		assert_eq!(commitment.when, 1);
		add_blocks(min_commitment);

		// Reveal is too early
		assert_noop!(
			NameService::reveal(Origin::signed(sender), name.clone(), secret, length),
			Error::<Test>::TooEarlyToReveal
		);

		// Cannot reveal if balance is too low. try one-character domain.
		let name = "i".as_bytes().to_vec();
		let commitment_hash = blake2_256(&(&name, secret).encode());
		assert_ok!(NameService::commit(Origin::signed(sender), owner, commitment_hash));

		add_blocks(min_commitment + 1);

		assert_noop!(
			NameService::reveal(Origin::signed(2), name.clone(), secret, length),
			BalancesError::InsufficientBalance,
		);

		// Cannot reveal a name that is too long.
		let max_len: u32 = <Test as crate::Config>::MaxNameLength::get();
		let name = vec![0; max_len as usize + 1];
		let commitment_hash = blake2_256(&(&name, secret).encode());
		assert_ok!(NameService::commit(Origin::signed(sender), owner, commitment_hash));

		add_blocks(min_commitment + 1);

		assert_noop!(
			NameService::reveal(Origin::signed(2), name.clone(), secret, length),
			Error::<Test>::NameTooLong,
		);
	});
}

// #[test]
// fn reveal_existing_registration_deposit_returned() {
// 	new_test_ext().execute_with(|| {
// 		let (name, _) = alice_register_bob_senario_setup();

// 		// second registration
// 		let sender = 2;
// 		let owner = 2;
// 		let secret = 6_u64;
// 		let commitment_hash = blake2_256(&(&name, secret).encode());
// 		let min_commitment: u64 = <Test as crate::Config>::MinCommitmentAge::get();

// 		// run until expiry
// 		add_blocks(1000);

// 		// second registration
// 		assert_ok!(NameService::commit(Origin::signed(sender), owner, commitment_hash));
// 		add_blocks(min_commitment + 1);
// 		assert_noop!(NameService::reveal(Origin::signed(sender), name.clone(), secret, 1));

// 		// deposit returned from initial registration
// 		// Note registration + length fee permanently lost. commit and name deposit returned.
// 		assert_eq!(Balances::free_balance(&1), 1098);
// 	});
// }

#[test]
fn reveal_ensure_active_registration_not_registered_again() {
	new_test_ext().execute_with(|| {
		assert_eq!(Balances::free_balance(&3), 300);
		assert_eq!(Balances::free_balance(&4), 400);
		let min_commitment: u64 = <Test as crate::Config>::MinCommitmentAge::get();
		let (name, name_hash) = alice_register_bob_senario_setup();

		// second registration
		let sender = 3;
		let owner = 4;
		let secret = 6_u64;
		let commitment_hash = blake2_256(&(&name, secret).encode());

		assert_ok!(NameService::commit(Origin::signed(sender), owner, commitment_hash));
		add_blocks(min_commitment + 1);

		// not available.
		assert_noop!(
			NameService::reveal(Origin::signed(sender), name.clone(), secret, 1),
			Error::<Test>::RegistrationExists
		);

		// initial registration (1) should still be owner of `Registration`.
		assert_eq!(Registrations::<Test>::get(name_hash).unwrap().owner, 2);
	});
}

#[test]
fn set_controller_works() {
	new_test_ext().execute_with(|| {
		let (_, name_hash) = alice_register_bob_senario_setup();

		// check current controller (2)
		assert_eq!(Registrations::<Test>::get(name_hash).unwrap().controller, 2);

		// transfer to new owner (4)
		let new_owner = 4;
		assert_ok!(NameService::set_controller(Origin::signed(2), name_hash, new_owner));

		// check new owner
		assert_eq!(Registrations::<Test>::get(name_hash).unwrap().controller, new_owner);
	});
}

#[test]
fn set_controller_handles_errors() {
	new_test_ext().execute_with(|| {
		let controller = 2;
		let other = 3;
		let (name_hash, _) = alice_register_bob_scenario_name_and_hash();

		// Registration not found
		assert_noop!(
			NameService::set_controller(Origin::signed(controller), name_hash, other),
			Error::<Test>::RegistrationNotFound
		);

		let (_, _) = alice_register_bob_senario_setup();

		// Not controller or owner of registration
		assert_noop!(
			NameService::set_controller(Origin::signed(other), name_hash, other),
			Error::<Test>::NotRegistrationOwner
		);
	});
}

#[test]
fn transfer_works() {
	new_test_ext().execute_with(|| {
		let (_, name_hash) = alice_register_bob_senario_setup();

		// check current owner (2)
		assert_eq!(Registrations::<Test>::get(name_hash).unwrap().owner, 2);

		// transfer to new owner (4)
		let new_owner = 4;
		assert_ok!(NameService::transfer(Origin::signed(2), 4, name_hash));

		// check new owner (4)
		assert_eq!(Registrations::<Test>::get(name_hash).unwrap().owner, new_owner);
	});
}

#[test]
fn transfer_handles_errors() {
	new_test_ext().execute_with(|| {
		let sender = 1;
		let owner = 2;
		let secret = 3_u64;
		let name = "alice".as_bytes().to_vec();
		let commitment_hash = (name.clone(), secret).using_encoded(blake2_256);
		let length = 1;
		let name_hash = sp_io::hashing::blake2_256(&name);
		let min_commitment: u64 = <Test as crate::Config>::MinCommitmentAge::get();

		// Registration not found
		assert_noop!(
			NameService::transfer(Origin::signed(sender), 2, name_hash),
			Error::<Test>::RegistrationNotFound
		);

		// Not registration owner
		assert_eq!(Balances::free_balance(&1), 100);
		assert_ok!(NameService::commit(Origin::signed(sender), owner, commitment_hash));

		add_blocks(min_commitment + 1);
		assert_ok!(NameService::reveal(Origin::signed(sender), name, secret, length));

		assert_noop!(
			NameService::transfer(Origin::signed(3), 4, name_hash),
			Error::<Test>::NotRegistrationOwner
		);
	});
}

#[test]
fn renew_works() {
	new_test_ext().execute_with(|| {
		let (_, name_hash) = alice_register_bob_senario_setup();

		let registration = Registrations::<Test>::get(name_hash).unwrap();
		assert_eq!(registration.expiry, Some(22));

		// `1` extends for 1 block
		let new_expiry = registration.expiry.unwrap() + 1;

		assert_eq!(Balances::free_balance(&1), 89);
		assert_ok!(NameService::renew(Origin::signed(1), name_hash, new_expiry));
		assert_eq!(Balances::free_balance(&1), 88);
		assert_eq!(Registrations::<Test>::get(name_hash).unwrap().expiry.unwrap(), 23);

		// `2` extends for 5 blocks
		let new_expiry = new_expiry + 5;

		assert_eq!(Balances::free_balance(&2), 200);
		assert_ok!(NameService::renew(Origin::signed(2), name_hash, new_expiry));
		assert_eq!(Balances::free_balance(&2), 195);
		assert_eq!(Registrations::<Test>::get(name_hash).unwrap().expiry.unwrap(), 28);
	});
}

#[test]
fn renew_handles_errors() {
	new_test_ext().execute_with(|| {
		let (_, name_hash) = alice_register_bob_senario_setup();

		// insufficient balance to renew
		assert_ok!(Balances::transfer(Origin::signed(1), 0, 88));
		assert_eq!(Balances::free_balance(1), 1);

		// explicitly running to block 15 to check ExpiryInvalid
		run_to_block(15);

		// try to renew with expiry less than current block
		let new_expiry_less_than_block = 14;
		assert_noop!(
			NameService::renew(Origin::signed(1), name_hash, new_expiry_less_than_block),
			Error::<Test>::ExpiryInvalid,
		);

		// try to renew with expiry less than current expiry
		let new_expiry_less_than_current = 21;
		assert_noop!(
			NameService::renew(Origin::signed(1), name_hash, new_expiry_less_than_current),
			Error::<Test>::ExpiryInvalid,
		);

		let new_expiry_too_expensive = 10000;
		assert_noop!(
			NameService::renew(Origin::signed(1), name_hash, new_expiry_too_expensive),
			BalancesError::InsufficientBalance,
		);
	});
}

#[test]
fn set_record_works() {
	new_test_ext().execute_with(|| {
		let (_, name_hash) = alice_register_bob_senario_setup();
		let addr_to_set = 1;

		// set address to `1`
		assert_ok!(NameService::set_record(Origin::signed(2), name_hash, addr_to_set));
		// record was saved
		assert!(Resolvers::<Test>::contains_key(name_hash));
		// address is correct
		assert_eq!(Resolvers::<Test>::get(name_hash).unwrap(), addr_to_set);
	});
}

#[test]
fn set_record_handles_errors() {
	new_test_ext().execute_with(|| {
		let non_owner = 1;
		let owner = 2;
		let some_name_hash = NameService::name_hash("alice".as_bytes());

		// Registration not found
		assert_noop!(
			NameService::set_record(Origin::signed(non_owner), some_name_hash, 2),
			Error::<Test>::RegistrationNotFound
		);

		// initial registration
		let (_, name_hash) = alice_register_bob_senario_setup();

		// Not registration owner
		assert_noop!(
			NameService::set_record(Origin::signed(non_owner), name_hash, 3),
			Error::<Test>::NotRegistrationOwner,
		);

		// set address
		assert_ok!(NameService::set_record(Origin::signed(owner), name_hash, 3));
	});
}

#[test]
fn deregister_works_owner() {
	new_test_ext().execute_with(|| {
		let owner = 2;
		let (_, name_hash) = alice_register_bob_senario_setup();

		let registration = Registrations::<Test>::get(name_hash).unwrap();
		assert_eq!(registration.owner, 2);
		assert_eq!(registration.expiry, Some(22));
		assert_eq!(registration.deposit, None);

		// set address
		assert_ok!(NameService::set_record(Origin::signed(owner), name_hash, owner));

		// deregister before expiry
		add_blocks(1000);
		assert_ok!(NameService::deregister(Origin::signed(owner), name_hash));

		// name has been removed
		assert!(!Registrations::<Test>::contains_key(name_hash));
		// resolver has been removed
		assert!(!Resolvers::<Test>::contains_key(name_hash));

		System::assert_last_event(NameServiceEvent::AddressDeregistered { name_hash }.into());
	});
}

#[test]
fn deregister_works_non_owner() {
	new_test_ext().execute_with(|| {
		let (_, name_hash) = alice_register_bob_senario_setup();

		let registration = Registrations::<Test>::get(name_hash).unwrap();
		assert_eq!(registration.owner, 2);
		assert_eq!(registration.expiry, Some(22));
		assert_eq!(registration.deposit, None);

		// go to expiry - 1
		add_blocks(10);

		// too early to expire for non_owner
		let non_owner = 1;
		assert_noop!(
			NameService::deregister(Origin::signed(non_owner), name_hash),
			Error::<Test>::NotRegistrationOwner
		);

		// now expired, ok to deregister
		add_blocks(1);
		assert_ok!(NameService::deregister(Origin::signed(non_owner), name_hash));

		// ensure name has been removed
		assert!(!Registrations::<Test>::contains_key(name_hash));
	});
}

#[test]
fn deregister_handles_errors_non_owner() {
	new_test_ext().execute_with(|| {
		let owner = 2;
		let non_owner = 3;
		let (name_hash, _) = alice_register_bob_scenario_name_and_hash();

		assert_noop!(
			NameService::deregister(Origin::signed(non_owner), name_hash),
			Error::<Test>::RegistrationNotFound
		);

		let (_, _) = alice_register_bob_senario_setup();

		// not owner
		assert_noop!(
			NameService::deregister(Origin::signed(non_owner), name_hash),
			Error::<Test>::NotRegistrationOwner
		);

		// let owner deregister early
		assert_ok!(NameService::deregister(Origin::signed(owner), name_hash));

		// cannot deregister again
		assert_noop!(
			NameService::deregister(Origin::signed(owner), name_hash),
			Error::<Test>::RegistrationNotFound
		);
	});
}

#[test]
fn force_register_no_expiry_works() {
	new_test_ext().execute_with(|| {
		let (name_hash, _) = alice_register_bob_scenario_name_and_hash();
		let who = 1;
		let length = None;

		// make permanent registry
		assert_ok!(NameService::force_register(Origin::root(), name_hash, who, length));
		assert!(Registrations::<Test>::contains_key(name_hash));

		// check no expiry
		let registration = Registrations::<Test>::get(name_hash).unwrap();
		assert_eq!(registration.expiry, None);

		// owner cannot renew with no expiry
		assert_noop!(
			NameService::renew(Origin::signed(1), name_hash, 10),
			Error::<Test>::RegistrationHasNoExpiry
		);
	});
}

#[test]
fn force_deregister_works() {
	new_test_ext().execute_with(|| {
		let (_, name_hash) = alice_register_bob_senario_setup();
		// set some address to deregister
		assert_ok!(NameService::set_record(Origin::signed(2), name_hash, 4));
		assert!(Resolvers::<Test>::contains_key(name_hash));

		// force the deregistration of `name_hash`
		assert!(Registrations::<Test>::contains_key(name_hash));
		assert_ok!(NameService::force_deregister(Origin::root(), name_hash));
		assert!(!Registrations::<Test>::contains_key(name_hash));
		assert!(!Resolvers::<Test>::contains_key(name_hash));
	});
}

#[test]
fn set_subnode_record_works() {
	new_test_ext().execute_with(|| {
		let (_, parent_hash) = alice_register_bob_senario_setup();

		let owner = 2;
		let label = "my".as_bytes();
		let label_hash = NameService::name_hash(label);

		assert_ok!(NameService::set_subnode_record(
			Origin::signed(owner),
			parent_hash,
			label.to_vec()
		));

		let name_hash = NameService::subnode_hash(parent_hash, label_hash);
		assert!(Registrations::<Test>::contains_key(name_hash));
		assert_eq!(Balances::free_balance(&2), 198);
	});
}

#[test]
fn set_subnode_record_handles_errors() {
	new_test_ext().execute_with(|| {
		let owner = 2;
		let not_owner = 1;
		let label = "my".as_bytes().to_vec();
		let (parent_hash, _) = alice_register_bob_scenario_name_and_hash();

		// parent hash has not yet been registered
		assert_noop!(
			NameService::set_subnode_record(Origin::signed(owner), parent_hash, label.clone()),
			Error::<Test>::RegistrationNotFound
		);
		let (_, parent_hash) = alice_register_bob_senario_setup();
		// label too short
		assert_noop!(
			NameService::set_subnode_record(
				Origin::signed(owner),
				parent_hash,
				"".as_bytes().to_vec()
			),
			Error::<Test>::LabelTooShort
		);
		// not the owner of parent hash
		assert_noop!(
			NameService::set_subnode_record(Origin::signed(not_owner), parent_hash, label.clone()),
			Error::<Test>::NotRegistrationOwner
		);
		// register subnode for further testing
		assert_ok!(NameService::set_subnode_record(
			Origin::signed(owner),
			parent_hash,
			label.clone()
		));
		// cannot register the same subnode again
		assert_noop!(
			NameService::set_subnode_record(Origin::signed(owner), parent_hash, label),
			Error::<Test>::RegistrationExists
		);

		// drain owner's balance to existential and attempt to register another label
		assert_ok!(Balances::transfer(Origin::signed(owner), 0, 197));
		assert_eq!(Balances::free_balance(2), 1);

		// not enough balance to register another subnode
		let label_2 = "second".as_bytes().to_vec();
		assert_noop!(
			NameService::set_subnode_record(Origin::signed(owner), parent_hash, label_2),
			BalancesError::InsufficientBalance
		);
	});
}

// #[test]
// fn set_subnode_owner_works() {
// 	new_test_ext().execute_with(|| {
// 		let owner = 2;
// 		let new_subnode_owner = 4;
// 		let label = "my".as_bytes().to_vec();
// 		let label_hash = sp_io::hashing::blake2_256(&label);

// 		// initial registration and subnode registration for further testing
// 		let (_, parent_hash) = alice_register_bob_senario_setup();
// 		assert_ok!(NameService::set_subnode_record(Origin::signed(owner), parent_hash, label));
// 		let name_hash = NameService::subnode_hash(parent_hash, label_hash);

// 		assert!(Registrations::<Test>::contains_key(name_hash));
// 		assert_eq!(Registrations::<Test>::get(name_hash).unwrap().owner, owner);

// 		// reserved balances prior new owner
// 		assert_eq!(Balances::reserved_balance(&owner), 2);
// 		assert_eq!(Balances::reserved_balance(&new_subnode_owner), 0);

// 		// change owner
// 		assert_ok!(NameService::set_subnode_owner(
// 			Origin::signed(owner),
// 			parent_hash,
// 			label_hash,
// 			new_subnode_owner
// 		));
// 		assert_eq!(Registrations::<Test>::get(name_hash).unwrap().owner, new_subnode_owner);

// 		// updated reserved balances
// 		assert_eq!(Balances::reserved_balance(&owner), 0);
// 		assert_eq!(Balances::reserved_balance(&new_subnode_owner), 2);
// 	});
// }

// #[test]
// fn set_subnode_owner_handles_errors() {
// 	new_test_ext().execute_with(|| {
// 		let owner = 2;
// 		let new_subnode_owner = 4;
// 		let label = "my".as_bytes().to_vec();
// 		let label_hash = sp_io::hashing::blake2_256(&label);
// 		let (parent_hash, _) = alice_register_bob_scenario_name_and_hash();

// 		// parent node does not yet exist
// 		assert_noop!(
// 			NameService::set_subnode_owner(
// 				Origin::signed(owner),
// 				parent_hash,
// 				label_hash,
// 				new_subnode_owner
// 			),
// 			Error::<Test>::RegistrationNotFound
// 		);

// 		// initial registration and subnode registration for further testing
// 		let (_, _) = alice_register_bob_senario_setup();
// 		assert_ok!(NameService::set_subnode_record(Origin::signed(owner), parent_hash, label));

// 		// cannot change owner of unregistered subnode of parent node
// 		let other_subnode_label = "imnothere".as_bytes().to_vec();
// 		let other_subnode_label_hash = sp_io::hashing::blake2_256(&other_subnode_label);

// 		assert_noop!(
// 			NameService::set_subnode_owner(
// 				Origin::signed(owner),
// 				parent_hash,
// 				other_subnode_label_hash,
// 				new_subnode_owner
// 			),
// 			Error::<Test>::RegistrationNotFound
// 		);

// 		// non-owner cannot change
// 		let not_owner = 3;
// 		assert_noop!(
// 			NameService::set_subnode_owner(
// 				Origin::signed(not_owner),
// 				parent_hash,
// 				label_hash,
// 				new_subnode_owner
// 			),
// 			Error::<Test>::NotRegistrationOwner
// 		);
// 	});
// }

#[test]
fn deregister_subnode_owner_works() {
	new_test_ext().execute_with(|| {
		let owner = 2;
		let label = "my".as_bytes().to_vec();
		let label_hash = sp_io::hashing::blake2_256(&label);
		let address = 2;

		// initial registration, subnode registration and address set for further testing
		let (_, parent_hash) = alice_register_bob_senario_setup();
		assert_ok!(NameService::set_subnode_record(Origin::signed(owner), parent_hash, label));
		let name_hash = NameService::subnode_hash(parent_hash, label_hash);
		assert!(Registrations::<Test>::contains_key(name_hash));
		assert_ok!(NameService::set_record(Origin::signed(owner), name_hash, address));
		assert!(Resolvers::<Test>::contains_key(name_hash));
		assert_eq!(Balances::free_balance(owner), 198);

		// perform deregistration of subnode by owner
		assert_ok!(NameService::deregister_subnode(Origin::signed(owner), parent_hash, label_hash));

		// registration no longer present
		assert!(!Registrations::<Test>::contains_key(name_hash));
		// resolver address no longer present
		assert!(!Resolvers::<Test>::contains_key(name_hash));
		// deposit should have been returned to subnode owner
		assert_eq!(Balances::free_balance(owner), 200);
	});
}

#[test]
fn deregister_subnode_non_owner_works() {
	new_test_ext().execute_with(|| {
		let owner = 2;
		let non_owner = 3;
		let label = "my".as_bytes().to_vec();
		let label_hash = sp_io::hashing::blake2_256(&label);
		let address = 2;

		// initial registration, subnode registration and address set for further testing
		let (_, parent_hash) = alice_register_bob_senario_setup();
		assert_ok!(NameService::set_subnode_record(Origin::signed(owner), parent_hash, label));
		let name_hash = NameService::subnode_hash(parent_hash, label_hash);
		assert!(Registrations::<Test>::contains_key(name_hash));
		assert_ok!(NameService::set_record(Origin::signed(owner), name_hash, address));
		assert!(Resolvers::<Test>::contains_key(name_hash));
		assert_eq!(Balances::free_balance(owner), 198);

		// run to TLD expiry
		add_blocks(1000 + 1);

		// deregister TLD by non-owner
		assert_ok!(NameService::deregister(Origin::signed(non_owner), parent_hash));

		// perform deregistration of subnode by non-owner
		assert_ok!(NameService::deregister_subnode(
			Origin::signed(non_owner),
			parent_hash,
			label_hash
		));

		// registration no longer present
		assert!(!Registrations::<Test>::contains_key(name_hash));
		// resolver address no longer present
		assert!(!Resolvers::<Test>::contains_key(name_hash));
		// deposit should have been returned to subnode owner
		assert_eq!(Balances::free_balance(owner), 200);
	});
}

#[test]
fn deregister_subnode_handles_errors() {
	new_test_ext().execute_with(|| {
		let owner = 2;
		let not_owner = 1;
		let label = "my".as_bytes().to_vec();
		let label_hash = sp_io::hashing::blake2_256(&label);
		let address = 2;

		// initial registration, subnode registration and address set for further testing
		let (_, parent_hash) = alice_register_bob_senario_setup();

		// subnode does not exist, should fail
		assert_noop!(
			NameService::deregister_subnode(Origin::signed(owner), parent_hash, label_hash),
			Error::<Test>::RegistrationNotFound
		);

		// subnode registration and address set for further testing
		assert_ok!(NameService::set_subnode_record(Origin::signed(owner), parent_hash, label));
		let name_hash = NameService::subnode_hash(parent_hash, label_hash);
		assert!(Registrations::<Test>::contains_key(name_hash));
		assert_ok!(NameService::set_record(Origin::signed(owner), name_hash, address));
		assert!(Resolvers::<Test>::contains_key(name_hash));
		assert_eq!(Balances::free_balance(owner), 198);

		// non-owner cannot de-register if parent has not been deregistered
		assert_noop!(
			NameService::deregister_subnode(Origin::signed(not_owner), parent_hash, label_hash),
			Error::<Test>::RegistrationNotExpired
		);
	});
}
