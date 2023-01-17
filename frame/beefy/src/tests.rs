// This file is part of Substrate.

// Copyright (C) 2021-2022 Parity Technologies (UK) Ltd.
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

use std::vec;

use beefy_primitives::{
	check_equivocation_proof, keyring::Keyring as BeefyKeyring, known_payloads::MMR_ROOT_ID,
	Payload, ValidatorSet,
};
use codec::Encode;

use sp_runtime::DigestItem;

use frame_support::{
	assert_ok,
	traits::{Currency, KeyOwnerProofSystem, OnInitialize},
};

use crate::mock::*;

fn init_block(block: u64) {
	System::set_block_number(block);
	Session::on_initialize(block);
}

pub fn beefy_log(log: ConsensusLog<BeefyId>) -> DigestItem {
	DigestItem::Consensus(BEEFY_ENGINE_ID, log.encode())
}

#[test]
fn genesis_session_initializes_authorities() {
	let authorities = mock_authorities(vec![1, 2, 3, 4]);
	let want = authorities.clone();

	new_test_ext_raw_authorities(authorities).execute_with(|| {
		let authorities = Beefy::authorities();

		assert_eq!(authorities.len(), 4);
		assert_eq!(want[0], authorities[0]);
		assert_eq!(want[1], authorities[1]);

		assert!(Beefy::validator_set_id() == 0);

		let next_authorities = Beefy::next_authorities();

		assert_eq!(next_authorities.len(), 4);
		assert_eq!(want[0], next_authorities[0]);
		assert_eq!(want[1], next_authorities[1]);
	});
}

#[test]
fn session_change_updates_authorities() {
	let authorities = mock_authorities(vec![1, 2, 3, 4]);
	let want_validators = authorities.clone();

	new_test_ext(vec![1, 2, 3, 4]).execute_with(|| {
		assert!(0 == Beefy::validator_set_id());

		init_block(1);

		assert!(1 == Beefy::validator_set_id());

		let want = beefy_log(ConsensusLog::AuthoritiesChange(
			ValidatorSet::new(want_validators, 1).unwrap(),
		));

		let log = System::digest().logs[0].clone();
		assert_eq!(want, log);

		init_block(2);

		assert!(2 == Beefy::validator_set_id());

		let want = beefy_log(ConsensusLog::AuthoritiesChange(
			ValidatorSet::new(vec![mock_beefy_id(2), mock_beefy_id(4)], 2).unwrap(),
		));

		let log = System::digest().logs[1].clone();
		assert_eq!(want, log);
	});
}

#[test]
fn session_change_updates_next_authorities() {
	let want = vec![mock_beefy_id(1), mock_beefy_id(2), mock_beefy_id(3), mock_beefy_id(4)];

	new_test_ext(vec![1, 2, 3, 4]).execute_with(|| {
		let next_authorities = Beefy::next_authorities();

		assert_eq!(next_authorities.len(), 4);
		assert_eq!(want[0], next_authorities[0]);
		assert_eq!(want[1], next_authorities[1]);
		assert_eq!(want[2], next_authorities[2]);
		assert_eq!(want[3], next_authorities[3]);

		init_block(1);

		let next_authorities = Beefy::next_authorities();

		assert_eq!(next_authorities.len(), 2);
		assert_eq!(want[1], next_authorities[0]);
		assert_eq!(want[3], next_authorities[1]);
	});
}

#[test]
fn validator_set_at_genesis() {
	let want = vec![mock_beefy_id(1), mock_beefy_id(2)];

	new_test_ext(vec![1, 2, 3, 4]).execute_with(|| {
		let vs = Beefy::validator_set().unwrap();

		assert_eq!(vs.id(), 0u64);
		assert_eq!(vs.validators()[0], want[0]);
		assert_eq!(vs.validators()[1], want[1]);
	});
}

#[test]
fn validator_set_updates_work() {
	let want = vec![mock_beefy_id(1), mock_beefy_id(2), mock_beefy_id(3), mock_beefy_id(4)];

	new_test_ext(vec![1, 2, 3, 4]).execute_with(|| {
		let vs = Beefy::validator_set().unwrap();
		assert_eq!(vs.id(), 0u64);
		assert_eq!(want[0], vs.validators()[0]);
		assert_eq!(want[1], vs.validators()[1]);
		assert_eq!(want[2], vs.validators()[2]);
		assert_eq!(want[3], vs.validators()[3]);

		init_block(1);

		let vs = Beefy::validator_set().unwrap();

		assert_eq!(vs.id(), 1u64);
		assert_eq!(want[0], vs.validators()[0]);
		assert_eq!(want[1], vs.validators()[1]);

		init_block(2);

		let vs = Beefy::validator_set().unwrap();

		assert_eq!(vs.id(), 2u64);
		assert_eq!(want[1], vs.validators()[0]);
		assert_eq!(want[3], vs.validators()[1]);
	});
}

/// Returns a list with 3 authorities with known keys:
/// Alice, Bob and Charlie.
pub fn test_authorities() -> Vec<BeefyId> {
	let authorities = vec![BeefyKeyring::Alice, BeefyKeyring::Bob, BeefyKeyring::Charlie];
	authorities.into_iter().map(|id| id.public()).collect()
}

#[test]
fn should_sign_and_verify() {
	use sp_runtime::traits::Keccak256;

	let set_id = 3;
	let payload1 = Payload::from_single_entry(MMR_ROOT_ID, vec![42]);
	let payload2 = Payload::from_single_entry(MMR_ROOT_ID, vec![128]);

	// generate an equivocation proof, with two votes in the same round for
	// same payload signed by the same key
	let equivocation_proof = generate_equivocation_proof(
		set_id,
		BeefyKeyring::Alice.public(),
		(1, payload1.clone(), &BeefyKeyring::Bob),
		(1, payload1.clone(), &BeefyKeyring::Bob),
	);
	// expect invalid equivocation proof
	assert!(!check_equivocation_proof::<_, _, Keccak256>(equivocation_proof));

	// generate an equivocation proof, with two votes in different rounds for
	// different payloads signed by the same key
	let equivocation_proof = generate_equivocation_proof(
		set_id,
		BeefyKeyring::Alice.public(),
		(1, payload1.clone(), &BeefyKeyring::Bob),
		(2, payload2.clone(), &BeefyKeyring::Bob),
	);
	// expect invalid equivocation proof
	assert!(!check_equivocation_proof::<_, _, Keccak256>(equivocation_proof));

	// generate an equivocation proof, with two votes in the same round for
	// different payloads signed by the same key
	let payload2 = Payload::from_single_entry(MMR_ROOT_ID, vec![128]);
	let equivocation_proof = generate_equivocation_proof(
		set_id,
		BeefyKeyring::Alice.public(),
		(1, payload1, &BeefyKeyring::Bob),
		(1, payload2, &BeefyKeyring::Bob),
	);
	// expect valid equivocation proof
	assert!(check_equivocation_proof::<_, _, Keccak256>(equivocation_proof));
}

#[test]
fn report_equivocation_current_set_works() {
	let authorities = test_authorities();

	new_test_ext_raw_authorities(authorities).execute_with(|| {
		assert_eq!(Staking::current_era(), Some(0));
		assert_eq!(Session::current_index(), 0);

		start_era(1);

		let block_num = System::block_number();
		let validator_set = Beefy::validator_set().unwrap();
		let authorities = validator_set.validators();
		let set_id = validator_set.id();
		let validators = Session::validators();

		// make sure that all validators have the same balance
		for validator in &validators {
			assert_eq!(Balances::total_balance(validator), 10_000_000);
			assert_eq!(Staking::slashable_balance_of(validator), 10_000);

			assert_eq!(
				Staking::eras_stakers(1, validator),
				pallet_staking::Exposure { total: 10_000, own: 10_000, others: vec![] },
			);
		}

		assert_eq!(authorities.len(), 2);
		let reporter_index = 0;
		let _reporter_key = authorities[reporter_index].clone();
		let equivocation_authority_index = 1;
		let equivocation_key = &authorities[equivocation_authority_index];
		let equivocation_keyring = BeefyKeyring::from_public(equivocation_key).unwrap();

		let payload1 = Payload::from_single_entry(MMR_ROOT_ID, vec![42]);
		let payload2 = Payload::from_single_entry(MMR_ROOT_ID, vec![128]);
		// generate an equivocation proof, with two votes in the same round for
		// different payloads signed by the same key
		let equivocation_proof = generate_equivocation_proof(
			set_id,
			// FIXME: test only passes for equivocation auto-report, why?
			// _reporter_key.clone(),
			equivocation_key.clone(),
			(block_num, payload1, &equivocation_keyring),
			(block_num, payload2, &equivocation_keyring),
		);

		// create the key ownership proof
		let key_owner_proof =
			Historical::prove((beefy_primitives::KEY_TYPE, &equivocation_key)).unwrap();

		// report the equivocation and the tx should be dispatched successfully
		assert_ok!(Beefy::report_equivocation_unsigned(
			RuntimeOrigin::none(),
			Box::new(equivocation_proof),
			key_owner_proof,
		),);

		start_era(2);

		// check that the balance of 0-th validator is slashed 100%.
		let equivocation_validator_id = validators[equivocation_authority_index];

		assert_eq!(Balances::total_balance(&equivocation_validator_id), 10_000_000 - 10_000);
		assert_eq!(Staking::slashable_balance_of(&equivocation_validator_id), 0);
		assert_eq!(
			Staking::eras_stakers(2, equivocation_validator_id),
			pallet_staking::Exposure { total: 0, own: 0, others: vec![] },
		);

		// check that the balances of all other validators are left intact.
		for validator in &validators {
			if *validator == equivocation_validator_id {
				continue
			}

			assert_eq!(Balances::total_balance(validator), 10_000_000);
			assert_eq!(Staking::slashable_balance_of(validator), 10_000);

			assert_eq!(
				Staking::eras_stakers(2, validator),
				pallet_staking::Exposure { total: 10_000, own: 10_000, others: vec![] },
			);
		}
	});
}

#[test]
fn report_equivocation_old_set_works() {
	let authorities = test_authorities();

	new_test_ext_raw_authorities(authorities).execute_with(|| {
		start_era(1);

		let block_num = System::block_number();
		let validator_set = Beefy::validator_set().unwrap();
		let authorities = validator_set.validators();
		let validators = Session::validators();
		let old_set_id = validator_set.id();

		assert_eq!(authorities.len(), 2);
		let equivocation_authority_index = 0;
		let equivocation_key = &authorities[equivocation_authority_index];
		let reporter_index = 1;
		let _reporter_key = authorities[reporter_index].clone();

		// create the key ownership proof in the "old" set
		let key_owner_proof =
			Historical::prove((beefy_primitives::KEY_TYPE, &equivocation_key)).unwrap();

		start_era(2);

		// make sure that all authorities have the same balance
		for validator in &validators {
			assert_eq!(Balances::total_balance(validator), 10_000_000);
			assert_eq!(Staking::slashable_balance_of(validator), 10_000);

			assert_eq!(
				Staking::eras_stakers(2, validator),
				pallet_staking::Exposure { total: 10_000, own: 10_000, others: vec![] },
			);
		}

		let validator_set = Beefy::validator_set().unwrap();
		let new_set_id = validator_set.id();
		assert_eq!(old_set_id + 3, new_set_id);

		let equivocation_keyring = BeefyKeyring::from_public(equivocation_key).unwrap();

		let payload1 = Payload::from_single_entry(MMR_ROOT_ID, vec![42]);
		let payload2 = Payload::from_single_entry(MMR_ROOT_ID, vec![128]);
		// generate an equivocation proof for the old set,
		let equivocation_proof = generate_equivocation_proof(
			old_set_id,
			// FIXME: test only passes for equivocation auto-report, why?
			// _reporter_key.clone(),
			equivocation_key.clone(),
			(block_num, payload1, &equivocation_keyring),
			(block_num, payload2, &equivocation_keyring),
		);

		// report the equivocation and the tx should be dispatched successfully
		assert_ok!(Beefy::report_equivocation_unsigned(
			RuntimeOrigin::none(),
			Box::new(equivocation_proof),
			key_owner_proof,
		),);

		start_era(3);

		// check that the balance of 0-th validator is slashed 100%.
		let equivocation_validator_id = validators[equivocation_authority_index];

		assert_eq!(Balances::total_balance(&equivocation_validator_id), 10_000_000 - 10_000);
		assert_eq!(Staking::slashable_balance_of(&equivocation_validator_id), 0);
		assert_eq!(
			Staking::eras_stakers(3, equivocation_validator_id),
			pallet_staking::Exposure { total: 0, own: 0, others: vec![] },
		);

		// check that the balances of all other validators are left intact.
		for validator in &validators {
			if *validator == equivocation_validator_id {
				continue
			}

			assert_eq!(Balances::total_balance(validator), 10_000_000);
			assert_eq!(Staking::slashable_balance_of(validator), 10_000);

			assert_eq!(
				Staking::eras_stakers(3, validator),
				pallet_staking::Exposure { total: 10_000, own: 10_000, others: vec![] },
			);
		}
	});
}
