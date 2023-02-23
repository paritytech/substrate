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

use std::vec;

use beefy_primitives::{
	check_equivocation_proof, generate_equivocation_proof, known_payloads::MMR_ROOT_ID,
	Keyring as BeefyKeyring, Payload, ValidatorSet,
};
use codec::Encode;

use sp_runtime::DigestItem;

use frame_support::{
	assert_err, assert_ok,
	dispatch::{GetDispatchInfo, Pays},
	traits::{Currency, KeyOwnerProofSystem, OnInitialize},
};

use crate::{mock::*, Call, Config, Error, Weight, WeightInfo};

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

#[test]
fn cleans_up_old_set_id_session_mappings() {
	new_test_ext(vec![1, 2, 3, 4]).execute_with(|| {
		let max_set_id_session_entries = MaxSetIdSessionEntries::get();

		// we have 3 sessions per era
		let era_limit = max_set_id_session_entries / 3;
		// sanity check against division precision loss
		assert_eq!(0, max_set_id_session_entries % 3);
		// go through `max_set_id_session_entries` sessions
		start_era(era_limit);

		// we should have a session id mapping for all the set ids from
		// `max_set_id_session_entries` eras we have observed
		for i in 1..=max_set_id_session_entries {
			assert!(Beefy::session_for_set(i as u64).is_some());
		}

		// go through another `max_set_id_session_entries` sessions
		start_era(era_limit * 2);

		// we should keep tracking the new mappings for new sessions
		for i in max_set_id_session_entries + 1..=max_set_id_session_entries * 2 {
			assert!(Beefy::session_for_set(i as u64).is_some());
		}

		// but the old ones should have been pruned by now
		for i in 1..=max_set_id_session_entries {
			assert!(Beefy::session_for_set(i as u64).is_none());
		}
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
		(1, payload1.clone(), set_id, &BeefyKeyring::Bob),
		(1, payload1.clone(), set_id, &BeefyKeyring::Bob),
	);
	// expect invalid equivocation proof
	assert!(!check_equivocation_proof::<_, _, Keccak256>(&equivocation_proof));

	// generate an equivocation proof, with two votes in different rounds for
	// different payloads signed by the same key
	let equivocation_proof = generate_equivocation_proof(
		(1, payload1.clone(), set_id, &BeefyKeyring::Bob),
		(2, payload2.clone(), set_id, &BeefyKeyring::Bob),
	);
	// expect invalid equivocation proof
	assert!(!check_equivocation_proof::<_, _, Keccak256>(&equivocation_proof));

	// generate an equivocation proof, with two votes by different authorities
	let equivocation_proof = generate_equivocation_proof(
		(1, payload1.clone(), set_id, &BeefyKeyring::Alice),
		(1, payload2.clone(), set_id, &BeefyKeyring::Bob),
	);
	// expect invalid equivocation proof
	assert!(!check_equivocation_proof::<_, _, Keccak256>(&equivocation_proof));

	// generate an equivocation proof, with two votes in different set ids
	let equivocation_proof = generate_equivocation_proof(
		(1, payload1.clone(), set_id, &BeefyKeyring::Bob),
		(1, payload2.clone(), set_id + 1, &BeefyKeyring::Bob),
	);
	// expect invalid equivocation proof
	assert!(!check_equivocation_proof::<_, _, Keccak256>(&equivocation_proof));

	// generate an equivocation proof, with two votes in the same round for
	// different payloads signed by the same key
	let payload2 = Payload::from_single_entry(MMR_ROOT_ID, vec![128]);
	let equivocation_proof = generate_equivocation_proof(
		(1, payload1, set_id, &BeefyKeyring::Bob),
		(1, payload2, set_id, &BeefyKeyring::Bob),
	);
	// expect valid equivocation proof
	assert!(check_equivocation_proof::<_, _, Keccak256>(&equivocation_proof));
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
		let equivocation_authority_index = 1;
		let equivocation_key = &authorities[equivocation_authority_index];
		let equivocation_keyring = BeefyKeyring::from_public(equivocation_key).unwrap();

		let payload1 = Payload::from_single_entry(MMR_ROOT_ID, vec![42]);
		let payload2 = Payload::from_single_entry(MMR_ROOT_ID, vec![128]);
		// generate an equivocation proof, with two votes in the same round for
		// different payloads signed by the same key
		let equivocation_proof = generate_equivocation_proof(
			(block_num, payload1, set_id, &equivocation_keyring),
			(block_num, payload2, set_id, &equivocation_keyring),
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
			(block_num, payload1, old_set_id, &equivocation_keyring),
			(block_num, payload2, old_set_id, &equivocation_keyring),
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

#[test]
fn report_equivocation_invalid_set_id() {
	let authorities = test_authorities();

	new_test_ext_raw_authorities(authorities).execute_with(|| {
		start_era(1);

		let block_num = System::block_number();
		let validator_set = Beefy::validator_set().unwrap();
		let authorities = validator_set.validators();
		let set_id = validator_set.id();

		let equivocation_authority_index = 0;
		let equivocation_key = &authorities[equivocation_authority_index];
		let equivocation_keyring = BeefyKeyring::from_public(equivocation_key).unwrap();

		let key_owner_proof =
			Historical::prove((beefy_primitives::KEY_TYPE, &equivocation_key)).unwrap();

		let payload1 = Payload::from_single_entry(MMR_ROOT_ID, vec![42]);
		let payload2 = Payload::from_single_entry(MMR_ROOT_ID, vec![128]);
		// generate an equivocation for a future set
		let equivocation_proof = generate_equivocation_proof(
			(block_num, payload1, set_id + 1, &equivocation_keyring),
			(block_num, payload2, set_id + 1, &equivocation_keyring),
		);

		// the call for reporting the equivocation should error
		assert_err!(
			Beefy::report_equivocation_unsigned(
				RuntimeOrigin::none(),
				Box::new(equivocation_proof),
				key_owner_proof,
			),
			Error::<Test>::InvalidEquivocationProof,
		);
	});
}

#[test]
fn report_equivocation_invalid_session() {
	let authorities = test_authorities();

	new_test_ext_raw_authorities(authorities).execute_with(|| {
		start_era(1);

		let block_num = System::block_number();
		let validator_set = Beefy::validator_set().unwrap();
		let authorities = validator_set.validators();

		let equivocation_authority_index = 0;
		let equivocation_key = &authorities[equivocation_authority_index];
		let equivocation_keyring = BeefyKeyring::from_public(equivocation_key).unwrap();

		// generate a key ownership proof at current era set id
		let key_owner_proof =
			Historical::prove((beefy_primitives::KEY_TYPE, &equivocation_key)).unwrap();

		start_era(2);

		let set_id = Beefy::validator_set().unwrap().id();

		let payload1 = Payload::from_single_entry(MMR_ROOT_ID, vec![42]);
		let payload2 = Payload::from_single_entry(MMR_ROOT_ID, vec![128]);
		// generate an equivocation proof at following era set id = 2
		let equivocation_proof = generate_equivocation_proof(
			(block_num, payload1, set_id, &equivocation_keyring),
			(block_num, payload2, set_id, &equivocation_keyring),
		);

		// report an equivocation for the current set using an key ownership
		// proof from the previous set, the session should be invalid.
		assert_err!(
			Beefy::report_equivocation_unsigned(
				RuntimeOrigin::none(),
				Box::new(equivocation_proof),
				key_owner_proof,
			),
			Error::<Test>::InvalidEquivocationProof,
		);
	});
}

#[test]
fn report_equivocation_invalid_key_owner_proof() {
	let authorities = test_authorities();

	new_test_ext_raw_authorities(authorities).execute_with(|| {
		start_era(1);

		let block_num = System::block_number();
		let validator_set = Beefy::validator_set().unwrap();
		let authorities = validator_set.validators();
		let set_id = validator_set.id();

		let invalid_owner_authority_index = 1;
		let invalid_owner_key = &authorities[invalid_owner_authority_index];

		// generate a key ownership proof for the authority at index 1
		let invalid_key_owner_proof =
			Historical::prove((beefy_primitives::KEY_TYPE, &invalid_owner_key)).unwrap();

		let equivocation_authority_index = 0;
		let equivocation_key = &authorities[equivocation_authority_index];
		let equivocation_keyring = BeefyKeyring::from_public(equivocation_key).unwrap();

		let payload1 = Payload::from_single_entry(MMR_ROOT_ID, vec![42]);
		let payload2 = Payload::from_single_entry(MMR_ROOT_ID, vec![128]);
		// generate an equivocation proof for the authority at index 0
		let equivocation_proof = generate_equivocation_proof(
			(block_num, payload1, set_id + 1, &equivocation_keyring),
			(block_num, payload2, set_id + 1, &equivocation_keyring),
		);

		// we need to start a new era otherwise the key ownership proof won't be
		// checked since the authorities are part of the current session
		start_era(2);

		// report an equivocation for the current set using a key ownership
		// proof for a different key than the one in the equivocation proof.
		assert_err!(
			Beefy::report_equivocation_unsigned(
				RuntimeOrigin::none(),
				Box::new(equivocation_proof),
				invalid_key_owner_proof,
			),
			Error::<Test>::InvalidKeyOwnershipProof,
		);
	});
}

#[test]
fn report_equivocation_invalid_equivocation_proof() {
	let authorities = test_authorities();

	new_test_ext_raw_authorities(authorities).execute_with(|| {
		start_era(1);

		let block_num = System::block_number();
		let validator_set = Beefy::validator_set().unwrap();
		let authorities = validator_set.validators();
		let set_id = validator_set.id();

		let equivocation_authority_index = 0;
		let equivocation_key = &authorities[equivocation_authority_index];
		let equivocation_keyring = BeefyKeyring::from_public(equivocation_key).unwrap();

		// generate a key ownership proof at set id in era 1
		let key_owner_proof =
			Historical::prove((beefy_primitives::KEY_TYPE, &equivocation_key)).unwrap();

		let assert_invalid_equivocation_proof = |equivocation_proof| {
			assert_err!(
				Beefy::report_equivocation_unsigned(
					RuntimeOrigin::none(),
					Box::new(equivocation_proof),
					key_owner_proof.clone(),
				),
				Error::<Test>::InvalidEquivocationProof,
			);
		};

		start_era(2);

		let payload1 = Payload::from_single_entry(MMR_ROOT_ID, vec![42]);
		let payload2 = Payload::from_single_entry(MMR_ROOT_ID, vec![128]);

		// both votes target the same block number and payload,
		// there is no equivocation.
		assert_invalid_equivocation_proof(generate_equivocation_proof(
			(block_num, payload1.clone(), set_id, &equivocation_keyring),
			(block_num, payload1.clone(), set_id, &equivocation_keyring),
		));

		// votes targeting different rounds, there is no equivocation.
		assert_invalid_equivocation_proof(generate_equivocation_proof(
			(block_num, payload1.clone(), set_id, &equivocation_keyring),
			(block_num + 1, payload2.clone(), set_id, &equivocation_keyring),
		));

		// votes signed with different authority keys
		assert_invalid_equivocation_proof(generate_equivocation_proof(
			(block_num, payload1.clone(), set_id, &equivocation_keyring),
			(block_num, payload1.clone(), set_id, &BeefyKeyring::Charlie),
		));

		// votes signed with a key that isn't part of the authority set
		assert_invalid_equivocation_proof(generate_equivocation_proof(
			(block_num, payload1.clone(), set_id, &equivocation_keyring),
			(block_num, payload1.clone(), set_id, &BeefyKeyring::Dave),
		));

		// votes targeting different set ids
		assert_invalid_equivocation_proof(generate_equivocation_proof(
			(block_num, payload1, set_id, &equivocation_keyring),
			(block_num, payload2, set_id + 1, &equivocation_keyring),
		));
	});
}

#[test]
fn report_equivocation_validate_unsigned_prevents_duplicates() {
	use sp_runtime::transaction_validity::{
		InvalidTransaction, TransactionPriority, TransactionSource, TransactionValidity,
		ValidTransaction,
	};

	let authorities = test_authorities();

	new_test_ext_raw_authorities(authorities).execute_with(|| {
		start_era(1);

		let block_num = System::block_number();
		let validator_set = Beefy::validator_set().unwrap();
		let authorities = validator_set.validators();
		let set_id = validator_set.id();

		// generate and report an equivocation for the validator at index 0
		let equivocation_authority_index = 0;
		let equivocation_key = &authorities[equivocation_authority_index];
		let equivocation_keyring = BeefyKeyring::from_public(equivocation_key).unwrap();

		let payload1 = Payload::from_single_entry(MMR_ROOT_ID, vec![42]);
		let payload2 = Payload::from_single_entry(MMR_ROOT_ID, vec![128]);
		let equivocation_proof = generate_equivocation_proof(
			(block_num, payload1, set_id, &equivocation_keyring),
			(block_num, payload2, set_id, &equivocation_keyring),
		);

		let key_owner_proof =
			Historical::prove((beefy_primitives::KEY_TYPE, &equivocation_key)).unwrap();

		let call = Call::report_equivocation_unsigned {
			equivocation_proof: Box::new(equivocation_proof.clone()),
			key_owner_proof: key_owner_proof.clone(),
		};

		// only local/inblock reports are allowed
		assert_eq!(
			<Beefy as sp_runtime::traits::ValidateUnsigned>::validate_unsigned(
				TransactionSource::External,
				&call,
			),
			InvalidTransaction::Call.into(),
		);

		// the transaction is valid when passed as local
		let tx_tag = (equivocation_key, set_id, 3u64);

		assert_eq!(
			<Beefy as sp_runtime::traits::ValidateUnsigned>::validate_unsigned(
				TransactionSource::Local,
				&call,
			),
			TransactionValidity::Ok(ValidTransaction {
				priority: TransactionPriority::max_value(),
				requires: vec![],
				provides: vec![("BeefyEquivocation", tx_tag).encode()],
				longevity: ReportLongevity::get(),
				propagate: false,
			})
		);

		// the pre dispatch checks should also pass
		assert_ok!(<Beefy as sp_runtime::traits::ValidateUnsigned>::pre_dispatch(&call));

		// we submit the report
		Beefy::report_equivocation_unsigned(
			RuntimeOrigin::none(),
			Box::new(equivocation_proof),
			key_owner_proof,
		)
		.unwrap();

		// the report should now be considered stale and the transaction is invalid
		// the check for staleness should be done on both `validate_unsigned` and on `pre_dispatch`
		assert_err!(
			<Beefy as sp_runtime::traits::ValidateUnsigned>::validate_unsigned(
				TransactionSource::Local,
				&call,
			),
			InvalidTransaction::Stale,
		);

		assert_err!(
			<Beefy as sp_runtime::traits::ValidateUnsigned>::pre_dispatch(&call),
			InvalidTransaction::Stale,
		);
	});
}

#[test]
fn report_equivocation_has_valid_weight() {
	// the weight depends on the size of the validator set,
	// but there's a lower bound of 100 validators.
	assert!((1..=100)
		.map(<Test as Config>::WeightInfo::report_equivocation)
		.collect::<Vec<_>>()
		.windows(2)
		.all(|w| w[0] == w[1]));

	// after 100 validators the weight should keep increasing
	// with every extra validator.
	assert!((100..=1000)
		.map(<Test as Config>::WeightInfo::report_equivocation)
		.collect::<Vec<_>>()
		.windows(2)
		.all(|w| w[0].ref_time() < w[1].ref_time()));
}

#[test]
fn valid_equivocation_reports_dont_pay_fees() {
	let authorities = test_authorities();

	new_test_ext_raw_authorities(authorities).execute_with(|| {
		start_era(1);

		let block_num = System::block_number();
		let validator_set = Beefy::validator_set().unwrap();
		let authorities = validator_set.validators();
		let set_id = validator_set.id();

		let equivocation_authority_index = 0;
		let equivocation_key = &authorities[equivocation_authority_index];
		let equivocation_keyring = BeefyKeyring::from_public(equivocation_key).unwrap();

		// generate equivocation proof
		let payload1 = Payload::from_single_entry(MMR_ROOT_ID, vec![42]);
		let payload2 = Payload::from_single_entry(MMR_ROOT_ID, vec![128]);
		let equivocation_proof = generate_equivocation_proof(
			(block_num, payload1, set_id, &equivocation_keyring),
			(block_num, payload2, set_id, &equivocation_keyring),
		);

		// create the key ownership proof.
		let key_owner_proof =
			Historical::prove((beefy_primitives::KEY_TYPE, &equivocation_key)).unwrap();

		// check the dispatch info for the call.
		let info = Call::<Test>::report_equivocation_unsigned {
			equivocation_proof: Box::new(equivocation_proof.clone()),
			key_owner_proof: key_owner_proof.clone(),
		}
		.get_dispatch_info();

		// it should have non-zero weight and the fee has to be paid.
		assert!(info.weight.any_gt(Weight::zero()));
		assert_eq!(info.pays_fee, Pays::Yes);

		// report the equivocation.
		let post_info = Beefy::report_equivocation_unsigned(
			RuntimeOrigin::none(),
			Box::new(equivocation_proof.clone()),
			key_owner_proof.clone(),
		)
		.unwrap();

		// the original weight should be kept, but given that the report
		// is valid the fee is waived.
		assert!(post_info.actual_weight.is_none());
		assert_eq!(post_info.pays_fee, Pays::No);

		// report the equivocation again which is invalid now since it is
		// duplicate.
		let post_info = Beefy::report_equivocation_unsigned(
			RuntimeOrigin::none(),
			Box::new(equivocation_proof),
			key_owner_proof,
		)
		.err()
		.unwrap()
		.post_info;

		// the fee is not waived and the original weight is kept.
		assert!(post_info.actual_weight.is_none());
		assert_eq!(post_info.pays_fee, Pays::Yes);
	})
}
