// This file is part of Substrate.

// Copyright (C) 2019-2020 Parity Technologies (UK) Ltd.
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

//! Consensus extension module tests for BABE consensus.

use super::*;
use mock::*;
use frame_support::traits::{Currency, OnFinalize};
use pallet_session::ShouldEndSession;
use sp_core::crypto::{IsWrappedBy, Pair};
use sp_consensus_babe::AllowedSlots;
use sp_consensus_vrf::schnorrkel::{VRFOutput, VRFProof};

const EMPTY_RANDOMNESS: [u8; 32] = [
	74, 25, 49, 128, 53, 97, 244, 49,
	222, 202, 176, 2, 231, 66, 95, 10,
	133, 49, 213, 228, 86, 161, 164, 127,
	217, 153, 138, 37, 48, 192, 248, 0,
];

#[test]
fn empty_randomness_is_correct() {
	let s = compute_randomness([0; RANDOMNESS_LENGTH], 0, std::iter::empty(), None);
	assert_eq!(s, EMPTY_RANDOMNESS);
}

#[test]
fn initial_values() {
	new_test_ext(4).execute_with(|| {
		assert_eq!(Babe::authorities().len(), 4)
	})
}

#[test]
fn check_module() {
	new_test_ext(4).execute_with(|| {
		assert!(!Babe::should_end_session(0), "Genesis does not change sessions");
		assert!(!Babe::should_end_session(200000),
			"BABE does not include the block number in epoch calculations");
	})
}

#[test]
fn first_block_epoch_zero_start() {
	let (pairs, mut ext) = new_test_ext_with_pairs(4);

	ext.execute_with(|| {
		let genesis_slot = 100;

		let pair = sp_core::sr25519::Pair::from_ref(&pairs[0]).as_ref();
		let transcript = sp_consensus_babe::make_transcript(
			&Babe::randomness(),
			genesis_slot,
			0,
		);
		let vrf_inout = pair.vrf_sign(transcript);
		let vrf_randomness: sp_consensus_vrf::schnorrkel::Randomness = vrf_inout.0
			.make_bytes::<[u8; 32]>(&sp_consensus_babe::BABE_VRF_INOUT_CONTEXT);
		let vrf_output = VRFOutput(vrf_inout.0.to_output());
		let vrf_proof = VRFProof(vrf_inout.1);

		let first_vrf = vrf_output;
		let pre_digest = make_pre_digest(
			0,
			genesis_slot,
			first_vrf.clone(),
			vrf_proof,
		);

		assert_eq!(Babe::genesis_slot(), 0);
		System::initialize(
			&1,
			&Default::default(),
			&Default::default(),
			&pre_digest,
			Default::default(),
		);

		// see implementation of the function for details why: we issue an
		// epoch-change digest but don't do it via the normal session mechanism.
		assert!(!Babe::should_end_session(1));
		assert_eq!(Babe::genesis_slot(), genesis_slot);
		assert_eq!(Babe::current_slot(), genesis_slot);
		assert_eq!(Babe::epoch_index(), 0);

		Babe::on_finalize(1);
		let header = System::finalize();

		assert_eq!(SegmentIndex::get(), 0);
		assert_eq!(UnderConstruction::get(0), vec![vrf_randomness]);
		assert_eq!(Babe::randomness(), [0; 32]);
		assert_eq!(NextRandomness::get(), [0; 32]);

		assert_eq!(header.digest.logs.len(), 2);
		assert_eq!(pre_digest.logs.len(), 1);
		assert_eq!(header.digest.logs[0], pre_digest.logs[0]);

		let consensus_log = sp_consensus_babe::ConsensusLog::NextEpochData(
			sp_consensus_babe::digests::NextEpochDescriptor {
				authorities: Babe::authorities(),
				randomness: Babe::randomness(),
			}
		);
		let consensus_digest = DigestItem::Consensus(BABE_ENGINE_ID, consensus_log.encode());

		// first epoch descriptor has same info as last.
		assert_eq!(header.digest.logs[1], consensus_digest.clone())
	})
}

#[test]
fn authority_index() {
	new_test_ext(4).execute_with(|| {
		assert_eq!(
			Babe::find_author((&[(BABE_ENGINE_ID, &[][..])]).into_iter().cloned()), None,
			"Trivially invalid authorities are ignored")
	})
}

#[test]
fn can_predict_next_epoch_change() {
	new_test_ext(1).execute_with(|| {
		assert_eq!(<Test as Trait>::EpochDuration::get(), 3);
		// this sets the genesis slot to 6;
		go_to_block(1, 6);
		assert_eq!(Babe::genesis_slot(), 6);
		assert_eq!(Babe::current_slot(), 6);
		assert_eq!(Babe::epoch_index(), 0);

		progress_to_block(5);

		assert_eq!(Babe::epoch_index(), 5 / 3);
		assert_eq!(Babe::current_slot(), 10);

		// next epoch change will be at
		assert_eq!(Babe::current_epoch_start(), 9); // next change will be 12, 2 slots from now
		assert_eq!(Babe::next_expected_epoch_change(System::block_number()), Some(5 + 2));
	})
}

#[test]
fn can_enact_next_config() {
	new_test_ext(1).execute_with(|| {
		assert_eq!(<Test as Trait>::EpochDuration::get(), 3);
		// this sets the genesis slot to 6;
		go_to_block(1, 6);
		assert_eq!(Babe::genesis_slot(), 6);
		assert_eq!(Babe::current_slot(), 6);
		assert_eq!(Babe::epoch_index(), 0);
		go_to_block(2, 7);

		Babe::plan_config_change(NextConfigDescriptor::V1 {
			c: (1, 4),
			allowed_slots: AllowedSlots::PrimarySlots,
		});

		progress_to_block(4);
		Babe::on_finalize(9);
		let header = System::finalize();

		let consensus_log = sp_consensus_babe::ConsensusLog::NextConfigData(
			sp_consensus_babe::digests::NextConfigDescriptor::V1 {
				c: (1, 4),
				allowed_slots: AllowedSlots::PrimarySlots,
			}
		);
		let consensus_digest = DigestItem::Consensus(BABE_ENGINE_ID, consensus_log.encode());

		assert_eq!(header.digest.logs[2], consensus_digest.clone())
	});
}

#[test]
fn report_equivocation_current_session_works() {
	let (pairs, mut ext) = new_test_ext_with_pairs(3);

	ext.execute_with(|| {
		start_era(1);

		let authorities = Babe::authorities();
		let validators = Session::validators();

		// make sure that all authorities have the same balance
		for validator in &validators {
			assert_eq!(Balances::total_balance(validator), 10_000_000);
			assert_eq!(Staking::slashable_balance_of(validator), 10_000);

			assert_eq!(
				Staking::eras_stakers(1, validator),
				pallet_staking::Exposure {
					total: 10_000,
					own: 10_000,
					others: vec![],
				},
			);
		}

		// we will use the validator at index 0 as the offending authority
		let offending_validator_index = 0;
		let offending_validator_id = Session::validators()[offending_validator_index];
		let offending_authority_pair = pairs
			.into_iter()
			.find(|p| p.public() == authorities[offending_validator_index].0)
			.unwrap();

		// generate an equivocation proof. it creates two votes at the given
		// slot with different block hashes and signed by the given key
		let equivocation_proof = generate_equivocation_proof(
			offending_validator_index as u32,
			&offending_authority_pair,
			CurrentSlot::get(),
		);

		// create the key ownership proof
		let key_owner_proof = Historical::prove(
			(sp_consensus_babe::KEY_TYPE, &offending_authority_pair.public()),
		).unwrap();

		// report the equivocation
		Babe::report_equivocation_unsigned(
			Origin::none(),
			equivocation_proof,
			key_owner_proof,
		).unwrap();

		// start a new era so that the results of the offence report
		// are applied at era end
		start_era(2);

		// check that the balance of 0-th validator is slashed 100%.
		assert_eq!(Balances::total_balance(&offending_validator_id), 10_000_000 - 10_000);
		assert_eq!(Staking::slashable_balance_of(&offending_validator_id), 0);

		assert_eq!(
			Staking::eras_stakers(2, offending_validator_id),
			pallet_staking::Exposure {
				total: 0,
				own: 0,
				others: vec![],
			},
		);

		// check that the balances of all other validators are left intact.
		for validator in &validators {
			if *validator == offending_validator_id {
				continue;
			}

			assert_eq!(Balances::total_balance(validator), 10_000_000);
			assert_eq!(Staking::slashable_balance_of(validator), 10_000);

			assert_eq!(
				Staking::eras_stakers(2, validator),
				pallet_staking::Exposure {
					total: 10_000,
					own: 10_000,
					others: vec![],
				},
			);
		}
	})
}
