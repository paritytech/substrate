// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
// Copyright (C) 2021 Subspace Labs, Inc.
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

//! Consensus extension module tests for Spartan consensus.

use super::*;
use frame_support::{assert_noop, traits::OnFinalize};
use mock::*;
use sp_consensus_poc::digests::Solution;
use sp_consensus_poc::{PoCEpochConfiguration, Slot};

const EMPTY_RANDOMNESS: [u8; 32] = [
    74, 25, 49, 128, 53, 97, 244, 49, 222, 202, 176, 2, 231, 66, 95, 10, 133, 49, 213, 228, 86,
    161, 164, 127, 217, 153, 138, 37, 48, 192, 248, 0,
];

#[test]
fn empty_randomness_is_correct() {
    let s = compute_randomness([0; RANDOMNESS_LENGTH], 0, std::iter::empty(), None);
    assert_eq!(s, EMPTY_RANDOMNESS);
}

#[test]
fn first_block_epoch_zero_start() {
    let mut ext = new_test_ext();

    ext.execute_with(|| {
        let genesis_slot = Slot::from(100);
        let solution = Solution::get_for_genesis();
        let por_randomness = sp_io::hashing::blake2_256(&solution.signature);
        let pre_digest = make_pre_digest(genesis_slot, solution);

        assert_eq!(Spartan::genesis_slot(), Slot::from(0));
        System::initialize(&1, &Default::default(), &pre_digest, Default::default());

        Spartan::do_initialize(1);
        assert_eq!(Spartan::genesis_slot(), genesis_slot);
        assert_eq!(Spartan::current_slot(), genesis_slot);
        assert_eq!(Spartan::epoch_index(), 0);
        assert_eq!(Spartan::author_por_randomness(), Some(por_randomness));

        Spartan::on_finalize(1);
        let header = System::finalize();

        assert_eq!(SegmentIndex::<Test>::get(), 0);
        assert_eq!(UnderConstruction::<Test>::get(0), vec![por_randomness]);
        assert_eq!(Spartan::randomness(), [0; 32]);
        assert_eq!(Spartan::author_por_randomness(), None);
        assert_eq!(NextRandomness::<Test>::get(), [0; 32]);

        assert_eq!(header.digest.logs.len(), 2);
        assert_eq!(pre_digest.logs.len(), 1);
        assert_eq!(header.digest.logs[0], pre_digest.logs[0]);

        let consensus_log = sp_consensus_poc::ConsensusLog::NextEpochData(
            sp_consensus_poc::digests::NextEpochDescriptor {
                randomness: Spartan::randomness(),
            },
        );
        let consensus_digest = DigestItem::Consensus(POC_ENGINE_ID, consensus_log.encode());

        // first epoch descriptor has same info as last.
        assert_eq!(header.digest.logs[1], consensus_digest.clone())
    })
}

#[test]
fn author_por_output() {
    let mut ext = new_test_ext();

    ext.execute_with(|| {
        let genesis_slot = Slot::from(10);
        let solution = Solution::get_for_genesis();
        let por_randomness = sp_io::hashing::blake2_256(&solution.signature);
        let pre_digest = make_pre_digest(genesis_slot, solution);

        System::initialize(&1, &Default::default(), &pre_digest, Default::default());
        assert_eq!(Spartan::author_por_randomness(), None);

        Spartan::do_initialize(1);
        assert_eq!(Spartan::author_por_randomness(), Some(por_randomness));

        Spartan::on_finalize(1);
        System::finalize();
        assert_eq!(Spartan::author_por_randomness(), None);
    })
}

#[test]
fn can_predict_next_epoch_change() {
    new_test_ext().execute_with(|| {
        assert_eq!(<Test as Config>::EpochDuration::get(), 3);
        // this sets the genesis slot to 6;
        go_to_block(1, 6);
        assert_eq!(*Spartan::genesis_slot(), 6);
        assert_eq!(*Spartan::current_slot(), 6);
        assert_eq!(Spartan::epoch_index(), 0);

        progress_to_block(5);

        assert_eq!(Spartan::epoch_index(), 5 / 3);
        assert_eq!(*Spartan::current_slot(), 10);

        // next epoch change will be at
        assert_eq!(*Spartan::current_epoch_start(), 9); // next change will be 12, 2 slots from now
        assert_eq!(
            Spartan::next_expected_epoch_change(System::block_number()),
            Some(5 + 2)
        );
    })
}

#[test]
fn can_enact_next_config() {
    new_test_ext().execute_with(|| {
        assert_eq!(<Test as Config>::EpochDuration::get(), 3);
        // this sets the genesis slot to 6;
        go_to_block(1, 6);
        assert_eq!(*Spartan::genesis_slot(), 6);
        assert_eq!(*Spartan::current_slot(), 6);
        assert_eq!(Spartan::epoch_index(), 0);
        go_to_block(2, 7);

        let current_config = PoCEpochConfiguration { c: (0, 4) };

        let next_config = PoCEpochConfiguration { c: (1, 4) };

        let next_next_config = PoCEpochConfiguration { c: (2, 4) };

        EpochConfig::<Test>::put(current_config);
        NextEpochConfig::<Test>::put(next_config.clone());

        assert_eq!(NextEpochConfig::<Test>::get(), Some(next_config.clone()));

        Spartan::plan_config_change(
            Origin::root(),
            NextConfigDescriptor::V1 {
                c: next_next_config.c,
            },
        )
        .unwrap();

        progress_to_block(4);
        Spartan::on_finalize(9);
        let header = System::finalize();

        assert_eq!(EpochConfig::<Test>::get(), Some(next_config));
        assert_eq!(
            NextEpochConfig::<Test>::get(),
            Some(next_next_config.clone())
        );

        let consensus_log =
            sp_consensus_poc::ConsensusLog::NextConfigData(NextConfigDescriptor::V1 {
                c: next_next_config.c,
            });
        let consensus_digest = DigestItem::Consensus(POC_ENGINE_ID, consensus_log.encode());

        assert_eq!(header.digest.logs[2], consensus_digest.clone())
    });
}

#[test]
fn only_root_can_enact_config_change() {
    use sp_runtime::DispatchError;

    new_test_ext().execute_with(|| {
        let next_config = NextConfigDescriptor::V1 { c: (1, 4) };

        let res = Spartan::plan_config_change(Origin::none(), next_config.clone());

        assert_noop!(res, DispatchError::BadOrigin);

        let res = Spartan::plan_config_change(Origin::signed(1), next_config.clone());

        assert_noop!(res, DispatchError::BadOrigin);

        let res = Spartan::plan_config_change(Origin::root(), next_config);

        assert!(res.is_ok());
    });
}

#[test]
fn can_fetch_current_and_next_epoch_data() {
    new_test_ext().execute_with(|| {
        EpochConfig::<Test>::put(PoCEpochConfiguration { c: (1, 4) });

        progress_to_block(System::block_number() + 4);

        let current_epoch = Spartan::current_epoch();
        assert_eq!(current_epoch.epoch_index, 1);
        assert_eq!(*current_epoch.start_slot, 4);

        let next_epoch = Spartan::next_epoch();
        assert_eq!(next_epoch.epoch_index, 2);
        assert_eq!(*next_epoch.start_slot, 7);

        // the on-chain randomness should always change across epochs
        assert_ne!(current_epoch.randomness, next_epoch.randomness);
    });
}

#[test]
fn tracks_block_numbers_when_current_and_previous_epoch_started() {
    new_test_ext().execute_with(|| {
        // an epoch is 3 slots therefore at block 8 we should be in epoch #3
        // with the previous epochs having the following blocks:
        // epoch 1 - [1, 2, 3]
        // epoch 2 - [4, 5, 6]
        // epoch 3 - [7, 8, 9]
        progress_to_block(8);

        let (last_epoch, current_epoch) = EpochStart::<Test>::get();

        assert_eq!(last_epoch, 4);
        assert_eq!(current_epoch, 7);

        // once we reach block 10 we switch to epoch #4
        progress_to_block(10);

        let (last_epoch, current_epoch) = EpochStart::<Test>::get();

        assert_eq!(last_epoch, 7);
        assert_eq!(current_epoch, 10);
    });
}

// TODO: milestone 3
// #[test]
// fn report_equivocation_current_session_works() {
// 	let (pairs, mut ext) = new_test_ext_with_pairs(3);
//
// 	ext.execute_with(|| {
// 		start_era(1);
//
// 		let authorities = Babe::authorities();
// 		let validators = Session::validators();
//
// 		// make sure that all authorities have the same balance
// 		for validator in &validators {
// 			assert_eq!(Balances::total_balance(validator), 10_000_000);
// 			assert_eq!(Staking::slashable_balance_of(validator), 10_000);
//
// 			assert_eq!(
// 				Staking::eras_stakers(1, validator),
// 				pallet_staking::Exposure {
// 					total: 10_000,
// 					own: 10_000,
// 					others: vec![],
// 				},
// 			);
// 		}
//
// 		// we will use the validator at index 0 as the offending authority
// 		let offending_validator_index = 0;
// 		let offending_validator_id = Session::validators()[offending_validator_index];
// 		let offending_authority_pair = pairs
// 			.into_iter()
// 			.find(|p| p.public() == authorities[offending_validator_index].0)
// 			.unwrap();
//
// 		// generate an equivocation proof. it creates two headers at the given
// 		// slot with different block hashes and signed by the given key
// 		let equivocation_proof = generate_equivocation_proof(
// 			offending_validator_index as u32,
// 			&offending_authority_pair,
// 			CurrentSlot::<Test>::get(),
// 		);
//
// 		// create the key ownership proof
// 		let key = (
// 			sp_consensus_poc::KEY_TYPE,
// 			&offending_authority_pair.public(),
// 		);
// 		let key_owner_proof = Historical::prove(key).unwrap();
//
// 		// report the equivocation
// 		Babe::report_equivocation_unsigned(Origin::none(), equivocation_proof, key_owner_proof)
// 			.unwrap();
//
// 		// start a new era so that the results of the offence report
// 		// are applied at era end
// 		start_era(2);
//
// 		// check that the balance of offending validator is slashed 100%.
// 		assert_eq!(
// 			Balances::total_balance(&offending_validator_id),
// 			10_000_000 - 10_000
// 		);
// 		assert_eq!(Staking::slashable_balance_of(&offending_validator_id), 0);
// 		assert_eq!(
// 			Staking::eras_stakers(2, offending_validator_id),
// 			pallet_staking::Exposure {
// 				total: 0,
// 				own: 0,
// 				others: vec![],
// 			},
// 		);
//
// 		// check that the balances of all other validators are left intact.
// 		for validator in &validators {
// 			if *validator == offending_validator_id {
// 				continue;
// 			}
//
// 			assert_eq!(Balances::total_balance(validator), 10_000_000);
// 			assert_eq!(Staking::slashable_balance_of(validator), 10_000);
// 			assert_eq!(
// 				Staking::eras_stakers(2, validator),
// 				pallet_staking::Exposure {
// 					total: 10_000,
// 					own: 10_000,
// 					others: vec![],
// 				},
// 			);
// 		}
// 	})
// }
//
// #[test]
// fn report_equivocation_old_session_works() {
// 	let (pairs, mut ext) = new_test_ext_with_pairs(3);
//
// 	ext.execute_with(|| {
// 		start_era(1);
//
// 		let authorities = Babe::authorities();
//
// 		// we will use the validator at index 0 as the offending authority
// 		let offending_validator_index = 0;
// 		let offending_validator_id = Session::validators()[offending_validator_index];
// 		let offending_authority_pair = pairs
// 			.into_iter()
// 			.find(|p| p.public() == authorities[offending_validator_index].0)
// 			.unwrap();
//
// 		// generate an equivocation proof at the current slot
// 		let equivocation_proof = generate_equivocation_proof(
// 			offending_validator_index as u32,
// 			&offending_authority_pair,
// 			CurrentSlot::<Test>::get(),
// 		);
//
// 		// create the key ownership proof
// 		let key = (
// 			sp_consensus_poc::KEY_TYPE,
// 			&offending_authority_pair.public(),
// 		);
// 		let key_owner_proof = Historical::prove(key).unwrap();
//
// 		// start a new era and report the equivocation
// 		// from the previous era
// 		start_era(2);
//
// 		// check the balance of the offending validator
// 		assert_eq!(Balances::total_balance(&offending_validator_id), 10_000_000);
// 		assert_eq!(
// 			Staking::slashable_balance_of(&offending_validator_id),
// 			10_000
// 		);
//
// 		// report the equivocation
// 		Babe::report_equivocation_unsigned(Origin::none(), equivocation_proof, key_owner_proof)
// 			.unwrap();
//
// 		// start a new era so that the results of the offence report
// 		// are applied at era end
// 		start_era(3);
//
// 		// check that the balance of offending validator is slashed 100%.
// 		assert_eq!(
// 			Balances::total_balance(&offending_validator_id),
// 			10_000_000 - 10_000
// 		);
// 		assert_eq!(Staking::slashable_balance_of(&offending_validator_id), 0);
// 		assert_eq!(
// 			Staking::eras_stakers(3, offending_validator_id),
// 			pallet_staking::Exposure {
// 				total: 0,
// 				own: 0,
// 				others: vec![],
// 			},
// 		);
// 	})
// }
//
// #[test]
// fn report_equivocation_invalid_key_owner_proof() {
// 	let (pairs, mut ext) = new_test_ext_with_pairs(3);
//
// 	ext.execute_with(|| {
// 		start_era(1);
//
// 		let authorities = Babe::authorities();
//
// 		// we will use the validator at index 0 as the offending authority
// 		let offending_validator_index = 0;
// 		let offending_authority_pair = pairs
// 			.into_iter()
// 			.find(|p| p.public() == authorities[offending_validator_index].0)
// 			.unwrap();
//
// 		// generate an equivocation proof at the current slot
// 		let equivocation_proof = generate_equivocation_proof(
// 			offending_validator_index as u32,
// 			&offending_authority_pair,
// 			CurrentSlot::<Test>::get(),
// 		);
//
// 		// create the key ownership proof
// 		let key = (
// 			sp_consensus_poc::KEY_TYPE,
// 			&offending_authority_pair.public(),
// 		);
// 		let mut key_owner_proof = Historical::prove(key).unwrap();
//
// 		// we change the session index in the key ownership proof
// 		// which should make it invalid
// 		key_owner_proof.session = 0;
// 		assert_err!(
// 			Babe::report_equivocation_unsigned(
// 				Origin::none(),
// 				equivocation_proof.clone(),
// 				key_owner_proof
// 			),
// 			Error::<Test>::InvalidKeyOwnershipProof,
// 		);
//
// 		// it should fail as well if we create a key owner proof
// 		// for a different authority than the offender
// 		let key = (sp_consensus_poc::KEY_TYPE, &authorities[1].0);
// 		let key_owner_proof = Historical::prove(key).unwrap();
//
// 		// we need to progress to a new era to make sure that the key
// 		// ownership proof is properly checked, otherwise since the state
// 		// is still available the historical module will just check
// 		// against current session data.
// 		start_era(2);
//
// 		assert_err!(
// 			Babe::report_equivocation_unsigned(Origin::none(), equivocation_proof, key_owner_proof),
// 			Error::<Test>::InvalidKeyOwnershipProof,
// 		);
// 	})
// }
//
// #[test]
// fn report_equivocation_invalid_equivocation_proof() {
// 	use sp_runtime::traits::Header;
//
// 	let (pairs, mut ext) = new_test_ext_with_pairs(3);
//
// 	ext.execute_with(|| {
// 		start_era(1);
//
// 		let authorities = Babe::authorities();
//
// 		// we will use the validator at index 0 as the offending authority
// 		let offending_validator_index = 0;
// 		let offending_authority_pair = pairs
// 			.into_iter()
// 			.find(|p| p.public() == authorities[offending_validator_index].0)
// 			.unwrap();
//
// 		// create the key ownership proof
// 		let key = (
// 			sp_consensus_poc::KEY_TYPE,
// 			&offending_authority_pair.public(),
// 		);
// 		let key_owner_proof = Historical::prove(key).unwrap();
//
// 		let assert_invalid_equivocation = |equivocation_proof| {
// 			assert_err!(
// 				Babe::report_equivocation_unsigned(
// 					Origin::none(),
// 					equivocation_proof,
// 					key_owner_proof.clone(),
// 				),
// 				Error::<Test>::InvalidEquivocationProof,
// 			)
// 		};
//
// 		// both headers have the same hash, no equivocation.
// 		let mut equivocation_proof = generate_equivocation_proof(
// 			offending_validator_index as u32,
// 			&offending_authority_pair,
// 			CurrentSlot::<Test>::get(),
// 		);
// 		equivocation_proof.second_header = equivocation_proof.first_header.clone();
// 		assert_invalid_equivocation(equivocation_proof);
//
// 		// missing preruntime digest from one header
// 		let mut equivocation_proof = generate_equivocation_proof(
// 			offending_validator_index as u32,
// 			&offending_authority_pair,
// 			CurrentSlot::<Test>::get(),
// 		);
// 		equivocation_proof.first_header.digest_mut().logs.remove(0);
// 		assert_invalid_equivocation(equivocation_proof);
//
// 		// missing seal from one header
// 		let mut equivocation_proof = generate_equivocation_proof(
// 			offending_validator_index as u32,
// 			&offending_authority_pair,
// 			CurrentSlot::<Test>::get(),
// 		);
// 		equivocation_proof.first_header.digest_mut().logs.remove(1);
// 		assert_invalid_equivocation(equivocation_proof);
//
// 		// invalid slot number in proof compared to runtime digest
// 		let mut equivocation_proof = generate_equivocation_proof(
// 			offending_validator_index as u32,
// 			&offending_authority_pair,
// 			CurrentSlot::<Test>::get(),
// 		);
// 		equivocation_proof.slot = Slot::from(0);
// 		assert_invalid_equivocation(equivocation_proof.clone());
//
// 		// different slot numbers in headers
// 		let h1 = equivocation_proof.first_header;
// 		let mut equivocation_proof = generate_equivocation_proof(
// 			offending_validator_index as u32,
// 			&offending_authority_pair,
// 			CurrentSlot::<Test>::get() + 1,
// 		);
//
// 		// use the header from the previous equivocation generated
// 		// at the previous slot
// 		equivocation_proof.first_header = h1.clone();
//
// 		assert_invalid_equivocation(equivocation_proof.clone());
//
// 		// invalid seal signature
// 		let mut equivocation_proof = generate_equivocation_proof(
// 			offending_validator_index as u32,
// 			&offending_authority_pair,
// 			CurrentSlot::<Test>::get() + 1,
// 		);
//
// 		// replace the seal digest with the digest from the
// 		// previous header at the previous slot
// 		equivocation_proof.first_header.digest_mut().pop();
// 		equivocation_proof
// 			.first_header
// 			.digest_mut()
// 			.push(h1.digest().logs().last().unwrap().clone());
//
// 		assert_invalid_equivocation(equivocation_proof.clone());
// 	})
// }
//
// #[test]
// fn report_equivocation_validate_unsigned_prevents_duplicates() {
// 	use sp_runtime::transaction_validity::{
// 		InvalidTransaction, TransactionPriority, TransactionSource, TransactionValidity,
// 		ValidTransaction,
// 	};
//
// 	let (pairs, mut ext) = new_test_ext_with_pairs(3);
//
// 	ext.execute_with(|| {
// 		start_era(1);
//
// 		let authorities = Babe::authorities();
//
// 		// generate and report an equivocation for the validator at index 0
// 		let offending_validator_index = 0;
// 		let offending_authority_pair = pairs
// 			.into_iter()
// 			.find(|p| p.public() == authorities[offending_validator_index].0)
// 			.unwrap();
//
// 		let equivocation_proof = generate_equivocation_proof(
// 			offending_validator_index as u32,
// 			&offending_authority_pair,
// 			CurrentSlot::<Test>::get(),
// 		);
//
// 		let key = (
// 			sp_consensus_poc::KEY_TYPE,
// 			&offending_authority_pair.public(),
// 		);
// 		let key_owner_proof = Historical::prove(key).unwrap();
//
// 		let inner =
// 			Call::report_equivocation_unsigned(equivocation_proof.clone(), key_owner_proof.clone());
//
// 		// only local/inblock reports are allowed
// 		assert_eq!(
// 			<Babe as sp_runtime::traits::ValidateUnsigned>::validate_unsigned(
// 				TransactionSource::External,
// 				&inner,
// 			),
// 			InvalidTransaction::Call.into(),
// 		);
//
// 		// the transaction is valid when passed as local
// 		let tx_tag = (offending_authority_pair.public(), CurrentSlot::<Test>::get());
// 		assert_eq!(
// 			<Babe as sp_runtime::traits::ValidateUnsigned>::validate_unsigned(
// 				TransactionSource::Local,
// 				&inner,
// 			),
// 			TransactionValidity::Ok(ValidTransaction {
// 				priority: TransactionPriority::max_value(),
// 				requires: vec![],
// 				provides: vec![("BabeEquivocation", tx_tag).encode()],
// 				longevity: ReportLongevity::get(),
// 				propagate: false,
// 			})
// 		);
//
// 		// the pre dispatch checks should also pass
// 		assert_ok!(<Babe as sp_runtime::traits::ValidateUnsigned>::pre_dispatch(&inner));
//
// 		// we submit the report
// 		Babe::report_equivocation_unsigned(Origin::none(), equivocation_proof, key_owner_proof)
// 			.unwrap();
//
// 		// the report should now be considered stale and the transaction is invalid.
// 		// the check for staleness should be done on both `validate_unsigned` and on `pre_dispatch`
// 		assert_err!(
// 			<Babe as sp_runtime::traits::ValidateUnsigned>::validate_unsigned(
// 				TransactionSource::Local,
// 				&inner,
// 			),
// 			InvalidTransaction::Stale,
// 		);
//
// 		assert_err!(
// 			<Babe as sp_runtime::traits::ValidateUnsigned>::pre_dispatch(&inner),
// 			InvalidTransaction::Stale,
// 		);
// 	});
// }
//
// #[test]
// fn report_equivocation_has_valid_weight() {
// 	// the weight depends on the size of the validator set,
// 	// but there's a lower bound of 100 validators.
// 	assert!(
// 		(1..=100)
// 			.map(<Test as Config>::WeightInfo::report_equivocation)
// 			.collect::<Vec<_>>()
// 			.windows(2)
// 			.all(|w| w[0] == w[1])
// 	);
//
// 	// after 100 validators the weight should keep increasing
// 	// with every extra validator.
// 	assert!(
// 		(100..=1000)
// 			.map(<Test as Config>::WeightInfo::report_equivocation)
// 			.collect::<Vec<_>>()
// 			.windows(2)
// 			.all(|w| w[0] < w[1])
// 	);
// }
//
// #[test]
// fn valid_equivocation_reports_dont_pay_fees() {
// 	let (pairs, mut ext) = new_test_ext_with_pairs(3);
//
// 	ext.execute_with(|| {
// 		start_era(1);
//
// 		let offending_authority_pair = &pairs[0];
//
// 		// generate an equivocation proof.
// 		let equivocation_proof =
// 			generate_equivocation_proof(0, &offending_authority_pair, CurrentSlot::<Test>::get());
//
// 		// create the key ownership proof.
// 		let key_owner_proof = Historical::prove((
// 			sp_consensus_poc::KEY_TYPE,
// 			&offending_authority_pair.public(),
// 		))
// 		.unwrap();
//
// 		// check the dispatch info for the call.
// 		let info = Call::<Test>::report_equivocation_unsigned(
// 			equivocation_proof.clone(),
// 			key_owner_proof.clone(),
// 		)
// 		.get_dispatch_info();
//
// 		// it should have non-zero weight and the fee has to be paid.
// 		assert!(info.weight > 0);
// 		assert_eq!(info.pays_fee, Pays::Yes);
//
// 		// report the equivocation.
// 		let post_info = Babe::report_equivocation_unsigned(
// 			Origin::none(),
// 			equivocation_proof.clone(),
// 			key_owner_proof.clone(),
// 		)
// 		.unwrap();
//
// 		// the original weight should be kept, but given that the report
// 		// is valid the fee is waived.
// 		assert!(post_info.actual_weight.is_none());
// 		assert_eq!(post_info.pays_fee, Pays::No);
//
// 		// report the equivocation again which is invalid now since it is
// 		// duplicate.
// 		let post_info =
// 			Babe::report_equivocation_unsigned(Origin::none(), equivocation_proof, key_owner_proof)
// 				.err()
// 				.unwrap()
// 				.post_info;
//
// 		// the fee is not waived and the original weight is kept.
// 		assert!(post_info.actual_weight.is_none());
// 		assert_eq!(post_info.pays_fee, Pays::Yes);
// 	})
// }

#[test]
fn add_epoch_configurations_migration_works() {
    use frame_support::storage::migration::{get_storage_value, put_storage_value};

    impl crate::migrations::PoCPalletPrefix for Test {
        fn pallet_prefix() -> &'static str {
            "Spartan"
        }
    }

    new_test_ext().execute_with(|| {
        let next_config_descriptor = NextConfigDescriptor::V1 { c: (3, 4) };

        put_storage_value(
            b"Spartan",
            b"NextEpochConfig",
            &[],
            Some(next_config_descriptor.clone()),
        );

        assert!(get_storage_value::<Option<NextConfigDescriptor>>(
            b"Spartan",
            b"NextEpochConfig",
            &[],
        )
        .is_some());

        let current_epoch = PoCEpochConfiguration { c: (1, 4) };

        crate::migrations::add_epoch_configuration::<Test>(current_epoch.clone());

        assert!(get_storage_value::<Option<NextConfigDescriptor>>(
            b"Spartan",
            b"NextEpochConfig",
            &[],
        )
        .is_none());

        assert_eq!(EpochConfig::<Test>::get(), Some(current_epoch));
        assert_eq!(
            PendingEpochConfigChange::<Test>::get(),
            Some(next_config_descriptor)
        );
    });
}
