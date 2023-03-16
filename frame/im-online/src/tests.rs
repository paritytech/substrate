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

//! Tests for the im-online module.

#![cfg(test)]

use super::*;
use crate::mock::*;
use frame_support::{assert_noop, dispatch};
use sp_core::{
	offchain::{
		testing::{TestOffchainExt, TestTransactionPoolExt},
		OffchainDbExt, OffchainWorkerExt, TransactionPoolExt,
	},
	OpaquePeerId,
};
use sp_runtime::{
	testing::UintAuthorityId,
	transaction_validity::{InvalidTransaction, TransactionValidityError},
};

#[test]
fn test_unresponsiveness_slash_fraction() {
	let dummy_offence =
		UnresponsivenessOffence { session_index: 0, validator_set_count: 50, offenders: vec![()] };
	// A single case of unresponsiveness is not slashed.
	assert_eq!(dummy_offence.slash_fraction(1), Perbill::zero());

	assert_eq!(
		dummy_offence.slash_fraction(5),
		Perbill::zero(), // 0%
	);

	assert_eq!(
		dummy_offence.slash_fraction(7),
		Perbill::from_parts(4200000), // 0.42%
	);

	// One third offline should be punished around 5%.
	assert_eq!(
		dummy_offence.slash_fraction(17),
		Perbill::from_parts(46200000), // 4.62%
	);

	// Offline offences should never lead to being disabled.
	assert_eq!(dummy_offence.disable_strategy(), DisableStrategy::Never);
}

#[test]
fn should_report_offline_validators() {
	new_test_ext().execute_with(|| {
		// given
		let block = 1;
		System::set_block_number(block);
		// buffer new validators
		advance_session();
		// enact the change and buffer another one
		let validators = vec![1, 2, 3, 4, 5, 6];
		Validators::mutate(|l| *l = Some(validators.clone()));
		advance_session();

		// when
		// we end current session and start the next one
		advance_session();

		// then
		let offences = Offences::take();
		assert_eq!(
			offences,
			vec![(
				vec![],
				UnresponsivenessOffence {
					session_index: 2,
					validator_set_count: 3,
					offenders: vec![(1, 1), (2, 2), (3, 3),],
				}
			)]
		);

		// should not report when heartbeat is sent
		for (idx, v) in validators.into_iter().take(4).enumerate() {
			let _ = heartbeat(block, 3, idx as u32, v.into(), Session::validators()).unwrap();
		}
		advance_session();

		// then
		let offences = Offences::take();
		assert_eq!(
			offences,
			vec![(
				vec![],
				UnresponsivenessOffence {
					session_index: 3,
					validator_set_count: 6,
					offenders: vec![(5, 5), (6, 6),],
				}
			)]
		);
	});
}

fn heartbeat(
	block_number: u64,
	session_index: u32,
	authority_index: u32,
	id: UintAuthorityId,
	validators: Vec<u64>,
) -> dispatch::DispatchResult {
	use frame_support::unsigned::ValidateUnsigned;

	let heartbeat = Heartbeat {
		block_number,
		network_state: OpaqueNetworkState {
			peer_id: OpaquePeerId(vec![1]),
			external_addresses: vec![],
		},
		session_index,
		authority_index,
		validators_len: validators.len() as u32,
	};
	let signature = id.sign(&heartbeat.encode()).unwrap();

	ImOnline::pre_dispatch(&crate::Call::heartbeat {
		heartbeat: heartbeat.clone(),
		signature: signature.clone(),
	})
	.map_err(|e| match e {
		TransactionValidityError::Invalid(InvalidTransaction::Custom(INVALID_VALIDATORS_LEN)) =>
			"invalid validators len",
		e @ _ => <&'static str>::from(e),
	})?;
	ImOnline::heartbeat(RuntimeOrigin::none(), heartbeat, signature)
}

#[test]
fn should_mark_online_validator_when_heartbeat_is_received() {
	new_test_ext().execute_with(|| {
		advance_session();
		// given
		Validators::mutate(|l| *l = Some(vec![1, 2, 3, 4, 5, 6]));
		assert_eq!(Session::validators(), Vec::<u64>::new());
		// enact the change and buffer another one
		advance_session();

		assert_eq!(Session::current_index(), 2);
		assert_eq!(Session::validators(), vec![1, 2, 3]);

		assert!(!ImOnline::is_online(0));
		assert!(!ImOnline::is_online(1));
		assert!(!ImOnline::is_online(2));

		// when
		let _ = heartbeat(1, 2, 0, 1.into(), Session::validators()).unwrap();

		// then
		assert!(ImOnline::is_online(0));
		assert!(!ImOnline::is_online(1));
		assert!(!ImOnline::is_online(2));

		// and when
		let _ = heartbeat(1, 2, 2, 3.into(), Session::validators()).unwrap();

		// then
		assert!(ImOnline::is_online(0));
		assert!(!ImOnline::is_online(1));
		assert!(ImOnline::is_online(2));
	});
}

#[test]
fn late_heartbeat_and_invalid_keys_len_should_fail() {
	new_test_ext().execute_with(|| {
		advance_session();
		// given
		Validators::mutate(|l| *l = Some(vec![1, 2, 3, 4, 5, 6]));
		assert_eq!(Session::validators(), Vec::<u64>::new());
		// enact the change and buffer another one
		advance_session();

		assert_eq!(Session::current_index(), 2);
		assert_eq!(Session::validators(), vec![1, 2, 3]);

		// when
		assert_noop!(
			heartbeat(1, 3, 0, 1.into(), Session::validators()),
			"Transaction is outdated"
		);
		assert_noop!(
			heartbeat(1, 1, 0, 1.into(), Session::validators()),
			"Transaction is outdated"
		);

		// invalid validators_len
		assert_noop!(heartbeat(1, 2, 0, 1.into(), vec![]), "invalid validators len");
	});
}

#[test]
fn should_generate_heartbeats() {
	use frame_support::traits::OffchainWorker;

	let mut ext = new_test_ext();
	let (offchain, _state) = TestOffchainExt::new();
	let (pool, state) = TestTransactionPoolExt::new();
	ext.register_extension(OffchainDbExt::new(offchain.clone()));
	ext.register_extension(OffchainWorkerExt::new(offchain));
	ext.register_extension(TransactionPoolExt::new(pool));

	ext.execute_with(|| {
		// given
		let block = 1;
		System::set_block_number(block);
		UintAuthorityId::set_all_keys(vec![0, 1, 2]);
		// buffer new validators
		Session::rotate_session();
		// enact the change and buffer another one
		Validators::mutate(|l| *l = Some(vec![1, 2, 3, 4, 5, 6]));
		Session::rotate_session();

		// when
		ImOnline::offchain_worker(block);

		// then
		let transaction = state.write().transactions.pop().unwrap();
		// All validators have `0` as their session key, so we generate 2 transactions.
		assert_eq!(state.read().transactions.len(), 2);

		// check stuff about the transaction.
		let ex: Extrinsic = Decode::decode(&mut &*transaction).unwrap();
		let heartbeat = match ex.call {
			crate::mock::RuntimeCall::ImOnline(crate::Call::heartbeat { heartbeat, .. }) =>
				heartbeat,
			e => panic!("Unexpected call: {:?}", e),
		};

		assert_eq!(
			heartbeat,
			Heartbeat {
				block_number: block,
				network_state: sp_io::offchain::network_state().unwrap(),
				session_index: 2,
				authority_index: 2,
				validators_len: 3,
			}
		);
	});
}

#[test]
fn should_cleanup_received_heartbeats_on_session_end() {
	new_test_ext().execute_with(|| {
		advance_session();

		Validators::mutate(|l| *l = Some(vec![1, 2, 3]));
		assert_eq!(Session::validators(), Vec::<u64>::new());

		// enact the change and buffer another one
		advance_session();

		assert_eq!(Session::current_index(), 2);
		assert_eq!(Session::validators(), vec![1, 2, 3]);

		// send an heartbeat from authority id 0 at session 2
		let _ = heartbeat(1, 2, 0, 1.into(), Session::validators()).unwrap();

		// the heartbeat is stored
		assert!(!ImOnline::received_heartbeats(&2, &0).is_none());

		advance_session();

		// after the session has ended we have already processed the heartbeat
		// message, so any messages received on the previous session should have
		// been pruned.
		assert!(ImOnline::received_heartbeats(&2, &0).is_none());
	});
}

#[test]
fn should_mark_online_validator_when_block_is_authored() {
	use pallet_authorship::EventHandler;

	new_test_ext().execute_with(|| {
		advance_session();
		// given
		Validators::mutate(|l| *l = Some(vec![1, 2, 3, 4, 5, 6]));
		assert_eq!(Session::validators(), Vec::<u64>::new());
		// enact the change and buffer another one
		advance_session();

		assert_eq!(Session::current_index(), 2);
		assert_eq!(Session::validators(), vec![1, 2, 3]);

		for i in 0..3 {
			assert!(!ImOnline::is_online(i));
		}

		// when
		ImOnline::note_author(1);

		// then
		assert!(ImOnline::is_online(0));
		assert!(!ImOnline::is_online(1));
		assert!(!ImOnline::is_online(2));
	});
}

#[test]
fn should_not_send_a_report_if_already_online() {
	use pallet_authorship::EventHandler;

	let mut ext = new_test_ext();
	let (offchain, _state) = TestOffchainExt::new();
	let (pool, pool_state) = TestTransactionPoolExt::new();
	ext.register_extension(OffchainDbExt::new(offchain.clone()));
	ext.register_extension(OffchainWorkerExt::new(offchain));
	ext.register_extension(TransactionPoolExt::new(pool));

	ext.execute_with(|| {
		advance_session();
		// given
		Validators::mutate(|l| *l = Some(vec![1, 2, 3, 4, 5, 6]));
		assert_eq!(Session::validators(), Vec::<u64>::new());
		// enact the change and buffer another one
		advance_session();
		assert_eq!(Session::current_index(), 2);
		assert_eq!(Session::validators(), vec![1, 2, 3]);
		ImOnline::note_author(2);
		ImOnline::note_author(3);

		// when
		UintAuthorityId::set_all_keys(vec![1, 2, 3]);
		// we expect error, since the authority is already online.
		let mut res = ImOnline::send_heartbeats(4).unwrap();
		res.next().unwrap().unwrap();
		assert_eq!(res.next().unwrap().unwrap_err(), OffchainErr::AlreadyOnline(1));
		assert_eq!(res.next().unwrap().unwrap_err(), OffchainErr::AlreadyOnline(2));
		assert_eq!(res.next(), None);

		// then
		let transaction = pool_state.write().transactions.pop().unwrap();
		// All validators have `0` as their session key, but we should only produce 1 heartbeat.
		assert_eq!(pool_state.read().transactions.len(), 0);
		// check stuff about the transaction.
		let ex: Extrinsic = Decode::decode(&mut &*transaction).unwrap();
		let heartbeat = match ex.call {
			crate::mock::RuntimeCall::ImOnline(crate::Call::heartbeat { heartbeat, .. }) =>
				heartbeat,
			e => panic!("Unexpected call: {:?}", e),
		};

		assert_eq!(
			heartbeat,
			Heartbeat {
				block_number: 4,
				network_state: sp_io::offchain::network_state().unwrap(),
				session_index: 2,
				authority_index: 0,
				validators_len: 3,
			}
		);
	});
}

#[test]
fn should_handle_missing_progress_estimates() {
	use frame_support::traits::OffchainWorker;

	let mut ext = new_test_ext();
	let (offchain, _state) = TestOffchainExt::new();
	let (pool, state) = TestTransactionPoolExt::new();
	ext.register_extension(OffchainDbExt::new(offchain.clone()));
	ext.register_extension(OffchainWorkerExt::new(offchain));
	ext.register_extension(TransactionPoolExt::new(pool));

	ext.execute_with(|| {
		let block = 1;

		System::set_block_number(block);
		UintAuthorityId::set_all_keys(vec![0, 1, 2]);

		// buffer new validators
		Session::rotate_session();

		// enact the change and buffer another one
		Validators::mutate(|l| *l = Some(vec![0, 1, 2]));
		Session::rotate_session();

		// we will return `None` on the next call to `estimate_current_session_progress`
		// and the offchain worker should fallback to checking `HeartbeatAfter`
		MockCurrentSessionProgress::mutate(|p| *p = Some(None));
		ImOnline::offchain_worker(block);

		assert_eq!(state.read().transactions.len(), 3);
	});
}

#[test]
fn should_handle_non_linear_session_progress() {
	// NOTE: this is the reason why we started using `EstimateNextSessionRotation` to figure out if
	// we should send a heartbeat, it's possible that between successive blocks we progress through
	// the session more than just one block increment (in BABE session length is defined in slots,
	// not block numbers).

	let mut ext = new_test_ext();
	let (offchain, _state) = TestOffchainExt::new();
	let (pool, _) = TestTransactionPoolExt::new();
	ext.register_extension(OffchainDbExt::new(offchain.clone()));
	ext.register_extension(OffchainWorkerExt::new(offchain));
	ext.register_extension(TransactionPoolExt::new(pool));

	ext.execute_with(|| {
		UintAuthorityId::set_all_keys(vec![0, 1, 2]);

		// buffer new validator
		Session::rotate_session();

		// mock the session length as being 10 blocks long,
		// enact the change and buffer another one
		Validators::mutate(|l| *l = Some(vec![0, 1, 2]));

		// mock the session length has being 10 which should make us assume the fallback for half
		// session will be reached by block 5.
		MockAverageSessionLength::mutate(|p| *p = Some(10));

		Session::rotate_session();

		// if we don't have valid results for the current session progres then
		// we'll fallback to `HeartbeatAfter` and only heartbeat on block 5.
		MockCurrentSessionProgress::mutate(|p| *p = Some(None));
		assert_eq!(ImOnline::send_heartbeats(2).err(), Some(OffchainErr::TooEarly));

		MockCurrentSessionProgress::mutate(|p| *p = Some(None));
		assert!(ImOnline::send_heartbeats(5).ok().is_some());

		// if we have a valid current session progress then we'll heartbeat as soon
		// as we're past 80% of the session regardless of the block number
		MockCurrentSessionProgress::mutate(|p| *p = Some(Some(Permill::from_percent(81))));

		assert!(ImOnline::send_heartbeats(2).ok().is_some());
	});
}

#[test]
fn test_does_not_heartbeat_early_in_the_session() {
	let mut ext = new_test_ext();
	let (offchain, _state) = TestOffchainExt::new();
	let (pool, _) = TestTransactionPoolExt::new();
	ext.register_extension(OffchainDbExt::new(offchain.clone()));
	ext.register_extension(OffchainWorkerExt::new(offchain));
	ext.register_extension(TransactionPoolExt::new(pool));

	ext.execute_with(|| {
		// mock current session progress as being 5%. we only randomly start
		// heartbeating after 10% of the session has elapsed.
		MockCurrentSessionProgress::mutate(|p| *p = Some(Some(Permill::from_float(0.05))));
		assert_eq!(ImOnline::send_heartbeats(2).err(), Some(OffchainErr::TooEarly));
	});
}

#[test]
fn test_probability_of_heartbeating_increases_with_session_progress() {
	let mut ext = new_test_ext();
	let (offchain, state) = TestOffchainExt::new();
	let (pool, _) = TestTransactionPoolExt::new();
	ext.register_extension(OffchainDbExt::new(offchain.clone()));
	ext.register_extension(OffchainWorkerExt::new(offchain));
	ext.register_extension(TransactionPoolExt::new(pool));

	ext.execute_with(|| {
		let set_test = |progress, random: f64| {
			// the average session length is 100 blocks, therefore the residual
			// probability of sending a heartbeat is 1%
			MockAverageSessionLength::mutate(|p| *p = Some(100));
			MockCurrentSessionProgress::mutate(|p| *p = Some(Some(Permill::from_float(progress))));

			let mut seed = [0u8; 32];
			let encoded = ((random * Permill::ACCURACY as f64) as u32).encode();
			seed[0..4].copy_from_slice(&encoded);
			state.write().seed = seed;
		};

		let assert_too_early = |progress, random| {
			set_test(progress, random);
			assert_eq!(ImOnline::send_heartbeats(2).err(), Some(OffchainErr::TooEarly));
		};

		let assert_heartbeat_ok = |progress, random| {
			set_test(progress, random);
			assert!(ImOnline::send_heartbeats(2).ok().is_some());
		};

		assert_too_early(0.05, 1.0);

		assert_too_early(0.1, 0.1);
		assert_too_early(0.1, 0.011);
		assert_heartbeat_ok(0.1, 0.010);

		assert_too_early(0.4, 0.015);
		assert_heartbeat_ok(0.4, 0.014);

		assert_too_early(0.5, 0.026);
		assert_heartbeat_ok(0.5, 0.025);

		assert_too_early(0.6, 0.057);
		assert_heartbeat_ok(0.6, 0.056);

		assert_too_early(0.65, 0.086);
		assert_heartbeat_ok(0.65, 0.085);

		assert_too_early(0.7, 0.13);
		assert_heartbeat_ok(0.7, 0.12);

		assert_too_early(0.75, 0.19);
		assert_heartbeat_ok(0.75, 0.18);
	});
}
