// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

//! Tests for Sassafras pallet.

// TODO-SASS-P2 remove
#![allow(unused_imports)]

use crate::*;
use mock::*;

use frame_support::{
	assert_err, assert_noop, assert_ok,
	dispatch::EncodeLike,
	traits::{ConstU32, Currency, EstimateNextSessionRotation, OnFinalize, OnInitialize},
	weights::{GetDispatchInfo, Pays},
	BoundedBTreeSet,
};
use hex_literal::hex;
use pallet_session::ShouldEndSession;
use sp_consensus_sassafras::{SassafrasEpochConfiguration, Slot};
use sp_consensus_vrf::schnorrkel::{VRFOutput, VRFProof};
use sp_core::crypto::Pair;
use sp_runtime::traits::Get;
use std::collections::BTreeSet;

#[test]
fn slot_ticket_fetch() {
	let max_tickets: u32 = <Test as crate::Config>::MaxTickets::get();

	let tickets: Vec<Ticket> = (0..max_tickets as u8)
		.into_iter()
		.map(|i| [i; 32].try_into().unwrap())
		.collect();
	let tickets =
		BoundedVec::<_, _>::try_from(tickets).expect("vector has been eventually truncated; qed");

	new_test_ext(4).execute_with(|| {
		Tickets::<Test>::put(tickets.clone());

		assert_eq!(Sassafras::slot_ticket(0.into()), Some(tickets[1]));
		assert_eq!(Sassafras::slot_ticket(1.into()), Some(tickets[3]));
		assert_eq!(Sassafras::slot_ticket(2.into()), Some(tickets[5]));
		assert_eq!(Sassafras::slot_ticket(3.into()), None);
		assert_eq!(Sassafras::slot_ticket(4.into()), None);
		assert_eq!(Sassafras::slot_ticket(5.into()), None);
		assert_eq!(Sassafras::slot_ticket(6.into()), None);
		assert_eq!(Sassafras::slot_ticket(7.into()), Some(tickets[4]));
		assert_eq!(Sassafras::slot_ticket(8.into()), Some(tickets[2]));
		assert_eq!(Sassafras::slot_ticket(9.into()), Some(tickets[0]));

		// TODO-SASS-P2: test next epoch tickets fetch
		assert_eq!(Sassafras::slot_ticket(10.into()), None);

		assert_eq!(Sassafras::slot_ticket(42.into()), None);
	});
}

#[test]
fn genesis_values() {
	new_test_ext(4).execute_with(|| {
		assert_eq!(Sassafras::authorities().len(), 4);
		assert_eq!(EpochConfig::<Test>::get(), Default::default());
	});
}

#[test]
fn on_first_after_genesis_block() {
	let (pairs, mut ext) = new_test_ext_with_pairs(4);

	ext.execute_with(|| {
		let start_slot = Slot::from(100);
		let start_block = 1;

		let digest = make_wrapped_pre_digest(0, start_slot, &pairs[0]);
		System::initialize(&start_block, &Default::default(), &digest);
		Sassafras::on_initialize(start_block);

		// Post-initialization status

		assert!(Initialized::<Test>::get().is_some());
		assert_eq!(Sassafras::genesis_slot(), start_slot);
		assert_eq!(Sassafras::current_slot(), start_slot);
		assert_eq!(Sassafras::epoch_index(), 0);
		assert_eq!(Sassafras::current_epoch_start(), start_slot);
		assert_eq!(Sassafras::current_slot_epoch_index(), 0);
		assert_eq!(Sassafras::randomness(), [0; 32]);
		assert_eq!(NextRandomness::<Test>::get(), [0; 32]);
		assert_eq!(RandomnessAccumulator::<Test>::get(), [0; 32]);

		Sassafras::on_finalize(1);
		let header = System::finalize();

		// Post-finalization status

		assert!(Initialized::<Test>::get().is_none());
		assert_eq!(Sassafras::genesis_slot(), start_slot);
		assert_eq!(Sassafras::current_slot(), start_slot);
		assert_eq!(Sassafras::epoch_index(), 0);
		assert_eq!(Sassafras::current_epoch_start(), start_slot);
		assert_eq!(Sassafras::current_slot_epoch_index(), 0);
		assert_eq!(Sassafras::randomness(), [0; 32]);
		assert_eq!(NextRandomness::<Test>::get(), [0; 32]);
		assert_eq!(
			RandomnessAccumulator::<Test>::get(),
			hex!("98dc63bd10704f60016011be269a02ec780e9b870222d12457ea7e8a05065028"),
		);

		// Header data check

		assert_eq!(header.digest.logs.len(), 2);
		assert_eq!(header.digest.logs[0], digest.logs[0]);

		// Genesis epoch start deposits consensus
		let consensus_log = sp_consensus_sassafras::digests::ConsensusLog::NextEpochData(
			sp_consensus_sassafras::digests::NextEpochDescriptor {
				authorities: NextAuthorities::<Test>::get().to_vec(),
				randomness: NextRandomness::<Test>::get(),
			},
		);
		let consensus_digest = DigestItem::Consensus(SASSAFRAS_ENGINE_ID, consensus_log.encode());
		assert_eq!(header.digest.logs[1], consensus_digest)
	})
}

#[test]
fn on_normal_block() {
	let (pairs, mut ext) = new_test_ext_with_pairs(4);

	ext.execute_with(|| {
		let start_slot = Slot::from(100);
		let start_block = 1;

		let digest = make_wrapped_pre_digest(0, start_slot, &pairs[0]);
		System::initialize(&start_block, &Default::default(), &digest);
		Sassafras::on_initialize(start_block);

		// We don't want to trigger an epoch change in this test.
		let epoch_duration: u64 = <Test as Config>::EpochDuration::get();
		assert!(epoch_duration > 2);
		let digest = progress_to_block(2, &pairs[0]).unwrap();

		// Post-initialization status

		assert!(Initialized::<Test>::get().is_some());
		assert_eq!(Sassafras::genesis_slot(), start_slot);
		assert_eq!(Sassafras::current_slot(), start_slot + 1);
		assert_eq!(Sassafras::epoch_index(), 0);
		assert_eq!(Sassafras::current_epoch_start(), start_slot);
		assert_eq!(Sassafras::current_slot_epoch_index(), 1);
		assert_eq!(Sassafras::randomness(), [0; 32]);
		assert_eq!(NextRandomness::<Test>::get(), [0; 32]);
		assert_eq!(
			RandomnessAccumulator::<Test>::get(),
			hex!("98dc63bd10704f60016011be269a02ec780e9b870222d12457ea7e8a05065028"),
		);

		Sassafras::on_finalize(2);
		let header = System::finalize();

		// Post-finalization status

		assert!(Initialized::<Test>::get().is_none());
		assert_eq!(Sassafras::genesis_slot(), start_slot);
		assert_eq!(Sassafras::current_slot(), start_slot + 1);
		assert_eq!(Sassafras::epoch_index(), 0);
		assert_eq!(Sassafras::current_epoch_start(), start_slot);
		assert_eq!(Sassafras::current_slot_epoch_index(), 1);
		assert_eq!(Sassafras::randomness(), [0; 32]);
		assert_eq!(NextRandomness::<Test>::get(), [0; 32]);
		assert_eq!(
			RandomnessAccumulator::<Test>::get(),
			hex!("180f852e5a4f4370071072402c395758efdb2a417e99deaed34acc269125ac3e"),
		);

		// Header data check

		assert_eq!(header.digest.logs.len(), 1);
		assert_eq!(header.digest.logs[0], digest.logs[0]);
	});
}

#[test]
fn epoch_change_block() {
	let (pairs, mut ext) = new_test_ext_with_pairs(4);

	ext.execute_with(|| {
		let start_slot = Slot::from(100);
		let start_block = 1;

		let digest = make_wrapped_pre_digest(0, start_slot, &pairs[0]);
		System::initialize(&start_block, &Default::default(), &digest);
		Sassafras::on_initialize(start_block);

		// We want to trigger an epoch change in this test.
		let epoch_duration: u64 = <Test as Config>::EpochDuration::get();
		let digest = progress_to_block(start_block + epoch_duration, &pairs[0]).unwrap();

		// Post-initialization status

		assert!(Initialized::<Test>::get().is_some());
		assert_eq!(Sassafras::genesis_slot(), start_slot);
		assert_eq!(Sassafras::current_slot(), start_slot + epoch_duration);
		assert_eq!(Sassafras::epoch_index(), 1);
		assert_eq!(Sassafras::current_epoch_start(), start_slot + epoch_duration);
		assert_eq!(Sassafras::current_slot_epoch_index(), 0);
		assert_eq!(Sassafras::randomness(), [0; 32],);
		assert_eq!(
			NextRandomness::<Test>::get(),
			hex!("dae0db238bd08ec36537d924cade5e5ad668e83f4e9a200a1e6aa1102919c999"),
		);
		assert_eq!(
			RandomnessAccumulator::<Test>::get(),
			hex!("4cfa0840c842f6095155b35bad7f0bf8113c11a12a8ab3e3d116d91b0e8f31f9"),
		);

		Sassafras::on_finalize(start_block + epoch_duration);
		let header = System::finalize();

		// Post-finalization status

		assert!(Initialized::<Test>::get().is_none());
		assert_eq!(Sassafras::genesis_slot(), start_slot);
		assert_eq!(Sassafras::current_slot(), start_slot + epoch_duration);
		assert_eq!(Sassafras::epoch_index(), 1);
		assert_eq!(Sassafras::current_epoch_start(), start_slot + epoch_duration);
		assert_eq!(Sassafras::current_slot_epoch_index(), 0);
		assert_eq!(Sassafras::randomness(), [0; 32]);
		assert_eq!(
			NextRandomness::<Test>::get(),
			hex!("dae0db238bd08ec36537d924cade5e5ad668e83f4e9a200a1e6aa1102919c999"),
		);
		assert_eq!(
			RandomnessAccumulator::<Test>::get(),
			hex!("98ed5e9a57afafaea3fddd98555a616f0fefdde27e316ca42cd29de323f90d2a"),
		);

		// Header data check

		assert_eq!(header.digest.logs.len(), 2);
		assert_eq!(header.digest.logs[0], digest.logs[0]);
		// Deposits consensus log on epoch change
		let consensus_log = sp_consensus_sassafras::digests::ConsensusLog::NextEpochData(
			sp_consensus_sassafras::digests::NextEpochDescriptor {
				authorities: NextAuthorities::<Test>::get().to_vec(),
				randomness: NextRandomness::<Test>::get(),
			},
		);
		let consensus_digest = DigestItem::Consensus(SASSAFRAS_ENGINE_ID, consensus_log.encode());
		assert_eq!(header.digest.logs[1], consensus_digest)
	})
}

#[test]
fn submit_enact_claim_tickets() {
	let (pairs, mut ext) = new_test_ext_with_pairs(4);

	ext.execute_with(|| {
		let start_slot = Slot::from(100);
		let start_block = 1;

		let digest = make_wrapped_pre_digest(0, start_slot, &pairs[0]);
		System::initialize(&start_block, &Default::default(), &digest);
		Sassafras::on_initialize(start_block);

		// We don't want to trigger an epoch change in this test.
		let epoch_duration: u64 = <Test as Config>::EpochDuration::get();
		assert!(epoch_duration > 2);
		let _digest = progress_to_block(2, &pairs[0]).unwrap();

		// Check state before tickets submission
		assert!(Tickets::<Test>::get().is_empty());
		assert!(NextTickets::<Test>::get().is_empty());

		// Submit authoring tickets.
		let mut tickets: Vec<Ticket> = make_tickets(start_slot + 1, 30, &pairs[0])
			.into_iter()
			.map(|(output, _)| output)
			.collect();

		Sassafras::submit_tickets(Origin::none(), tickets.clone()).unwrap();

		let max_tickets: u32 = <Test as Config>::MaxTickets::get();
		tickets.sort();
		let front = tickets.iter().take(max_tickets as usize / 2);
		let back = tickets.iter().rev().take(max_tickets as usize / 2);
		let mut expected_tickets = front.chain(back).map(|t| *t).collect::<Vec<_>>();
		expected_tickets.sort();

		// Check state
		assert!(Tickets::<Test>::get().is_empty());
		let next_tickets = NextTickets::<Test>::get().into_iter().collect::<Vec<Ticket>>();
		assert_eq!(expected_tickets, next_tickets);

		// Process up to the last epoch slot (do not enact epoch change)
		let _digest = progress_to_block(epoch_duration, &pairs[0]).unwrap();
		assert!(Tickets::<Test>::get().is_empty());
		let next_tickets = NextTickets::<Test>::get().into_iter().collect::<Vec<Ticket>>();
		assert_eq!(expected_tickets, next_tickets);

		// Check if we can claim next epoch tickets in outside-in fashion.
		//
		// This is to allow native code to eventually fetch the first ticket for a new epoch,
		// before the epoch data is effectivelly enacted by the runtime
		// (block authors tries to claim a ticket before block construction).
		let slot = Sassafras::current_slot();
		assert_eq!(Sassafras::slot_ticket(slot + 1).unwrap(), expected_tickets[1]);
		assert_eq!(Sassafras::slot_ticket(slot + 2).unwrap(), expected_tickets[3]);
		assert_eq!(Sassafras::slot_ticket(slot + 3).unwrap(), expected_tickets[5]);
		assert!(Sassafras::slot_ticket(slot + 4).is_none());
		assert!(Sassafras::slot_ticket(slot + 7).is_none());
		assert_eq!(Sassafras::slot_ticket(slot + 8).unwrap(), expected_tickets[4]);
		assert_eq!(Sassafras::slot_ticket(slot + 9).unwrap(), expected_tickets[2]);
		assert_eq!(Sassafras::slot_ticket(slot + 10).unwrap(), expected_tickets[0]);
		assert!(Sassafras::slot_ticket(slot + 11).is_none());

		// Enact epoch tickets by progressing one more block

		let _digest = progress_to_block(epoch_duration + 1, &pairs[0]).unwrap();
		let curr_tickets = Tickets::<Test>::get().into_iter().collect::<Vec<Ticket>>();
		assert_eq!(expected_tickets, curr_tickets);
		assert!(NextTickets::<Test>::get().is_empty());

		let slot = Sassafras::current_slot();
		assert_eq!(Sassafras::slot_ticket(slot).unwrap(), expected_tickets[1]);
		assert_eq!(Sassafras::slot_ticket(slot + 1).unwrap(), expected_tickets[3]);
		assert_eq!(Sassafras::slot_ticket(slot + 2).unwrap(), expected_tickets[5]);
		assert!(Sassafras::slot_ticket(slot + 3).is_none());
		assert!(Sassafras::slot_ticket(slot + 6).is_none());
		assert_eq!(Sassafras::slot_ticket(slot + 7).unwrap(), expected_tickets[4]);
		assert_eq!(Sassafras::slot_ticket(slot + 8).unwrap(), expected_tickets[2]);
		assert_eq!(Sassafras::slot_ticket(slot + 9).unwrap(), expected_tickets[0]);
		assert!(Sassafras::slot_ticket(slot + 10).is_none());
	});
}

#[test]
fn block_skips_epochs() {
	let (pairs, mut ext) = new_test_ext_with_pairs(4);

	ext.execute_with(|| {
		let start_slot = Slot::from(100);
		let start_block = 1;

		let digest = make_wrapped_pre_digest(0, start_slot, &pairs[0]);
		System::initialize(&start_block, &Default::default(), &digest);
		Sassafras::on_initialize(start_block);

		let tickets: Vec<Ticket> = make_tickets(start_slot + 1, 30, &pairs[0])
			.into_iter()
			.map(|(output, _)| output)
			.collect();
		Sassafras::submit_tickets(Origin::none(), tickets.clone()).unwrap();

		assert!(Tickets::<Test>::get().is_empty());
		assert!(!NextTickets::<Test>::get().is_empty());
		let next_random = NextRandomness::<Test>::get();

		// We want to trigger an skip epoch in this test.
		let epoch_duration: u64 = <Test as Config>::EpochDuration::get();
		let offset = 3 * epoch_duration;
		let _digest = go_to_block(start_block + offset, start_slot + offset, &pairs[0]);

		// Post-initialization status

		assert!(Initialized::<Test>::get().is_some());
		assert_eq!(Sassafras::genesis_slot(), start_slot);
		assert_eq!(Sassafras::current_slot(), start_slot + offset);
		assert_eq!(Sassafras::epoch_index(), 3);
		assert_eq!(Sassafras::current_epoch_start(), start_slot + offset);
		assert_eq!(Sassafras::current_slot_epoch_index(), 0);
		// Tickets were discarded
		assert!(Tickets::<Test>::get().is_empty());
		assert!(NextTickets::<Test>::get().is_empty());
		// We've used the last known next epoch randomness as a fallback
		assert_eq!(next_random, Sassafras::randomness());
	});
}
