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

use crate::*;
use mock::*;

use frame_support::traits::{OnFinalize, OnInitialize};
use hex_literal::hex;
use sp_consensus_sassafras::Slot;
use sp_runtime::traits::Get;

#[test]
fn genesis_values_sanity_check() {
	new_test_ext(4).execute_with(|| {
		assert_eq!(Sassafras::authorities().len(), 4);
		assert_eq!(EpochConfig::<Test>::get(), Default::default());
	});
}

#[test]
fn slot_ticket_fetch() {
	let genesis_slot = Slot::from(100);
	let max_tickets: u32 = <Test as crate::Config>::MaxTickets::get();
	assert_eq!(max_tickets, 6);

	let curr_tickets: Vec<Ticket> = (0..max_tickets as u8)
		.into_iter()
		.map(|i| [i; 32].try_into().unwrap())
		.collect();

	let next_tickets: Vec<Ticket> = (0..(max_tickets - 1) as u8)
		.into_iter()
		.map(|i| [max_tickets as u8 + i; 32].try_into().unwrap())
		.collect();

	new_test_ext(4).execute_with(|| {
		curr_tickets.iter().enumerate().for_each(|(i, ticket)| {
			Tickets::<Test>::insert((0, i as u32), ticket);
		});
		next_tickets.iter().enumerate().for_each(|(i, ticket)| {
			Tickets::<Test>::insert((1, i as u32), ticket);
		});
		TicketsMeta::<Test>::set(TicketsMetadata {
			tickets_count: [curr_tickets.len() as u32, next_tickets.len() as u32],
			segments_count: 0,
		});

		// Before initializing `GenesisSlot` value the pallet always return the first slot
		// This is a kind of special case hardcoded policy that should never happen in practice
		// (i.e. the first thing the pallet does is to initialize the genesis slot).
		assert_eq!(Sassafras::slot_ticket(0.into()), Some(curr_tickets[1]));
		assert_eq!(Sassafras::slot_ticket(genesis_slot + 0), Some(curr_tickets[1]));
		assert_eq!(Sassafras::slot_ticket(genesis_slot + 1), Some(curr_tickets[1]));
		assert_eq!(Sassafras::slot_ticket(genesis_slot + 100), Some(curr_tickets[1]));

		// Initialize genesis slot..
		GenesisSlot::<Test>::set(genesis_slot);

		// Try fetch a ticket for a slot before current session.
		assert_eq!(Sassafras::slot_ticket(0.into()), None);

		// Current session tickets.
		assert_eq!(Sassafras::slot_ticket(genesis_slot + 0), Some(curr_tickets[1]));
		assert_eq!(Sassafras::slot_ticket(genesis_slot + 1), Some(curr_tickets[3]));
		assert_eq!(Sassafras::slot_ticket(genesis_slot + 2), Some(curr_tickets[5]));
		assert_eq!(Sassafras::slot_ticket(genesis_slot + 3), None);
		assert_eq!(Sassafras::slot_ticket(genesis_slot + 4), None);
		assert_eq!(Sassafras::slot_ticket(genesis_slot + 5), None);
		assert_eq!(Sassafras::slot_ticket(genesis_slot + 6), None);
		assert_eq!(Sassafras::slot_ticket(genesis_slot + 7), Some(curr_tickets[4]));
		assert_eq!(Sassafras::slot_ticket(genesis_slot + 8), Some(curr_tickets[2]));
		assert_eq!(Sassafras::slot_ticket(genesis_slot + 9), Some(curr_tickets[0]));

		// Next session tickets.
		assert_eq!(Sassafras::slot_ticket(genesis_slot + 10), Some(next_tickets[1]));
		assert_eq!(Sassafras::slot_ticket(genesis_slot + 11), Some(next_tickets[3]));
		assert_eq!(Sassafras::slot_ticket(genesis_slot + 12), None); //Some(next_tickets[5]));
		assert_eq!(Sassafras::slot_ticket(genesis_slot + 13), None);
		assert_eq!(Sassafras::slot_ticket(genesis_slot + 14), None);
		assert_eq!(Sassafras::slot_ticket(genesis_slot + 15), None);
		assert_eq!(Sassafras::slot_ticket(genesis_slot + 16), None);
		assert_eq!(Sassafras::slot_ticket(genesis_slot + 17), Some(next_tickets[4]));
		assert_eq!(Sassafras::slot_ticket(genesis_slot + 18), Some(next_tickets[2]));
		assert_eq!(Sassafras::slot_ticket(genesis_slot + 19), Some(next_tickets[0]));

		// Try fetch tickets for slots beyend next session.
		assert_eq!(Sassafras::slot_ticket(genesis_slot + 20), None);
		assert_eq!(Sassafras::slot_ticket(genesis_slot + 42), None);
	});
}

#[test]
fn on_first_block_after_genesis() {
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
		assert_eq!(Sassafras::current_slot_index(), 0);
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
		assert_eq!(Sassafras::current_slot_index(), 0);
		assert_eq!(Sassafras::randomness(), [0; 32]);
		assert_eq!(NextRandomness::<Test>::get(), [0; 32]);
		assert_eq!(
			RandomnessAccumulator::<Test>::get(),
			hex!("50f7d623e15560a3681b085d0dc67b12fa16fefe5366987b58e0c16ba412a14a"),
		);

		// Header data check

		assert_eq!(header.digest.logs.len(), 2);
		assert_eq!(header.digest.logs[0], digest.logs[0]);

		// Genesis epoch start deposits consensus
		let consensus_log = sp_consensus_sassafras::digests::ConsensusLog::NextEpochData(
			sp_consensus_sassafras::digests::NextEpochDescriptor {
				authorities: NextAuthorities::<Test>::get().to_vec(),
				randomness: NextRandomness::<Test>::get(),
				config: None,
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
		assert_eq!(Sassafras::current_slot_index(), 1);
		assert_eq!(Sassafras::randomness(), [0; 32]);
		assert_eq!(NextRandomness::<Test>::get(), [0; 32]);
		assert_eq!(
			RandomnessAccumulator::<Test>::get(),
			hex!("50f7d623e15560a3681b085d0dc67b12fa16fefe5366987b58e0c16ba412a14a"),
		);

		Sassafras::on_finalize(2);
		let header = System::finalize();

		// Post-finalization status

		assert!(Initialized::<Test>::get().is_none());
		assert_eq!(Sassafras::genesis_slot(), start_slot);
		assert_eq!(Sassafras::current_slot(), start_slot + 1);
		assert_eq!(Sassafras::epoch_index(), 0);
		assert_eq!(Sassafras::current_epoch_start(), start_slot);
		assert_eq!(Sassafras::current_slot_index(), 1);
		assert_eq!(Sassafras::randomness(), [0; 32]);
		assert_eq!(NextRandomness::<Test>::get(), [0; 32]);
		assert_eq!(
			RandomnessAccumulator::<Test>::get(),
			hex!("ea16f22af4afe5bfb8e3be3e257c3a88ae0c2406a4afc067871b6e5a7ae8756e"),
		);

		// Header data check

		assert_eq!(header.digest.logs.len(), 1);
		assert_eq!(header.digest.logs[0], digest.logs[0]);
	});
}

#[test]
fn produce_epoch_change_digest() {
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
		assert_eq!(Sassafras::current_slot_index(), 0);
		assert_eq!(Sassafras::randomness(), [0; 32],);
		assert_eq!(
			NextRandomness::<Test>::get(),
			hex!("99da0ef0252bb8104737d1db0d80ae46079024c377f5bcecfe6545bd93c38d7b"),
		);
		assert_eq!(
			RandomnessAccumulator::<Test>::get(),
			hex!("ec9f2acd75e3a901b3a3fad95267a275af1aded3df8bebebb8d14ebd2190ce59"),
		);

		Sassafras::on_finalize(start_block + epoch_duration);
		let header = System::finalize();

		// Post-finalization status

		assert!(Initialized::<Test>::get().is_none());
		assert_eq!(Sassafras::genesis_slot(), start_slot);
		assert_eq!(Sassafras::current_slot(), start_slot + epoch_duration);
		assert_eq!(Sassafras::epoch_index(), 1);
		assert_eq!(Sassafras::current_epoch_start(), start_slot + epoch_duration);
		assert_eq!(Sassafras::current_slot_index(), 0);
		assert_eq!(Sassafras::randomness(), [0; 32]);
		assert_eq!(
			NextRandomness::<Test>::get(),
			hex!("99da0ef0252bb8104737d1db0d80ae46079024c377f5bcecfe6545bd93c38d7b"),
		);
		assert_eq!(
			RandomnessAccumulator::<Test>::get(),
			hex!("d017578d6bad1856315866ce1ef845c2584873fcbc011db7dcb99f1f19baa6f3"),
		);

		// Header data check

		assert_eq!(header.digest.logs.len(), 2);
		assert_eq!(header.digest.logs[0], digest.logs[0]);
		// Deposits consensus log on epoch change
		let consensus_log = sp_consensus_sassafras::digests::ConsensusLog::NextEpochData(
			sp_consensus_sassafras::digests::NextEpochDescriptor {
				authorities: NextAuthorities::<Test>::get().to_vec(),
				randomness: NextRandomness::<Test>::get(),
				config: None,
			},
		);
		let consensus_digest = DigestItem::Consensus(SASSAFRAS_ENGINE_ID, consensus_log.encode());
		assert_eq!(header.digest.logs[1], consensus_digest)
	})
}

#[test]
fn produce_epoch_change_digest_with_config() {
	let (pairs, mut ext) = new_test_ext_with_pairs(4);

	ext.execute_with(|| {
		let start_slot = Slot::from(100);
		let start_block = 1;

		let digest = make_wrapped_pre_digest(0, start_slot, &pairs[0]);
		System::initialize(&start_block, &Default::default(), &digest);
		Sassafras::on_initialize(start_block);

		let config = SassafrasEpochConfiguration { redundancy_factor: 1, attempts_number: 123 };
		Sassafras::plan_config_change(RuntimeOrigin::root(), config.clone()).unwrap();

		// We want to trigger an epoch change in this test.
		let epoch_duration: u64 = <Test as Config>::EpochDuration::get();
		let digest = progress_to_block(start_block + epoch_duration, &pairs[0]).unwrap();

		Sassafras::on_finalize(start_block + epoch_duration);

		// Header data check.
		// Skip pallet status checks that were already performed by other tests.

		let header = System::finalize();
		assert_eq!(header.digest.logs.len(), 2);
		assert_eq!(header.digest.logs[0], digest.logs[0]);
		// Deposits consensus log on epoch change
		let consensus_log = sp_consensus_sassafras::digests::ConsensusLog::NextEpochData(
			sp_consensus_sassafras::digests::NextEpochDescriptor {
				authorities: NextAuthorities::<Test>::get().to_vec(),
				randomness: NextRandomness::<Test>::get(),
				config: Some(config), // We are mostly interested in this
			},
		);
		let consensus_digest = DigestItem::Consensus(SASSAFRAS_ENGINE_ID, consensus_log.encode());
		assert_eq!(header.digest.logs[1], consensus_digest)
	})
}

#[test]
fn segments_incremental_sortition_works() {
	let (pairs, mut ext) = new_test_ext_with_pairs(1);
	let pair = &pairs[0];
	let segments_num = 14;

	ext.execute_with(|| {
		let start_slot = Slot::from(100);
		let start_block = 1;
		let max_tickets: u32 = <Test as Config>::MaxTickets::get();

		let digest = make_wrapped_pre_digest(0, start_slot, &pairs[0]);
		System::initialize(&start_block, &Default::default(), &digest);
		Sassafras::on_initialize(start_block);

		// Submit authoring tickets in three different batches.
		// We can ignore the threshold since we are not passing through the unsigned extrinsic
		// validation.
		let tickets: Vec<TicketEnvelope> =
			make_tickets(start_slot + 1, segments_num * max_tickets, pair);
		let segment_len = tickets.len() / segments_num as usize;
		for i in 0..segments_num as usize {
			let segment =
				tickets[i * segment_len..(i + 1) * segment_len].to_vec().try_into().unwrap();
			Sassafras::submit_tickets(RuntimeOrigin::none(), segment).unwrap();
		}

		let epoch_duration: u64 = <Test as Config>::EpochDuration::get();

		// Proceed to half of the epoch (sortition should not have been started yet)
		let half_epoch_block = start_block + epoch_duration / 2;
		progress_to_block(half_epoch_block, pair);

		// Check that next epoch tickets sortition is not started yet
		let meta = TicketsMeta::<Test>::get();
		assert_eq!(meta.segments_count, segments_num);
		assert_eq!(meta.tickets_count, [0, 0]);

		// Monitor incremental sortition

		progress_to_block(half_epoch_block + 1, pair);
		let meta = TicketsMeta::<Test>::get();
		assert_eq!(meta.segments_count, 12);
		assert_eq!(meta.tickets_count, [0, 0]);

		progress_to_block(half_epoch_block + 2, pair);
		let meta = TicketsMeta::<Test>::get();
		assert_eq!(meta.segments_count, 9);
		assert_eq!(meta.tickets_count, [0, 0]);

		progress_to_block(half_epoch_block + 3, pair);
		let meta = TicketsMeta::<Test>::get();
		assert_eq!(meta.segments_count, 6);
		assert_eq!(meta.tickets_count, [0, 0]);

		progress_to_block(half_epoch_block + 4, pair);
		let meta = TicketsMeta::<Test>::get();
		assert_eq!(meta.segments_count, 3);
		assert_eq!(meta.tickets_count, [0, 0]);

		Sassafras::on_finalize(half_epoch_block + 4);
		let header = System::finalize();
		let meta = TicketsMeta::<Test>::get();
		assert_eq!(meta.segments_count, 0);
		assert_eq!(meta.tickets_count, [0, 6]);
		assert_eq!(header.digest.logs.len(), 1);

		// The next block will be the first produced on the new epoch,
		// At this point the tickets were found to be sorted and ready to be used.
		let slot = Sassafras::current_slot() + 1;
		let digest = make_wrapped_pre_digest(0, slot, pair);
		let number = System::block_number() + 1;
		System::initialize(&number, &header.hash(), &digest);
		Sassafras::on_initialize(number);
		Sassafras::on_finalize(half_epoch_block + 5);
		let header = System::finalize();
		assert_eq!(header.digest.logs.len(), 2);
	});
}

#[test]
fn submit_enact_claim_tickets() {
	let (pairs, mut ext) = new_test_ext_with_pairs(4);

	ext.execute_with(|| {
		let start_slot = Slot::from(100);
		let start_block = 1;
		let max_tickets: u32 = <Test as Config>::MaxTickets::get();

		let digest = make_wrapped_pre_digest(0, start_slot, &pairs[0]);
		System::initialize(&start_block, &Default::default(), &digest);
		Sassafras::on_initialize(start_block);

		// We don't want to trigger an epoch change in this test.
		let epoch_duration: u64 = <Test as Config>::EpochDuration::get();
		assert!(epoch_duration > 2);
		let _digest = progress_to_block(2, &pairs[0]).unwrap();

		// Check state before tickets submission
		assert!(Tickets::<Test>::iter().next().is_none());

		// Submit authoring tickets in three different batches.
		// We can ignore the threshold since we are not passing through the unsigned extrinsic
		// validation.
		let tickets: Vec<TicketEnvelope> = make_tickets(start_slot + 1, 3 * max_tickets, &pairs[0]);
		let tickets0 = tickets[0..6].to_vec().try_into().unwrap();
		Sassafras::submit_tickets(RuntimeOrigin::none(), tickets0).unwrap();
		let tickets1 = tickets[6..12].to_vec().try_into().unwrap();
		Sassafras::submit_tickets(RuntimeOrigin::none(), tickets1).unwrap();
		let tickets2 = tickets[12..18].to_vec().try_into().unwrap();
		Sassafras::submit_tickets(RuntimeOrigin::none(), tickets2).unwrap();

		let mut expected_tickets: Vec<_> = tickets.into_iter().map(|t| t.ticket).collect();
		expected_tickets.sort();
		expected_tickets.truncate(max_tickets as usize);

		// Check state after submit
		let meta = TicketsMeta::<Test>::get();
		assert!(Tickets::<Test>::iter().next().is_none());
		assert_eq!(meta.segments_count, 3);
		assert_eq!(meta.tickets_count, [0, 0]);

		// Process up to the last epoch slot (do not enact epoch change)
		let _digest = progress_to_block(epoch_duration, &pairs[0]).unwrap();

		// At this point next tickets should have been sorted
		let meta = TicketsMeta::<Test>::get();
		assert_eq!(meta.segments_count, 0);
		assert_eq!(meta.tickets_count, [0, 6]);

		// Check if we can claim next epoch tickets in outside-in fashion.
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

		// Enact session change by progressing one more block

		let _digest = progress_to_block(epoch_duration + 1, &pairs[0]).unwrap();

		let meta = TicketsMeta::<Test>::get();
		assert_eq!(meta.segments_count, 0);
		assert_eq!(meta.tickets_count, [0, 6]);

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
fn block_allowed_to_skip_epochs() {
	let (pairs, mut ext) = new_test_ext_with_pairs(4);

	ext.execute_with(|| {
		let start_slot = Slot::from(100);
		let start_block = 1;
		let epoch_duration: u64 = <Test as Config>::EpochDuration::get();

		let digest = make_wrapped_pre_digest(0, start_slot, &pairs[0]);
		System::initialize(&start_block, &Default::default(), &digest);
		Sassafras::on_initialize(start_block);

		let tickets: Vec<TicketEnvelope> = make_tickets(start_slot + 1, 3, &pairs[0]);
		Sassafras::submit_tickets(
			RuntimeOrigin::none(),
			BoundedVec::truncate_from(tickets.clone()),
		)
		.unwrap();

		// Force enact of next tickets
		assert_eq!(TicketsMeta::<Test>::get().segments_count, 1);
		Sassafras::slot_ticket(start_slot + epoch_duration).unwrap();
		assert_eq!(TicketsMeta::<Test>::get().segments_count, 0);

		let next_random = NextRandomness::<Test>::get();

		// We want to trigger an skip epoch in this test.
		let offset = 3 * epoch_duration;
		let _digest = go_to_block(start_block + offset, start_slot + offset, &pairs[0]);

		// Post-initialization status

		assert!(Initialized::<Test>::get().is_some());
		assert_eq!(Sassafras::genesis_slot(), start_slot);
		assert_eq!(Sassafras::current_slot(), start_slot + offset);
		assert_eq!(Sassafras::epoch_index(), 3);
		assert_eq!(Sassafras::current_epoch_start(), start_slot + offset);
		assert_eq!(Sassafras::current_slot_index(), 0);

		// Tickets were discarded
		let meta = TicketsMeta::<Test>::get();
		assert_eq!(meta, TicketsMetadata::default());
		// We've used the last known next epoch randomness as a fallback
		assert_eq!(next_random, Sassafras::randomness());
	});
}
