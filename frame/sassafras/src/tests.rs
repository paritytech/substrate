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
fn slot_ticket_fetch() {
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
			tickets_count: [max_tickets, max_tickets - 1],
			segments_count: 0,
			sort_started: false,
		});

		// Test next session tickets fetch
		assert_eq!(Sassafras::slot_ticket(0.into()), Some(curr_tickets[1]));
		assert_eq!(Sassafras::slot_ticket(1.into()), Some(curr_tickets[3]));
		assert_eq!(Sassafras::slot_ticket(2.into()), Some(curr_tickets[5]));
		assert_eq!(Sassafras::slot_ticket(3.into()), None);
		assert_eq!(Sassafras::slot_ticket(4.into()), None);
		assert_eq!(Sassafras::slot_ticket(5.into()), None);
		assert_eq!(Sassafras::slot_ticket(6.into()), None);
		assert_eq!(Sassafras::slot_ticket(7.into()), Some(curr_tickets[4]));
		assert_eq!(Sassafras::slot_ticket(8.into()), Some(curr_tickets[2]));
		assert_eq!(Sassafras::slot_ticket(9.into()), Some(curr_tickets[0]));

		// Test next session tickets fetch
		assert_eq!(Sassafras::slot_ticket(10.into()), Some(next_tickets[1]));
		assert_eq!(Sassafras::slot_ticket(11.into()), Some(next_tickets[3]));
		assert_eq!(Sassafras::slot_ticket(12.into()), None); //Some(next_tickets[5]));
		assert_eq!(Sassafras::slot_ticket(13.into()), None);
		assert_eq!(Sassafras::slot_ticket(14.into()), None);
		assert_eq!(Sassafras::slot_ticket(15.into()), None);
		assert_eq!(Sassafras::slot_ticket(16.into()), None);
		assert_eq!(Sassafras::slot_ticket(17.into()), Some(next_tickets[4]));
		assert_eq!(Sassafras::slot_ticket(18.into()), Some(next_tickets[2]));
		assert_eq!(Sassafras::slot_ticket(19.into()), Some(next_tickets[0]));

		// Test fetch beyend next session
		assert_eq!(Sassafras::slot_ticket(20.into()), None);
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
		assert_eq!(Sassafras::current_slot_epoch_index(), 1);
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
		assert_eq!(Sassafras::current_slot_epoch_index(), 1);
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
		assert_eq!(Sassafras::current_slot_epoch_index(), 0);
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
		let mut tickets: Vec<Ticket> = make_tickets(start_slot + 1, 3 * max_tickets, &pairs[0])
			.into_iter()
			.map(|(output, _)| output)
			.collect();
		let tickets0 = tickets[0..6].to_vec().try_into().unwrap();
		Sassafras::submit_tickets(Origin::none(), tickets0).unwrap();
		let tickets1 = tickets[6..12].to_vec().try_into().unwrap();
		Sassafras::submit_tickets(Origin::none(), tickets1).unwrap();
		let tickets2 = tickets[12..18].to_vec().try_into().unwrap();
		Sassafras::submit_tickets(Origin::none(), tickets2).unwrap();

		tickets.sort();
		tickets.truncate(max_tickets as usize);
		let expected_tickets = tickets;

		// Check state after submit
		let meta = TicketsMeta::<Test>::get();
		assert!(Tickets::<Test>::iter().next().is_none());
		assert_eq!(meta.segments_count, 3);
		assert_eq!(meta.tickets_count, [0, 0]);

		// Process up to the last epoch slot (do not enact epoch change)
		let _digest = progress_to_block(epoch_duration, &pairs[0]).unwrap();

		// TODO-SASS-P2: at this point next tickets should have been sorted
		//assert_eq!(NextTicketsSegmentsCount::<Test>::get(), 0);
		//assert!(Tickets::<Test>::iter().next().is_some());

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
fn block_skips_epochs() {
	let (pairs, mut ext) = new_test_ext_with_pairs(4);

	ext.execute_with(|| {
		let start_slot = Slot::from(100);
		let start_block = 1;
		let epoch_duration: u64 = <Test as Config>::EpochDuration::get();

		let digest = make_wrapped_pre_digest(0, start_slot, &pairs[0]);
		System::initialize(&start_block, &Default::default(), &digest);
		Sassafras::on_initialize(start_block);

		let tickets: Vec<Ticket> = make_tickets(start_slot + 1, 3, &pairs[0])
			.into_iter()
			.map(|(output, _)| output)
			.collect();
		Sassafras::submit_tickets(Origin::none(), BoundedVec::truncate_from(tickets.clone()))
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
		assert_eq!(Sassafras::current_slot_epoch_index(), 0);

		// Tickets were discarded
		let meta = TicketsMeta::<Test>::get();
		assert_eq!(meta, TicketsMetadata::default());
		// We've used the last known next epoch randomness as a fallback
		assert_eq!(next_random, Sassafras::randomness());
	});
}
