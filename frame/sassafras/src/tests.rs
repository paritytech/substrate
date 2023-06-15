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

use sp_consensus_sassafras::Slot;
use sp_runtime::traits::Get;

fn h2b<const N: usize>(hex: &str) -> [u8; N] {
	array_bytes::hex2array_unchecked(hex)
}

fn b2h<const N: usize>(bytes: [u8; N]) -> String {
	array_bytes::bytes2hex("", &bytes)
}

#[test]
fn genesis_values_assumptions_check() {
	new_test_ext(4).execute_with(|| {
		assert_eq!(Sassafras::authorities().len(), 4);
		assert_eq!(EpochConfig::<Test>::get(), TEST_EPOCH_CONFIGURATION);
	});
}

#[test]
fn slot_ticket_id_fetch() {
	let genesis_slot = Slot::from(100);
	let max_tickets: u32 = <Test as crate::Config>::MaxTickets::get();
	assert_eq!(max_tickets, 6);

	// Current epoch tickets
	let curr_tickets: Vec<TicketId> = (0..max_tickets).map(|i| i as TicketId).collect();

	let next_tickets: Vec<TicketId> =
		(0..max_tickets - 1).map(|i| (i + max_tickets) as TicketId).collect();

	new_test_ext(4).execute_with(|| {
		curr_tickets
			.iter()
			.enumerate()
			.for_each(|(i, id)| TicketsIds::<Test>::insert((0, i as u32), id));

		next_tickets
			.iter()
			.enumerate()
			.for_each(|(i, id)| TicketsIds::<Test>::insert((1, i as u32), id));

		TicketsMeta::<Test>::set(TicketsMetadata {
			tickets_count: [curr_tickets.len() as u32, next_tickets.len() as u32],
			segments_count: 0,
		});

		// Before initializing `GenesisSlot` value the pallet always return the first slot
		// This is a kind of special hardcoded case that should never happen in practice
		// (i.e. the first thing the pallet does is to initialize the genesis slot).

		assert_eq!(Sassafras::slot_ticket_id(0.into()), Some(curr_tickets[1]));
		assert_eq!(Sassafras::slot_ticket_id(genesis_slot + 0), Some(curr_tickets[1]));
		assert_eq!(Sassafras::slot_ticket_id(genesis_slot + 1), Some(curr_tickets[1]));
		assert_eq!(Sassafras::slot_ticket_id(genesis_slot + 100), Some(curr_tickets[1]));

		// Initialize genesis slot..
		GenesisSlot::<Test>::set(genesis_slot);

		// Try fetch a ticket for a slot before current epoch.
		assert_eq!(Sassafras::slot_ticket_id(0.into()), None);

		// Current epoch tickets.
		assert_eq!(Sassafras::slot_ticket_id(genesis_slot + 0), Some(curr_tickets[1]));
		assert_eq!(Sassafras::slot_ticket_id(genesis_slot + 1), Some(curr_tickets[3]));
		assert_eq!(Sassafras::slot_ticket_id(genesis_slot + 2), Some(curr_tickets[5]));
		assert_eq!(Sassafras::slot_ticket_id(genesis_slot + 3), None);
		assert_eq!(Sassafras::slot_ticket_id(genesis_slot + 4), None);
		assert_eq!(Sassafras::slot_ticket_id(genesis_slot + 5), None);
		assert_eq!(Sassafras::slot_ticket_id(genesis_slot + 6), None);
		assert_eq!(Sassafras::slot_ticket_id(genesis_slot + 7), Some(curr_tickets[4]));
		assert_eq!(Sassafras::slot_ticket_id(genesis_slot + 8), Some(curr_tickets[2]));
		assert_eq!(Sassafras::slot_ticket_id(genesis_slot + 9), Some(curr_tickets[0]));

		// Next epoch tickets (note that only 5 tickets are available)
		assert_eq!(Sassafras::slot_ticket_id(genesis_slot + 10), Some(next_tickets[1]));
		assert_eq!(Sassafras::slot_ticket_id(genesis_slot + 11), Some(next_tickets[3]));
		assert_eq!(Sassafras::slot_ticket_id(genesis_slot + 12), None);
		assert_eq!(Sassafras::slot_ticket_id(genesis_slot + 13), None);
		assert_eq!(Sassafras::slot_ticket_id(genesis_slot + 14), None);
		assert_eq!(Sassafras::slot_ticket_id(genesis_slot + 15), None);
		assert_eq!(Sassafras::slot_ticket_id(genesis_slot + 16), None);
		assert_eq!(Sassafras::slot_ticket_id(genesis_slot + 17), Some(next_tickets[4]));
		assert_eq!(Sassafras::slot_ticket_id(genesis_slot + 18), Some(next_tickets[2]));
		assert_eq!(Sassafras::slot_ticket_id(genesis_slot + 19), Some(next_tickets[0]));

		// Try fetch tickets for slots beyend next epoch.
		assert_eq!(Sassafras::slot_ticket_id(genesis_slot + 20), None);
		assert_eq!(Sassafras::slot_ticket_id(genesis_slot + 42), None);
	});
}

#[test]
fn on_first_block_after_genesis() {
	let (pairs, mut ext) = new_test_ext_with_pairs(4);

	ext.execute_with(|| {
		let start_slot = Slot::from(100);
		let start_block = 1;

		let digest = initialize_block(start_block, start_slot, Default::default(), &pairs[0]);

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

		let header = finalize_block(start_block);

		// Post-finalization status

		assert!(Initialized::<Test>::get().is_none());
		assert_eq!(Sassafras::genesis_slot(), start_slot);
		assert_eq!(Sassafras::current_slot(), start_slot);
		assert_eq!(Sassafras::epoch_index(), 0);
		assert_eq!(Sassafras::current_epoch_start(), start_slot);
		assert_eq!(Sassafras::current_slot_index(), 0);
		assert_eq!(Sassafras::randomness(), [0; 32]);
		assert_eq!(NextRandomness::<Test>::get(), [0; 32]);
		println!("{}", b2h(RandomnessAccumulator::<Test>::get()));
		assert_eq!(
			RandomnessAccumulator::<Test>::get(),
			h2b("eb169de47822691578f74204ace5bc57c38f86f97e15a8abf71114541e7ca9e8"),
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
		let end_block = start_block + 1;

		initialize_block(start_block, start_slot, Default::default(), &pairs[0]);

		// We don't want to trigger an epoch change in this test.
		let epoch_duration: u64 = <Test as Config>::EpochDuration::get();
		assert!(epoch_duration > end_block);

		// Progress to block 2
		let digest = progress_to_block(end_block, &pairs[0]).unwrap();

		// Post-initialization status

		assert!(Initialized::<Test>::get().is_some());
		assert_eq!(Sassafras::genesis_slot(), start_slot);
		assert_eq!(Sassafras::current_slot(), start_slot + 1);
		assert_eq!(Sassafras::epoch_index(), 0);
		assert_eq!(Sassafras::current_epoch_start(), start_slot);
		assert_eq!(Sassafras::current_slot_index(), 1);
		assert_eq!(Sassafras::randomness(), [0; 32]);
		assert_eq!(NextRandomness::<Test>::get(), [0; 32]);
		println!("{}", b2h(RandomnessAccumulator::<Test>::get()));
		assert_eq!(
			RandomnessAccumulator::<Test>::get(),
			h2b("eb169de47822691578f74204ace5bc57c38f86f97e15a8abf71114541e7ca9e8"),
		);

		let header = finalize_block(end_block);

		// Post-finalization status

		assert!(Initialized::<Test>::get().is_none());
		assert_eq!(Sassafras::genesis_slot(), start_slot);
		assert_eq!(Sassafras::current_slot(), start_slot + 1);
		assert_eq!(Sassafras::epoch_index(), 0);
		assert_eq!(Sassafras::current_epoch_start(), start_slot);
		assert_eq!(Sassafras::current_slot_index(), 1);
		assert_eq!(Sassafras::randomness(), [0; 32]);
		assert_eq!(NextRandomness::<Test>::get(), [0; 32]);
		println!("{}", b2h(RandomnessAccumulator::<Test>::get()));
		assert_eq!(
			RandomnessAccumulator::<Test>::get(),
			h2b("c5e06d78bf5351b3a740c6838976e571ee14c595a206278f3f4ce0157f538318"),
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

		initialize_block(start_block, start_slot, Default::default(), &pairs[0]);

		// We want to trigger an epoch change in this test.
		let epoch_duration: u64 = <Test as Config>::EpochDuration::get();
		let end_block = start_block + epoch_duration;

		let digest = progress_to_block(end_block, &pairs[0]).unwrap();

		// Post-initialization status

		assert!(Initialized::<Test>::get().is_some());
		assert_eq!(Sassafras::genesis_slot(), start_slot);
		assert_eq!(Sassafras::current_slot(), start_slot + epoch_duration);
		assert_eq!(Sassafras::epoch_index(), 1);
		assert_eq!(Sassafras::current_epoch_start(), start_slot + epoch_duration);
		assert_eq!(Sassafras::current_slot_index(), 0);
		assert_eq!(Sassafras::randomness(), [0; 32]);
		println!("{}", b2h(NextRandomness::<Test>::get()));
		assert_eq!(
			NextRandomness::<Test>::get(),
			h2b("a7abdd705eb72383f60f6f093dea4bbfb65a1992099b4928ca30076f71a73682"),
		);
		println!("{}", b2h(RandomnessAccumulator::<Test>::get()));
		assert_eq!(
			RandomnessAccumulator::<Test>::get(),
			h2b("a9d8fc258ba0274d7815664b4e153904c44d2e850e98cffc0ba03ea018611348"),
		);

		let header = finalize_block(end_block);

		// Post-finalization status

		assert!(Initialized::<Test>::get().is_none());
		assert_eq!(Sassafras::genesis_slot(), start_slot);
		assert_eq!(Sassafras::current_slot(), start_slot + epoch_duration);
		assert_eq!(Sassafras::epoch_index(), 1);
		assert_eq!(Sassafras::current_epoch_start(), start_slot + epoch_duration);
		assert_eq!(Sassafras::current_slot_index(), 0);
		assert_eq!(Sassafras::randomness(), [0; 32]);
		println!("{}", b2h(NextRandomness::<Test>::get()));
		assert_eq!(
			NextRandomness::<Test>::get(),
			h2b("a7abdd705eb72383f60f6f093dea4bbfb65a1992099b4928ca30076f71a73682"),
		);
		println!("{}", b2h(RandomnessAccumulator::<Test>::get()));
		assert_eq!(
			RandomnessAccumulator::<Test>::get(),
			h2b("53b4e087baba183a2973552ba57b6c8f489959c8e5f838d59884d37c6d494e2f"),
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

		initialize_block(start_block, start_slot, Default::default(), &pairs[0]);

		let config = SassafrasEpochConfiguration { redundancy_factor: 1, attempts_number: 123 };
		Sassafras::plan_config_change(RuntimeOrigin::root(), config.clone()).unwrap();

		// We want to trigger an epoch change in this test.
		let epoch_duration: u64 = <Test as Config>::EpochDuration::get();
		let end_block = start_block + epoch_duration;

		let digest = progress_to_block(end_block, &pairs[0]).unwrap();

		let header = finalize_block(end_block);

		// Header data check.
		// Skip pallet status checks that were already performed by other tests.

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

// TODO davxy: create a read_tickets method which reads pre-constructed good tickets
// from a file. Creating this stuff "on-the-fly" is just too much expensive
#[test]
fn submit_segments_works() {
	let (pairs, mut ext) = new_test_ext_with_pairs(1);
	let pair = &pairs[0];
	// We're going to generate 14 segments.
	let segments_count = 3;

	println!("TEST BEGIN");
	let ring_ctx = RingVrfContext::new_testing();
	println!("RING CTX BUILT");

	ext.execute_with(|| {
		let start_slot = Slot::from(100);
		let start_block = 1;
		let max_tickets: u32 = <Test as Config>::MaxTickets::get();

		initialize_block(start_block, start_slot, Default::default(), &pairs[0]);

		// Tweak the epoch config to discard some of the tickets
		let mut config = EpochConfig::<Test>::get();
		config.redundancy_factor = 2;
		EpochConfig::<Test>::set(config);

		RingContext::<Test>::set(Some(ring_ctx.clone()));

		// Populate the segments via the `submit_tickets`
		let tickets = make_tickets(start_slot + 1, segments_count * max_tickets, pair, &ring_ctx);
		let segment_len = tickets.len() / segments_count as usize;
		for i in 0..segments_count as usize {
			let segment =
				tickets[i * segment_len..(i + 1) * segment_len].to_vec().try_into().unwrap();
			Sassafras::submit_tickets(RuntimeOrigin::none(), segment).unwrap();
		}

		finalize_block(start_block);

		// Check against the expected results given the known inputs
		let meta = TicketsMeta::<Test>::get();
		assert_eq!(meta.segments_count, segments_count);
		assert_eq!(meta.tickets_count, [0, 0]);
		let seg = NextTicketsSegments::<Test>::get(0);
		assert_eq!(seg.len(), 3);
		let seg = NextTicketsSegments::<Test>::get(1);
		assert_eq!(seg.len(), 5);
		let seg = NextTicketsSegments::<Test>::get(2);
		assert_eq!(seg.len(), 5);
	})
}

// #[test]
// fn segments_incremental_sortition_works() {
// 	let (pairs, mut ext) = new_test_ext_with_pairs(1);
// 	let pair = &pairs[0];
// 	let segments_count = 14;

// 	ext.execute_with(|| {
// 		let start_slot = Slot::from(100);
// 		let start_block = 1;
// 		let max_tickets: u32 = <Test as Config>::MaxTickets::get();

// 		initialize_block(start_block, start_slot, Default::default(), &pairs[0]);

// 		// Manually populate the segments to fool the threshold check
// 		let tickets = make_tickets(start_slot + 1, segments_count * max_tickets, pair);
// 		let segment_len = tickets.len() / segments_count as usize;

// 		for i in 0..segments_count as usize {
// 			let segment: Vec<TicketId> = tickets[i * segment_len..(i + 1) * segment_len]
// 				.iter()
// 				.enumerate()
// 				.map(|(j, ticket)| {
// 					let ticket_id = (i * segment_len + j) as TicketId;
// 					TicketsData::<Test>::set(ticket_id, ticket.data.clone());
// 					ticket_id
// 				})
// 				.collect();
// 			let segment = BoundedVec::truncate_from(segment);
// 			NextTicketsSegments::<Test>::insert(i as u32, segment);
// 		}
// 		let meta = TicketsMetadata { segments_count, tickets_count: [0, 0] };
// 		TicketsMeta::<Test>::set(meta);

// 		let epoch_duration: u64 = <Test as Config>::EpochDuration::get();

// 		// Proceed to half of the epoch (sortition should not have been started yet)
// 		let half_epoch_block = start_block + epoch_duration / 2;
// 		progress_to_block(half_epoch_block, pair);

// 		// Check that next epoch tickets sortition is not started yet
// 		let meta = TicketsMeta::<Test>::get();
// 		assert_eq!(meta.segments_count, segments_count);
// 		assert_eq!(meta.tickets_count, [0, 0]);

// 		// Follow incremental sortition block by block

// 		progress_to_block(half_epoch_block + 1, pair);
// 		let meta = TicketsMeta::<Test>::get();
// 		assert_eq!(meta.segments_count, 12);
// 		assert_eq!(meta.tickets_count, [0, 0]);

// 		progress_to_block(half_epoch_block + 2, pair);
// 		let meta = TicketsMeta::<Test>::get();
// 		assert_eq!(meta.segments_count, 9);
// 		assert_eq!(meta.tickets_count, [0, 0]);

// 		progress_to_block(half_epoch_block + 3, pair);
// 		let meta = TicketsMeta::<Test>::get();
// 		assert_eq!(meta.segments_count, 6);
// 		assert_eq!(meta.tickets_count, [0, 0]);

// 		progress_to_block(half_epoch_block + 4, pair);
// 		let meta = TicketsMeta::<Test>::get();
// 		assert_eq!(meta.segments_count, 3);
// 		assert_eq!(meta.tickets_count, [0, 0]);

// 		let header = finalize_block(half_epoch_block + 4);

// 		// Sort should be finished.
// 		// Check that next epoch tickets count have the correct value (6).
// 		// Bigger values were discarded during sortition.
// 		let meta = TicketsMeta::<Test>::get();
// 		assert_eq!(meta.segments_count, 0);
// 		assert_eq!(meta.tickets_count, [0, 6]);
// 		assert_eq!(header.digest.logs.len(), 1);

// 		// The next block will be the first produced on the new epoch,
// 		// At this point the tickets are found already sorted and ready to be used.
// 		let slot = Sassafras::current_slot() + 1;
// 		let number = System::block_number() + 1;
// 		initialize_block(number, slot, header.hash(), pair);
// 		let header = finalize_block(number);
// 		// Epoch changes digest is also produced
// 		assert_eq!(header.digest.logs.len(), 2);
// 	});
// }

// #[test]
// fn submit_enact_claim_tickets() {
// 	let (pairs, mut ext) = new_test_ext_with_pairs(4);

// 	ext.execute_with(|| {
// 		let start_slot = Slot::from(100);
// 		let start_block = 1;
// 		let max_tickets: u32 = <Test as Config>::MaxTickets::get();
// 		let pair = &pairs[0];

// 		initialize_block(start_block, start_slot, Default::default(), pair);

// 		// We don't want to trigger an epoch change in this test.
// 		let epoch_duration: u64 = <Test as Config>::EpochDuration::get();
// 		assert!(epoch_duration > 2);
// 		progress_to_block(2, &pairs[0]).unwrap();

// 		// // Check state before tickets submission
// 		assert_eq!(
// 			TicketsMeta::<Test>::get(),
// 			TicketsMetadata { segments_count: 0, tickets_count: [0, 0] },
// 		);

// 		// Submit authoring tickets in three different segments.
// 		let tickets = make_tickets(start_slot + 1, 3 * max_tickets, pair);
// 		let tickets0 = tickets[0..6].to_vec().try_into().unwrap();
// 		Sassafras::submit_tickets(RuntimeOrigin::none(), tickets0).unwrap();
// 		let tickets1 = tickets[6..12].to_vec().try_into().unwrap();
// 		Sassafras::submit_tickets(RuntimeOrigin::none(), tickets1).unwrap();
// 		let tickets2 = tickets[12..18].to_vec().try_into().unwrap();
// 		Sassafras::submit_tickets(RuntimeOrigin::none(), tickets2).unwrap();

// 		// Check state after submit
// 		assert_eq!(
// 			TicketsMeta::<Test>::get(),
// 			TicketsMetadata { segments_count: 3, tickets_count: [0, 0] },
// 		);

// 		// Progress up to the last epoch slot (do not enact epoch change)
// 		progress_to_block(epoch_duration, &pairs[0]).unwrap();

// 		// At this point next tickets should have been sorted
// 		// Check state after submit
// 		assert_eq!(
// 			TicketsMeta::<Test>::get(),
// 			TicketsMetadata { segments_count: 0, tickets_count: [0, 6] },
// 		);

// 		// Compute and sort the tickets ids (aka tickets scores)
// 		let mut expected_ids: Vec<_> = tickets
// 			.iter()
// 			.map(|t| {
// 				let epoch_idx = Sassafras::epoch_index() + 1;
// 				let randomness = Sassafras::next_randomness();
// 				let vrf_input = sp_consensus_sassafras::ticket_id_vrf_input(
// 					&randomness,
// 					t.data.attempt_idx,
// 					epoch_idx,
// 				);
// 				sp_consensus_sassafras::ticket_id(&vrf_input, &t.vrf_preout)
// 			})
// 			.collect();
// 		expected_ids.sort();
// 		expected_ids.truncate(max_tickets as usize);

// 		// Check if we can claim next epoch tickets in outside-in fashion.
// 		let slot = Sassafras::current_slot();
// 		assert_eq!(Sassafras::slot_ticket_id(slot + 1).unwrap(), expected_ids[1]);
// 		assert_eq!(Sassafras::slot_ticket_id(slot + 2).unwrap(), expected_ids[3]);
// 		assert_eq!(Sassafras::slot_ticket_id(slot + 3).unwrap(), expected_ids[5]);
// 		assert!(Sassafras::slot_ticket_id(slot + 4).is_none());
// 		assert!(Sassafras::slot_ticket_id(slot + 7).is_none());
// 		assert_eq!(Sassafras::slot_ticket_id(slot + 8).unwrap(), expected_ids[4]);
// 		assert_eq!(Sassafras::slot_ticket_id(slot + 9).unwrap(), expected_ids[2]);
// 		assert_eq!(Sassafras::slot_ticket_id(slot + 10).unwrap(), expected_ids[0]);
// 		assert!(Sassafras::slot_ticket_id(slot + 11).is_none());

// 		// Enact epoch change by progressing one more block

// 		progress_to_block(epoch_duration + 1, &pairs[0]).unwrap();

// 		let meta = TicketsMeta::<Test>::get();
// 		assert_eq!(meta.segments_count, 0);
// 		assert_eq!(meta.tickets_count, [0, 6]);

// 		let slot = Sassafras::current_slot();
// 		assert_eq!(Sassafras::slot_ticket_id(slot).unwrap(), expected_ids[1]);
// 		assert_eq!(Sassafras::slot_ticket_id(slot + 1).unwrap(), expected_ids[3]);
// 		assert_eq!(Sassafras::slot_ticket_id(slot + 2).unwrap(), expected_ids[5]);
// 		assert!(Sassafras::slot_ticket_id(slot + 3).is_none());
// 		assert!(Sassafras::slot_ticket_id(slot + 6).is_none());
// 		assert_eq!(Sassafras::slot_ticket_id(slot + 7).unwrap(), expected_ids[4]);
// 		assert_eq!(Sassafras::slot_ticket_id(slot + 8).unwrap(), expected_ids[2]);
// 		assert_eq!(Sassafras::slot_ticket_id(slot + 9).unwrap(), expected_ids[0]);
// 		assert!(Sassafras::slot_ticket_id(slot + 10).is_none());
// 	});
// }

// #[test]
// fn block_allowed_to_skip_epochs() {
// 	let (pairs, mut ext) = new_test_ext_with_pairs(4);

// 	ext.execute_with(|| {
// 		let start_slot = Slot::from(100);
// 		let start_block = 1;
// 		let epoch_duration: u64 = <Test as Config>::EpochDuration::get();

// 		initialize_block(start_block, start_slot, Default::default(), &pairs[0]);

// 		let tickets = make_tickets(start_slot + 1, 3, &pairs[0]);
// 		Sassafras::submit_tickets(
// 			RuntimeOrigin::none(),
// 			BoundedVec::truncate_from(tickets.clone()),
// 		)
// 		.unwrap();

// 		// Force sortition of next tickets (enactment) by explicitly querying next epoch tickets.
// 		assert_eq!(TicketsMeta::<Test>::get().segments_count, 1);
// 		Sassafras::slot_ticket(start_slot + epoch_duration).unwrap();
// 		assert_eq!(TicketsMeta::<Test>::get().segments_count, 0);

// 		let next_random = NextRandomness::<Test>::get();

// 		// We want to trigger a skip epoch in this test.
// 		let offset = 3 * epoch_duration;
// 		go_to_block(start_block + offset, start_slot + offset, &pairs[0]);

// 		// Post-initialization status

// 		assert!(Initialized::<Test>::get().is_some());
// 		assert_eq!(Sassafras::genesis_slot(), start_slot);
// 		assert_eq!(Sassafras::current_slot(), start_slot + offset);
// 		assert_eq!(Sassafras::epoch_index(), 3);
// 		assert_eq!(Sassafras::current_epoch_start(), start_slot + offset);
// 		assert_eq!(Sassafras::current_slot_index(), 0);

// 		// Tickets were discarded
// 		let meta = TicketsMeta::<Test>::get();
// 		assert_eq!(meta, TicketsMetadata::default());
// 		// We used the last known next epoch randomness as a fallback
// 		assert_eq!(next_random, Sassafras::randomness());
// 	});
// }
