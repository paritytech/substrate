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

//! Stress tests pallet-message-queue. Defines its own runtime config to use larger constants for
//! `HeapSize` and `MaxStale`.

#![cfg(test)]

use crate::{
	mock::{
		new_test_ext, CountingMessageProcessor, IntoWeight, MockedWeightInfo, NumMessagesProcessed,
	},
	*,
};

use crate as pallet_message_queue;
use frame_support::{
	parameter_types,
	traits::{ConstU32, ConstU64},
};
use rand::{rngs::StdRng, Rng, SeedableRng};
use rand_distr::Pareto;
use sp_core::H256;
use sp_runtime::{
	testing::Header,
	traits::{BlakeTwo256, IdentityLookup},
};

type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Test>;
type Block = frame_system::mocking::MockBlock<Test>;

frame_support::construct_runtime!(
	pub enum Test where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic,
	{
		System: frame_system::{Pallet, Call, Config, Storage, Event<T>},
		MessageQueue: pallet_message_queue::{Pallet, Call, Storage, Event<T>},
	}
);

parameter_types! {
	pub BlockWeights: frame_system::limits::BlockWeights =
		frame_system::limits::BlockWeights::simple_max(frame_support::weights::Weight::from_ref_time(1024));
}
impl frame_system::Config for Test {
	type BaseCallFilter = frame_support::traits::Everything;
	type BlockWeights = ();
	type BlockLength = ();
	type DbWeight = ();
	type RuntimeOrigin = RuntimeOrigin;
	type Index = u64;
	type BlockNumber = u64;
	type Hash = H256;
	type RuntimeCall = RuntimeCall;
	type Hashing = BlakeTwo256;
	type AccountId = u64;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type RuntimeEvent = RuntimeEvent;
	type BlockHashCount = ConstU64<250>;
	type Version = ();
	type PalletInfo = PalletInfo;
	type AccountData = ();
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
	type SS58Prefix = ();
	type OnSetCode = ();
	type MaxConsumers = ConstU32<16>;
}

parameter_types! {
	pub const HeapSize: u32 = 32 * 1024;
	pub const MaxStale: u32 = 32;
	pub static ServiceWeight: Option<Weight> = Some(Weight::from_parts(100, 100));
}

impl Config for Test {
	type RuntimeEvent = RuntimeEvent;
	type WeightInfo = MockedWeightInfo;
	type MessageProcessor = CountingMessageProcessor;
	type Size = u32;
	type QueueChangeHandler = ();
	type HeapSize = HeapSize;
	type MaxStale = MaxStale;
	type ServiceWeight = ServiceWeight;
}

/// Simulates heavy usage by enqueueing and processing large amounts of messages.
///
/// Best to run with `-r`, `RUST_LOG=info` and `RUSTFLAGS='-Cdebug-assertions=y'`.
///
/// # Example output
///
/// ```pre
/// Enqueued 1189 messages across 176 queues. Payload 46.97 KiB    
/// Processing 772 of 1189 messages    
/// Enqueued 9270 messages across 1559 queues. Payload 131.85 KiB    
/// Processing 6262 of 9687 messages    
/// Enqueued 5025 messages across 1225 queues. Payload 100.23 KiB    
/// Processing 1739 of 8450 messages    
/// Enqueued 42061 messages across 6357 queues. Payload 536.29 KiB    
/// Processing 11675 of 48772 messages    
/// Enqueued 20253 messages across 2420 queues. Payload 288.34 KiB    
/// Processing 28711 of 57350 messages
/// Processing all remaining 28639 messages
/// ```
#[test]
#[ignore] // Only run in the CI.
fn stress_test_enqueue_and_service() {
	let blocks = 20;
	let max_queues = 10_000;
	let max_messages_per_queue = 10_000;
	let max_msg_len = MaxMessageLenOf::<Test>::get();
	let mut rng = StdRng::seed_from_u64(42);

	new_test_ext::<Test>().execute_with(|| {
		let mut msgs_remaining = 0;
		for _ in 0..blocks {
			// Start by enqueuing a large number of messages.
			let (enqueued, _) =
				enqueue_messages(max_queues, max_messages_per_queue, max_msg_len, &mut rng);
			msgs_remaining += enqueued;

			// Pick a fraction of all messages currently in queue and process them.
			let processed = rng.gen_range(1..=msgs_remaining);
			log::info!("Processing {} of all messages {}", processed, msgs_remaining);
			process_messages(processed); // This also advances the block.
			msgs_remaining -= processed;
		}
		log::info!("Processing all remaining {} messages", msgs_remaining);
		process_messages(msgs_remaining);
		post_conditions();
	});
}

/// Enqueue a random number of random messages into a random number of queues.
fn enqueue_messages(
	max_queues: u32,
	max_per_queue: u32,
	max_msg_len: u32,
	rng: &mut StdRng,
) -> (u32, usize) {
	let num_queues = rng.gen_range(1..max_queues);
	let mut num_messages = 0;
	let mut total_msg_len = 0;
	for origin in 0..num_queues {
		let num_messages_per_queue =
			(rng.sample(Pareto::new(1.0, 1.1).unwrap()) as u32).min(max_per_queue);

		for m in 0..num_messages_per_queue {
			let mut message = format!("{}:{}", &origin, &m).into_bytes();
			let msg_len = (rng.sample(Pareto::new(1.0, 1.0).unwrap()) as u32)
				.clamp(message.len() as u32, max_msg_len);
			message.resize(msg_len as usize, 0);
			MessageQueue::enqueue_message(
				BoundedSlice::defensive_truncate_from(&message),
				origin.into(),
			);
			total_msg_len += msg_len;
		}
		num_messages += num_messages_per_queue;
	}
	log::info!(
		"Enqueued {} messages across {} queues. Payload {:.2} KiB",
		num_messages,
		num_queues,
		total_msg_len as f64 / 1024.0
	);
	(num_messages, total_msg_len as usize)
}

/// Process the number of messages.
fn process_messages(num_msgs: u32) {
	let weight = (num_msgs as u64).into_weight();
	ServiceWeight::set(Some(weight));
	let consumed = next_block();

	assert_eq!(consumed, weight, "\n{}", MessageQueue::debug_info());
	assert_eq!(NumMessagesProcessed::take(), num_msgs as usize);
}

/// Returns the weight consumed by `MessageQueue::on_initialize()`.
fn next_block() -> Weight {
	MessageQueue::on_finalize(System::block_number());
	System::on_finalize(System::block_number());
	System::set_block_number(System::block_number() + 1);
	System::on_initialize(System::block_number());
	MessageQueue::on_initialize(System::block_number())
}

/// Assert that the pallet is in the expected post state.
fn post_conditions() {
	// All queues are empty.
	for (_, book) in BookStateFor::<Test>::iter() {
		assert!(book.end >= book.begin);
		assert_eq!(book.count, 0);
		assert_eq!(book.size, 0);
		assert_eq!(book.message_count, 0);
		assert!(book.ready_neighbours.is_none());
	}
	// No pages remain.
	assert_eq!(Pages::<Test>::iter().count(), 0);
	// Service head is gone.
	assert!(ServiceHead::<Test>::get().is_none());
	// This still works fine.
	assert_eq!(MessageQueue::service_queues(Weight::MAX), Weight::zero(), "Nothing left");
	next_block();
}
