// Copyright 2021 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! Stress tests pallet-message-queue. Defines its own runtime config to use larger constants for
//! `HeapSize` and `MaxStale`.

#![cfg(test)]

use crate::{
	mock::{
		new_test_ext, IntoWeight, MockedWeightInfo, NumMessagesProcessed,
		SimpleTestMessageProcessor,
	},
	*,
};

use crate as pallet_message_queue;
use frame_support::{
	assert_noop, assert_ok, assert_storage_noop, parameter_types,
	traits::{ConstU32, ConstU64},
};
use rand::{prelude::*, Rng, SeedableRng};
use rand_distr::Pareto;
use sp_core::H256;
use sp_runtime::{
	testing::Header,
	traits::{BlakeTwo256, IdentityLookup},
};
use sp_std::collections::btree_map::BTreeMap;

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
	pub const HeapSize: u32 = 64 * 1024;
	pub const MaxStale: u32 = 256;
}

impl Config for Test {
	type RuntimeEvent = RuntimeEvent;
	type WeightInfo = MockedWeightInfo;
	type MessageProcessor = SimpleTestMessageProcessor;
	type Size = u32;
	type HeapSize = HeapSize;
	type MaxStale = MaxStale;
}

/// Simulates heavy usage by enqueueing and processing large amounts of messages.
#[test]
fn stress_test_enqueue_and_service() {
	let blocks = 10;
	let max_queues = 10_000;
	let max_messages_per_queue = 100_000;
	let max_msg_len = MaxMessageLenOf::<Test>::get();
	let mut rng = rand::rngs::StdRng::seed_from_u64(42);

	new_test_ext::<Test>().execute_with(|| {
		for _ in 0..blocks {
			let num_queues = rng.gen_range(1..max_queues);
			let mut num_messages = 0;
			let mut total_msg_len = 0;

			for origin in 0..num_queues {
				let num_messages_per_queue =
					(rng.sample(Pareto::new(1.0, 1.1).unwrap()) as u32).min(max_messages_per_queue);

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
				"Enqueued {} messages across {} queues. Total payload {:.2} KiB",
				num_messages,
				num_queues,
				total_msg_len as f64 / 1024.0
			);

			let mut msgs_remaining = num_messages as u64;
			while !msgs_remaining.is_zero() {
				// We have to use at least 1 here since otherwise messages will be as permanently
				// marked overweight.
				let weight = rng.gen_range(1..=msgs_remaining).into_weight();

				log::info!("Processing {} messages...", weight.ref_time());
				let consumed = MessageQueue::service_queues(weight);
				if consumed != weight {
					panic!(
						"consumed != weight: {} != {}\n{}",
						consumed, weight, "MessageQueue::debug_info()"
					);
				}
				let processed = NumMessagesProcessed::take();
				assert_eq!(processed, weight.ref_time() as usize);
				System::reset_events();
				msgs_remaining = msgs_remaining.saturating_sub(weight.ref_time());
			}
			assert_eq!(MessageQueue::service_queues(Weight::MAX), Weight::zero(), "Nothing left");
		}
	});
}
