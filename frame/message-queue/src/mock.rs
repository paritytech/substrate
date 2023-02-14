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

//! Test helpers and runtime setup for the message queue pallet.

#![cfg(test)]

pub use super::mock_helpers::*;
use super::*;

use crate as pallet_message_queue;
use frame_support::{
	parameter_types,
	traits::{ConstU32, ConstU64},
};
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
	pub const HeapSize: u32 = 24;
	pub const MaxStale: u32 = 2;
	pub const ServiceWeight: Option<Weight> = Some(Weight::from_parts(10, 10));
}
impl Config for Test {
	type RuntimeEvent = RuntimeEvent;
	type WeightInfo = MockedWeightInfo;
	type MessageProcessor = RecordingMessageProcessor;
	type Size = u32;
	type QueueChangeHandler = RecordingQueueChangeHandler;
	type HeapSize = HeapSize;
	type MaxStale = MaxStale;
	type ServiceWeight = ServiceWeight;
}

/// Mocked `WeightInfo` impl with allows to set the weight per call.
pub struct MockedWeightInfo;

parameter_types! {
	/// Storage for `MockedWeightInfo`, do not use directly.
	pub static WeightForCall: BTreeMap<String, Weight> = Default::default();
}

/// Set the return value for a function from the `WeightInfo` trait.
impl MockedWeightInfo {
	/// Set the weight of a specific weight function.
	pub fn set_weight<T: Config>(call_name: &str, weight: Weight) {
		let mut calls = WeightForCall::get();
		calls.insert(call_name.into(), weight);
		WeightForCall::set(calls);
	}
}

impl crate::weights::WeightInfo for MockedWeightInfo {
	fn reap_page() -> Weight {
		WeightForCall::get().get("reap_page").copied().unwrap_or_default()
	}
	fn execute_overweight_page_updated() -> Weight {
		WeightForCall::get()
			.get("execute_overweight_page_updated")
			.copied()
			.unwrap_or_default()
	}
	fn execute_overweight_page_removed() -> Weight {
		WeightForCall::get()
			.get("execute_overweight_page_removed")
			.copied()
			.unwrap_or_default()
	}
	fn service_page_base_completion() -> Weight {
		WeightForCall::get()
			.get("service_page_base_completion")
			.copied()
			.unwrap_or_default()
	}
	fn service_page_base_no_completion() -> Weight {
		WeightForCall::get()
			.get("service_page_base_no_completion")
			.copied()
			.unwrap_or_default()
	}
	fn service_queue_base() -> Weight {
		WeightForCall::get().get("service_queue_base").copied().unwrap_or_default()
	}
	fn bump_service_head() -> Weight {
		WeightForCall::get().get("bump_service_head").copied().unwrap_or_default()
	}
	fn service_page_item() -> Weight {
		WeightForCall::get().get("service_page_item").copied().unwrap_or_default()
	}
	fn ready_ring_knit() -> Weight {
		WeightForCall::get().get("ready_ring_knit").copied().unwrap_or_default()
	}
	fn ready_ring_unknit() -> Weight {
		WeightForCall::get().get("ready_ring_unknit").copied().unwrap_or_default()
	}
}

parameter_types! {
	pub static MessagesProcessed: Vec<(Vec<u8>, MessageOrigin)> = vec![];
}

/// A message processor which records all processed messages into [`MessagesProcessed`].
pub struct RecordingMessageProcessor;
impl ProcessMessage for RecordingMessageProcessor {
	/// The transport from where a message originates.
	type Origin = MessageOrigin;

	/// Process the given message, using no more than `weight_limit` in weight to do so.
	///
	/// Consumes exactly `n` weight of all components if it starts `weight=n` and `1` otherwise.
	/// Errors if given the `weight_limit` is insufficient to process the message or if the message
	/// is `badformat`, `corrupt` or `unsupported` with the respective error.
	fn process_message(
		message: &[u8],
		origin: Self::Origin,
		weight_limit: Weight,
	) -> Result<(bool, Weight), ProcessMessageError> {
		processing_message(message)?;

		let weight = if message.starts_with(&b"weight="[..]) {
			let mut w: u64 = 0;
			for &c in &message[7..] {
				if (b'0'..=b'9').contains(&c) {
					w = w * 10 + (c - b'0') as u64;
				} else {
					break
				}
			}
			w
		} else {
			1
		};
		let weight = Weight::from_parts(weight, weight);

		if weight.all_lte(weight_limit) {
			let mut m = MessagesProcessed::get();
			m.push((message.to_vec(), origin));
			MessagesProcessed::set(m);
			Ok((true, weight))
		} else {
			Err(ProcessMessageError::Overweight(weight))
		}
	}
}

/// Processed a mocked message. Messages that end with `badformat`, `corrupt` or `unsupported` will
/// fail with the respective error.
fn processing_message(msg: &[u8]) -> Result<(), ProcessMessageError> {
	let msg = String::from_utf8_lossy(msg);
	if msg.ends_with("badformat") {
		Err(ProcessMessageError::BadFormat)
	} else if msg.ends_with("corrupt") {
		Err(ProcessMessageError::Corrupt)
	} else if msg.ends_with("unsupported") {
		Err(ProcessMessageError::Unsupported)
	} else {
		Ok(())
	}
}

parameter_types! {
	pub static NumMessagesProcessed: usize = 0;
	pub static NumMessagesErrored: usize = 0;
}

/// Similar to [`RecordingMessageProcessor`] but only counts the number of messages processed and
/// does always consume one weight per message.
///
/// The [`RecordingMessageProcessor`] is a bit too slow for the integration tests.
pub struct CountingMessageProcessor;
impl ProcessMessage for CountingMessageProcessor {
	type Origin = MessageOrigin;

	fn process_message(
		message: &[u8],
		_origin: Self::Origin,
		weight_limit: Weight,
	) -> Result<(bool, Weight), ProcessMessageError> {
		if let Err(e) = processing_message(message) {
			NumMessagesErrored::set(NumMessagesErrored::get() + 1);
			return Err(e)
		}
		let weight = Weight::from_parts(1, 1);

		if weight.all_lte(weight_limit) {
			NumMessagesProcessed::set(NumMessagesProcessed::get() + 1);
			Ok((true, weight))
		} else {
			Err(ProcessMessageError::Overweight(weight))
		}
	}
}

parameter_types! {
	/// Storage for `RecordingQueueChangeHandler`, do not use directly.
	pub static QueueChanges: Vec<(MessageOrigin, u64, u64)> = vec![];
}

/// Records all queue changes into [`QueueChanges`].
pub struct RecordingQueueChangeHandler;
impl OnQueueChanged<MessageOrigin> for RecordingQueueChangeHandler {
	fn on_queue_changed(id: MessageOrigin, items_count: u64, items_size: u64) {
		QueueChanges::mutate(|cs| cs.push((id, items_count, items_size)));
	}
}

/// Create new test externalities.
///
/// Is generic since it is used by the unit test, integration tests and benchmarks.
pub fn new_test_ext<T: Config>() -> sp_io::TestExternalities
where
	<T as frame_system::Config>::BlockNumber: From<u32>,
{
	sp_tracing::try_init_simple();
	WeightForCall::take();
	QueueChanges::take();
	NumMessagesErrored::take();
	let t = frame_system::GenesisConfig::default().build_storage::<T>().unwrap();
	let mut ext = sp_io::TestExternalities::new(t);
	ext.execute_with(|| frame_system::Pallet::<T>::set_block_number(1.into()));
	ext
}

/// Set the weight of a specific weight function.
pub fn set_weight(name: &str, w: Weight) {
	MockedWeightInfo::set_weight::<Test>(name, w);
}

/// Assert that exactly these pages are present. Assumes `Here` origin.
pub fn assert_pages(indices: &[u32]) {
	assert_eq!(Pages::<Test>::iter().count(), indices.len());
	for i in indices {
		assert!(Pages::<Test>::contains_key(MessageOrigin::Here, i));
	}
}

/// Build a ring with three queues: `Here`, `There` and `Everywhere(0)`.
pub fn build_triple_ring() {
	use MessageOrigin::*;
	build_ring::<Test>(&[Here, There, Everywhere(0)])
}

/// Shim to get rid of the annoying `::<Test>` everywhere.
pub fn assert_ring(queues: &[MessageOrigin]) {
	super::mock_helpers::assert_ring::<Test>(queues);
}

pub fn knit(queue: &MessageOrigin) {
	super::mock_helpers::knit::<Test>(queue);
}

pub fn unknit(queue: &MessageOrigin) {
	super::mock_helpers::unknit::<Test>(queue);
}
