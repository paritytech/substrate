// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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

// Tests for Multisig Pallet

#![cfg(test)]

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
	pub const HeapSize: u32 = 131072;
	pub const MaxReady: u32 = 3;
}

impl Config for Test {
	type RuntimeEvent = RuntimeEvent;
	type WeightInfo = ();
	type MessageProcessor = TestMessageProcessor;
	type Size = u32;
	type HeapSize = HeapSize;
	type MaxReady = MaxReady;
}

#[derive(Copy, Clone, Eq, PartialEq, Encode, Decode, MaxEncodedLen, TypeInfo, Debug)]
pub enum MessageOrigin {
	Here,
	There,
	Everywhere(u8),
}

parameter_types! {
	pub static MessagesProcessed: Vec<(Vec<u8>, MessageOrigin)> = vec![];
}

pub struct TestMessageProcessor;
impl ProcessMessage for TestMessageProcessor {
	/// The transport from where a message originates.
	type Origin = MessageOrigin;

	/// Process the given message, using no more than `weight_limit` in weight to do so.
	fn process_message(
		message: &[u8],
		origin: Self::Origin,
		weight_limit: Weight,
	) -> Result<(bool, Weight), ProcessMessageError> {
		let weight = Weight::from_components(1, 1);
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

pub fn new_test_ext() -> sp_io::TestExternalities {
	let t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
	let mut ext = sp_io::TestExternalities::new(t);
	ext.execute_with(|| System::set_block_number(1));
	ext
}

pub trait IntoWeight {
	fn into_weight(self) -> Weight;
}
impl IntoWeight for u64 {
	fn into_weight(self) -> Weight {
		Weight::from_components(self, self)
	}
}

#[test]
fn enqueue_within_one_page_works() {
	new_test_ext().execute_with(|| {
		use MessageOrigin::*;
		MessageQueue::enqueue_message(BoundedSlice::truncate_from(&b"hello"[..]), Here);
		MessageQueue::enqueue_message(BoundedSlice::truncate_from(&b"world"[..]), Here);
		MessageQueue::enqueue_message(BoundedSlice::truncate_from(&b"gav"[..]), Here);
		assert_eq!(MessageQueue::service_queues(2.into_weight()), 2.into_weight());
		assert_eq!(
			MessagesProcessed::get(),
			vec![(b"hello".to_vec(), Here), (b"world".to_vec(), Here)]
		);

		MessagesProcessed::set(vec![]);
		assert_eq!(MessageQueue::service_queues(2.into_weight()), 1.into_weight());
		assert_eq!(MessagesProcessed::get(), vec![(b"gav".to_vec(), Here)]);

		MessagesProcessed::set(vec![]);
		assert_eq!(MessageQueue::service_queues(2.into_weight()), 0.into_weight());
		assert_eq!(MessagesProcessed::get(), vec![]);

		MessageQueue::enqueue_messages(
			[
				BoundedSlice::truncate_from(&b"boo"[..]),
				BoundedSlice::truncate_from(&b"yah"[..]),
				BoundedSlice::truncate_from(&b"kah"[..]),
			]
			.into_iter(),
			There,
		);

		MessagesProcessed::set(vec![]);
		assert_eq!(MessageQueue::service_queues(2.into_weight()), 2.into_weight());
		assert_eq!(
			MessagesProcessed::get(),
			vec![(b"boo".to_vec(), There), (b"yah".to_vec(), There),]
		);

		MessageQueue::enqueue_message(BoundedSlice::truncate_from(&b"sha"[..]), Everywhere(1));

		MessagesProcessed::set(vec![]);
		assert_eq!(MessageQueue::service_queues(2.into_weight()), 2.into_weight());
		assert_eq!(MessageQueue::service_queues(2.into_weight()), 0.into_weight());
		assert_eq!(
			MessagesProcessed::get(),
			vec![(b"kah".to_vec(), There), (b"sha".to_vec(), Everywhere(1))]
		);
	});
}

fn msg<N: Get<u32>>(x: &'static str) -> BoundedSlice<u8, N> {
	BoundedSlice::truncate_from(x.as_bytes())
}

fn vmsg(x: &'static str) -> Vec<u8> {
	x.as_bytes().to_vec()
}

#[test]
fn queue_priority_retains() {
	new_test_ext().execute_with(|| {
		use MessageOrigin::*;
		assert_eq!(ReadyRing::<Test>::new().collect::<Vec<_>>(), vec![]);
		MessageQueue::enqueue_message(msg(&"a"), Everywhere(1));
		assert_eq!(ReadyRing::<Test>::new().collect::<Vec<_>>(), vec![Everywhere(1)]);
		MessageQueue::enqueue_message(msg(&"b"), Everywhere(2));
		assert_eq!(
			ReadyRing::<Test>::new().collect::<Vec<_>>(),
			vec![Everywhere(1), Everywhere(2)]
		);
		MessageQueue::enqueue_message(msg(&"c"), Everywhere(3));
		assert_eq!(
			ReadyRing::<Test>::new().collect::<Vec<_>>(),
			vec![Everywhere(1), Everywhere(2), Everywhere(3)]
		);
		MessageQueue::enqueue_message(msg(&"d"), Everywhere(2));
		assert_eq!(
			ReadyRing::<Test>::new().collect::<Vec<_>>(),
			vec![Everywhere(1), Everywhere(2), Everywhere(3)]
		);
		// service head is 1, it will process a, leaving service head at 2. it also processes b but
		// doees not empty queue 2, so service head will end at 2.
		assert_eq!(MessageQueue::service_queues(2.into_weight()), 2.into_weight());
		assert_eq!(
			MessagesProcessed::get(),
			vec![(vmsg(&"a"), Everywhere(1)), (vmsg(&"b"), Everywhere(2)),]
		);
		assert_eq!(
			ReadyRing::<Test>::new().collect::<Vec<_>>(),
			vec![Everywhere(2), Everywhere(3)]
		);
		// service head is 2, so will process d first, then c.
		assert_eq!(MessageQueue::service_queues(2.into_weight()), 2.into_weight());
		assert_eq!(
			MessagesProcessed::get(),
			vec![
				(vmsg(&"a"), Everywhere(1)),
				(vmsg(&"b"), Everywhere(2)),
				(vmsg(&"d"), Everywhere(2)),
				(vmsg(&"c"), Everywhere(3)),
			]
		);
		assert_eq!(ReadyRing::<Test>::new().collect::<Vec<_>>(), vec![]);
	});
}

#[test]
fn queue_priority_reset_once_serviced() {
	new_test_ext().execute_with(|| {
		use MessageOrigin::*;
		MessageQueue::enqueue_message(msg(&"a"), Everywhere(1));
		MessageQueue::enqueue_message(msg(&"b"), Everywhere(2));
		MessageQueue::enqueue_message(msg(&"c"), Everywhere(3));
		// service head is 1, it will process a, leaving service head at 2. it also processes b and
		// empties queue 2, so service head will end at 3.
		assert_eq!(MessageQueue::service_queues(2.into_weight()), 2.into_weight());
		MessageQueue::enqueue_message(msg(&"d"), Everywhere(2));
		// service head is 3, so will process c first, then d.
		assert_eq!(MessageQueue::service_queues(2.into_weight()), 2.into_weight());

		assert_eq!(
			MessagesProcessed::get(),
			vec![
				(vmsg(&"a"), Everywhere(1)),
				(vmsg(&"b"), Everywhere(2)),
				(vmsg(&"c"), Everywhere(3)),
				(vmsg(&"d"), Everywhere(2)),
			]
		);
	});
}
