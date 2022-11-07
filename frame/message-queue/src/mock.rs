// Copyright 2022 Parity Technologies (UK) Ltd.
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

#![cfg(any(test, feature = "runtime-benchmarks"))]

use super::*;

use crate as pallet_message_queue;
use frame_support::{
	assert_noop, assert_ok, parameter_types,
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
}

impl Config for Test {
	type RuntimeEvent = RuntimeEvent;
	type WeightInfo = MockedWeightInfo;
	type MessageProcessor = TestMessageProcessor;
	type Size = u32;
	type HeapSize = HeapSize;
	type MaxStale = MaxStale;
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
	fn service_page_base() -> Weight {
		WeightForCall::get().get("service_page_base").copied().unwrap_or_default()
	}
	fn service_queue_base() -> Weight {
		WeightForCall::get().get("service_queue_base").copied().unwrap_or_default()
	}
	fn service_page_process_message() -> Weight {
		WeightForCall::get()
			.get("service_page_process_message")
			.copied()
			.unwrap_or_default()
	}
	fn bump_service_head() -> Weight {
		WeightForCall::get().get("bump_service_head").copied().unwrap_or_default()
	}
	fn service_page_item() -> Weight {
		WeightForCall::get().get("service_page_item").copied().unwrap_or_default()
	}
	fn ready_ring_unknit() -> Weight {
		WeightForCall::get().get("ready_ring_unknit").copied().unwrap_or_default()
	}
}

parameter_types! {
	pub static MessagesProcessed: Vec<(Vec<u8>, MessageOrigin)> = vec![];
}

pub struct TestMessageProcessor;
impl ProcessMessage for TestMessageProcessor {
	/// The transport from where a message originates.
	type Origin = MessageOrigin;

	/// Process the given message, using no more than `weight_limit` in weight to do so.
	///
	/// Consumes exactly `n` weight of all components if it starts `weight=n` and `1` otherwise.
	/// Errors if given the `weight_limit` is insufficient to process the message.
	fn process_message(
		message: &[u8],
		origin: Self::Origin,
		weight_limit: Weight,
	) -> Result<(bool, Weight), ProcessMessageError> {
		let weight = if message.starts_with(&b"weight="[..]) {
			let mut w: u64 = 0;
			for &c in &message[7..] {
				if c >= b'0' && c <= b'9' {
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

parameter_types! {
	pub static NumMessagesProcessed: usize = 0;
}

/// Similar to [`TestMessageProcessor`] but only counts the number of messages processed and does
/// always consume one weight per message.
///
/// The [`TestMessageProcessor`] is a bit too slow for the integration tests.
pub struct SimpleTestMessageProcessor;
impl ProcessMessage for SimpleTestMessageProcessor {
	type Origin = MessageOrigin;

	fn process_message(
		message: &[u8],
		origin: Self::Origin,
		weight_limit: Weight,
	) -> Result<(bool, Weight), ProcessMessageError> {
		let weight = Weight::from_parts(1, 1);

		if weight.all_lte(weight_limit) {
			NumMessagesProcessed::set(NumMessagesProcessed::get() + 1);
			Ok((true, weight))
		} else {
			Err(ProcessMessageError::Overweight(weight))
		}
	}
}

/// Create new test externalities.
///
/// Is generic since it is used by the unit test, integration tests and benchmarks.
pub fn new_test_ext<T: Config>() -> sp_io::TestExternalities
where
	<T as frame_system::Config>::BlockNumber: From<u32>,
{
	#[cfg(test)] // Only log in tests, not in in benchmarks.
	sp_tracing::try_init_simple();
	WeightForCall::set(Default::default());
	let t = frame_system::GenesisConfig::default().build_storage::<T>().unwrap();
	let mut ext = sp_io::TestExternalities::new(t);
	ext.execute_with(|| frame_system::Pallet::<T>::set_block_number(1.into()));
	ext
}

/// Set the weight of a specific weight function.
pub fn set_weight(name: &str, w: Weight) {
	MockedWeightInfo::set_weight::<Test>(name, w);
}

#[derive(Copy, Clone, Eq, PartialEq, Encode, Decode, MaxEncodedLen, TypeInfo, Debug)]
pub enum MessageOrigin {
	Here,
	There,
	Everywhere(u32),
}

impl From<u32> for MessageOrigin {
	fn from(i: u32) -> Self {
		Self::Everywhere(i)
	}
}

/// Converts `Self` into a `Weight` by using `Self` for all components.
pub trait IntoWeight {
	fn into_weight(self) -> Weight;
}

impl IntoWeight for u64 {
	fn into_weight(self) -> Weight {
		Weight::from_parts(self, self)
	}
}

pub fn msg<N: Get<u32>>(x: &'static str) -> BoundedSlice<u8, N> {
	BoundedSlice::defensive_truncate_from(x.as_bytes())
}

pub fn vmsg(x: &'static str) -> Vec<u8> {
	x.as_bytes().to_vec()
}

pub fn page<T: Config>(msg: &[u8]) -> PageOf<T> {
	PageOf::<T>::from_message::<T>(msg.try_into().unwrap())
}

pub fn single_page_book<T: Config>() -> BookStateOf<T> {
	BookState { begin: 0, end: 1, count: 1, ready_neighbours: None, message_count: 0, size: 0 }
}

/// Returns a page filled with empty messages and the number of messages.
pub fn full_page<T: Config>() -> (PageOf<T>, usize) {
	let mut msgs = 0;
	let mut page = PageOf::<T>::default();
	for i in 0..u32::MAX {
		let r = i.using_encoded(|d| page.try_append_message::<T>(d.try_into().unwrap()));
		if r.is_err() {
			break
		} else {
			msgs += 1;
		}
	}
	assert!(msgs > 0, "page must hold at least one message");
	(page, msgs)
}

/// Returns a page filled with empty messages and the number of messages.
pub fn book_for<T: Config>(page: &PageOf<T>) -> BookStateOf<T> {
	BookState {
		count: 1,
		begin: 0,
		end: 1,
		ready_neighbours: None,
		message_count: page.remaining.into(),
		size: page.remaining_size.into(),
	}
}

#[allow(dead_code)]
pub fn assert_last_event<T: Config>(generic_event: <T as Config>::RuntimeEvent) {
	assert!(
		!frame_system::Pallet::<T>::block_number().is_zero(),
		"The genesis block has n o events"
	);
	frame_system::Pallet::<T>::assert_last_event(generic_event.into());
}
