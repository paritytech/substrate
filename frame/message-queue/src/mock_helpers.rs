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

//! Std setup helpers for testing and benchmarking.
//!
//! Cannot be put into mock.rs since benchmarks require no-std and mock.rs is std.

use crate::*;
use frame_support::traits::Defensive;

/// Converts `Self` into a `Weight` by using `Self` for all components.
pub trait IntoWeight {
	fn into_weight(self) -> Weight;
}

impl IntoWeight for u64 {
	fn into_weight(self) -> Weight {
		Weight::from_parts(self, self)
	}
}

/// Mocked message origin for testing.
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

/// Processes any message and consumes `(REQUIRED_WEIGHT, REQUIRED_WEIGHT)` weight.
///
/// Returns [ProcessMessageError::Overweight] error if the weight limit is not sufficient.
pub struct NoopMessageProcessor<Origin, const REQUIRED_WEIGHT: u64 = 1>(PhantomData<Origin>);
impl<Origin, const REQUIRED_WEIGHT: u64> ProcessMessage
	for NoopMessageProcessor<Origin, REQUIRED_WEIGHT>
where
	Origin: codec::FullCodec + MaxEncodedLen + Clone + Eq + PartialEq + TypeInfo + Debug,
{
	type Origin = Origin;

	fn process_message(
		_message: &[u8],
		_origin: Self::Origin,
		meter: &mut WeightMeter,
		_id: &mut [u8; 32],
	) -> Result<bool, ProcessMessageError> {
		let required = Weight::from_parts(REQUIRED_WEIGHT, REQUIRED_WEIGHT);

		if meter.check_accrue(required) {
			Ok(true)
		} else {
			Err(ProcessMessageError::Overweight(required))
		}
	}
}

/// Create a message from the given data.
pub fn msg<N: Get<u32>>(x: &str) -> BoundedSlice<u8, N> {
	BoundedSlice::defensive_truncate_from(x.as_bytes())
}

pub fn vmsg(x: &str) -> Vec<u8> {
	x.as_bytes().to_vec()
}

/// Create a page from a single message.
pub fn page<T: Config>(msg: &[u8]) -> PageOf<T> {
	PageOf::<T>::from_message::<T>(msg.try_into().unwrap())
}

pub fn single_page_book<T: Config>() -> BookStateOf<T> {
	BookState { begin: 0, end: 1, count: 1, ..Default::default() }
}

pub fn empty_book<T: Config>() -> BookStateOf<T> {
	BookState { begin: 0, end: 1, count: 1, ..Default::default() }
}

/// Returns a full page of messages with their index as payload and the number of messages.
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
		message_count: page.remaining.into() as u64,
		size: page.remaining_size.into() as u64,
		..Default::default()
	}
}

/// Assert the last event that was emitted.
#[cfg(any(feature = "std", feature = "runtime-benchmarks", test))]
pub fn assert_last_event<T: Config>(generic_event: <T as Config>::RuntimeEvent) {
	assert!(
		!frame_system::Pallet::<T>::block_number().is_zero(),
		"The genesis block has n o events"
	);
	frame_system::Pallet::<T>::assert_last_event(generic_event.into());
}

/// Provide a setup for `bump_service_head`.
pub fn setup_bump_service_head<T: Config>(
	current: <<T as Config>::MessageProcessor as ProcessMessage>::Origin,
	next: <<T as Config>::MessageProcessor as ProcessMessage>::Origin,
) {
	let mut book = single_page_book::<T>();
	book.ready_neighbours = Some(Neighbours::<MessageOriginOf<T>> { prev: next.clone(), next });
	ServiceHead::<T>::put(&current);
	BookStateFor::<T>::insert(&current, &book);
}

/// Knit a queue into the ready-ring and write it back to storage.
pub fn knit<T: Config>(o: &<<T as Config>::MessageProcessor as ProcessMessage>::Origin) {
	let mut b = BookStateFor::<T>::get(o);
	b.ready_neighbours = crate::Pallet::<T>::ready_ring_knit(o).ok().defensive();
	BookStateFor::<T>::insert(o, b);
}

/// Unknit a queue into the ready-ring and write it back to storage.
pub fn unknit<T: Config>(o: &<<T as Config>::MessageProcessor as ProcessMessage>::Origin) {
	let mut b = BookStateFor::<T>::get(o);
	crate::Pallet::<T>::ready_ring_unknit(o, b.ready_neighbours.unwrap());
	b.ready_neighbours = None;
	BookStateFor::<T>::insert(o, b);
}

/// Build a ring with three queues: `Here`, `There` and `Everywhere(0)`.
pub fn build_ring<T: Config>(
	queues: &[<<T as Config>::MessageProcessor as ProcessMessage>::Origin],
) {
	for queue in queues {
		BookStateFor::<T>::insert(queue, empty_book::<T>());
	}
	for queue in queues {
		knit::<T>(queue);
	}
	assert_ring::<T>(queues);
}

/// Check that the Ready Ring consists of `queues` in that exact order.
///
/// Also check that all backlinks are valid and that the first element is the service head.
pub fn assert_ring<T: Config>(
	queues: &[<<T as Config>::MessageProcessor as ProcessMessage>::Origin],
) {
	for (i, origin) in queues.iter().enumerate() {
		let book = BookStateFor::<T>::get(origin);
		assert_eq!(
			book.ready_neighbours,
			Some(Neighbours {
				prev: queues[(i + queues.len() - 1) % queues.len()].clone(),
				next: queues[(i + 1) % queues.len()].clone(),
			})
		);
	}
	assert_eq!(ServiceHead::<T>::get(), queues.first().cloned());
}
