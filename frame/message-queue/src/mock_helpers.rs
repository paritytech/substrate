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

//! Setup helpers for testing and benchmarking.
//!
//! Cannot be put into mock.rs since benchmarks require no-std and mock.rs is std.

use crate::*;

/// Converts `Self` into a `Weight` by using `Self` for all components.
pub trait IntoWeight {
	fn into_weight(self) -> Weight;
}

impl IntoWeight for u64 {
	fn into_weight(self) -> Weight {
		Weight::from_parts(self, self)
	}
}

/// Mocked message origin.
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

/// Processes any message and consumes (1, 1) weight per message.
pub struct NoopMessageProcessor;
impl ProcessMessage for NoopMessageProcessor {
	type Origin = MessageOrigin;

	fn process_message(
		_message: &[u8],
		_origin: Self::Origin,
		weight_limit: Weight,
	) -> Result<(bool, Weight), ProcessMessageError> {
		let weight = Weight::from_parts(1, 1);

		if weight.all_lte(weight_limit) {
			Ok((true, weight))
		} else {
			Err(ProcessMessageError::Overweight(weight))
		}
	}
}

/// Create a message from the given data.
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

/// Assert the last event that was emitted.
pub fn assert_last_event<T: Config>(generic_event: <T as Config>::RuntimeEvent) {
	assert!(
		!frame_system::Pallet::<T>::block_number().is_zero(),
		"The genesis block has n o events"
	);
	frame_system::Pallet::<T>::assert_last_event(generic_event.into());
}
