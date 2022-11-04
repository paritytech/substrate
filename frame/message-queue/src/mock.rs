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

use frame_support::{assert_noop, assert_ok, parameter_types};
use sp_std::collections::btree_map::BTreeMap;

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

pub fn page<T: Config>(msg: &[u8], origin: MessageOrigin) -> PageOf<T> {
	PageOf::<T>::from_message::<T>(
		msg.try_into().unwrap(),
		BoundedSlice::try_from(&origin.encode()[..]).unwrap(),
	)
}

pub fn single_page_book<T: Config>() -> BookStateOf<T> {
	BookStateOf::<T> { begin: 0, end: 1, count: 1, ready_neighbours: None }
}

/// Returns a page filled with empty messages and the number of messages.
pub fn full_page<T: Config>() -> (PageOf<T>, usize) {
	let mut msgs = 0;
	let mut page = PageOf::<T>::default();
	for i in 0..u32::MAX {
		if page
			.try_append_message::<T>(
				[][..].try_into().unwrap(),
				MessageOrigin::Everywhere(i).encode()[..].try_into().unwrap(),
			)
			.is_err()
		{
			break
		} else {
			msgs += 1;
		}
	}
	assert!(msgs > 0, "page must hold at least one message");
	(page, msgs)
}

pub fn assert_last_event<T: Config>(generic_event: <T as Config>::RuntimeEvent) {
	assert!(
		!frame_system::Pallet::<T>::block_number().is_zero(),
		"The genesis block has n o events"
	);
	frame_system::Pallet::<T>::assert_last_event(generic_event.into());
}
