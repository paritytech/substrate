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
	BoundedSlice::truncate_from(x.as_bytes())
}

pub fn vmsg(x: &'static str) -> Vec<u8> {
	x.as_bytes().to_vec()
}

/// Returns a full page and its number of empty messages.
pub fn full_page<T: Config>() -> (PageOf<T>, usize) {
	let mut msgs = 0;
	let mut page = PageOf::<T>::default();
	for i in 0..u32::MAX {
		if page.try_append_message(&[], &MessageOrigin::Everywhere(i).encode()).is_err() {
			break
		} else {
			msgs += 1;
		}
	}
	assert!(msgs > 0, "page must hold at least one message");
	(page, msgs)
}
