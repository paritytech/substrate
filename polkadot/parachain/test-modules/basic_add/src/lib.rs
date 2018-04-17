// Copyright 2017 Parity Technologies (UK) Ltd.
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

//! Basic parachain that adds a number as part of its state.

#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(not(feature = "std"), feature(alloc, core_intrinsics, global_allocator, lang_items))]

#[cfg(not(feature = "std"))]
extern crate alloc;

extern crate polkadot_parachain as parachain;
extern crate wee_alloc;
extern crate tiny_keccak;

use parachain::codec::{Slicable, Input};

#[cfg(not(feature = "std"))]
mod wasm;

#[cfg(not(feature = "std"))]
pub use wasm::validate;

#[cfg(not(feature = "std"))]
use alloc::vec::Vec;

// Define global allocator.
#[cfg(not(feature = "std"))]
#[global_allocator]
static ALLOC: wee_alloc::WeeAlloc = wee_alloc::WeeAlloc::INIT;

/// Head data for this parachain.
#[derive(Default)]
pub struct HeadData {
	/// Block number
	pub number: u64,
	/// parent block keccak256
	pub parent_hash: [u8; 32],
	/// hash of post-execution state.
	pub post_state: [u8; 32],
}

impl Slicable for HeadData {
	fn encode(&self) -> Vec<u8> {
		let mut v = Vec::new();

		self.number.using_encoded(|s| v.extend(s));
		self.parent_hash.using_encoded(|s| v.extend(s));
		self.post_state.using_encoded(|s| v.extend(s));

		v
	}

	fn decode<I: Input>(input: &mut I) -> Option<Self> {
		Some(HeadData {
			number: Slicable::decode(input)?,
			parent_hash: Slicable::decode(input)?,
			post_state: Slicable::decode(input)?,
		})
	}
}

/// Block data for this parachain.
#[derive(Default)]
pub struct BlockData {
	/// State to begin from.
	pub state: u64,
	/// Amount to add (overflowing)
	pub add: u64,
}

impl Slicable for BlockData {
	fn encode(&self) -> Vec<u8> {
		let mut v = Vec::new();

		self.state.using_encoded(|s| v.extend(s));
		self.add.using_encoded(|s| v.extend(s));

		v
	}

	fn decode<I: Input>(input: &mut I) -> Option<Self> {
		Some(BlockData {
			state: Slicable::decode(input)?,
			add: Slicable::decode(input)?,
		})
	}
}
