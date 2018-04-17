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

//! Defines primitive types for creating or validating a parachain.

extern crate substrate_codec as codec;

#[cfg_attr(not(feature = "std"), no_std)]
#[cfg_attr(not(feature = "std"), feature(alloc))]

#[cfg(not(feature = "std"))]
extern crate alloc;

#[cfg(not(feature = "std"))]
use alloc::vec::Vec;

use codec::Slicable;

/// Validation parameters for evaluating the parachain validity function.
// TODO: consolidated ingress and balance downloads
#[derive(PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct ValidationParams {
	/// The collation body.
	pub block_data: Vec<u8>,
	/// Previous head-data.
	pub parent_head: Vec<u8>,
}

impl Slicable for ValidationParams {
	fn encode(&self) -> Vec<u8> {
		let mut v = Vec::new();

		self.block_data.using_encoded(|s| v.extend(s));
		self.parent_head.using_encoded(|s| v.extend(s));

		v
	}

	fn decode<I: codec::Input>(input: &mut I) -> Option<Self> {
		Some(ValidationParams {
			block_data: Slicable::decode(input)?,
			parent_head: Slicable::decode(input)?,
		})
	}
}

/// The result of parachain validation.
// TODO: egress and balance uploads
#[derive(PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct ValidationResult {
	/// New head data that should be included in the relay chain state.
	pub head_data: Vec<u8>
}

impl Slicable for ValidationResult {
	fn encode(&self) -> Vec<u8> {
		self.head_data.encode()
	}

	fn decode<I: codec::Input>(input: &mut I) -> Option<Self> {
		Some(ValidationResult {
			head_data: Slicable::decode(input)?,
		})
	}
}
