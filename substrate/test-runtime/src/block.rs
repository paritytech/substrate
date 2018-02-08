// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! A toy unchecked transaction complete with signature.

use rstd::prelude::*;
use codec::{Input, Slicable, Joiner};
use super::{Header, UncheckedTransaction};

#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Debug))]
/// A coupling between a header and a list of transactions.
pub struct Block {
	/// The block header.
	pub header: Header,
	/// The list of transactions in the block.
	pub transactions: Vec<UncheckedTransaction>,
}

impl Slicable for Block {
	fn decode<I: Input>(input: &mut I) -> Option<Self> {
		Some(Block {
			header: Slicable::decode(input)?,
			transactions: Slicable::decode(input)?,
		})
	}

	fn encode(&self) -> Vec<u8> {
		Vec::new()
			.and(&self.header)
			.and(&self.transactions)
	}
}

impl ::codec::NonTrivialSlicable for Block {}
