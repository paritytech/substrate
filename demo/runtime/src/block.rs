// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Substrate Demo.

// Substrate Demo is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate Demo is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate Demo.  If not, see <http://www.gnu.org/licenses/>.

//! Block and header type definitions.

use rstd::prelude::*;
use codec::{Input, Slicable};
use extrinsic::UncheckedExtrinsic;
use runtime_primitives::Blocky;
pub use demo_primitives::header::{Header, Digest, Log, Number, HeaderHash};

/// A block on the chain.
#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Serialize, Debug))]
pub struct Block {
	/// The block header.
	pub header: Header,
	/// All relay-chain transactions.
	pub transactions: Vec<UncheckedExtrinsic>,	// TODO: rename extrinsics.
}

impl Blocky for Block {
	type Extrinsic = UncheckedExtrinsic;
	type Header = Header;
	fn header(&self) -> &Self::Header {
		&self.header
	}
	fn extrinsics(&self) -> &[Self::Extrinsic] {
		&self.transactions[..]
	}
	fn deconstruct(self) -> (Self::Header, Vec<Self::Extrinsic>) {
		(self.header, self.transactions)
	}
}

impl Slicable for Block {
	fn decode<I: Input>(input: &mut I) -> Option<Self> {
		let (header, transactions) = Slicable::decode(input)?;
		Some(Block { header, transactions })
	}

	fn encode(&self) -> Vec<u8> {
		let mut v = Vec::new();

		v.extend(self.header.encode());
		v.extend(self.transactions.encode());

		v
	}
}
