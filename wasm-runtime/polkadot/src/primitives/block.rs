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

//! Block type.

use runtime_std::prelude::*;
use codec::{StreamReader, Joiner, Slicable, NonTrivialSlicable};
use primitives::{Header, UncheckedTransaction};

/// A Polkadot relay chain block.
#[cfg_attr(feature = "std", derive(PartialEq, Debug))]
pub struct Block {
	/// The header of the block.
	pub header: Header,
	/// All transactions.
	pub transactions: Vec<UncheckedTransaction>,
}

impl Slicable for Block {
	fn from_slice(value: &[u8]) -> Option<Self> {
		let mut reader = StreamReader::new(value);
		Some(Block {
			header: reader.read()?,
			transactions: reader.read()?,
		})
	}

	fn set_as_slice<F: Fn(&mut [u8], usize) -> bool>(_fill_slice: F) -> Option<Self> {
		unimplemented!();
	}

	fn to_vec(&self) -> Vec<u8> {
		Vec::new()
			.join(&self.header)
			.join(&self.transactions)
	}

	fn size_of(data: &[u8]) -> Option<usize> {
		let first_part = Header::size_of(data)?;
		let second_part = <Vec<UncheckedTransaction>>::size_of(&data[first_part..])?;
		Some(first_part + second_part)
	}
}

impl NonTrivialSlicable for Block {}
