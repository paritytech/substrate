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

//! Transaction type.

use runtime_std::prelude::*;
use codec::{StreamReader, Joiner, Slicable, NonTrivialSlicable};
use primitives::{AccountID, TxOrder, Function};
use runtime_std::mem;

/// A vetted and verified transaction from the external world.
#[cfg_attr(feature = "with-std", derive(PartialEq, Debug))]
pub struct Transaction {
	/// Who signed it (note this is not a signature).
	pub signed: AccountID,
	/// The number of transactions have come before from the same signer.
	pub nonce: TxOrder,
	/// The function that should be called.
	pub function: Function,
	/// Serialised input data to the function.
	pub input_data: Vec<u8>,
}

impl Slicable for Transaction {
	fn from_slice(value: &[u8]) -> Option<Self> {
		let mut reader = StreamReader::new(value);
		Some(Transaction {
			signed: reader.read()?,
			nonce: reader.read()?,
			function: Function::from_u8(reader.read()?)?,
			input_data: reader.read()?,
		})
	}

	fn set_as_slice<F: Fn(&mut [u8], usize) -> bool>(_fill_slice: &F) -> Option<Self> {
		unimplemented!();
	}

	fn to_vec(&self) -> Vec<u8> {
		Vec::new()
			.join(&self.signed)
			.join(&self.nonce)
			.join(&(self.function as u8))
			.join(&self.input_data)
	}

	fn size_of(data: &[u8]) -> Option<usize> {
		let first_part = mem::size_of::<AccountID>() + mem::size_of::<TxOrder>() + mem::size_of::<u8>();
		let second_part = <Vec<u8>>::size_of(&data[first_part..])?;
		Some(first_part + second_part)
	}
}

impl NonTrivialSlicable for Transaction {}
