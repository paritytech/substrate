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

//! Unchecked Transaction type.

use slicable::{Slicable, NonTrivialSlicable};
use streamreader::StreamReader;
use joiner::Joiner;
use primitives::Transaction;
use runtime_support::{mem, ed25519_verify};
use runtime_support::prelude::*;

#[cfg(feature = "with-std")]
use std::fmt;

/// A transactions right from the external world. Unchecked.
pub struct UncheckedTransaction {
	/// The actual transaction information.
	pub transaction: Transaction,
	/// The signature; should be an Ed25519 signature applied to the serialised `transaction` field.
	pub signature: [u8; 64],
}

impl UncheckedTransaction {
	/// Verify the signature.
	pub fn ed25519_verify(&self) -> bool {
		let msg = self.transaction.to_vec();
		ed25519_verify(&self.signature, &msg, &self.transaction.signed)
	}
}

#[cfg(feature = "with-std")]
impl PartialEq for UncheckedTransaction {
	fn eq(&self, other: &Self) -> bool {
		self.signature.iter().eq(other.signature.iter()) && self.transaction == other.transaction
	}
}

#[cfg(feature = "with-std")]
impl fmt::Debug for UncheckedTransaction {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "UncheckedTransaction({:?})", self.transaction)
	}
}

impl Slicable for UncheckedTransaction {
	fn from_slice(value: &[u8]) -> Option<Self> {
		let mut reader = StreamReader::new(value);
		Some(UncheckedTransaction {
			signature: reader.read()?,
			transaction: reader.read()?,
		})
	}

	fn set_as_slice<F: Fn(&mut [u8], usize) -> bool>(_fill_slice: &F) -> Option<Self> {
		unimplemented!();
	}

	fn to_vec(&self) -> Vec<u8> {
		Vec::new()
			.join(&self.signature)
			.join(&self.transaction)
	}

	fn size_of(data: &[u8]) -> Option<usize> {
		let first_part = mem::size_of::<[u8; 64]>();
		let second_part = <Transaction>::size_of(&data[first_part..])?;
		Some(first_part + second_part)
	}
}

impl NonTrivialSlicable for UncheckedTransaction {}
