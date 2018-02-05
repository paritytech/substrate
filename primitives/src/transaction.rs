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

use bytes::{self, Vec};
use codec::Slicable;
use runtime_function::Function;

#[cfg(feature = "std")]
use std::fmt;

#[cfg(not(feature = "std"))]
use alloc::fmt;

/// A vetted and verified transaction from the external world.
#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize)]
pub struct Transaction {
	/// Who signed it (note this is not a signature).
	pub signed: ::AccountId,
	/// The number of transactions have come before from the same signer.
	pub nonce: ::TxOrder,
	/// The function that should be called.
	pub function: Function,
	/// Serialised input data to the function.
	#[serde(with = "bytes")]
	pub input_data: Vec<u8>,
}

/// A transactions right from the external world. Unchecked.
#[derive(Eq, Clone, Serialize, Deserialize)]
pub struct UncheckedTransaction {
	/// The actual transaction information.
	pub transaction: Transaction,
	/// The signature; should be an Ed25519 signature applied to the serialised `transaction` field.
	pub signature: ::Signature,
}

impl Slicable for UncheckedTransaction {
	fn from_slice(value: &mut &[u8]) -> Option<Self> {
		Some(UncheckedTransaction {
			transaction: Transaction {
				signed: try_opt!(Slicable::from_slice(value)),
				nonce: try_opt!(Slicable::from_slice(value)),
				function: try_opt!(Slicable::from_slice(value)),
				input_data: try_opt!(Slicable::from_slice(value)),
			},
			signature: try_opt!(Slicable::from_slice(value)),
		})
	}

	fn to_vec(&self) -> Vec<u8> {
		let mut v = Vec::new();

		self.transaction.signed.as_slice_then(|s| v.extend(s));
		self.transaction.nonce.as_slice_then(|s| v.extend(s));
		self.transaction.function.as_slice_then(|s| v.extend(s));
		self.transaction.input_data.as_slice_then(|s| v.extend(s));
		self.signature.as_slice_then(|s| v.extend(s));

		v
	}

	fn as_slice_then<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
		f(self.to_vec().as_slice())
	}
}

impl ::codec::NonTrivialSlicable for UncheckedTransaction {}

impl PartialEq for UncheckedTransaction {
	fn eq(&self, other: &Self) -> bool {
		self.signature.iter().eq(other.signature.iter()) && self.transaction == other.transaction
	}
}

impl fmt::Debug for UncheckedTransaction {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "UncheckedTransaction({:?})", self.transaction)
	}
}
