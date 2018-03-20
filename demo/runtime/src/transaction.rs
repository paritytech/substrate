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

//! Transaction type.

use rstd::prelude::*;
use rstd::ops;
use codec::{Input, Slicable};
use demo_primitives::{AccountId, TxOrder, Signature};
use dispatch::PubCall;

#[cfg(feature = "std")]
use std::fmt;

/// A vetted and verified transaction from the external world.
#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug))]
pub struct Transaction {
	/// Who signed it (note this is not a signature).
	pub signed: AccountId,
	/// The number of transactions have come before from the same signer.
	pub nonce: TxOrder,
	/// The function that should be called.
	pub function: PubCall,
}

impl Slicable for Transaction {
	fn decode<I: Input>(input: &mut I) -> Option<Self> {
		Some(Transaction {
			signed: Slicable::decode(input)?,
			nonce: Slicable::decode(input)?,
			function: Slicable::decode(input)?,
		})
	}

	fn encode(&self) -> Vec<u8> {
		let mut v = Vec::new();

		self.signed.using_encoded(|s| v.extend(s));
		self.nonce.using_encoded(|s| v.extend(s));
		self.function.using_encoded(|s| v.extend(s));

		v
	}
}

impl ::codec::NonTrivialSlicable for Transaction {}

/// A transactions right from the external world. Unchecked.
#[derive(Eq, Clone)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
pub struct UncheckedTransaction {
	/// The actual transaction information.
	pub transaction: Transaction,
	/// The signature; should be an Ed25519 signature applied to the serialised `transaction` field.
	pub signature: Signature,
}

impl Slicable for UncheckedTransaction {
	fn decode<I: Input>(input: &mut I) -> Option<Self> {
		// This is a little more complicated than usual since the binary format must be compatible
		// with substrate's generic `Vec<u8>` type. Basically this just means accepting that there
		// will be a prefix of u32, which has the total number of bytes following (we don't need
		// to use this).
		let _length_do_not_remove_me_see_above: u32 = Slicable::decode(input)?;

		Some(UncheckedTransaction {
			transaction: Slicable::decode(input)?,
			signature: Slicable::decode(input)?,
		})
	}

	fn encode(&self) -> Vec<u8> {
		let mut v = Vec::new();

		// need to prefix with the total length as u32 to ensure it's binary comptible with
		// Vec<u8>. we'll make room for it here, then overwrite once we know the length.
		v.extend(&[0u8; 4]);

		self.transaction.signed.using_encoded(|s| v.extend(s));
		self.transaction.nonce.using_encoded(|s| v.extend(s));
		self.transaction.function.using_encoded(|s| v.extend(s));
		self.signature.using_encoded(|s| v.extend(s));

		let length = (v.len() - 4) as u32;
		length.using_encoded(|s| v[0..4].copy_from_slice(s));

		v
	}
}

impl ::codec::NonTrivialSlicable for UncheckedTransaction {}

impl PartialEq for UncheckedTransaction {
	fn eq(&self, other: &Self) -> bool {
		self.signature.iter().eq(other.signature.iter()) && self.transaction == other.transaction
	}
}

#[cfg(feature = "std")]
impl fmt::Debug for UncheckedTransaction {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "UncheckedTransaction({:?})", self.transaction)
	}
}

/// A type-safe indicator that a transaction has been checked.
#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct CheckedTransaction(UncheckedTransaction);

impl CheckedTransaction {
	/// Get a reference to the checked signature.
	pub fn signature(&self) -> &Signature {
		&self.0.signature
	}

	/// Get the inner object.
	pub fn drain(self) -> UncheckedTransaction {
		self.0
	}
}

impl ops::Deref for CheckedTransaction {
	type Target = Transaction;

	fn deref(&self) -> &Transaction {
		&self.0.transaction
	}
}

/// Check the signature on a transaction.
///
/// On failure, return the transaction back.
pub fn check(tx: UncheckedTransaction) -> Result<CheckedTransaction, UncheckedTransaction> {
	let msg = ::codec::Slicable::encode(&tx.transaction);
	if ::runtime_io::ed25519_verify(&tx.signature.0, &msg, &tx.transaction.signed) {
		Ok(CheckedTransaction(tx))
	} else {
		Err(tx)
	}
}


#[cfg(test)]
mod tests {
	use super::*;
	use primitives;
	use codec::Slicable;
	use primitives::hexdisplay::HexDisplay;
	use dispatch::public::Call;
	use runtime::timestamp::public::Call as TimestampCall;

	#[test]
	fn serialize_unchecked() {
		let tx = UncheckedTransaction {
			transaction: Transaction {
				signed: [1; 32],
				nonce: 999u64,
				function: Call::Timestamp(TimestampCall::set(135135)),
			},
			signature: primitives::hash::H512([0; 64]),
		};
		// 71000000
		// 0101010101010101010101010101010101010101010101010101010101010101
		// e703000000000000
		// 00
		// df0f0200
		// 0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

		let v = Slicable::encode(&tx);
		println!("{}", HexDisplay::from(&v));
		assert_eq!(UncheckedTransaction::decode(&mut &v[..]).unwrap(), tx);
	}
}
