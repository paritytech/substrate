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

//! Extrinsic type.

use rstd::prelude::*;
use rstd::ops;
use codec::{Input, Slicable};
use demo_primitives::{AccountId, TxOrder, Signature};
use runtime::Call;
use runtime_primitives::{Checkable, Applyable};
use runtime_support::AuxDispatchable;

#[cfg(feature = "std")]
use std::fmt;

/// A vetted and verified transaction from the external world.
#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Serialize, Debug))]
pub struct Extrinsic {
	/// Who signed it (note this is not a signature).
	pub signed: AccountId,
	/// The number of transactions have come before from the same signer.
	pub nonce: TxOrder,
	/// The function that should be called.
	pub function: Call,
}

impl Slicable for Extrinsic {
	fn decode<I: Input>(input: &mut I) -> Option<Self> {
		Some(Extrinsic {
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

impl ::codec::NonTrivialSlicable for Extrinsic {}

/// A transactions right from the external world. Unchecked.
#[derive(Eq, Clone)]
#[cfg_attr(feature = "std", derive(Serialize))]
pub struct UncheckedExtrinsic {
	/// The actual transaction information.
	pub transaction: Extrinsic,
	/// The signature; should be an Ed25519 signature applied to the serialised `transaction` field.
	pub signature: Signature,
}

impl Slicable for UncheckedExtrinsic {
	fn decode<I: Input>(input: &mut I) -> Option<Self> {
		// This is a little more complicated than usual since the binary format must be compatible
		// with substrate's generic `Vec<u8>` type. Basically this just means accepting that there
		// will be a prefix of u32, which has the total number of bytes following (we don't need
		// to use this).
		let _length_do_not_remove_me_see_above: u32 = Slicable::decode(input)?;

		Some(UncheckedExtrinsic {
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

impl ::codec::NonTrivialSlicable for UncheckedExtrinsic {}

impl PartialEq for UncheckedExtrinsic {
	fn eq(&self, other: &Self) -> bool {
		self.signature.iter().eq(other.signature.iter()) && self.transaction == other.transaction
	}
}

#[cfg(feature = "std")]
impl fmt::Debug for UncheckedExtrinsic {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "UncheckedExtrinsic({:?})", self.transaction)
	}
}

/// A type-safe indicator that a transaction has been checked.
#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct CheckedExtrinsic(UncheckedExtrinsic);

impl CheckedExtrinsic {
	/// Get a reference to the checked signature.
	pub fn signature(&self) -> &Signature {
		&self.0.signature
	}
}

impl ops::Deref for CheckedExtrinsic {
	type Target = Extrinsic;

	fn deref(&self) -> &Extrinsic {
		&self.0.transaction
	}
}

/// Check the signature on a transaction.
///
/// On failure, return the transaction back.
pub fn check(tx: UncheckedExtrinsic) -> Result<CheckedExtrinsic, UncheckedExtrinsic> {
	let msg = ::codec::Slicable::encode(&tx.transaction);
	if ::runtime_io::ed25519_verify(&tx.signature.0, &msg, &tx.transaction.signed) {
		Ok(CheckedExtrinsic(tx))
	} else {
		Err(tx)
	}
}

impl Checkable for UncheckedExtrinsic {
	type CheckedType = CheckedExtrinsic;

	fn check(self) -> Result<Self::CheckedType, Self> {
		check(self)
	}
}

impl Applyable for CheckedExtrinsic {
	type IndexType = TxOrder;
	type AccountIdType = AccountId;

	fn index(&self) -> &Self::IndexType {
		&self.0.transaction.nonce
	}

	fn sender(&self) -> &Self::AccountIdType {
		&self.0.transaction.signed
	}

	fn apply(self) {
		let tx = self.0.transaction;
		//TODO: take payment e.g. public_pass_from_payment
		tx.function.dispatch(&tx.signed);
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use substrate_primitives;
	use codec::Slicable;
	use substrate_primitives::hexdisplay::HexDisplay;
	use timestamp;
	use runtime::Call;

	#[test]
	fn serialize_unchecked() {
		let tx = UncheckedExtrinsic {
			transaction: Extrinsic {
				signed: [1; 32],
				nonce: 999u64,
				function: Call::Timestamp(timestamp::Call::set(135135)),
			},
			signature: substrate_primitives::hash::H512([0; 64]),
		};
		// 71000000
		// 0101010101010101010101010101010101010101010101010101010101010101
		// e703000000000000
		// 00
		// df0f0200
		// 0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

		let v = Slicable::encode(&tx);
		println!("{}", HexDisplay::from(&v));
		assert_eq!(UncheckedExtrinsic::decode(&mut &v[..]).unwrap(), tx);
	}
}
