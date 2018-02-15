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
use codec::{Input, Slicable};
use super::{Signature, Transaction};

/// A transactions right from the external world. Unchecked.
#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct UncheckedTransaction {
	/// The actual transaction information.
	pub tx: Transaction,
	/// The signature; should be an Ed25519 signature applied to the serialised `transaction` field.
	pub signature: Signature,
}

impl Slicable for UncheckedTransaction {
	fn decode<I: Input>(input: &mut I) -> Option<Self> {
		// This is a little more complicated than usua since the binary format must be compatible
		// with substrate's generic `Vec<u8>` type. Basically this just means accepting that there
		// will be a prefix of u32, which has the total number of bytes following (we don't need
		// to use this).
		let _length_do_not_remove_me_see_above: u32 = Slicable::decode(input)?;
		Some(UncheckedTransaction {
			tx: Slicable::decode(input)?,
			signature: Slicable::decode(input)?,
		})
	}

	fn encode(&self) -> Vec<u8> {
		let mut v = Vec::new();

		// need to prefix with the total length as u32 to ensure it's binary comptible with
		// Vec<u8>. we'll make room for it here, then overwrite once we know the length.
		v.extend(&[0u8; 4]);

		self.tx.using_encoded(|s| v.extend(s));
		self.signature.using_encoded(|s| v.extend(s));

		let length = (v.len() - 4) as u32;
		length.using_encoded(|s| v[0..4].copy_from_slice(s));

		v
	}
}

impl ::codec::NonTrivialSlicable for UncheckedTransaction {}

#[cfg(test)]
mod tests {
	use super::*;
	use keyring::Keyring;
	use ::Transaction;

	#[test]
	fn test_unchecked_encoding() {
		let tx = Transaction {
			from: Keyring::Alice.to_raw_public(),
			to: Keyring::Bob.to_raw_public(),
			amount: 69,
			nonce: 34,
		};
		let signature = Keyring::from_raw_public(tx.from).unwrap().sign(&tx.encode());
		let signed = UncheckedTransaction { tx, signature };

		assert_eq!(signed.encode(), vec![
			// length
			144, 0, 0, 0,
			// from
			209, 114, 167, 76, 218, 76, 134, 89, 18, 195, 43, 160, 168, 10, 87, 174, 105, 171, 174, 65, 14, 92, 203, 89, 222, 232, 78, 47, 68, 50, 219, 79,
			// to
			215, 86, 142, 95, 10, 126, 218, 103, 168, 38, 145, 255, 55, 154, 196, 187, 164, 249, 201, 184, 89, 254, 119, 155, 93, 70, 54, 59, 97, 173, 45, 185,
			// amount
			69, 0, 0, 0, 0, 0, 0, 0,
			// nonce
			34, 0, 0, 0, 0, 0, 0, 0,
			// signature
			207, 69, 156, 55, 7, 227, 202, 3, 114, 111, 43, 46, 227, 38, 39, 122, 245, 69, 195, 117, 190, 154, 89, 76, 134, 91, 251, 230, 31, 221, 1, 194, 144, 34, 33, 58, 220, 154, 205, 135, 224, 52, 248, 198, 12, 17, 96, 53, 110, 160, 194, 10, 9, 60, 40, 133, 57, 112, 151, 200, 105, 198, 245, 10
		]);
	}
}
