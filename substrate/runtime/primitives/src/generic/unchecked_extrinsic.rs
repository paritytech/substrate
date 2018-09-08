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

//! Generic implementation of an unchecked (pre-verification) extrinsic.

#[cfg(feature = "std")]
use std::fmt;

use rstd::prelude::*;
use codec::{Decode, Encode, Input};
use traits::{self, Member, SimpleArithmetic, MaybeDisplay};
use super::CheckedExtrinsic;

/// A extrinsic right from the external world. This is unchecked and so
/// can contain a signature.
#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
pub struct UncheckedExtrinsic<Address, Index, Call, Signature> {
	/// The signature and address, if this is a signed extrinsic.
	pub signature: Option<(Address, Signature)>,
	/// The number of extrinsics have come before from the same signer.
	pub index: Index,
	/// The function that should be called.
	pub function: Call,
}

impl<Address, Index, Call, Signature> UncheckedExtrinsic<Address, Index, Call, Signature> {
	/// New instance of a signed extrinsic aka "transaction".
	pub fn new_signed(index: Index, function: Call, signed: Address, signature: Signature) -> Self {
		UncheckedExtrinsic {
			signature: Some((signed, signature)),
			index,
			function,
		}
	}

	/// New instance of an unsigned extrinsic aka "inherent".
	pub fn new_unsigned(index: Index, function: Call) -> Self {
		UncheckedExtrinsic {
			signature: None,
			index,
			function,
		}
	}

	/// `true` if there is a signature.
	pub fn is_signed(&self) -> bool {
		self.signature.is_some()
	}
}

impl<Address, AccountId, Index, Call, Signature, ThisLookup> traits::Checkable<ThisLookup>
	for UncheckedExtrinsic<Address, Index, Call, Signature>
where
	Address: Member + MaybeDisplay,
	Index: Encode + Member + MaybeDisplay + SimpleArithmetic,
	Call: Encode + Member,
	Signature: Member + traits::Verify<Signer=AccountId>,
	AccountId: Member + MaybeDisplay,
	ThisLookup: FnOnce(Address) -> Result<AccountId, &'static str>,
{
	type Checked = CheckedExtrinsic<AccountId, Index, Call>;

	fn check_with(self, lookup: ThisLookup) -> Result<Self::Checked, &'static str> {
		Ok(match self.signature {
			Some((signed, signature)) => {
				let payload = (self.index, self.function);
				let signed = lookup(signed)?;
				if !::verify_encoded_lazy(&signature, &payload, &signed) {
					return Err("bad signature in extrinsic")
				}
				CheckedExtrinsic {
					signed: Some(signed),
					index: payload.0,
					function: payload.1,
				}
			}
			None => CheckedExtrinsic {
				signed: None,
				index: self.index,
				function: self.function,
			},
		})
	}
}

impl<Address, Index, Call, Signature> Decode
	for UncheckedExtrinsic<Address, Index, Call, Signature>
where
	Address: Decode,
	Signature: Decode,
	Index: Decode,
	Call: Decode,
{
	fn decode<I: Input>(input: &mut I) -> Option<Self> {
		// This is a little more complicated than usual since the binary format must be compatible
		// with substrate's generic `Vec<u8>` type. Basically this just means accepting that there
		// will be a prefix of u32, which has the total number of bytes following (we don't need
		// to use this).
		let _length_do_not_remove_me_see_above: u32 = Decode::decode(input)?;

		Some(UncheckedExtrinsic {
			signature: Decode::decode(input)?,
			index: Decode::decode(input)?,
			function: Decode::decode(input)?,
		})
	}
}

impl<Address, Index, Call, Signature> Encode
	for UncheckedExtrinsic<Address, Index, Call, Signature>
where
	Address: Encode,
	Signature: Encode,
	Index: Encode,
	Call: Encode,
{
	fn encode(&self) -> Vec<u8> {
		let mut v = Vec::new();

		// need to prefix with the total length as u32 to ensure it's binary comptible with
		// Vec<u8>. we'll make room for it here, then overwrite once we know the length.
		v.extend(&[0u8; 4]);

		self.signature.encode_to(&mut v);
		self.index.encode_to(&mut v);
		self.function.encode_to(&mut v);

		let length = (v.len() - 4) as u32;
		length.using_encoded(|s| v[0..4].copy_from_slice(s));

		v
	}
}

/// TODO: use derive when possible.
#[cfg(feature = "std")]
impl<Address, Index, Call, Signature> fmt::Debug for UncheckedExtrinsic<Address, Index, Call, Signature> where
	Address: fmt::Debug,
	Index: fmt::Debug,
	Call: fmt::Debug,
{
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "UncheckedExtrinsic({:?}, {:?}, {:?})", self.signature.as_ref().map(|x| &x.0), self.function, self.index)
	}
}
