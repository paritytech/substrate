// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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
use crate::codec::{Decode, Encode, Codec, Input, HasCompact};
use crate::traits::{self, Member, SimpleArithmetic, MaybeDisplay, Lookup, Extrinsic};
use super::{CheckedExtrinsic, Tip, Tippable};

#[derive(PartialEq, Eq, Clone, Encode, Decode)]
pub struct SignatureContent<Address, Index, Signature>
where
	Address: Codec,
	Index: HasCompact + Codec,
	Signature: Codec,
{
	signed: Address,
	signature: Signature,
	index: Index,
}

/// A extrinsic right from the external world. This is unchecked and so
/// can contain a signature.
#[derive(PartialEq, Eq, Clone)]
pub struct UncheckedExtrinsic<Address, Index, Call, Signature, Balance>
where
	Address: Codec,
	Index: HasCompact + Codec,
	Signature: Codec,
{
	/// The signature, address and number of extrinsics have come before from
	/// the same signer, if this is a signed extrinsic.
	pub signature: Option<SignatureContent<Address, Index, Signature>>,
	/// The function that should be called.
	pub function: Call,
	/// The tip for this transaction
	pub tip: Tip<Balance>,
}

impl<Address, Index, Signature, Call, Balance> UncheckedExtrinsic<Address, Index, Call, Signature, Balance>
where
	Address: Codec,
	Index: HasCompact + Codec,
	Signature: Codec,
	// Balance: Codec,
{
	/// New instance of a signed extrinsic aka "transaction".
	pub fn new_signed(index: Index,
		function: Call,
		signed: Address,
		signature: Signature,
		tip: Tip<Balance>)
	-> Self {
		UncheckedExtrinsic {
			signature: Some(SignatureContent{signed, signature, index}),
			function,
			tip,
		}
	}

	/// New instance of an unsigned extrinsic aka "inherent".
	pub fn new_unsigned(function: Call, tip: Tip<Balance>) -> Self {
		UncheckedExtrinsic {
			signature: None,
			function,
			tip,
		}
	}
}

impl<Address, Index, Signature, Call, AccountId, Context, Balance> traits::Checkable<Context>
	for UncheckedExtrinsic<Address, Index, Call, Signature, Balance>
where
	Address: Member + MaybeDisplay + Codec,
	Index: Member + MaybeDisplay + SimpleArithmetic + Codec,
	Call: Encode + Member,
	Signature: Member + traits::Verify<Signer=AccountId> + Codec,
	AccountId: Member + MaybeDisplay,
	Context: Lookup<Source=Address, Target=AccountId>,
	// Balance: Codec,
{
	type Checked = CheckedExtrinsic<AccountId, Index, Call, Balance>;

	fn check(self, context: &Context) -> Result<Self::Checked, &'static str> {
		Ok(match self.signature {
			Some(SignatureContent{signed, signature, index}) => {
				let payload = (index, self.function);
				let signed = context.lookup(signed)?;
				if !crate::verify_encoded_lazy(&signature, &payload, &signed) {
					return Err(crate::BAD_SIGNATURE)
				}
				CheckedExtrinsic {
					signed: Some((signed, payload.0)),
					function: payload.1,
					tip: self.tip,
				}
			}
			None => CheckedExtrinsic {
				signed: None,
				function: self.function,
				tip: self.tip,
			},
		})
	}
}

// TODO: remove not needed encode/decode bounds for balance
impl<Address, Index, Signature, Call, Balance> Tippable<Balance>
	for UncheckedExtrinsic<Address, Index, Call, Signature, Balance>
where
	Index: HasCompact + Codec,
	Signature: Codec,
	Address: Codec,
	Balance: Clone,
{
	fn tip(&self) -> Tip<Balance> {
		self.tip.clone()
	}
}

impl<
	Address: Codec,
	Index: HasCompact + Codec,
	Signature: Codec,
	Call,
	Balance,
> Extrinsic for UncheckedExtrinsic<Address, Index, Call, Signature, Balance> {
	fn is_signed(&self) -> Option<bool> {
		Some(self.signature.is_some())
	}
}

impl<Address: Codec, Index: HasCompact + Codec, Signature: Codec, Call: Decode, Balance: Codec> Decode
	for UncheckedExtrinsic<Address, Index, Call, Signature, Balance>
{
	fn decode<I: Input>(input: &mut I) -> Option<Self> {
		// This is a little more complicated than usual since the binary format must be compatible
		// with substrate's generic `Vec<u8>` type. Basically this just means accepting that there
		// will be a prefix of vector length (we don't need
		// to use this).
		let _length_do_not_remove_me_see_above: Vec<()> = Decode::decode(input)?;

		Some(UncheckedExtrinsic {
			signature: Decode::decode(input)?,
			function: Decode::decode(input)?,
			tip: Decode::decode(input).unwrap_or_default(),
		})
	}
}

impl<Address: Codec, Index: HasCompact + Codec, Signature: Codec, Call: Encode, Balance: Codec> Encode
	for UncheckedExtrinsic<Address, Index, Call, Signature, Balance>
{
	fn encode(&self) -> Vec<u8> {
		super::encode_with_vec_prefix::<Self, _>(|v| {
			self.signature.encode_to(v);
			self.function.encode_to(v);
			self.tip.encode_to(v);
		})
	}
}

#[cfg(feature = "std")]
impl<Address: Codec, Index: HasCompact + Codec, Signature: Codec, Call: Encode, Balance: Codec> serde::Serialize
	for UncheckedExtrinsic<Address, Index, Call, Signature, Balance>
{
	fn serialize<S>(&self, seq: S) -> Result<S::Ok, S::Error> where S: ::serde::Serializer {
		self.using_encoded(|bytes| ::substrate_primitives::bytes::serialize(bytes, seq))
	}
}

#[cfg(feature = "std")]
impl<Address, Index, Signature, Call, Balance> fmt::Debug
	for UncheckedExtrinsic<Address, Index, Call, Signature, Balance>
where
	Address: fmt::Debug + Codec,
	Index: fmt::Debug + HasCompact + Codec,
	Signature: Codec,
	Call: fmt::Debug,
	Balance: fmt::Debug,
{
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(
			f,
			"UncheckedExtrinsic({:?}, {:?}, {:?})",
			self.signature.as_ref().map(|x| (&x.signed, &x.index)),
			self.function,
			self.tip,
		)
	}
}

#[cfg(test)]
mod test {
	use crate::codec::{Decode, Encode};
	use super::{UncheckedExtrinsic, Tip};
	type Extrinsic = UncheckedExtrinsic<u32, u32, u32, u32, u32>;


	#[test]
	fn encoding_matches_vec() {
		let ex = Extrinsic::new_unsigned(42, Tip::Sender(10_u32));
		let encoded = ex.encode();
		let decoded = Extrinsic::decode(&mut encoded.as_slice()).unwrap();
		assert_eq!(decoded, ex);
		let as_vec: Vec<u8> = Decode::decode(&mut encoded.as_slice()).unwrap();
		assert_eq!(as_vec.encode(), encoded);
	}

	#[test]
	fn unprovided_tip_will_not_fail() {
		// without tip
		//                       len sig f(u32).....
		let bytes: Vec<u8> = vec![24, 0, 42, 0, 0, 0];
		let decoded: Extrinsic = Decode::decode(&mut bytes.as_slice()).unwrap();
		assert_eq!(decoded, Extrinsic::new_unsigned(42, Tip::default()));
		// with tip
		let bytes: Vec<u8> = vec![40, 0, 42, 0, 0, 0, 1, 10, 0, 0, 0];
		let decoded: Extrinsic = Decode::decode(&mut bytes.as_slice()).unwrap();
		assert_eq!(decoded, Extrinsic::new_unsigned(42, Tip::Sender(10)));

	}

	#[test]
	#[cfg(feature = "std")]
	fn serialization_of_unchecked_extrinsics() {
		type Extrinsic = UncheckedExtrinsic<u32, u32, u32, u32, u32>;
		let ex = Extrinsic::new_unsigned(42, Tip::None);
		assert_eq!(serde_json::to_string(&ex).unwrap(), "\"0x18002a00000000\"");
	}
}
