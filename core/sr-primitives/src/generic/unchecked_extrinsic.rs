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
use runtime_io::blake2_256;
use crate::codec::{Decode, Encode, Codec, Input, Compact};
use crate::traits::{
	self, Member, SimpleArithmetic, MaybeDebug, MaybeDisplay, CurrentHeight, SignedExtension,
	BlockNumberToHash, Lookup, Checkable, Extrinsic, SaturatedConversion, DispatchError
};
use super::{CheckedExtrinsic, Era};

const TRANSACTION_VERSION: u8 = 1;
/*
/// A type with which the signed payload of a transaction may be extended.
pub trait OSignedExtension: Codec + MaybeDebug {}

impl<T: Codec + fmt::Debug> SignedExtra for T {}

/// A type that names a `SignedExtension` and knows how to deal with it.
pub trait OExtension<AccountId, Call> {
	/// An extra data field that should go into the signed part of the payload.
	type SignedPayload: OSignedExtension;

	/// Anything that should be executed immediately before dispatch.
	fn pre_dispatch(
		a: &AccountId,
		c: &Call,
		e: Self::SignedPayload
	) -> Result<(), DispatchError>;
}

impl<AccountId, Call> OExtension<AccountId, Call> for () {
	type SignedPayload = ();

	fn pre_dispatch(
		_: &AccountId,
		_: &Call,
		_: ()
	) -> Result<(), DispatchError> { Ok(()) }
}
*/
/// A extrinsic right from the external world. This is unchecked and so
/// can contain a signature.
#[derive(PartialEq, Eq, Clone)]
pub struct UncheckedExtrinsic<Address, Index, Call, Signature, Extra>
where
	Extra: SignedExtension
{
	/// The signature, address, number of extrinsics have come before from
	/// the same signer and an era describing the longevity of this transaction,
	/// if this is a signed extrinsic.
	pub signature: Option<(Address, Signature, Compact<Index>, Era, Extra)>,
	/// The function that should be called.
	pub function: Call,
}

impl<Address, Index, Call, Signature, Extra: SignedExtension>
	UncheckedExtrinsic<Address, Index, Call, Signature, Extra>
{
	/// New instance of a signed extrinsic aka "transaction".
	pub fn new_signed(
		index: Index,
		function: Call,
		signed: Address,
		signature: Signature,
		era: Era,
		extra: Extra
	) -> Self {
		UncheckedExtrinsic {
			signature: Some((signed, signature, index.into(), era, extra)),
			function,
		}
	}

	/// New instance of an unsigned extrinsic aka "inherent".
	pub fn new_unsigned(function: Call) -> Self {
		UncheckedExtrinsic {
			signature: None,
			function,
		}
	}
}

impl<Address, Index, Call, Signature, Extra: SignedExtension> Extrinsic
	for UncheckedExtrinsic<Address, Index, Call, Signature, Extra>
{
	fn is_signed(&self) -> Option<bool> {
		Some(self.signature.is_some())
	}
}

impl<Address, AccountId, Index, Call, Signature, Extra, Context, Hash, BlockNumber>
	Checkable<Context>
for
	UncheckedExtrinsic<Address, Index, Call, Signature, Extra>
where
	Address: Member + MaybeDisplay,
	Index: Member + MaybeDisplay + SimpleArithmetic,
	Compact<Index>: Encode,
	Call: Encode + Member,
	Signature: Member + traits::Verify<Signer=AccountId>,
	Extra: SignedExtension<AccountId=AccountId, Index=Index, Call=Call>,
	AccountId: Member + MaybeDisplay,
	BlockNumber: SimpleArithmetic,
	Hash: Encode,
	Context: Lookup<Source=Address, Target=AccountId>
		+ CurrentHeight<BlockNumber=BlockNumber>
		+ BlockNumberToHash<BlockNumber=BlockNumber, Hash=Hash>,
{
	type Checked = CheckedExtrinsic<AccountId, Index, Call, Extra>;

	fn check(self, context: &Context) -> Result<Self::Checked, &'static str> {
		Ok(match self.signature {
			Some((signed, signature, index, era, extra)) => {
				let current_u64 = context.current_height().saturated_into::<u64>();
				let h = context.block_number_to_hash(era.birth(current_u64).saturated_into())
					.ok_or("transaction birth block ancient")?;
				let signed = context.lookup(signed)?;
				let raw_payload = (index, self.function, era, h, extra);
				if !raw_payload.using_encoded(|payload| {
					if payload.len() > 256 {
						signature.verify(&blake2_256(payload)[..], &signed)
					} else {
						signature.verify(payload, &signed)
					}
				}) {
					return Err(crate::BAD_SIGNATURE)
				}
				CheckedExtrinsic {
					signed: Some((signed, (raw_payload.0).0, raw_payload.4)),
					function: raw_payload.1,
				}
			}
			None => CheckedExtrinsic {
				signed: None,
				function: self.function,
			},
		})
	}
}

impl<Address, Index, Call, Signature, Extra> Decode
	for UncheckedExtrinsic<Address, Index, Call, Signature, Extra>
where
	Address: Decode,
	Signature: Decode,
	Compact<Index>: Decode,
	Call: Decode,
	Extra: SignedExtension,
{
	fn decode<I: Input>(input: &mut I) -> Option<Self> {
		// This is a little more complicated than usual since the binary format must be compatible
		// with substrate's generic `Vec<u8>` type. Basically this just means accepting that there
		// will be a prefix of vector length (we don't need
		// to use this).
		let _length_do_not_remove_me_see_above: Vec<()> = Decode::decode(input)?;

		let version = input.read_byte()?;

		let is_signed = version & 0b1000_0000 != 0;
		let version = version & 0b0111_1111;
		if version != TRANSACTION_VERSION {
			return None
		}

		Some(UncheckedExtrinsic {
			signature: if is_signed { Some(Decode::decode(input)?) } else { None },
			function: Decode::decode(input)?,
		})
	}
}

impl<Address, Index, Call, Signature, Extra> Encode
	for UncheckedExtrinsic<Address, Index, Call, Signature, Extra>
where
	Address: Encode,
	Signature: Encode,
	Compact<Index>: Encode,
	Call: Encode,
	Extra: SignedExtension,
{
	fn encode(&self) -> Vec<u8> {
		super::encode_with_vec_prefix::<Self, _>(|v| {
			// 1 byte version id.
			match self.signature.as_ref() {
				Some(s) => {
					v.push(TRANSACTION_VERSION | 0b1000_0000);
					s.encode_to(v);
				}
				None => {
					v.push(TRANSACTION_VERSION & 0b0111_1111);
				}
			}
			self.function.encode_to(v);
		})
	}
}

#[cfg(feature = "std")]
impl<Address: Encode, Index, Signature: Encode, Call: Encode, Extra: SignedExtension> serde::Serialize
	for UncheckedExtrinsic<Address, Index, Call, Signature, Extra>
	where Compact<Index>: Encode
{
	fn serialize<S>(&self, seq: S) -> Result<S::Ok, S::Error> where S: ::serde::Serializer {
		self.using_encoded(|bytes| seq.serialize_bytes(bytes))
	}
}

#[cfg(feature = "std")]
impl<Address, Index, Call, Signature, Extra> fmt::Debug
	for UncheckedExtrinsic<Address, Index, Call, Signature, Extra>
where
	Address: fmt::Debug,
	Index: fmt::Debug,
	Call: fmt::Debug,
	Extra: SignedExtension,
{
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "UncheckedExtrinsic({:?}, {:?})", self.signature.as_ref().map(|x| (&x.0, &x.2, &x.4)), self.function)
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use runtime_io::blake2_256;
	use crate::codec::{Encode, Decode};
	use crate::traits::{SignedExtension, DispatchError};
	use serde::{Serialize, Deserialize};

	struct TestContext;
	impl Lookup for TestContext {
		type Source = u64;
		type Target = u64;
		fn lookup(&self, s: u64) -> Result<u64, &'static str> { Ok(s) }
	}
	impl CurrentHeight for TestContext {
		type BlockNumber = u64;
		fn current_height(&self) -> u64 { 42 }
	}
	impl BlockNumberToHash for TestContext {
		type BlockNumber = u64;
		type Hash = u64;
		fn block_number_to_hash(&self, n: u64) -> Option<u64> { Some(n) }
	}

	#[derive(Eq, PartialEq, Clone, Debug, Serialize, Deserialize, Encode, Decode)]
	struct TestSig(u64, Vec<u8>);
	impl traits::Verify for TestSig {
		type Signer = u64;
		fn verify<L: traits::Lazy<[u8]>>(&self, mut msg: L, signer: &Self::Signer) -> bool {
			*signer == self.0 && msg.get() == &self.1[..]
		}
	}

	const DUMMY_ACCOUNTID: u64 = 0;

	#[derive(Debug, Encode, Decode, Clone, Eq, PartialEq, Ord, PartialOrd)]
	struct TestExtra;
	impl SignedExtension for TestExtra {
		type AccountId = u64;
		type Index = u64;
		type Call = Vec<u8>;
		fn pre_dispatch(
			self,
			_a: &Self::AccountId,
			_i: &Self::Index,
			_c: &Self::Call,
			_w: crate::weights::Weight,
		) -> Result<(), DispatchError> {
			Ok(())
		}
	}
	type Ex = UncheckedExtrinsic<u64, u64, Vec<u8>, TestSig, TestExtra>;
	type CEx = CheckedExtrinsic<u64, u64, Vec<u8>, TestExtra>;

	#[test]
	fn unsigned_codec_should_work() {
		let ux = Ex::new_unsigned(vec![0u8;0]);
		let encoded = ux.encode();
		assert_eq!(Ex::decode(&mut &encoded[..]), Some(ux));
	}

	#[test]
	fn signed_codec_should_work() {
		let ux = Ex::new_signed(0, vec![0u8;0], DUMMY_ACCOUNTID, TestSig(DUMMY_ACCOUNTID, (DUMMY_ACCOUNTID, vec![0u8;0], Era::immortal(), 0u64).encode()), Era::immortal(), TestExtra);
		let encoded = ux.encode();
		assert_eq!(Ex::decode(&mut &encoded[..]), Some(ux));
	}

	#[test]
	fn large_signed_codec_should_work() {
		let ux = Ex::new_signed(0, vec![0u8;0], DUMMY_ACCOUNTID, TestSig(DUMMY_ACCOUNTID, (DUMMY_ACCOUNTID, vec![0u8; 257], Era::immortal(), 0u64).using_encoded(blake2_256)[..].to_owned()), Era::immortal(), TestExtra);
		let encoded = ux.encode();
		assert_eq!(Ex::decode(&mut &encoded[..]), Some(ux));
	}

	#[test]
	fn unsigned_check_should_work() {
		let ux = Ex::new_unsigned(vec![0u8;0]);
		assert!(!ux.is_signed().unwrap_or(false));
		assert!(<Ex as Checkable<TestContext>>::check(ux, &TestContext).is_ok());
	}

	#[test]
	fn badly_signed_check_should_fail() {
		let ux = Ex::new_signed(0, vec![0u8;0], DUMMY_ACCOUNTID, TestSig(DUMMY_ACCOUNTID, vec![0u8]), Era::immortal(), TestExtra);
		assert!(ux.is_signed().unwrap_or(false));
		assert_eq!(<Ex as Checkable<TestContext>>::check(ux, &TestContext), Err(crate::BAD_SIGNATURE));
	}

	#[test]
	fn immortal_signed_check_should_work() {
		let ux = Ex::new_signed(0, vec![0u8;0], DUMMY_ACCOUNTID, TestSig(DUMMY_ACCOUNTID, (Compact::from(DUMMY_ACCOUNTID), vec![0u8;0], Era::immortal(), 0u64).encode()), Era::immortal(), TestExtra);
		assert!(ux.is_signed().unwrap_or(false));
		assert_eq!(<Ex as Checkable<TestContext>>::check(ux, &TestContext), Ok(CEx { signed: Some((DUMMY_ACCOUNTID, 0, TestExtra)), function: vec![0u8;0] }));
	}

	#[test]
	fn mortal_signed_check_should_work() {
		let ux = Ex::new_signed(0, vec![0u8;0], DUMMY_ACCOUNTID, TestSig(DUMMY_ACCOUNTID, (Compact::from(DUMMY_ACCOUNTID), vec![0u8;0], Era::mortal(32, 42), 42u64).encode()), Era::mortal(32, 42), TestExtra);
		assert!(ux.is_signed().unwrap_or(false));
		assert_eq!(<Ex as Checkable<TestContext>>::check(ux, &TestContext), Ok(CEx { signed: Some((DUMMY_ACCOUNTID, 0, TestExtra)), function: vec![0u8;0] }));
	}

	#[test]
	fn later_mortal_signed_check_should_work() {
		let ux = Ex::new_signed(0, vec![0u8;0], DUMMY_ACCOUNTID, TestSig(DUMMY_ACCOUNTID, (Compact::from(DUMMY_ACCOUNTID), vec![0u8;0], Era::mortal(32, 11), 11u64).encode()), Era::mortal(32, 11), TestExtra);
		assert!(ux.is_signed().unwrap_or(false));
		assert_eq!(<Ex as Checkable<TestContext>>::check(ux, &TestContext), Ok(CEx { signed: Some((DUMMY_ACCOUNTID, 0, TestExtra)), function: vec![0u8;0] }));
	}

	#[test]
	fn too_late_mortal_signed_check_should_fail() {
		let ux = Ex::new_signed(0, vec![0u8;0], DUMMY_ACCOUNTID, TestSig(DUMMY_ACCOUNTID, (DUMMY_ACCOUNTID, vec![0u8;0], Era::mortal(32, 10), 10u64).encode()), Era::mortal(32, 10), TestExtra);
		assert!(ux.is_signed().unwrap_or(false));
		assert_eq!(<Ex as Checkable<TestContext>>::check(ux, &TestContext), Err(crate::BAD_SIGNATURE));
	}

	#[test]
	fn too_early_mortal_signed_check_should_fail() {
		let ux = Ex::new_signed(0, vec![0u8;0], DUMMY_ACCOUNTID, TestSig(DUMMY_ACCOUNTID, (DUMMY_ACCOUNTID, vec![0u8;0], Era::mortal(32, 43), 43u64).encode()), Era::mortal(32, 43), TestExtra);
		assert!(ux.is_signed().unwrap_or(false));
		assert_eq!(<Ex as Checkable<TestContext>>::check(ux, &TestContext), Err(crate::BAD_SIGNATURE));
	}

	#[test]
	fn encoding_matches_vec() {
		let ex = Ex::new_unsigned(vec![0u8;0]);
		let encoded = ex.encode();
		let decoded = Ex::decode(&mut encoded.as_slice()).unwrap();
		assert_eq!(decoded, ex);
		let as_vec: Vec<u8> = Decode::decode(&mut encoded.as_slice()).unwrap();
		assert_eq!(as_vec.encode(), encoded);
	}
}
