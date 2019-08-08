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
use crate::codec::{Decode, Encode, Input, Error};
use crate::traits::{self, Member, MaybeDisplay, SignedExtension, Checkable, Extrinsic};
use super::CheckedExtrinsic;

const TRANSACTION_VERSION: u8 = 3;

/// A extrinsic right from the external world. This is unchecked and so
/// can contain a signature.
#[derive(PartialEq, Eq, Clone)]
pub struct UncheckedExtrinsic<Address, Call, Signature, Extra>
where
	Extra: SignedExtension
{
	/// The signature, address, number of extrinsics have come before from
	/// the same signer and an era describing the longevity of this transaction,
	/// if this is a signed extrinsic.
	pub signature: Option<(Address, Signature, Extra)>,
	/// The function that should be called.
	pub function: Call,
}

impl<Address, Call, Signature, Extra: SignedExtension>
	UncheckedExtrinsic<Address, Call, Signature, Extra>
{
	/// New instance of a signed extrinsic aka "transaction".
	pub fn new_signed(
		function: Call,
		signed: Address,
		signature: Signature,
		extra: Extra
	) -> Self {
		UncheckedExtrinsic {
			signature: Some((signed, signature, extra)),
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

impl<Address, Call, Signature, Extra: SignedExtension> Extrinsic
	for UncheckedExtrinsic<Address, Call, Signature, Extra>
{
	type Call = Call;

	fn is_signed(&self) -> Option<bool> {
		Some(self.signature.is_some())
	}

	fn new_unsigned(function: Call) -> Option<Self> {
		Some(UncheckedExtrinsic::new_unsigned(function))
	}
}

impl<Address, AccountId, Call, Signature, Extra, Lookup>
	Checkable<Lookup>
for
	UncheckedExtrinsic<Address, Call, Signature, Extra>
where
	Address: Member + MaybeDisplay,
	Call: Encode + Member,
	Signature: Member + traits::Verify<Signer=AccountId>,
	Extra: SignedExtension<AccountId=AccountId>,
	AccountId: Member + MaybeDisplay,
	Lookup: traits::Lookup<Source=Address, Target=AccountId>
{
	type Checked = CheckedExtrinsic<AccountId, Call, Extra>;

	fn check(self, lookup: &Lookup) -> Result<Self::Checked, &'static str> {
		Ok(match self.signature {
			Some((signed, signature, extra)) => {
				let additional_signed = extra.additional_signed()?;
				let raw_payload = (self.function, extra, additional_signed);
				let signed = lookup.lookup(signed)?;
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
					signed: Some((signed, raw_payload.1)),
					function: raw_payload.0,
				}
			}
			None => CheckedExtrinsic {
				signed: None,
				function: self.function,
			},
		})
	}
}

impl<Address, Call, Signature, Extra> Decode
	for UncheckedExtrinsic<Address, Call, Signature, Extra>
where
	Address: Decode,
	Signature: Decode,
	Call: Decode,
	Extra: SignedExtension,
{
	fn decode<I: Input>(input: &mut I) -> Result<Self, Error> {
		// This is a little more complicated than usual since the binary format must be compatible
		// with substrate's generic `Vec<u8>` type. Basically this just means accepting that there
		// will be a prefix of vector length (we don't need
		// to use this).
		let _length_do_not_remove_me_see_above: Vec<()> = Decode::decode(input)?;

		let version = input.read_byte()?;

		let is_signed = version & 0b1000_0000 != 0;
		let version = version & 0b0111_1111;
		if version != TRANSACTION_VERSION {
			return Err("Invalid transaction version".into());
		}

		Ok(UncheckedExtrinsic {
			signature: if is_signed { Some(Decode::decode(input)?) } else { None },
			function: Decode::decode(input)?,
		})
	}
}

impl<Address, Call, Signature, Extra> Encode
	for UncheckedExtrinsic<Address, Call, Signature, Extra>
where
	Address: Encode,
	Signature: Encode,
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
impl<Address: Encode, Signature: Encode, Call: Encode, Extra: SignedExtension> serde::Serialize
	for UncheckedExtrinsic<Address, Call, Signature, Extra>
{
	fn serialize<S>(&self, seq: S) -> Result<S::Ok, S::Error> where S: ::serde::Serializer {
		self.using_encoded(|bytes| seq.serialize_bytes(bytes))
	}
}

#[cfg(feature = "std")]
impl<Address, Call, Signature, Extra> fmt::Debug
	for UncheckedExtrinsic<Address, Call, Signature, Extra>
where
	Address: fmt::Debug,
	Call: fmt::Debug,
	Extra: SignedExtension,
{
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "UncheckedExtrinsic({:?}, {:?})", self.signature.as_ref().map(|x| (&x.0, &x.2)), self.function)
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use runtime_io::blake2_256;
	use crate::codec::{Encode, Decode};
	use crate::traits::{SignedExtension, Lookup};
	use serde::{Serialize, Deserialize};

	struct TestContext;
	impl Lookup for TestContext {
		type Source = u64;
		type Target = u64;
		fn lookup(&self, s: u64) -> Result<u64, &'static str> { Ok(s) }
	}

	#[derive(Eq, PartialEq, Clone, Debug, Serialize, Deserialize, Encode, Decode)]
	struct TestSig(u64, Vec<u8>);
	impl traits::Verify for TestSig {
		type Signer = u64;
		fn verify<L: traits::Lazy<[u8]>>(&self, mut msg: L, signer: &Self::Signer) -> bool {
			*signer == self.0 && msg.get() == &self.1[..]
		}
	}

	type TestAccountId = u64;
	type TestCall = Vec<u8>;

	const TEST_ACCOUNT: TestAccountId = 0;

	// NOTE: this is demonstration. One can simply use `()` for testing.
	#[derive(Debug, Encode, Decode, Clone, Eq, PartialEq, Ord, PartialOrd)]
	struct TestExtra;
	impl SignedExtension for TestExtra {
		type AccountId = u64;
		type Call = ();
		type AdditionalSigned = ();
		type Pre = ();

		fn additional_signed(&self) -> rstd::result::Result<(), &'static str> { Ok(()) }
	}

	type Ex = UncheckedExtrinsic<TestAccountId, TestCall, TestSig, TestExtra>;
	type CEx = CheckedExtrinsic<TestAccountId, TestCall, TestExtra>;

	#[test]
	fn unsigned_codec_should_work() {
		let ux = Ex::new_unsigned(vec![0u8; 0]);
		let encoded = ux.encode();
		assert_eq!(Ex::decode(&mut &encoded[..]), Ok(ux));
	}

	#[test]
	fn signed_codec_should_work() {
		let ux = Ex::new_signed(
			vec![0u8; 0],
			TEST_ACCOUNT,
			TestSig(TEST_ACCOUNT, (vec![0u8; 0], TestExtra).encode()),
			TestExtra
		);
		let encoded = ux.encode();
		assert_eq!(Ex::decode(&mut &encoded[..]), Ok(ux));
	}

	#[test]
	fn large_signed_codec_should_work() {
		let ux = Ex::new_signed(
			vec![0u8; 0],
			TEST_ACCOUNT,
			TestSig(TEST_ACCOUNT, (vec![0u8; 257], TestExtra)
				.using_encoded(blake2_256)[..].to_owned()),
			TestExtra
		);
		let encoded = ux.encode();
		assert_eq!(Ex::decode(&mut &encoded[..]), Ok(ux));
	}

	#[test]
	fn unsigned_check_should_work() {
		let ux = Ex::new_unsigned(vec![0u8; 0]);
		assert!(!ux.is_signed().unwrap_or(false));
		assert!(<Ex as Checkable<TestContext>>::check(ux, &TestContext).is_ok());
	}

	#[test]
	fn badly_signed_check_should_fail() {
		let ux = Ex::new_signed(
			vec![0u8; 0],
			TEST_ACCOUNT,
			TestSig(TEST_ACCOUNT, vec![0u8; 0]),
			TestExtra
		);
		assert!(ux.is_signed().unwrap_or(false));
		assert_eq!(<Ex as Checkable<TestContext>>::check(ux, &TestContext), Err(crate::BAD_SIGNATURE));
	}

	#[test]
	fn signed_check_should_work() {
		let ux = Ex::new_signed(
			vec![0u8; 0],
			TEST_ACCOUNT,
			TestSig(TEST_ACCOUNT, (vec![0u8; 0], TestExtra).encode()),
			TestExtra
		);
		assert!(ux.is_signed().unwrap_or(false));
		assert_eq!(
			<Ex as Checkable<TestContext>>::check(ux, &TestContext),
			Ok(CEx { signed: Some((TEST_ACCOUNT, TestExtra)), function: vec![0u8; 0] })
		);
	}

	#[test]
	fn encoding_matches_vec() {
		let ex = Ex::new_unsigned(vec![0u8; 0]);
		let encoded = ex.encode();
		let decoded = Ex::decode(&mut encoded.as_slice()).unwrap();
		assert_eq!(decoded, ex);
		let as_vec: Vec<u8> = Decode::decode(&mut encoded.as_slice()).unwrap();
		assert_eq!(as_vec.encode(), encoded);
	}
}
