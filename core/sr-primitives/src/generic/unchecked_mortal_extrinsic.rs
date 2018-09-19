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
use traits::{self, Member, SimpleArithmetic, MaybeDisplay, GetHeight, BlockNumberToHash, Lookup,
	Checkable};
use super::{CheckedExtrinsic, Era};

const TRANSACTION_VERSION: u8 = 1;

/// A extrinsic right from the external world. This is unchecked and so
/// can contain a signature.
#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
pub struct UncheckedMortalExtrinsic<Address, Index, Call, Signature> {
	/// The signature, address, number of extrinsics have come before from
	/// the same signer and an era describing the longevity of this transaction,
	/// if this is a signed extrinsic.
	pub signature: Option<(Address, Signature, Index, Era)>,
	/// The function that should be called.
	pub function: Call,
}

impl<Address, Index, Call, Signature> UncheckedMortalExtrinsic<Address, Index, Call, Signature> {
	/// New instance of a signed extrinsic aka "transaction".
	pub fn new_signed(index: Index, function: Call, signed: Address, signature: Signature, era: Era) -> Self {
		UncheckedMortalExtrinsic {
			signature: Some((signed, signature, index, era)),
			function,
		}
	}

	/// New instance of an unsigned extrinsic aka "inherent".
	pub fn new_unsigned(function: Call) -> Self {
		UncheckedMortalExtrinsic {
			signature: None,
			function,
		}
	}

	/// `true` if there is a signature.
	pub fn is_signed(&self) -> bool {
		self.signature.is_some()
	}
}

impl<Address, AccountId, Index, Call, Signature, Context, Hash, BlockNumber> Checkable<Context>
	for UncheckedMortalExtrinsic<Address, Index, Call, Signature>
where
	Address: Member + MaybeDisplay,
	Index: Encode + Member + MaybeDisplay + SimpleArithmetic,
	Call: Encode + Member,
	Signature: Member + traits::Verify<Signer=AccountId>,
	AccountId: Member + MaybeDisplay,
	BlockNumber: SimpleArithmetic,
	Hash: Encode,
	Context: Lookup<Source=Address, Target=AccountId>
		+ GetHeight<BlockNumber=BlockNumber>
		+ BlockNumberToHash<BlockNumber=BlockNumber, Hash=Hash>,
{
	type Checked = CheckedExtrinsic<AccountId, Index, Call>;

	fn check(self, context: &Context) -> Result<Self::Checked, &'static str> {
		Ok(match self.signature {
			Some((signed, signature, index, era)) => {
				let h = context.block_number_to_hash(BlockNumber::sa(era.birth(context.get_height().as_())))
					.ok_or("transaction birth block ancient")?;
				let payload = (index, self.function, h);
				let signed = context.lookup(signed)?;
				if !::verify_encoded_lazy(&signature, &payload, &signed) {
					return Err("bad signature in extrinsic")
				}
				CheckedExtrinsic {
					signed: Some((signed, payload.0)),
					function: payload.1,
				}
			}
			None => CheckedExtrinsic {
				signed: None,
				function: self.function,
			},
		})
	}
}

impl<Address, Index, Call, Signature> Decode
	for UncheckedMortalExtrinsic<Address, Index, Call, Signature>
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

		let version = input.read_byte()?;

		let is_signed = version & 0b1000_0000 != 0;
		let version = version & 0b0111_1111;
		if version != TRANSACTION_VERSION {
			return None
		}

		Some(UncheckedMortalExtrinsic {
			signature: if is_signed { Some(Decode::decode(input)?) } else { None },
			function: Decode::decode(input)?,
		})
	}
}

impl<Address, Index, Call, Signature> Encode
	for UncheckedMortalExtrinsic<Address, Index, Call, Signature>
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

		// 1 byte version id.
		match self.signature.as_ref() {
			Some(s) => {
				v.push(TRANSACTION_VERSION | 0b1000_0000);
				s.encode_to(&mut v);
			}
			None => {
				v.push(TRANSACTION_VERSION & 0b0111_1111);
			}
		}
		self.function.encode_to(&mut v);

		let length = (v.len() - 4) as u32;
		length.using_encoded(|s| v[0..4].copy_from_slice(s));

		v
	}
}

/// TODO: use derive when possible.
#[cfg(feature = "std")]
impl<Address, Index, Call, Signature> fmt::Debug for UncheckedMortalExtrinsic<Address, Index, Call, Signature> where
	Address: fmt::Debug,
	Index: fmt::Debug,
	Call: fmt::Debug,
{
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "UncheckedMortalExtrinsic({:?}, {:?})", self.signature.as_ref().map(|x| (&x.0, &x.2)), self.function)
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	struct TestContext;
	impl Lookup for TestContext {
		type Source = u64;
		type Target = u64;
		fn lookup(&self, s: u64) -> Result<u64, &'static str> { Ok(s) }
	}
	impl GetHeight for TestContext {
		type BlockNumber = u64;
		fn get_height(&self) -> u64 { 42 }
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

	const DUMMY_FUNCTION: u64 = 0;
	const DUMMY_ACCOUNTID: u64 = 0;
	
	type Ex = UncheckedMortalExtrinsic<u64, u64, u64, TestSig>;
	type CEx = CheckedExtrinsic<u64, u64, u64>;

	#[test]
	fn unsigned_codec_should_work() {
		let ux = Ex::new_unsigned(DUMMY_FUNCTION);
		let encoded = ux.encode();
		assert_eq!(Ex::decode(&mut &encoded[..]), Some(ux));
	}

	#[test]
	fn signed_codec_should_work() {
		let ux = Ex::new_signed(0, DUMMY_FUNCTION, DUMMY_ACCOUNTID, TestSig(DUMMY_ACCOUNTID, (DUMMY_ACCOUNTID, DUMMY_FUNCTION, 0u64).encode()), Era::immortal());
		let encoded = ux.encode();
		assert_eq!(Ex::decode(&mut &encoded[..]), Some(ux));
	}

	#[test]
	fn unsigned_check_should_work() {
		let ux = Ex::new_unsigned(DUMMY_FUNCTION);
		assert!(!ux.is_signed());
		assert!(<Ex as Checkable<TestContext>>::check(ux, &TestContext).is_ok());
	}

	#[test]
	fn badly_signed_check_should_fail() {
		let ux = Ex::new_signed(0, DUMMY_FUNCTION, DUMMY_ACCOUNTID, TestSig(DUMMY_ACCOUNTID, vec![0u8]), Era::immortal());
		assert!(ux.is_signed());
		assert_eq!(<Ex as Checkable<TestContext>>::check(ux, &TestContext), Err("bad signature in extrinsic"));
	}

	#[test]
	fn immortal_signed_check_should_work() {
		let ux = Ex::new_signed(0, DUMMY_FUNCTION, DUMMY_ACCOUNTID, TestSig(DUMMY_ACCOUNTID, (DUMMY_ACCOUNTID, DUMMY_FUNCTION, 0u64).encode()), Era::immortal());
		assert!(ux.is_signed());
		assert_eq!(<Ex as Checkable<TestContext>>::check(ux, &TestContext), Ok(CEx { signed: Some((DUMMY_ACCOUNTID, 0)), function: DUMMY_FUNCTION }));
	}

	#[test]
	fn mortal_signed_check_should_work() {
		let ux = Ex::new_signed(0, DUMMY_FUNCTION, DUMMY_ACCOUNTID, TestSig(DUMMY_ACCOUNTID, (DUMMY_ACCOUNTID, DUMMY_FUNCTION, 42u64).encode()), Era::mortal(32, 42));
		assert!(ux.is_signed());
		assert_eq!(<Ex as Checkable<TestContext>>::check(ux, &TestContext), Ok(CEx { signed: Some((DUMMY_ACCOUNTID, 0)), function: DUMMY_FUNCTION }));
	}

	#[test]
	fn later_mortal_signed_check_should_work() {
		let ux = Ex::new_signed(0, DUMMY_FUNCTION, DUMMY_ACCOUNTID, TestSig(DUMMY_ACCOUNTID, (DUMMY_ACCOUNTID, DUMMY_FUNCTION, 11u64).encode()), Era::mortal(32, 11));
		assert!(ux.is_signed());
		assert_eq!(<Ex as Checkable<TestContext>>::check(ux, &TestContext), Ok(CEx { signed: Some((DUMMY_ACCOUNTID, 0)), function: DUMMY_FUNCTION }));
	}

	#[test]
	fn too_late_mortal_signed_check_should_fail() {
		let ux = Ex::new_signed(0, DUMMY_FUNCTION, DUMMY_ACCOUNTID, TestSig(DUMMY_ACCOUNTID, (DUMMY_ACCOUNTID, DUMMY_FUNCTION, 10u64).encode()), Era::mortal(32, 10));
		assert!(ux.is_signed());
		assert_eq!(<Ex as Checkable<TestContext>>::check(ux, &TestContext), Err("bad signature in extrinsic"));
	}

	#[test]
	fn too_early_mortal_signed_check_should_fail() {
		let ux = Ex::new_signed(0, DUMMY_FUNCTION, DUMMY_ACCOUNTID, TestSig(DUMMY_ACCOUNTID, (DUMMY_ACCOUNTID, DUMMY_FUNCTION, 43u64).encode()), Era::mortal(32, 43));
		assert!(ux.is_signed());
		assert_eq!(<Ex as Checkable<TestContext>>::check(ux, &TestContext), Err("bad signature in extrinsic"));
	}
}