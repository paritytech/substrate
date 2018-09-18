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
use traits::{self, Member, SimpleArithmetic, MaybeDisplay, GetBlockNumber, BlockNumberToHash, Lookup,
	Checkable};
use super::CheckedExtrinsic;

const TRANSACTION_VERSION: i8 = 1;

/// An era to describe the longevity of a transaction.
#[derive(PartialEq, Eq, Clone, Copy, Encode, Decode)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
pub struct Era(u16);

/*
E.g. with period == 4:
0         10        20        30        40
0123456789012345678901234567890123456789012
             |...|
   authored -/   \- expiry
phase = 1
n = Q(current - phase, period) + phase
*/
impl Era {
	/// Create a new era based on a period (which should be a power of two between 4 and 131072 inclusive)
	/// and a block number which on which it should start (or, for long periods, be shortly after the start).
	///
	/// Once created, check the 
	pub fn new(period: u64, current: u64) -> Self {
		let log_period_minus_two = period.checked_next_power_of_two()
			.unwrap_or(1 << 17)
			.trailing_zeros()
			.min(17)
			.max(2) - 2;
		let period = 4 << log_period_minus_two;
		let phase = current - current / period * period;
		let encoded_phase = (phase / (period >> 12).max(1)).min(1 << 12 - 1);

		Era(encoded_phase as u16 | (log_period_minus_two << 12) as u16)
	}

	/// The phase in the period that this transaction's lifetime begins (and, importantly,
	/// implies which block hash is included in the signature material). If the `period` is
	/// greater than 1 << 12, then it will be a factor of the times greater than 1<<12 that
	/// `period` is.
	pub fn phase(self) -> u64 {
		(self.0 as u64) % (1 << 12) * (self.period() >> 12).max(1)
	}

	/// The period of validity from the block hash found in the signing material.
	pub fn period(self) -> u64 {
		4 << (self.0 as u64 >> 12)
	}

	/// Get the block number of the start of the era whose properties this object
	/// describes that `current` belongs to. 
	pub fn birth(self, current: u64) -> u64 {
		let phase = self.phase();
		let period = self.period();
		(current - phase) / period * period + phase
	}

	/// Get the block number of the first block at which the era has ended.
	pub fn death(self, current: u64) -> u64 {
		self.birth(current) + self.period()
	}
}

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
		+ GetBlockNumber<BlockNumber=BlockNumber>
		+ BlockNumberToHash<BlockNumber=BlockNumber, Hash=Hash>,
{
	type Checked = CheckedExtrinsic<AccountId, Index, Call>;

	fn check(self, context: &Context) -> Result<Self::Checked, &'static str> {
		Ok(match self.signature {
			Some((signed, signature, index, era)) => {
				let h = context.block_number_to_hash(BlockNumber::sa(era.birth(context.get_block_number().as_())))
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

		let version: i8 = Decode::decode(input)?;

		if version != TRANSACTION_VERSION {
			return None
		}

		Some(UncheckedMortalExtrinsic {
			signature: Decode::decode(input)?,
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
		TRANSACTION_VERSION.encode_to(&mut v);
		self.signature.encode_to(&mut v);
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
