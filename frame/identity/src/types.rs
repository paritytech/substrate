// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use super::*;
use codec::{Decode, Encode, MaxEncodedLen};
use enumflags2::BitFlags;
use frame_support::{
	traits::{ConstU32, Get},
	BoundedVec, CloneNoBound, PartialEqNoBound, RuntimeDebugNoBound,
};
use sp_runtime::{traits::Zero, RuntimeDebug};
use sp_std::{fmt::Debug, iter::once, ops::Add, prelude::*};

/// Either underlying data blob if it is at most 32 bytes, or a hash of it. If the data is greater
/// than 32-bytes then it will be truncated when encoding.
///
/// Can also be `None`.
#[derive(Clone, Eq, PartialEq, RuntimeDebug, MaxEncodedLen)]
pub enum Data {
	/// No data here.
	None,
	/// The data is stored directly.
	Raw(BoundedVec<u8, ConstU32<32>>),
	/// Only the Blake2 hash of the data is stored. The preimage of the hash may be retrieved
	/// through some hash-lookup service.
	BlakeTwo256([u8; 32]),
	/// Only the SHA2-256 hash of the data is stored. The preimage of the hash may be retrieved
	/// through some hash-lookup service.
	Sha256([u8; 32]),
	/// Only the Keccak-256 hash of the data is stored. The preimage of the hash may be retrieved
	/// through some hash-lookup service.
	Keccak256([u8; 32]),
	/// Only the SHA3-256 hash of the data is stored. The preimage of the hash may be retrieved
	/// through some hash-lookup service.
	ShaThree256([u8; 32]),
}

impl Decode for Data {
	fn decode<I: codec::Input>(input: &mut I) -> sp_std::result::Result<Self, codec::Error> {
		let b = input.read_byte()?;
		Ok(match b {
			0 => Data::None,
			n @ 1..=33 => {
				let mut r: BoundedVec<_, _> = vec![0u8; n as usize - 1]
					.try_into()
					.expect("bound checked in match arm condition; qed");
				input.read(&mut r[..])?;
				Data::Raw(r)
			},
			34 => Data::BlakeTwo256(<[u8; 32]>::decode(input)?),
			35 => Data::Sha256(<[u8; 32]>::decode(input)?),
			36 => Data::Keccak256(<[u8; 32]>::decode(input)?),
			37 => Data::ShaThree256(<[u8; 32]>::decode(input)?),
			_ => return Err(codec::Error::from("invalid leading byte")),
		})
	}
}

impl Encode for Data {
	fn encode(&self) -> Vec<u8> {
		match self {
			Data::None => vec![0u8; 1],
			Data::Raw(ref x) => {
				let l = x.len().min(32);
				let mut r = vec![l as u8 + 1; l + 1];
				r[1..].copy_from_slice(&x[..l as usize]);
				r
			},
			Data::BlakeTwo256(ref h) => once(34u8).chain(h.iter().cloned()).collect(),
			Data::Sha256(ref h) => once(35u8).chain(h.iter().cloned()).collect(),
			Data::Keccak256(ref h) => once(36u8).chain(h.iter().cloned()).collect(),
			Data::ShaThree256(ref h) => once(37u8).chain(h.iter().cloned()).collect(),
		}
	}
}
impl codec::EncodeLike for Data {}

impl Default for Data {
	fn default() -> Self {
		Self::None
	}
}

/// An identifier for a single name registrar/identity verification service.
pub type RegistrarIndex = u32;

/// An attestation of a registrar over how accurate some `IdentityInfo` is in describing an account.
///
/// NOTE: Registrars may pay little attention to some fields. Registrars may want to make clear
/// which fields their attestation is relevant for by off-chain means.
#[derive(Copy, Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug, MaxEncodedLen)]
pub enum Judgement<Balance: Encode + Decode + MaxEncodedLen + Copy + Clone + Debug + Eq + PartialEq>
{
	/// The default value; no opinion is held.
	Unknown,
	/// No judgement is yet in place, but a deposit is reserved as payment for providing one.
	FeePaid(Balance),
	/// The data appears to be reasonably acceptable in terms of its accuracy, however no in depth
	/// checks (such as in-person meetings or formal KYC) have been conducted.
	Reasonable,
	/// The target is known directly by the registrar and the registrar can fully attest to the
	/// the data's accuracy.
	KnownGood,
	/// The data was once good but is currently out of date. There is no malicious intent in the
	/// inaccuracy. This judgement can be removed through updating the data.
	OutOfDate,
	/// The data is imprecise or of sufficiently low-quality to be problematic. It is not
	/// indicative of malicious intent. This judgement can be removed through updating the data.
	LowQuality,
	/// The data is erroneous. This may be indicative of malicious intent. This cannot be removed
	/// except by the registrar.
	Erroneous,
}

impl<Balance: Encode + Decode + MaxEncodedLen + Copy + Clone + Debug + Eq + PartialEq>
	Judgement<Balance>
{
	/// Returns `true` if this judgement is indicative of a deposit being currently held. This means
	/// it should not be cleared or replaced except by an operation which utilizes the deposit.
	pub(crate) fn has_deposit(&self) -> bool {
		match self {
			Judgement::FeePaid(_) => true,
			_ => false,
		}
	}

	/// Returns `true` if this judgement is one that should not be generally be replaced outside
	/// of specialized handlers. Examples include "malicious" judgements and deposit-holding
	/// judgements.
	pub(crate) fn is_sticky(&self) -> bool {
		match self {
			Judgement::FeePaid(_) | Judgement::Erroneous => true,
			_ => false,
		}
	}
}

/// The fields that we use to identify the owner of an account with. Each corresponds to a field
/// in the `IdentityInfo` struct.
#[repr(u64)]
#[derive(Encode, Decode, Clone, Copy, PartialEq, Eq, BitFlags, RuntimeDebug)]
pub enum IdentityField {
	Display = 0b0000000000000000000000000000000000000000000000000000000000000001,
	Legal = 0b0000000000000000000000000000000000000000000000000000000000000010,
	Web = 0b0000000000000000000000000000000000000000000000000000000000000100,
	Riot = 0b0000000000000000000000000000000000000000000000000000000000001000,
	Email = 0b0000000000000000000000000000000000000000000000000000000000010000,
	PgpFingerprint = 0b0000000000000000000000000000000000000000000000000000000000100000,
	Image = 0b0000000000000000000000000000000000000000000000000000000001000000,
	Twitter = 0b0000000000000000000000000000000000000000000000000000000010000000,
}

impl MaxEncodedLen for IdentityField {
	fn max_encoded_len() -> usize {
		u64::max_encoded_len()
	}
}

/// Wrapper type for `BitFlags<IdentityField>` that implements `Codec`.
#[derive(Clone, Copy, PartialEq, Default, RuntimeDebug)]
pub struct IdentityFields(pub(crate) BitFlags<IdentityField>);

impl MaxEncodedLen for IdentityFields {
	fn max_encoded_len() -> usize {
		IdentityField::max_encoded_len()
	}
}

impl Eq for IdentityFields {}
impl Encode for IdentityFields {
	fn using_encoded<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
		self.0.bits().using_encoded(f)
	}
}
impl Decode for IdentityFields {
	fn decode<I: codec::Input>(input: &mut I) -> sp_std::result::Result<Self, codec::Error> {
		let field = u64::decode(input)?;
		Ok(Self(<BitFlags<IdentityField>>::from_bits(field as u64).map_err(|_| "invalid value")?))
	}
}

/// Information concerning the identity of the controller of an account.
///
/// NOTE: This should be stored at the end of the storage item to facilitate the addition of extra
/// fields in a backwards compatible way through a specialized `Decode` impl.
#[derive(
	CloneNoBound, Encode, Decode, Eq, MaxEncodedLen, PartialEqNoBound, RuntimeDebugNoBound,
)]
#[codec(mel_bound(FieldLimit: Get<u32>))]
#[cfg_attr(test, derive(frame_support::DefaultNoBound))]
pub struct IdentityInfo<FieldLimit: Get<u32>> {
	/// Additional fields of the identity that are not catered for with the struct's explicit
	/// fields.
	pub additional: BoundedVec<(Data, Data), FieldLimit>,

	/// A reasonable display name for the controller of the account. This should be whatever it is
	/// that it is typically known as and should not be confusable with other entities, given
	/// reasonable context.
	///
	/// Stored as UTF-8.
	pub display: Data,

	/// The full legal name in the local jurisdiction of the entity. This might be a bit
	/// long-winded.
	///
	/// Stored as UTF-8.
	pub legal: Data,

	/// A representative website held by the controller of the account.
	///
	/// NOTE: `https://` is automatically prepended.
	///
	/// Stored as UTF-8.
	pub web: Data,

	/// The Riot/Matrix handle held by the controller of the account.
	///
	/// Stored as UTF-8.
	pub riot: Data,

	/// The email address of the controller of the account.
	///
	/// Stored as UTF-8.
	pub email: Data,

	/// The PGP/GPG public key of the controller of the account.
	pub pgp_fingerprint: Option<[u8; 20]>,

	/// A graphic image representing the controller of the account. Should be a company,
	/// organization or project logo or a headshot in the case of a human.
	pub image: Data,

	/// The Twitter identity. The leading `@` character may be elided.
	pub twitter: Data,
}

/// Information concerning the identity of the controller of an account.
///
/// NOTE: This is stored separately primarily to facilitate the addition of extra fields in a
/// backwards compatible way through a specialized `Decode` impl.
#[derive(CloneNoBound, Encode, Eq, MaxEncodedLen, PartialEqNoBound, RuntimeDebugNoBound)]
#[codec(mel_bound(
	Balance: Encode + Decode + MaxEncodedLen + Copy + Clone + Debug + Eq + PartialEq + Zero + Add,
	MaxJudgements: Get<u32>,
	MaxAdditionalFields: Get<u32>,
))]
pub struct Registration<
	Balance: Encode + Decode + MaxEncodedLen + Copy + Clone + Debug + Eq + PartialEq,
	MaxJudgements: Get<u32>,
	MaxAdditionalFields: Get<u32>,
> {
	/// Judgements from the registrars on this identity. Stored ordered by `RegistrarIndex`. There
	/// may be only a single judgement from each registrar.
	pub judgements: BoundedVec<(RegistrarIndex, Judgement<Balance>), MaxJudgements>,

	/// Amount held on deposit for this information.
	pub deposit: Balance,

	/// Information on the identity.
	pub info: IdentityInfo<MaxAdditionalFields>,
}

impl<
		Balance: Encode + Decode + MaxEncodedLen + Copy + Clone + Debug + Eq + PartialEq + Zero + Add,
		MaxJudgements: Get<u32>,
		MaxAdditionalFields: Get<u32>,
	> Registration<Balance, MaxJudgements, MaxAdditionalFields>
{
	pub(crate) fn total_deposit(&self) -> Balance {
		self.deposit +
			self.judgements
				.iter()
				.map(|(_, ref j)| if let Judgement::FeePaid(fee) = j { *fee } else { Zero::zero() })
				.fold(Zero::zero(), |a, i| a + i)
	}
}

impl<
		Balance: Encode + Decode + MaxEncodedLen + Copy + Clone + Debug + Eq + PartialEq,
		MaxJudgements: Get<u32>,
		MaxAdditionalFields: Get<u32>,
	> Decode for Registration<Balance, MaxJudgements, MaxAdditionalFields>
{
	fn decode<I: codec::Input>(input: &mut I) -> sp_std::result::Result<Self, codec::Error> {
		let (judgements, deposit, info) = Decode::decode(&mut AppendZerosInput::new(input))?;
		Ok(Self { judgements, deposit, info })
	}
}

/// Information concerning a registrar.
#[derive(Clone, Encode, Decode, Eq, PartialEq, RuntimeDebug, MaxEncodedLen)]
pub struct RegistrarInfo<
	Balance: Encode + Decode + Clone + Debug + Eq + PartialEq,
	AccountId: Encode + Decode + Clone + Debug + Eq + PartialEq,
> {
	/// The account of the registrar.
	pub account: AccountId,

	/// Amount required to be given to the registrar for them to provide judgement.
	pub fee: Balance,

	/// Relevant fields for this registrar. Registrar judgements are limited to attestations on
	/// these fields.
	pub fields: IdentityFields,
}
