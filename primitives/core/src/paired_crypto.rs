// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! API for using a pair of crypto schemes together.

#[cfg(feature = "std")]
use crate::crypto::Ss58Codec;
use crate::crypto::{ByteArray, CryptoType, Derive, Public as TraitPublic, UncheckedFrom};
#[cfg(feature = "full_crypto")]
use crate::crypto::{DeriveError, DeriveJunction, Pair as TraitPair, SecretStringError};

#[cfg(feature = "full_crypto")]
use sp_std::vec::Vec;

use codec::{Decode, Encode, MaxEncodedLen};
use scale_info::TypeInfo;
#[cfg(feature = "std")]
use serde::{de, Deserialize, Deserializer, Serialize, Serializer};

use sp_runtime_interface::pass_by::PassByInner;
use sp_std::convert::TryFrom;

/// ECDSA and BLS-377 paired crypto scheme
#[cfg(feature = "bls-experimental")]
pub mod ecdsa_n_bls377 {
	use crate::crypto::CryptoTypeId;
	use crate::{bls377, ecdsa};

	/// An identifier used to match public keys against BLS12-377 keys
	pub const CRYPTO_ID: CryptoTypeId = CryptoTypeId(*b"ecb7");

	const PUBLIC_KEY_LEN: usize = 33 + crate::bls::PUBLIC_KEY_SERIALIZED_SIZE;
	const LEFT_SIGNATURE_LEN: usize = 65;
	const RIGHT_SIGNATURE_LEN: usize = crate::bls::SIGNATURE_SERIALIZED_SIZE;
	const SIGNATURE_LEN: usize = LEFT_SIGNATURE_LEN + RIGHT_SIGNATURE_LEN;

	/// (ECDSA, BLS12-377) key-pair pair.
	#[cfg(feature = "full_crypto")]
	pub type Pair = super::Pair<ecdsa::Pair, bls377::Pair, PUBLIC_KEY_LEN, SIGNATURE_LEN>;
	/// (ECDSA, BLS12-377) public key pair.
	pub type Public = super::Public<ecdsa::Public, bls377::Public, PUBLIC_KEY_LEN>;
	/// (ECDSA, BLS12-377) signature pair.
	pub type Signature = super::Signature<ecdsa::Signature, bls377::Signature, SIGNATURE_LEN>;

	impl super::SignaturePair for Signature {
		const LEFT_SIGNATURE_LEN: usize = LEFT_SIGNATURE_LEN;
		const RIGHT_SIGNATURE_LEN: usize = RIGHT_SIGNATURE_LEN;
		const LEFT_PLUS_RIGHT_LEN: usize = SIGNATURE_LEN;
	}

	#[cfg(feature = "full_crypto")]
	impl super::DoublePair for Pair {
		const PUBLIC_KEY_LEN: usize = PUBLIC_KEY_LEN;
		const SIGNATURE_LEN: usize = SIGNATURE_LEN;
	}

	impl super::CryptoType for Public {
		#[cfg(feature = "full_crypto")]
		type Pair = Pair;
	}

	impl super::CryptoType for Signature {
		#[cfg(feature = "full_crypto")]
		type Pair = Pair;
	}

	#[cfg(feature = "full_crypto")]
	impl super::CryptoType for Pair {
		type Pair = Pair;
	}
}

/// currently only supporting sub-schemes whose seed is a 32-bytes array.
#[cfg(feature = "full_crypto")]
const SECURE_SEED_LEN: usize = 32;

/// A secret seed.
///
/// It's not called a "secret key" because ring doesn't expose the secret keys
/// of the key pair (yeah, dumb); as such we're forced to remember the seed manually if we
/// will need it later (such as for HDKD).
#[cfg(feature = "full_crypto")]
type Seed = [u8; SECURE_SEED_LEN];

/// trait characterizing Public key which could be used as individual component of an `paired_crypto:Public` pair.
pub trait PublicKeyBound:
	TraitPublic
	+ Sized
	+ Derive
	+ sp_std::hash::Hash
	+ ByteArray
	+ for<'a> TryFrom<&'a [u8]>
	+ AsMut<[u8]>
	+ CryptoType
{
}

impl<
		PublicKeyTrait: TraitPublic
			+ Sized
			+ Derive
			+ sp_std::hash::Hash
			+ ByteArray
			+ for<'a> TryFrom<&'a [u8]>
			+ AsMut<[u8]>
			+ CryptoType,
	> PublicKeyBound for PublicKeyTrait
{
}

/// A public key.
#[derive(Clone, Encode, Decode, MaxEncodedLen, TypeInfo, PartialEq, Eq, PartialOrd, Ord)]
#[scale_info(skip_type_params(T))]
pub struct Public<
	LeftPublic: PublicKeyBound,
	RightPublic: PublicKeyBound,
	const LEFT_PLUS_RIGHT_LEN: usize,
> {
	left: LeftPublic,
	right: RightPublic,
	inner: [u8; LEFT_PLUS_RIGHT_LEN],
}

// We essentially could implement the following instead of storing left and right but we are going to end up copying and deserializing left and right, to perform any operation and that will take a hit on performance.
// impl<LeftPublic: PublicKeyBound, RightPublic: PublicKeyBound, const LEFT_PLUS_RIGHT_LEN: usize>  Public<LeftPublic, RightPublic, LEFT_PLUS_RIGHT_LEN> {
//     inline fn left<'a>(&self)-> &'a LeftPublic {
// 	&LeftPublic::try_from(&self.inner[0..LeftPublic::LEN]).unwrap()
//     }

//     fn right<'a>(&self)-> &'a RightPublic {
// 	&RightPublic::try_from(&self.inner[LeftPublic::LEN..LEFT_PLUS_RIGHT_LEN]).unwrap()
//     }

// }

#[cfg(feature = "full_crypto")]
impl<LeftPublic: PublicKeyBound, RightPublic: PublicKeyBound, const LEFT_PLUS_RIGHT_LEN: usize>
	sp_std::hash::Hash for Public<LeftPublic, RightPublic, LEFT_PLUS_RIGHT_LEN>
{
	fn hash<H: sp_std::hash::Hasher>(&self, state: &mut H) {
		self.left.hash(state);
		self.right.hash(state);
	}
}

impl<LeftPublic: PublicKeyBound, RightPublic: PublicKeyBound, const LEFT_PLUS_RIGHT_LEN: usize>
	ByteArray for Public<LeftPublic, RightPublic, LEFT_PLUS_RIGHT_LEN>
{
	const LEN: usize = LEFT_PLUS_RIGHT_LEN;
}

impl<LeftPublic: PublicKeyBound, RightPublic: PublicKeyBound, const LEFT_PLUS_RIGHT_LEN: usize>
	TryFrom<&[u8]> for Public<LeftPublic, RightPublic, LEFT_PLUS_RIGHT_LEN>
{
	type Error = ();

	fn try_from(data: &[u8]) -> Result<Self, Self::Error> {
		if data.len() != LEFT_PLUS_RIGHT_LEN {
			return Err(());
		}
		let left: LeftPublic = data[0..LeftPublic::LEN].try_into()?;
		let right: RightPublic = data[LeftPublic::LEN..LEFT_PLUS_RIGHT_LEN].try_into()?;

		let mut inner = [0u8; LEFT_PLUS_RIGHT_LEN];
		inner.copy_from_slice(data);
		Ok(Public { left, right, inner })
	}
}

impl<LeftPublic: PublicKeyBound, RightPublic: PublicKeyBound, const LEFT_PLUS_RIGHT_LEN: usize>
	AsMut<[u8]> for Public<LeftPublic, RightPublic, LEFT_PLUS_RIGHT_LEN>
{
	fn as_mut(&mut self) -> &mut [u8] {
		&mut self.inner[..]
	}
}

impl<LeftPublic: PublicKeyBound, RightPublic: PublicKeyBound, const LEFT_PLUS_RIGHT_LEN: usize>
	AsRef<[u8; LEFT_PLUS_RIGHT_LEN]> for Public<LeftPublic, RightPublic, LEFT_PLUS_RIGHT_LEN>
{
	fn as_ref(&self) -> &[u8; LEFT_PLUS_RIGHT_LEN] {
		&self.inner
	}
}

impl<LeftPublic: PublicKeyBound, RightPublic: PublicKeyBound, const LEFT_PLUS_RIGHT_LEN: usize>
	AsRef<[u8]> for Public<LeftPublic, RightPublic, LEFT_PLUS_RIGHT_LEN>
{
	fn as_ref(&self) -> &[u8] {
		&self.inner[..]
	}
}

impl<LeftPublic: PublicKeyBound, RightPublic: PublicKeyBound, const LEFT_PLUS_RIGHT_LEN: usize>
	PassByInner for Public<LeftPublic, RightPublic, LEFT_PLUS_RIGHT_LEN>
{
	type Inner = [u8; LEFT_PLUS_RIGHT_LEN];

	fn into_inner(self) -> Self::Inner {
		self.inner
	}

	fn inner(&self) -> &Self::Inner {
		&self.inner
	}

	fn from_inner(inner: Self::Inner) -> Self {
		let left: LeftPublic = inner[0..LeftPublic::LEN].try_into().unwrap();
		let right: RightPublic = inner[LeftPublic::LEN..LEFT_PLUS_RIGHT_LEN].try_into().unwrap();

		Self { left, right, inner }
	}
}

#[cfg(feature = "full_crypto")]
impl<
		LeftPair: TraitPair,
		RightPair: TraitPair,
		LeftPublic: PublicKeyBound,
		RightPublic: PublicKeyBound,
		const LEFT_PLUS_RIGHT_PUBLIC_LEN: usize,
		const SIGNATURE_LEN: usize,
	> From<Pair<LeftPair, RightPair, LEFT_PLUS_RIGHT_PUBLIC_LEN, SIGNATURE_LEN>>
	for Public<LeftPublic, RightPublic, LEFT_PLUS_RIGHT_PUBLIC_LEN>
where
	Pair<LeftPair, RightPair, LEFT_PLUS_RIGHT_PUBLIC_LEN, SIGNATURE_LEN>:
		TraitPair<Public = Public<LeftPublic, RightPublic, LEFT_PLUS_RIGHT_PUBLIC_LEN>>,
{
	fn from(x: Pair<LeftPair, RightPair, LEFT_PLUS_RIGHT_PUBLIC_LEN, SIGNATURE_LEN>) -> Self {
		x.public()
	}
}

impl<LeftPublic: PublicKeyBound, RightPublic: PublicKeyBound, const LEFT_PLUS_RIGHT_LEN: usize>
	UncheckedFrom<[u8; LEFT_PLUS_RIGHT_LEN]> for Public<LeftPublic, RightPublic, LEFT_PLUS_RIGHT_LEN>
{
	fn unchecked_from(data: [u8; LEFT_PLUS_RIGHT_LEN]) -> Self {
		let left: LeftPublic = data[0..LeftPublic::LEN].try_into().unwrap();
		let right: RightPublic = data[LeftPublic::LEN..LEFT_PLUS_RIGHT_LEN].try_into().unwrap();

		Public { left, right, inner: data }
	}
}

#[cfg(feature = "std")]
impl<LeftPublic: PublicKeyBound, RightPublic: PublicKeyBound, const LEFT_PLUS_RIGHT_LEN: usize>
	std::str::FromStr for Public<LeftPublic, RightPublic, LEFT_PLUS_RIGHT_LEN>
where
	Public<LeftPublic, RightPublic, LEFT_PLUS_RIGHT_LEN>: CryptoType,
{
	type Err = crate::crypto::PublicError;

	fn from_str(s: &str) -> Result<Self, Self::Err> {
		<Self as Ss58Codec>::from_ss58check(s)
	}
}

#[cfg(feature = "std")]
impl<LeftPublic: PublicKeyBound, RightPublic: PublicKeyBound, const LEFT_PLUS_RIGHT_LEN: usize>
	std::fmt::Display for Public<LeftPublic, RightPublic, LEFT_PLUS_RIGHT_LEN>
where
	Public<LeftPublic, RightPublic, LEFT_PLUS_RIGHT_LEN>: CryptoType,
{
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		write!(f, "{}", self.to_ss58check())
	}
}

#[cfg(feature = "std")]
impl<LeftPublic: PublicKeyBound, RightPublic: PublicKeyBound, const LEFT_PLUS_RIGHT_LEN: usize>
	sp_std::fmt::Debug for Public<LeftPublic, RightPublic, LEFT_PLUS_RIGHT_LEN>
where
	Public<LeftPublic, RightPublic, LEFT_PLUS_RIGHT_LEN>: CryptoType,
	[u8; LEFT_PLUS_RIGHT_LEN]: crate::hexdisplay::AsBytesRef,
{
	fn fmt(&self, f: &mut sp_std::fmt::Formatter) -> sp_std::fmt::Result {
		let s = self.to_ss58check();
		write!(f, "{} ({}...)", crate::hexdisplay::HexDisplay::from(&self.inner), &s[0..8])
	}
}

#[cfg(not(feature = "std"))]
impl<LeftPublic: PublicKeyBound, RightPublic: PublicKeyBound, const LEFT_PLUS_RIGHT_LEN: usize>
	sp_std::fmt::Debug for Public<LeftPublic, RightPublic, LEFT_PLUS_RIGHT_LEN>
{
	fn fmt(&self, _: &mut sp_std::fmt::Formatter) -> sp_std::fmt::Result {
		Ok(())
	}
}

#[cfg(feature = "std")]
impl<LeftPublic: PublicKeyBound, RightPublic: PublicKeyBound, const LEFT_PLUS_RIGHT_LEN: usize>
	Serialize for Public<LeftPublic, RightPublic, LEFT_PLUS_RIGHT_LEN>
where
	Public<LeftPublic, RightPublic, LEFT_PLUS_RIGHT_LEN>: CryptoType,
{
	fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
	where
		S: Serializer,
	{
		serializer.serialize_str(&self.to_ss58check())
	}
}

#[cfg(feature = "std")]
impl<
		'de,
		LeftPublic: PublicKeyBound,
		RightPublic: PublicKeyBound,
		const LEFT_PLUS_RIGHT_LEN: usize,
	> Deserialize<'de> for Public<LeftPublic, RightPublic, LEFT_PLUS_RIGHT_LEN>
where
	Public<LeftPublic, RightPublic, LEFT_PLUS_RIGHT_LEN>: CryptoType,
{
	fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
	where
		D: Deserializer<'de>,
	{
		Public::from_ss58check(&String::deserialize(deserializer)?)
			.map_err(|e| de::Error::custom(format!("{:?}", e)))
	}
}

impl<LeftPublic: PublicKeyBound, RightPublic: PublicKeyBound, const LEFT_PLUS_RIGHT_LEN: usize>
	TraitPublic for Public<LeftPublic, RightPublic, LEFT_PLUS_RIGHT_LEN>
where
	Public<LeftPublic, RightPublic, LEFT_PLUS_RIGHT_LEN>: CryptoType,
{
}

impl<LeftPublic: PublicKeyBound, RightPublic: PublicKeyBound, const LEFT_PLUS_RIGHT_LEN: usize>
	Derive for Public<LeftPublic, RightPublic, LEFT_PLUS_RIGHT_LEN>
{
}

#[cfg(not(feature = "full_crypto"))]
impl<
		LeftPublic: PublicKeyBound,
		RightPublic: PublicKeyBound,
		const LEFT_PLUS_RIGHT_PUBLIC_LEN: usize,
	> CryptoType for Public<LeftPublic, RightPublic, LEFT_PLUS_RIGHT_PUBLIC_LEN>
{
}

/// trait characterizing a signature which could be used as individual component of an `paired_crypto:Signature` pair.
pub trait SignatureBound: sp_std::hash::Hash + for<'a> TryFrom<&'a [u8]> + AsRef<[u8]> {}

impl<SignatureTrait: sp_std::hash::Hash + for<'a> TryFrom<&'a [u8]> + AsRef<[u8]>> SignatureBound
	for SignatureTrait
{
}

/// A pair of signatures of different types
#[derive(Encode, Decode, MaxEncodedLen, TypeInfo, PartialEq, Eq)]
#[scale_info(skip_type_params(T))]
pub struct Signature<
	LeftSignature: SignatureBound,
	RightSignature: SignatureBound,
	const LEFT_PLUS_RIGHT_LEN: usize,
> {
	left: LeftSignature,
	right: RightSignature,
	inner: [u8; LEFT_PLUS_RIGHT_LEN],
}

trait SignaturePair {
	const LEFT_SIGNATURE_LEN: usize;
	const RIGHT_SIGNATURE_LEN: usize;
	const LEFT_PLUS_RIGHT_LEN: usize;
}

#[cfg(feature = "full_crypto")]
impl<
		LeftSignature: SignatureBound,
		RightSignature: SignatureBound,
		const LEFT_PLUS_RIGHT_LEN: usize,
	> sp_std::hash::Hash for Signature<LeftSignature, RightSignature, LEFT_PLUS_RIGHT_LEN>
{
	fn hash<H: sp_std::hash::Hasher>(&self, state: &mut H) {
		self.left.hash(state);
		self.right.hash(state);
	}
}

impl<
		LeftSignature: SignatureBound,
		RightSignature: SignatureBound,
		const LEFT_PLUS_RIGHT_LEN: usize,
	> TryFrom<&[u8]> for Signature<LeftSignature, RightSignature, LEFT_PLUS_RIGHT_LEN>
where
	Signature<LeftSignature, RightSignature, LEFT_PLUS_RIGHT_LEN>: SignaturePair,
{
	type Error = ();

	fn try_from(data: &[u8]) -> Result<Self, Self::Error> {
		if data.len() != LEFT_PLUS_RIGHT_LEN {
			return Err(());
		}
		let Ok(left) : Result<LeftSignature, _> = data[0..Self::LEFT_SIGNATURE_LEN].try_into() else { panic!("invalid signature") };
		let Ok(right) : Result<RightSignature, _>= data[Self::LEFT_SIGNATURE_LEN..LEFT_PLUS_RIGHT_LEN].try_into() else { panic!("invalid signature") };

		let mut inner = [0u8; LEFT_PLUS_RIGHT_LEN];
		inner[..Self::LEFT_SIGNATURE_LEN].copy_from_slice(left.as_ref());
		inner[Self::LEFT_SIGNATURE_LEN..].copy_from_slice(right.as_ref());

		Ok(Signature { left, right, inner })
	}
}

impl<
		LeftSignature: SignatureBound,
		RightSignature: SignatureBound,
		const LEFT_PLUS_RIGHT_LEN: usize,
	> AsMut<[u8]> for Signature<LeftSignature, RightSignature, LEFT_PLUS_RIGHT_LEN>
{
	fn as_mut(&mut self) -> &mut [u8] {
		&mut self.inner[..]
	}
}

impl<
		LeftSignature: SignatureBound,
		RightSignature: SignatureBound,
		const LEFT_PLUS_RIGHT_LEN: usize,
	> AsRef<[u8; LEFT_PLUS_RIGHT_LEN]>
	for Signature<LeftSignature, RightSignature, LEFT_PLUS_RIGHT_LEN>
{
	fn as_ref(&self) -> &[u8; LEFT_PLUS_RIGHT_LEN] {
		&self.inner
	}
}

impl<
		LeftSignature: SignatureBound,
		RightSignature: SignatureBound,
		const LEFT_PLUS_RIGHT_LEN: usize,
	> AsRef<[u8]> for Signature<LeftSignature, RightSignature, LEFT_PLUS_RIGHT_LEN>
{
	fn as_ref(&self) -> &[u8] {
		&self.inner[..]
	}
}
#[cfg(feature = "std")]
impl<
		LeftSignature: SignatureBound,
		RightSignature: SignatureBound,
		const LEFT_PLUS_RIGHT_LEN: usize,
	> Serialize for Signature<LeftSignature, RightSignature, LEFT_PLUS_RIGHT_LEN>
{
	fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
	where
		S: Serializer,
	{
		serializer.serialize_str(&array_bytes::bytes2hex("", self))
	}
}

#[cfg(feature = "serde")]
impl<
		'de,
		LeftSignature: SignatureBound,
		RightSignature: SignatureBound,
		const LEFT_PLUS_RIGHT_LEN: usize,
	> Deserialize<'de> for Signature<LeftSignature, RightSignature, LEFT_PLUS_RIGHT_LEN>
where
	Signature<LeftSignature, RightSignature, LEFT_PLUS_RIGHT_LEN>: SignaturePair,
{
	fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
	where
		D: Deserializer<'de>,
	{
		let signature_hex = array_bytes::hex2bytes(&String::deserialize(deserializer)?)
			.map_err(|e| de::Error::custom(format!("{:?}", e)))?;
		Signature::<LeftSignature, RightSignature, LEFT_PLUS_RIGHT_LEN>::try_from(
			signature_hex.as_ref(),
		)
		.map_err(|e| {
			de::Error::custom(format!(
				"Error in converting deserialized data into signature: {:?}",
				e
			))
		})
	}
}

impl<
		LeftSignature: SignatureBound,
		RightSignature: SignatureBound,
		const LEFT_PLUS_RIGHT_LEN: usize,
	> From<Signature<LeftSignature, RightSignature, LEFT_PLUS_RIGHT_LEN>>
	for [u8; LEFT_PLUS_RIGHT_LEN]
{
	fn from(
		signature: Signature<LeftSignature, RightSignature, LEFT_PLUS_RIGHT_LEN>,
	) -> [u8; LEFT_PLUS_RIGHT_LEN] {
		signature.inner
	}
}

impl<
		LeftSignature: SignatureBound,
		RightSignature: SignatureBound,
		const LEFT_PLUS_RIGHT_LEN: usize,
	> sp_std::fmt::Debug for Signature<LeftSignature, RightSignature, LEFT_PLUS_RIGHT_LEN>
where
	[u8; LEFT_PLUS_RIGHT_LEN]: crate::hexdisplay::AsBytesRef,
{
	#[cfg(feature = "std")]
	fn fmt(&self, f: &mut sp_std::fmt::Formatter) -> sp_std::fmt::Result {
		write!(f, "{}", crate::hexdisplay::HexDisplay::from(&self.inner))
	}

	#[cfg(not(feature = "std"))]
	fn fmt(&self, _: &mut sp_std::fmt::Formatter) -> sp_std::fmt::Result {
		Ok(())
	}
}

impl<
		LeftSignature: SignatureBound,
		RightSignature: SignatureBound,
		const LEFT_PLUS_RIGHT_LEN: usize,
	> UncheckedFrom<[u8; LEFT_PLUS_RIGHT_LEN]>
	for Signature<LeftSignature, RightSignature, LEFT_PLUS_RIGHT_LEN>
where
	Signature<LeftSignature, RightSignature, LEFT_PLUS_RIGHT_LEN>: SignaturePair,
{
	fn unchecked_from(data: [u8; LEFT_PLUS_RIGHT_LEN]) -> Self {
		let Ok(left) = data[0..Self::LEFT_SIGNATURE_LEN].try_into() else { panic!("invalid signature") };
		let Ok(right) = data[Self::LEFT_SIGNATURE_LEN..LEFT_PLUS_RIGHT_LEN].try_into() else { panic!("invalid signature") };

		Signature { left, right, inner: data }
	}
}

/// A key pair.
#[cfg(feature = "full_crypto")]
#[derive(Clone)]
pub struct Pair<
	LeftPair: TraitPair,
	RightPair: TraitPair,
	const PUBLIC_KEY_LEN: usize,
	const SIGNATURE_LEN: usize,
> {
	left: LeftPair,
	right: RightPair,
}

trait DoublePair {
	const PUBLIC_KEY_LEN: usize;
	const SIGNATURE_LEN: usize;
}

#[cfg(feature = "full_crypto")]
impl<
		LeftPair: TraitPair,
		RightPair: TraitPair,
		const PUBLIC_KEY_LEN: usize,
		const SIGNATURE_LEN: usize,
	> Pair<LeftPair, RightPair, PUBLIC_KEY_LEN, SIGNATURE_LEN>
{
}

#[cfg(feature = "full_crypto")]
impl<
		LeftPair: TraitPair,
		RightPair: TraitPair,
		const PUBLIC_KEY_LEN: usize,
		const SIGNATURE_LEN: usize,
	> TraitPair for Pair<LeftPair, RightPair, PUBLIC_KEY_LEN, SIGNATURE_LEN>
where
	Pair<LeftPair, RightPair, PUBLIC_KEY_LEN, SIGNATURE_LEN>: DoublePair + CryptoType,
	LeftPair::Signature: SignatureBound,
	RightPair::Signature: SignatureBound,
	Public<LeftPair::Public, RightPair::Public, PUBLIC_KEY_LEN>: CryptoType,
	Signature<LeftPair::Signature, RightPair::Signature, SIGNATURE_LEN>: SignaturePair,
	LeftPair::Seed: From<[u8; SECURE_SEED_LEN]> + Into<[u8; SECURE_SEED_LEN]>,
	RightPair::Seed: From<[u8; SECURE_SEED_LEN]> + Into<[u8; SECURE_SEED_LEN]>,
{
	type Seed = Seed;
	type Public = Public<LeftPair::Public, RightPair::Public, PUBLIC_KEY_LEN>;
	type Signature = Signature<LeftPair::Signature, RightPair::Signature, SIGNATURE_LEN>;

	fn from_seed_slice(seed_slice: &[u8]) -> Result<Self, SecretStringError> {
		if seed_slice.len() != SECURE_SEED_LEN {
			return Err(SecretStringError::InvalidSeedLength);
		}
		let left = LeftPair::from_seed_slice(&seed_slice)?;
		let right = RightPair::from_seed_slice(&seed_slice)?;
		Ok(Pair { left, right })
	}

	fn derive<Iter: Iterator<Item = DeriveJunction>>(
		&self,
		path: Iter,
		seed: Option<Self::Seed>,
	) -> Result<(Self, Option<Self::Seed>), DeriveError> {
		let (left_seed_option, right_seed_option) = match seed {
			Some(seed) => {
				let (left_seed, right_seed): (LeftPair::Seed, RightPair::Seed) =
					(seed.clone().into(), seed.into());
				(Some(left_seed), Some(right_seed))
			},
			None => (None, None),
		};

		let left_path: Vec<_> = path.map(|p| p.clone()).collect();
		let right_path = left_path.clone();
		let derived_left = self.left.derive(left_path.into_iter(), left_seed_option)?;
		let derived_right = self.right.derive(right_path.into_iter(), right_seed_option)?;

		let optional_seed: Option<[u8; SECURE_SEED_LEN]> = match (derived_left.1, derived_right.1) {
			(Some(seed_left), Some(seed_right)) => {
				if seed_left.as_ref() == seed_right.as_ref() {
					Some(seed_left.into())
				} else {
					None
				}
			},
			_ => None,
		};
		Ok((Self { left: derived_left.0, right: derived_right.0 }, optional_seed))
	}

	fn public(&self) -> Self::Public {
		let mut raw = [0u8; PUBLIC_KEY_LEN];
		let left_pub = self.left.public();
		let right_pub = self.right.public();
		raw[..LeftPair::Public::LEN].copy_from_slice(left_pub.as_ref());
		raw[LeftPair::Public::LEN..].copy_from_slice(right_pub.as_ref());
		Self::Public::unchecked_from(raw)
	}

	fn sign(&self, message: &[u8]) -> Self::Signature {
		let mut r: [u8; SIGNATURE_LEN] = [0u8; SIGNATURE_LEN];
		r[..Self::Signature::LEFT_SIGNATURE_LEN].copy_from_slice(self.left.sign(message).as_ref());
		r[Self::Signature::LEFT_SIGNATURE_LEN..].copy_from_slice(self.right.sign(message).as_ref());
		Self::Signature::unchecked_from(r)
	}

	fn verify<M: AsRef<[u8]>>(sig: &Self::Signature, message: M, pubkey: &Self::Public) -> bool {
		let mut vec_message = vec![0u8; message.as_ref().len()];
		vec_message.clone_from_slice(message.as_ref());

		LeftPair::verify(&sig.left, message, &pubkey.left)
			&& RightPair::verify(&sig.right, vec_message, &pubkey.right)
	}

	/// Get the seed/secret key for each key and then concatenate them.
	fn to_raw_vec(&self) -> Vec<u8> {
		[self.left.to_raw_vec(), self.right.to_raw_vec()].concat()
	}
}

// Test set exercising the (ECDSA, BLS12-377) implementation
#[cfg(test)]
mod test {
	use super::*;
	use crate::crypto::DEV_PHRASE;
	use ecdsa_n_bls377::{Pair, Signature};
	use hex_literal::hex;

	#[test]
	fn default_phrase_should_be_used() {
		assert_eq!(
			Pair::from_string("//Alice///password", None).unwrap().public(),
			Pair::from_string(&format!("{}//Alice", DEV_PHRASE), Some("password"))
				.unwrap()
				.public(),
		);
	}

	#[test]
	fn seed_and_derive_should_work() {
		let seed_for_right_and_left =
			hex!("9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60");
		let pair = Pair::from_seed(&seed_for_right_and_left);
		// we are using hash to field so this is not going to work
		// assert_eq!(pair.seed(), seed);
		let path = vec![DeriveJunction::Hard([0u8; 32])];
		let derived = pair.derive(path.into_iter(), None).ok().unwrap().0;
		assert_eq!(
			derived.to_raw_vec(),
			[
				hex!("b8eefc4937200a8382d00050e050ced2d4ab72cc2ef1b061477afb51564fdd61"),
				hex!("3a0626d095148813cd1642d38254f1cfff7eb8cc1a2fc83b2a135377c3554c12")
			]
			.concat()
		);
	}

	#[test]
	fn test_vector_should_work() {
		let seed_left_and_right =
			hex!("9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60");
		let pair = Pair::from_seed(&([seed_left_and_right].concat()[..].try_into().unwrap()));
		let public = pair.public();
		assert_eq!(
			public,
			Public::unchecked_from(
				hex!("028db55b05db86c0b1786ca49f095d76344c9e6056b2f02701a7e7f3c20aabfd917a84ca8ce4c37c93c95ecee6a3c0c9a7b9c225093cf2f12dc4f69cbfb847ef9424a18f5755d5a742247d386ff2aabb806bcf160eff31293ea9616976628f77266c8a8cc1d8753be04197bd6cdd8c5c87a148f782c4c1568d599b48833fd539001e580cff64bbc71850605433fcd051f3afc3b74819786f815ffb5272030a8d03e5df61e6183f8fd8ea85f26defa83400"
 ),
    		),
    	);
		let message = b"";
		let signature = hex!("3dde91174bd9359027be59a428b8146513df80a2a3c7eda2194f64de04a69ab97b753169e94db6ffd50921a2668a48b94ca11e3d32c1ff19cfe88890aa7e8f3c00d1e3013161991e142d8751017d4996209c2ff8a9ee160f373733eda3b4b785ba6edce9f45f87104bbe07aa6aa6eb2780aa705efb2c13d3b317d6409d159d23bdc7cdd5c2a832d1551cf49d811d49c901495e527dbd532e3a462335ce2686009104aba7bc11c5b22be78f3198d2727a0b");
		let signature = Signature::unchecked_from(signature);
		assert!(pair.sign(&message[..]) == signature);
		assert!(Pair::verify(&signature, &message[..], &public));
	}

	#[test]
	fn test_vector_by_string_should_work() {
		let pair = Pair::from_string(
			"0x9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60",
			None,
		)
		.unwrap();
		let public = pair.public();
		assert_eq!(
			public,
			Public::unchecked_from(
				hex!("028db55b05db86c0b1786ca49f095d76344c9e6056b2f02701a7e7f3c20aabfd916dc6be608fab3c6bd894a606be86db346cc170db85c733853a371f3db54ae1b12052c0888d472760c81b537572a26f00db865e5963aef8634f9917571c51b538b564b2a9ceda938c8b930969ee3b832448e08e33a79e9ddd28af419a3ce45300f5dbc768b067781f44f3fe05a19e6b07b1c4196151ec3f8ea37e4f89a8963030d2101e931276bb9ebe1f20102239d780"
 ),
    		),
    	);
		let message = b"";
		let signature = hex!("3dde91174bd9359027be59a428b8146513df80a2a3c7eda2194f64de04a69ab97b753169e94db6ffd50921a2668a48b94ca11e3d32c1ff19cfe88890aa7e8f3c00bbb395bbdee1a35930912034f5fde3b36df2835a0536c865501b0675776a1d5931a3bea2e66eff73b2546c6af2061a8019223e4ebbbed661b2538e0f5823f2c708eb89c406beca8fcb53a5c13dbc7c0c42e4cf2be2942bba96ea29297915a06bd2b1b979c0e2ac8fd4ec684a6b5d110c");
		let signature = Signature::unchecked_from(signature);
		assert!(pair.sign(&message[..]) == signature);
		assert!(Pair::verify(&signature, &message[..], &public));
	}

	#[test]
	fn generated_pair_should_work() {
		let (pair, _) = Pair::generate();
		let public = pair.public();
		let message = b"Something important";
		let signature = pair.sign(&message[..]);
		assert!(Pair::verify(&signature, &message[..], &public));
		assert!(!Pair::verify(&signature, b"Something else", &public));
	}

	#[test]
	fn seeded_pair_should_work() {
		let pair =
			Pair::from_seed(&(b"12345678901234567890123456789012".as_slice().try_into().unwrap()));
		let public = pair.public();
		assert_eq!(
    		public,
			Public::unchecked_from(
				hex!("035676109c54b9a16d271abeb4954316a40a32bcce023ac14c8e26e958aa68fba9754d2f2bbfa67df54d7e0e951979a18a1e0f45948857752cc2bac6bbb0b1d05e8e48bcc453920bf0c4bbd5993212480112a1fb433f04d74af0a8b700d93dc957ab3207f8d071e948f5aca1a7632c00bdf6d06be05b43e2e6216dccc8a5d55a0071cb2313cfd60b7e9114619cd17c06843b352f0b607a99122f6651df8f02e1ad3697bd208e62af047ddd7b942ba80080")
 ),
    	);
		let message =
    	hex!("2f8c6129d816cf51c374bc7f08c3e63ed156cf78aefb4a6550d97b87997977ee00000000000000000200d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a4500000000000000"
    );
		let signature = pair.sign(&message[..]);
		println!("Correct signature: {:?}", signature);
		assert!(Pair::verify(&signature, &message[..], &public));
		assert!(!Pair::verify(&signature, "Other message", &public));
	}

	#[test]
	fn generate_with_phrase_recovery_possible() {
		let (pair1, phrase, _) = Pair::generate_with_phrase(None);
		let (pair2, _) = Pair::from_phrase(&phrase, None).unwrap();

		assert_eq!(pair1.public(), pair2.public());
	}

	#[test]
	fn generate_with_password_phrase_recovery_possible() {
		let (pair1, phrase, _) = Pair::generate_with_phrase(Some("password"));
		let (pair2, _) = Pair::from_phrase(&phrase, Some("password")).unwrap();

		assert_eq!(pair1.public(), pair2.public());
	}

	#[test]
	fn password_does_something() {
		let (pair1, phrase, _) = Pair::generate_with_phrase(Some("password"));
		let (pair2, _) = Pair::from_phrase(&phrase, None).unwrap();

		assert_ne!(pair1.public(), pair2.public());
	}

	#[test]
	fn ss58check_roundtrip_works() {
		let pair =
			Pair::from_seed(&(b"12345678901234567890123456789012".as_slice().try_into().unwrap()));
		let public = pair.public();
		let s = public.to_ss58check();
		println!("Correct: {}", s);
		let cmp = Public::from_ss58check(&s).unwrap();
		assert_eq!(cmp, public);
	}

	#[test]
	fn signature_serialization_works() {
		let pair =
			Pair::from_seed(&(b"12345678901234567890123456789012".as_slice().try_into().unwrap()));
		let message = b"Something important";
		let signature = pair.sign(&message[..]);

		let serialized_signature = serde_json::to_string(&signature).unwrap();
		println!("{:?} -- {:}", signature.inner, serialized_signature);
		// Signature is 177 bytes, hexify * 2, so 354  chars + 2 quote charsy
		assert_eq!(serialized_signature.len(), 356);
		let signature = serde_json::from_str(&serialized_signature).unwrap();
		assert!(Pair::verify(&signature, &message[..], &pair.public()));
	}

	#[test]
	fn signature_serialization_doesnt_panic() {
		fn deserialize_signature(text: &str) -> Result<Signature, serde_json::error::Error> {
			serde_json::from_str(text)
		}
		assert!(deserialize_signature("Not valid json.").is_err());
		assert!(deserialize_signature("\"Not an actual signature.\"").is_err());
		// Poorly-sized
		assert!(deserialize_signature("\"abc123\"").is_err());
	}
}
