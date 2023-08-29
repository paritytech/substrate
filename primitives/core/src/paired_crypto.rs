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
// distributed under the Licenseff is distributed on an "AS IS" BASIS,
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
use sp_std::{convert::TryFrom, marker::PhantomData, ops::Deref};

/// ECDSA and BLS-377 specialized types
pub mod ecdsa_n_bls377 {
    use crate::crypto::{CryptoTypeId};
    use crate::{ecdsa, ed25519};
    
	/// An identifier used to match public keys against BLS12-377 keys
	pub const CRYPTO_ID: CryptoTypeId = CryptoTypeId(*b"ecb7");

	/// BLS12-377 key pair.
	#[cfg(feature = "full_crypto")]
	pub type Pair = super::Pair<ecdsa::Pair, ed25519::Pair>;
	/// BLS12-377 public key.
	pub type Public = super::Public<ecdsa::Public, ed25519::Public, 64>;
	// /// BLS12-377 signature.
	//pub type Signature = super::Signature<ecdsa:Signature, bls377:Signature>;

    // impl super::CryptoType for Public
    // {
    // 	#[cfg(feature = "full_crypto")]
    // 	type Pair = Pair;
    // }
	// impl super::HardJunctionId for TinyBLS377 {
	// 	const ID: &'static str = "BLS12377HDKD";
	// }

//     impl<T: BlsBound> CryptoType for Signature<T> {
// 	#[cfg(feature = "full_crypto")]
// 	type Pair = Pair<T>;
// }

}

/// A secret seed.
///
/// It's not called a "secret key" because ring doesn't expose the secret keys
/// of the key pair (yeah, dumb); as such we're forced to remember the seed manually if we
/// will need it later (such as for HDKD).
#[cfg(feature = "full_crypto")]
type Seed<const LEFT_PLUS_RIGHT_LEN: usize> = [u8; {LEFT_PLUS_RIGHT_LEN}];

//pub trait Public: ByteArray + Derive + CryptoType + PartialEq + Eq + Clone + Send + Sync {}
pub trait PublicKeyBound: TraitPublic + Sized + Derive + sp_std::hash::Hash + ByteArray + for<'a> TryFrom<&'a[u8]> + AsMut<[u8]> + CryptoType {}

impl<PublicKeyTrait:  TraitPublic + Sized + Derive + sp_std::hash::Hash + ByteArray + for<'a> TryFrom<&'a[u8]> + AsMut<[u8]> + CryptoType> PublicKeyBound for PublicKeyTrait {}

/// A public key.
#[derive(Clone, Encode, Decode, MaxEncodedLen, TypeInfo, PartialEq, Eq, PartialOrd, Ord)]
#[scale_info(skip_type_params(T))]
pub struct Public<LeftPublic: PublicKeyBound, RightPublic: PublicKeyBound, const LEFT_PLUS_RIGHT_LEN: usize,> {
    left: LeftPublic,
    right: RightPublic,
    inner: [u8; LEFT_PLUS_RIGHT_LEN],
}

// We essentially could implement this instead of storing left and right but we are going to end up copying left and right.
// impl<LeftPublic: PublicKeyBound, RightPublic: PublicKeyBound, const LEFT_PLUS_RIGHT_LEN: usize>  Public<LeftPublic, RightPublic, LEFT_PLUS_RIGHT_LEN> {
//     inline fn left<'a>(&self)-> &'a LeftPublic {
// 	&LeftPublic::try_from(&self.inner[0..LeftPublic::LEN]).unwrap()
//     }

//     fn right<'a>(&self)-> &'a RightPublic {
// 	&RightPublic::try_from(&self.inner[LeftPublic::LEN..LEFT_PLUS_RIGHT_LEN]).unwrap()
//     }

    
// }

#[cfg(feature = "full_crypto")]
impl<LeftPublic: PublicKeyBound, RightPublic: PublicKeyBound, const LEFT_PLUS_RIGHT_LEN: usize> sp_std::hash::Hash for Public<LeftPublic, RightPublic, LEFT_PLUS_RIGHT_LEN> {
    fn hash<H: sp_std::hash::Hasher>(&self, state: &mut H) {
 	    self.left.hash(state);
	    self.right.hash(state);
	}
}

impl<LeftPublic: PublicKeyBound, RightPublic: PublicKeyBound, const LEFT_PLUS_RIGHT_LEN: usize> ByteArray  for Public<LeftPublic, RightPublic, LEFT_PLUS_RIGHT_LEN>   {
     const LEN: usize = LEFT_PLUS_RIGHT_LEN;
}

impl<'a,LeftPublic: PublicKeyBound, RightPublic: PublicKeyBound, const LEFT_PLUS_RIGHT_LEN: usize>  TryFrom<&'a[u8]> for Public<LeftPublic, RightPublic, LEFT_PLUS_RIGHT_LEN> {
     type Error = ();

     fn try_from(data: &[u8]) -> Result<Self, Self::Error> {
  		if data.len() != 	LEFT_PLUS_RIGHT_LEN {
 			return Err(())
 		}
         	 let mut left : LeftPublic = data[0..LeftPublic::LEN].try_into().unwrap();
	 let mut right : RightPublic = data[LeftPublic::LEN..LEFT_PLUS_RIGHT_LEN].try_into().unwrap();

	 let mut inner = [0u8; LEFT_PLUS_RIGHT_LEN];
	 Ok(Public { left, right, inner })

     }
}
	
impl<LeftPublic: PublicKeyBound, RightPublic: PublicKeyBound, const LEFT_PLUS_RIGHT_LEN: usize> AsMut<[u8]> for Public<LeftPublic, RightPublic, LEFT_PLUS_RIGHT_LEN> {
    fn as_mut(&mut self) -> &mut [u8] {
	&mut self.inner[..]
    }
}

impl<LeftPublic: PublicKeyBound, RightPublic: PublicKeyBound, const LEFT_PLUS_RIGHT_LEN: usize> AsRef<[u8; LEFT_PLUS_RIGHT_LEN]> for Public<LeftPublic, RightPublic, LEFT_PLUS_RIGHT_LEN>  {
    fn as_ref(&self) -> &[u8; LEFT_PLUS_RIGHT_LEN] {
		&self.inner
    }
}

impl<LeftPublic: PublicKeyBound, RightPublic: PublicKeyBound, const LEFT_PLUS_RIGHT_LEN: usize,> AsRef<[u8]> for Public<LeftPublic, RightPublic, LEFT_PLUS_RIGHT_LEN> {
    fn as_ref(&self) -> &[u8] {
	&self.inner[..]
    }
}

impl<LeftPublic: PublicKeyBound, RightPublic: PublicKeyBound, const LEFT_PLUS_RIGHT_LEN: usize,> PassByInner for Public<LeftPublic, RightPublic, LEFT_PLUS_RIGHT_LEN> {
	type Inner = [u8; LEFT_PLUS_RIGHT_LEN];

	fn into_inner(self) -> Self::Inner {
		self.inner
	}

	fn inner(&self) -> &Self::Inner {
		&self.inner
	}

	fn from_inner(inner: Self::Inner) -> Self {
        let mut left : LeftPublic = inner[0..LeftPublic::LEN].try_into().unwrap();
	    let mut right : RightPublic = inner[LeftPublic::LEN..LEFT_PLUS_RIGHT_LEN].try_into().unwrap();

		Self { left, right, inner }
	}
}

#[cfg(feature = "full_crypto")]
impl<LeftPair: TraitPair, RightPair: TraitPair, LeftPublic: PublicKeyBound, RightPublic: PublicKeyBound, const LEFT_PLUS_RIGHT_PUBLIC_LEN: usize,> From<Pair<LeftPair, RightPair>> for Public<LeftPublic, RightPublic, LEFT_PLUS_RIGHT_PUBLIC_LEN> where Pair<LeftPair, RightPair> : TraitPair<Public = Public<LeftPublic, RightPublic, LEFT_PLUS_RIGHT_PUBLIC_LEN>>,
    {
	fn from(x: Pair<LeftPair, RightPair>) -> Self {
		x.public()
	}
}

impl<LeftPublic: PublicKeyBound, RightPublic: PublicKeyBound, const LEFT_PLUS_RIGHT_LEN: usize,> UncheckedFrom<[u8; LEFT_PLUS_RIGHT_LEN]> for Public<LeftPublic, RightPublic, LEFT_PLUS_RIGHT_LEN> {
	fn unchecked_from(data: [u8; LEFT_PLUS_RIGHT_LEN]) -> Self {
 	 let mut left : LeftPublic = data[0..LeftPublic::LEN].try_into().unwrap();
	 let mut right : RightPublic = data[LeftPublic::LEN..LEFT_PLUS_RIGHT_LEN].try_into().unwrap();

	 let mut inner = [0u8; LEFT_PLUS_RIGHT_LEN];
	 Public { left, right, inner }
	}

}

#[cfg(feature = "std")]
impl<LeftPublic: PublicKeyBound, RightPublic: PublicKeyBound, const LEFT_PLUS_RIGHT_LEN: usize,> std::str::FromStr for Public<LeftPublic, RightPublic, LEFT_PLUS_RIGHT_LEN> where Public<LeftPublic, RightPublic, LEFT_PLUS_RIGHT_LEN> : CryptoType {
	type Err = crate::crypto::PublicError;

	fn from_str(s: &str) -> Result<Self, Self::Err> {
		<Self as Ss58Codec>::from_ss58check(s)
	}
}

#[cfg(feature = "std")]
impl<LeftPublic: PublicKeyBound, RightPublic: PublicKeyBound, const LEFT_PLUS_RIGHT_LEN: usize,> std::fmt::Display for Public<LeftPublic, RightPublic, LEFT_PLUS_RIGHT_LEN> where Public<LeftPublic, RightPublic, LEFT_PLUS_RIGHT_LEN> : CryptoType {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		write!(f, "{}", self.to_ss58check())
	}
}

#[cfg(feature = "std")]
impl<LeftPublic: PublicKeyBound, RightPublic: PublicKeyBound, const LEFT_PLUS_RIGHT_LEN: usize,> sp_std::fmt::Debug for Public<LeftPublic, RightPublic, LEFT_PLUS_RIGHT_LEN> where Public<LeftPublic, RightPublic, LEFT_PLUS_RIGHT_LEN> : CryptoType, [u8;LEFT_PLUS_RIGHT_LEN]: crate::hexdisplay::AsBytesRef {
	fn fmt(&self, f: &mut sp_std::fmt::Formatter) -> sp_std::fmt::Result {
		let s = self.to_ss58check();
		write!(f, "{} ({}...)", crate::hexdisplay::HexDisplay::from(&self.inner), &s[0..8])
	}
}

#[cfg(not(feature = "std"))]
impl<LeftPublic: PublicKeyBound, RightPublic: PublicKeyBound, const LEFT_PLUS_RIGHT_LEN: usize,> sp_std::fmt::Debug for Public<LeftPublic, RightPublic, LEFT_PLUS_RIGHT_LEN>  {
	fn fmt(&self, _: &mut sp_std::fmt::Formatter) -> sp_std::fmt::Result {

	    Ok(())
	}
}

#[cfg(feature = "std")]
impl<LeftPublic: PublicKeyBound, RightPublic: PublicKeyBound, const LEFT_PLUS_RIGHT_LEN: usize,> Serialize for Public<LeftPublic, RightPublic, LEFT_PLUS_RIGHT_LEN> where  Public<LeftPublic, RightPublic, LEFT_PLUS_RIGHT_LEN> : CryptoType {
	fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
	where
		S: Serializer,
    {
	    		serializer.serialize_str(&self.to_ss58check())

	}
}

#[cfg(feature = "std")]
impl<'de, LeftPublic: PublicKeyBound, RightPublic: PublicKeyBound, const LEFT_PLUS_RIGHT_LEN: usize> Deserialize<'de> for Public<LeftPublic, RightPublic, LEFT_PLUS_RIGHT_LEN> where Public<LeftPublic, RightPublic, LEFT_PLUS_RIGHT_LEN> : CryptoType {
	fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
	where
		D: Deserializer<'de>,
    {
	    		Public::from_ss58check(&String::deserialize(deserializer)?)
			.map_err(|e| de::Error::custom(format!("{:?}", e)))

	}
}

impl<LeftPublic: PublicKeyBound, RightPublic: PublicKeyBound, const LEFT_PLUS_RIGHT_LEN: usize,> TraitPublic for Public<LeftPublic, RightPublic, LEFT_PLUS_RIGHT_LEN> where Public<LeftPublic, RightPublic, LEFT_PLUS_RIGHT_LEN> : CryptoType {}

impl<LeftPublic: PublicKeyBound, RightPublic: PublicKeyBound, const LEFT_PLUS_RIGHT_LEN: usize,> Derive for Public<LeftPublic, RightPublic, LEFT_PLUS_RIGHT_LEN> {}

#[cfg(not(feature = "full_crypto"))]
impl<LeftPublic: PublicKeyBound, RightPublic: PublicKeyBound, const LEFT_PLUS_RIGHT_PUBLIC_LEN: usize,> CryptoType for Public<LeftPublic, RightPublic, LEFT_PLUS_RIGHT_PUBLIC_LEN> 
{}

//pub trait Public: ByteArray + Derive + CryptoType + PartialEq + Eq + Clone + Send + Sync {}
pub trait SignatureBound: sp_std::hash::Hash + for<'a> TryFrom<&'a[u8]> {}

/// A pair of signatures of different types
#[derive(Encode, Decode, MaxEncodedLen, TypeInfo, PartialEq, Eq)]
#[scale_info(skip_type_params(T))]
pub struct Signature<LeftSignature: SignatureBound, RightSignature: SignatureBound, const LEFT_PLUS_RIGHT_LEN: usize,> {
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
impl<LeftSignature: SignatureBound, RightSignature: SignatureBound, const LEFT_PLUS_RIGHT_LEN: usize> sp_std::hash::Hash for Signature<LeftSignature, RightSignature, LEFT_PLUS_RIGHT_LEN> {
    fn hash<H: sp_std::hash::Hasher>(&self, state: &mut H) {
 	    self.left.hash(state);
	    self.right.hash(state);
	}
}

impl<'a,LeftSignature: SignatureBound, RightSignature: SignatureBound, const LEFT_PLUS_RIGHT_LEN: usize>  TryFrom<&'a[u8]> for Signature<LeftSignature, RightSignature, LEFT_PLUS_RIGHT_LEN> where Signature<LeftSignature, RightSignature, LEFT_PLUS_RIGHT_LEN>: SignaturePair {
     type Error = ();

     fn try_from(data: &[u8]) -> Result<Self, Self::Error> {
  		if data.len() != 	LEFT_PLUS_RIGHT_LEN {
 			return Err(())
 		}
         	 let Ok(mut left)  = data[0..Self::LEFT_SIGNATURE_LEN].try_into() else { panic!("invalid signature") };
	 let Ok(mut right) = data[Self::LEFT_SIGNATURE_LEN..LEFT_PLUS_RIGHT_LEN].try_into() else { panic!("invalid signature") };

	 let mut inner = [0u8; LEFT_PLUS_RIGHT_LEN];
	 Ok(Signature { left, right, inner })

     }
}
	
impl<LeftSignature: SignatureBound, RightSignature: SignatureBound, const LEFT_PLUS_RIGHT_LEN: usize> AsMut<[u8]> for Signature<LeftSignature, RightSignature, LEFT_PLUS_RIGHT_LEN> {
    fn as_mut(&mut self) -> &mut [u8] {
	&mut self.inner[..]
    }
}

impl<LeftSignature: SignatureBound, RightSignature: SignatureBound, const LEFT_PLUS_RIGHT_LEN: usize> AsRef<[u8; LEFT_PLUS_RIGHT_LEN]> for Signature<LeftSignature, RightSignature, LEFT_PLUS_RIGHT_LEN>  {
    fn as_ref(&self) -> &[u8; LEFT_PLUS_RIGHT_LEN] {
		&self.inner
    }
}

impl<LeftSignature: SignatureBound, RightSignature: SignatureBound, const LEFT_PLUS_RIGHT_LEN: usize,> AsRef<[u8]> for Signature<LeftSignature, RightSignature, LEFT_PLUS_RIGHT_LEN> {
    fn as_ref(&self) -> &[u8] {
	&self.inner[..]
    }
}
#[cfg(feature = "std")]
impl<LeftSignature: SignatureBound, RightSignature: SignatureBound, const LEFT_PLUS_RIGHT_LEN: usize,> Serialize for Signature<LeftSignature, RightSignature, LEFT_PLUS_RIGHT_LEN> {
	fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
	where
		S: Serializer,
	{
		serializer.serialize_str(&array_bytes::bytes2hex("", self))
	}
}

#[cfg(feature = "std")]
impl<'de, LeftSignature: SignatureBound, RightSignature: SignatureBound, const LEFT_PLUS_RIGHT_LEN: usize,> Deserialize<'de> for Signature<LeftSignature, RightSignature, LEFT_PLUS_RIGHT_LEN> {
	fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
	where
		D: Deserializer<'de>,
	{
		let signature_hex = array_bytes::hex2bytes(&String::deserialize(deserializer)?)
			.map_err(|e| de::Error::custom(format!("{:?}", e)))?;
		Signature::try_from(signature_hex.as_ref())
			.map_err(|e| de::Error::custom(format!("{:?}", e)))
	}
}

impl<LeftSignature: SignatureBound, RightSignature: SignatureBound, const LEFT_PLUS_RIGHT_LEN: usize,> From<Signature<LeftSignature, RightSignature, LEFT_PLUS_RIGHT_LEN>> for [u8; LEFT_PLUS_RIGHT_LEN]
{
	fn from(signature: Signature<LeftSignature, RightSignature, LEFT_PLUS_RIGHT_LEN>) -> [u8; LEFT_PLUS_RIGHT_LEN] {
		signature.inner
	}
}

impl<LeftSignature: SignatureBound, RightSignature: SignatureBound, const LEFT_PLUS_RIGHT_LEN: usize,> sp_std::fmt::Debug for Signature<LeftSignature, RightSignature, LEFT_PLUS_RIGHT_LEN> {
	#[cfg(feature = "std")]
	fn fmt(&self, f: &mut sp_std::fmt::Formatter) -> sp_std::fmt::Result {
		write!(f, "{}", crate::hexdisplay::HexDisplay::from(&self.inner))
	}

	#[cfg(not(feature = "std"))]
	fn fmt(&self, _: &mut sp_std::fmt::Formatter) -> sp_std::fmt::Result {
		Ok(())
	}
}

impl<LeftSignature: SignatureBound, RightSignature: SignatureBound,  const LEFT_PLUS_RIGHT_LEN: usize,> UncheckedFrom<[u8; LEFT_PLUS_RIGHT_LEN]> for Signature<LeftSignature, RightSignature,LEFT_PLUS_RIGHT_LEN> where Signature<LeftSignature, RightSignature, LEFT_PLUS_RIGHT_LEN>: SignaturePair {
	fn unchecked_from(data: [u8; LEFT_PLUS_RIGHT_LEN]) -> Self {
        let mut left : LeftSignature = data[0..Self::LEFT_SIGNATURE_LEN].try_into().unwrap();
	 let mut right : RightSignature = data[Self::LEFT_SIGNATURE_LEN..LEFT_PLUS_RIGHT_LEN].try_into().unwrap();

	 let mut inner = [0u8; LEFT_PLUS_RIGHT_LEN];
	 Signature { left, right, inner }
	}
}

/// A key pair.
#[cfg(feature = "full_crypto")]
#[derive(Clone)]
pub struct Pair<LeftPair: TraitPair, RightPair: TraitPair,> {
    left: LeftPair,
    right: RightPair,
    
}


trait DoublePair {
    const PUBLIC_KEY_LEN: usize;
    const LEFT_SIGNATURE_LEN: usize;
    const RIGHT_SIGNATURE_LEN:usize;
    const SIGNATURE_LEN: usize;
    const LEFT_SEED_LEN: usize;
    const RIGHT_SEED_LEN: usize;
}

trait HardJunctionId {
	const ID: &'static str;
}

#[cfg(feature = "full_crypto")]
impl<LeftPair: TraitPair, RightPair: TraitPair> Pair<LeftPair, RightPair> {
}

#[cfg(feature = "full_crypto")]
impl<LeftPair: TraitPair, RightPair: TraitPair> TraitPair for Pair<LeftPair, RightPair> where
    Pair<LeftPair, RightPair>: DoublePair + CryptoType,
    LeftPair::Signature: SignatureBound,
    RightPair::Signature: SignatureBound,
{
	type Seed = (LeftPair::Seed, RightPair::Seed);
	type Public = Public<LeftPair::Public, RightPair::Public, {<Self as DoublePair>::PUBLIC_KEY_LEN}>;
	type Signature = Signature<LeftPair::Signature, RightPair::Signature, { Self::SIGNATURE_LEN }>;

	fn from_seed_slice(seed_slice: &[u8]) -> Result<Self, SecretStringError> {
		if seed_slice.len() != Self::RIGHT_SEED_LEN + Self::LEFT_SEED_LEN {
			return Err(SecretStringError::InvalidSeedLength)
		}
		let left = LeftPair::from_seed_slice(seed_slice[0..Self::LEFT_SEED_LEN])?;
        let right =	RightPair::from_seed_slice(seed_slice[Self::LEFT_SEED_LEN..Self::RIGHT_SEED_LEN + Self::LEFT_SEED_LEN])?;
		Ok(Pair { left, right })
	}

	// fn derive<Iter: Iterator<Item = DeriveJunction>>(
	// 	&self,
	// 	path: Iter,
	// 	_seed: Option<Seed>,
	// ) -> Result<(Self, Option<Seed>), DeriveError> {
	// 	let mut acc: [u8; SECRET_KEY_SERIALIZED_SIZE] =
	// 		self.0.secret.to_bytes().try_into().expect(
	// 			"Secret key serializer returns a vector of SECRET_KEY_SERIALIZED_SIZE size",
	// 		);
	// 	for j in path {
	// 		match j {
	// 			DeriveJunction::Soft(_cc) => return Err(DeriveError::SoftKeyInPath),
	// 			DeriveJunction::Hard(cc) => acc = derive_hard_junction::<T>(&acc, &cc),
	// 		}
	// 	}
	// 	Ok((Self::from_seed(&acc), Some(acc)))
	// }

	// fn public(&self) -> Self::Public {
	// 	let mut raw = [0u8; PUBLIC_KEY_SERIALIZED_SIZE];
	// 	let pk = DoublePublicKeyScheme::into_double_public_key(&self.0).to_bytes();
	// 	raw.copy_from_slice(pk.as_slice());
	// 	Self::Public::unchecked_from(raw)
	// }

	// fn sign(&self, message: &[u8]) -> Self::Signature {
	// 	let mut mutable_self = self.clone();
	// 	let r: [u8; SIGNATURE_SERIALIZED_SIZE] =
	// 		DoublePublicKeyScheme::sign(&mut mutable_self.0, &Message::new(b"", message))
	// 			.to_bytes()
	// 			.try_into()
	// 			.expect("Signature serializer returns vectors of SIGNATURE_SERIALIZED_SIZE size");
	// 	Self::Signature::unchecked_from(r)
	// }

	// fn verify<M: AsRef<[u8]>>(sig: &Self::Signature, message: M, pubkey: &Self::Public) -> bool {
	// 	let pubkey_array: [u8; PUBLIC_KEY_SERIALIZED_SIZE] =
	// 		match <[u8; PUBLIC_KEY_SERIALIZED_SIZE]>::try_from(pubkey.as_ref()) {
	// 			Ok(pk) => pk,
	// 			Err(_) => return false,
	// 		};
	// 	let public_key = match w3f_bls::double::DoublePublicKey::<T>::from_bytes(&pubkey_array) {
	// 		Ok(pk) => pk,
	// 		Err(_) => return false,
	// 	};

	// 	let sig_array = match sig.inner[..].try_into() {
	// 		Ok(s) => s,
	// 		Err(_) => return false,
	// 	};
	// 	let sig = match w3f_bls::double::DoubleSignature::from_bytes(sig_array) {
	// 		Ok(s) => s,
	// 		Err(_) => return false,
	// 	};

	// 	sig.verify(&Message::new(b"", message.as_ref()), &public_key)
	// }

	// /// Get the seed for this key.
	// fn to_raw_vec(&self) -> Vec<u8> {
	// 	self.0
	// 		.secret
	// 		.to_bytes()
	// 		.try_into()
	// 		.expect("Secret key serializer returns a vector of SECRET_KEY_SERIALIZED_SIZE size")
	// }
}
