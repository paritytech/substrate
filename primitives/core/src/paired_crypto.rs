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
}

/// A secret seed.
///
/// It's not called a "secret key" because ring doesn't expose the secret keys
/// of the key pair (yeah, dumb); as such we're forced to remember the seed manually if we
/// will need it later (such as for HDKD).
#[cfg(feature = "full_crypto")]
//type Seed = [u8; SECRET_KEY_SERIALIZED_SIZE];

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
impl<LeftPublic: PublicKeyBound, RightPublic: PublicKeyBound, const LEFT_PLUS_RIGHT_LEN: usize,>_sp_std::fmt::Debug for Public<LeftPublic, RightPublic, LEFT_PLUS_RIGHT_LEN>  {
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
pub struct Signature<LeftSignature: SignatureBound, RightSignature: SignatureBound, const LEFT_LEN: usize, const RIGHT_LEN: usize, const LEFT_PLUS_RIGHT_LEN: usize,> {
    left: LeftSignature,
    right: RightSignature,
    inner: [u8; LEFT_PLUS_RIGHT_LEN],
}

#[cfg(feature = "full_crypto")]
impl<LeftSignature: SignatureBound, RightSignature: SignatureBound, const LEFT_LEN: usize, const RIGHT_LEN: usize, const LEFT_PLUS_RIGHT_LEN: usize> sp_std::hash::Hash for Signature<LeftSignature, RightSignature, LEFT_LEN, RIGHT_LEN, LEFT_PLUS_RIGHT_LEN> {
    fn hash<H: sp_std::hash::Hasher>(&self, state: &mut H) {
 	    self.left.hash(state);
	    self.right.hash(state);
	}
}

impl<'a,LeftSignature: SignatureBound, RightSignature: SignatureBound, const LEFT_LEN: usize, const RIGHT_LEN: usize, const LEFT_PLUS_RIGHT_LEN: usize>  TryFrom<&'a[u8]> for Signature<LeftSignature, RightSignature, LEFT_LEN, RIGHT_LEN, LEFT_PLUS_RIGHT_LEN> {
     type Error = ();

     fn try_from(data: &[u8]) -> Result<Self, Self::Error> {
  		if data.len() != 	LEFT_PLUS_RIGHT_LEN {
 			return Err(())
 		}
         	 let Ok(mut left)  = data[0..LEFT_LEN].try_into() else { panic!("invalid signature") };
	 let Ok(mut right) = data[LEFT_LEN..LEFT_PLUS_RIGHT_LEN].try_into() else { panic!("invalid signature") };

	 let mut inner = [0u8; LEFT_PLUS_RIGHT_LEN];
	 Ok(Signature { left, right, inner })

     }
}
	
impl<LeftSignature: SignatureBound, RightSignature: SignatureBound, const LEFT_LEN: usize, const RIGHT_LEN: usize, const LEFT_PLUS_RIGHT_LEN: usize> AsMut<[u8]> for Signature<LeftSignature, RightSignature, LEFT_LEN, RIGHT_LEN, LEFT_PLUS_RIGHT_LEN> {
    fn as_mut(&mut self) -> &mut [u8] {
	&mut self.inner[..]
    }
}

impl<LeftSignature: SignatureBound, RightSignature: SignatureBound, const LEFT_LEN: usize, const RIGHT_LEN: usize, const LEFT_PLUS_RIGHT_LEN: usize> AsRef<[u8; LEFT_PLUS_RIGHT_LEN]> for Signature<LeftSignature, RightSignature, LEFT_LEN, RIGHT_LEN, LEFT_PLUS_RIGHT_LEN>  {
    fn as_ref(&self) -> &[u8; LEFT_PLUS_RIGHT_LEN] {
		&self.inner
    }
}

impl<LeftSignature: SignatureBound, RightSignature: SignatureBound, const LEFT_LEN: usize, const RIGHT_LEN: usize, const LEFT_PLUS_RIGHT_LEN: usize,> AsRef<[u8]> for Signature<LeftSignature, RightSignature, LEFT_LEN, RIGHT_LEN, LEFT_PLUS_RIGHT_LEN> {
    fn as_ref(&self) -> &[u8] {
	&self.inner[..]
    }
}
		// serializer.serialize_str(&array_bytes::bytes2hex("", self))

		// let signature_hex = array_bytes::hex2bytes(&String::deserialize(deserializer)?)
		// 	.map_err(|e| de::Error::custom(format!("{:?}", e)))?;
		// Signature::try_from(signature_hex.as_ref())
		// 	.map_err(|e| de::Error::custom(format!("{:?}", e)))

/// A key pair.
#[cfg(feature = "full_crypto")]
#[derive(Clone)]
pub struct Pair<LeftPair: TraitPair, RightPair: TraitPair>(LeftPair, RightPair);



