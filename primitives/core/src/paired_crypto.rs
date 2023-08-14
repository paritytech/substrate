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
	//pub type Pair = super::Pair<ecdsa:Pair, bls377:Pair>;
	/// BLS12-377 public key.
	pub type Public = super::Public<ecdsa::Public, ed25519::Public, 32, 32>;
	// /// BLS12-377 signature.
	//pub type Signature = super::Signature<ecdsa:Signature, bls377:Signature>;

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

pub trait PublicKeyBound: TraitPublic + sp_std::hash::Hash + ByteArray  {}
/// A public key.
#[derive(Clone, Encode, Decode, MaxEncodedLen, TypeInfo, PartialEq, Eq, PartialOrd, Ord)]
#[scale_info(skip_type_params(T))]
pub struct Public<LeftPublic: PublicKeyBound, RightPublic: PublicKeyBound, const LEFT_LEN: usize, const RIGHT_LEN: usize,> (LeftPublic, RightPublic);

#[cfg(feature = "full_crypto")]
impl<LeftPublic: PublicKeyBound + UncheckedFrom<[u8; LEFT_LEN]>, RightPublic: PublicKeyBound + UncheckedFrom<[u8; RIGHT_LEN]>, const LEFT_LEN: usize, const RIGHT_LEN: usize> sp_std::hash::Hash for Public<LeftPublic, RightPublic, LEFT_LEN, RIGHT_LEN> {
  	fn hash<H: sp_std::hash::Hasher>(&self, state: &mut H) {
 	    self.0.hash(state);
	    self.1.hash(state);
	}
}

impl<LeftPublic: PublicKeyBound, RightPublic: PublicKeyBound, const LEFT_LEN: usize, const RIGHT_LEN: usize> ByteArray  for Public<LeftPublic, RightPublic, LEFT_LEN, RIGHT_LEN> where for<'a>  Public<LeftPublic, RightPublic, LEFT_LEN, RIGHT_LEN>: TryFrom<&'a [u8], Error = ()> + AsRef<[u8]> + AsMut<[u8]>  {
     const LEN: usize = LeftPublic::LEN + RightPublic::LEN;
}

impl<'a,LeftPublic: PublicKeyBound + UncheckedFrom<[u8; LEFT_LEN]>, RightPublic: PublicKeyBound + UncheckedFrom<[u8; RIGHT_LEN]>, const LEFT_LEN: usize, const RIGHT_LEN: usize>  TryFrom<&'a[u8]> for Public<LeftPublic, RightPublic, LEFT_LEN, RIGHT_LEN> {
    type Error = ();

    fn try_from(data: &[u8]) -> Result<Self, Self::Error> {
 		if data.len() != 	LEFT_LEN + RIGHT_LEN {
			return Err(())
		}
	
 		let mut r0 = [0u8;  LEFT_LEN];
 		let mut r1 = [0u8; RIGHT_LEN];
		r0.copy_from_slice(&data[0..LEFT_LEN]);  
 		r1.copy_from_slice(&data[LEFT_LEN..RIGHT_LEN]);
		Ok(Self(LeftPublic::unchecked_from(r0),RightPublic::unchecked_from(r1)))
    }
}

// impl<LeftPublic: PublicKeyBound, RightPublic: PublicKeyBound, const LEFT_LEN: usize, const RIGHT_LEN: usize> AsMut<[u8]> for Public<LeftPublic, RightPublic, LEFT_LEN, RIGHT_LEN> {
//  	fn as_mut(&mut self) -> &mut [u8] {
//  	 &mut [self.0.as_mut(), self.1.as_mut()].concat()
//  	}
// }

// impl<LeftPublic: PublicKeyBound, RightPublic: PublicKeyBound, const LEFT_LEN: usize, const RIGHT_LEN: usize, const RIGHT_PLUS_LEFT_LEN: usize> AsRef<[u8; RIGHT_PLUS_LEFT_LEN]> for Public<LeftPublic, RightPublic, LEFT_LEN, RIGHT_LEN> where for<'a>  Public<LeftPublic, RightPublic, LEFT_LEN, RIGHT_LEN>: TryFrom<&'a [u8], Error = ()> {
//     fn as_ref(&self) -> &[u8; RIGHT_PLUS_LEFT_LEN] {
// 	let mut r = [0u8; RIGHT_PLUS_LEFT_LEN];
// 	r.copy_from_slice(self.0.as_ref());
// 	r[LeftPublic::LEN..].copy_from_slice(self.1.as_ref());
// 	&r
//     }
// }

// impl<LeftPublic: PublicKeyBound, RightPublic: PublicKeyBound, const LEFT_LEN: usize, const RIGHT_LEN: usize,> AsRef<[u8]> for Public<LeftPublic, RightPublic, LEFT_LEN, RIGHT_LEN> {
//     fn as_ref(&self) -> &[u8] {
// 	//let mut r : Vec<u8> = vec![0u8; LEFT_LEN + RIGHT_LEN];
// 	//r.copy_from_slice(self.0.as_ref(), LeftPublic::LEN);
// 	//r[LeftPublic::LEN..].copy_from_slice(self.1.as_ref(), RightPublic::LEN);
// 	let mut r :Vec<u8> = [self.0.as_ref(), self.1.as_ref()].concat();
// 	&r[..]
//     }
// }
