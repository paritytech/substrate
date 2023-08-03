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
	pub type Public = super::Public<ecdsa::Public, ed25519::Public>;
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

pub trait PublicKeyBound: TraitPublic + sp_std::hash::Hash + ByteArray {}
/// A public key.
#[derive(Clone, Encode, Decode, MaxEncodedLen, TypeInfo, PartialEq, Eq, PartialOrd, Ord)]
#[scale_info(skip_type_params(T))]
pub struct PublicWithInner<LeftPublic: PublicKeyBound, RightPublic: PublicKeyBound, const LEFT_PLUS_RIGHT_SIZE: usize> {
    inner: [u8; LEFT_PLUS_RIGHT_SIZE],
 	_phantom: PhantomData<fn() -> (LeftPublic, RightPublic)>,
}

pub struct Public<LeftPublic: PublicKeyBound, RightPublic: PublicKeyBound> {
    left_public : LeftPublic,
    right_public: RightPublic,
}

// #[cfg(feature = "full_crypto")]
// impl<T1: PublicKeyBound, T2: PublicKeyBound> sp_std::hash::Hash for Public<T1,T2> {
//  	fn hash<H: sp_std::hash::Hasher>(&self, state: &mut H) {
//  		self.left_public.hash(state);
//         self.right_public.hash(state);
//  	}
// }

// impl<T1: TraitPublic, T2: TraitPublic> ByteArray for Public<T1,T2> {
//  	const LEN: usize = T1::LEN + T2::LEN;
// }

// impl<T1: PublicKeyBound, T2: PublicKeyBound> TryFrom<&[u8]> for Public<T1,T2> {
//  	type Error = ();

//  	fn try_from(data: &[u8]) -> Result<Self, Self::Error> {
// // 		if data.len() != PUBLIC_KEY_SERIALIZED_SIZE {
// // 			return Err(())
// // 		}
// // 		let mut r = [0u8; PUBLIC_KEY_SERIALIZED_SIZE];
// // 		r.copy_from_slice(data);
// // 		Ok(Self::unchecked_from(r))
//  	}
// }

// impl<T1,T2> AsMut<[u8]> for Public<T1,T2> {
//  	fn as_mut(&mut self) -> &mut [u8] {
//  		&mut self.inner[..]
//  	}
// }
