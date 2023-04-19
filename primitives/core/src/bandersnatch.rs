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

//! TODO DOCS.

#![allow(unused)]

#[cfg(feature = "std")]
use crate::crypto::Ss58Codec;
#[cfg(feature = "full_crypto")]
use crate::crypto::{DeriveError, DeriveJunction, Pair as TraitPair, SecretStringError};
use bandersnatch_vrfs::{CanonicalSerialize, PublicKey, SecretKey, ThinVrfSignature};
#[cfg(feature = "full_crypto")]
use sp_std::vec::Vec;

use crate::{
	crypto::{ByteArray, CryptoType, CryptoTypeId, Derive, Public as TraitPublic, UncheckedFrom},
	hash::{H256, H512},
};
use codec::{Decode, Encode, MaxEncodedLen};
use scale_info::TypeInfo;
use sp_std::ops::Deref;

#[cfg(feature = "std")]
use serde::{de, Deserialize, Deserializer, Serialize, Serializer};
use sp_runtime_interface::pass_by::PassByInner;

/// Identifier used to match public keys against bandersnatch-vrf keys.
pub const CRYPTO_ID: CryptoTypeId = CryptoTypeId(*b"bs38");

const SEED_SERIALIZED_LEN: usize = 32;
const PUBLIC_SERIALIZED_LEN: usize = 32;
const SIGNATURE_SERIALIZED_LEN: usize = 64;

/// XXX.
#[cfg_attr(feature = "full_crypto", derive(Hash))]
#[derive(
	PartialEq,
	Eq,
	PartialOrd,
	Ord,
	Clone,
	Copy,
	Encode,
	Decode,
	PassByInner,
	MaxEncodedLen,
	TypeInfo,
)]
pub struct Public(pub [u8; PUBLIC_SERIALIZED_LEN]);

impl UncheckedFrom<[u8; PUBLIC_SERIALIZED_LEN]> for Public {
	fn unchecked_from(raw: [u8; PUBLIC_SERIALIZED_LEN]) -> Self {
		Public(raw)
	}
}

// impl AsRef<[u8; PUBLIC_SERIALIZED_LEN]> for Public {
// 	fn as_ref(&self) -> &[u8; PUBLIC_SERIALIZED_LEN] {
// 		&self.0
// 	}
// }

impl AsRef<[u8]> for Public {
	fn as_ref(&self) -> &[u8] {
		&self.0[..]
	}
}

impl AsMut<[u8]> for Public {
	fn as_mut(&mut self) -> &mut [u8] {
		&mut self.0[..]
	}
}

impl Deref for Public {
	type Target = [u8];

	fn deref(&self) -> &Self::Target {
		&self.0
	}
}

impl TryFrom<&[u8]> for Public {
	type Error = ();

	fn try_from(data: &[u8]) -> Result<Self, Self::Error> {
		if data.len() != PUBLIC_SERIALIZED_LEN {
			return Err(())
		}
		let mut r = [0u8; PUBLIC_SERIALIZED_LEN];
		r.copy_from_slice(data);
		Ok(Self::unchecked_from(r))
	}
}

// impl From<Public> for [u8; PUBLIC_SERIALIZED_LEN] {
// 	fn from(x: Public) -> [u8; PUBLIC_SERIALIZED_LEN] {
// 		x.0
// 	}
// }

// impl From<Public> for H256 {
// 	fn from(x: Public) -> H256 {
// 		x.0.into()
// 	}
// }

// #[cfg(feature = "std")]
// impl std::str::FromStr for Public {
// 	type Err = crate::crypto::PublicError;

// 	fn from_str(s: &str) -> Result<Self, Self::Err> {
// 		Self::from_ss58check(s)
// 	}
// }

// impl UncheckedFrom<H256> for Public {
// 	fn unchecked_from(x: H256) -> Self {
// 		Public::from_h256(x)
// 	}
// }

// #[cfg(feature = "std")]
// impl std::fmt::Display for Public {
// 	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
// 		write!(f, "{}", self.to_ss58check())
// 	}
// }

// impl sp_std::fmt::Debug for Public {
// 	#[cfg(feature = "std")]
// 	fn fmt(&self, f: &mut sp_std::fmt::Formatter) -> sp_std::fmt::Result {
// 		let s = self.to_ss58check();
// 		write!(f, "{} ({}...)", crate::hexdisplay::HexDisplay::from(&self.0), &s[0..8])
// 	}

// 	#[cfg(not(feature = "std"))]
// 	fn fmt(&self, _: &mut sp_std::fmt::Formatter) -> sp_std::fmt::Result {
// 		Ok(())
// 	}
// }

// #[cfg(feature = "std")]
// impl Serialize for Public {
// 	fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
// 	where
// 		S: Serializer,
// 	{
// 		serializer.serialize_str(&self.to_ss58check())
// 	}
// }

// #[cfg(feature = "std")]
// impl<'de> Deserialize<'de> for Public {
// 	fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
// 	where
// 		D: Deserializer<'de>,
// 	{
// 		Public::from_ss58check(&String::deserialize(deserializer)?)
// 			.map_err(|e| de::Error::custom(format!("{:?}", e)))
// 	}
// }

impl ByteArray for Public {
	const LEN: usize = PUBLIC_SERIALIZED_LEN;
}

impl TraitPublic for Public {}

impl CryptoType for Public {
	#[cfg(feature = "full_crypto")]
	type Pair = Pair;
}

impl Derive for Public {}

/// DAVXY TODO: DOCS
#[cfg_attr(feature = "full_crypto", derive(Hash))]
#[derive(Encode, Decode, PartialEq, Eq, PassByInner, MaxEncodedLen, TypeInfo)]
pub struct Signature(pub [u8; SIGNATURE_SERIALIZED_LEN]);

// impl AsRef<[u8; 64]> for Signature {
// 	fn as_ref(&self) -> &[u8; 64] {
// 		&self.0
// 	}
// }

impl AsRef<[u8]> for Signature {
	fn as_ref(&self) -> &[u8] {
		&self.0[..]
	}
}

impl AsMut<[u8]> for Signature {
	fn as_mut(&mut self) -> &mut [u8] {
		&mut self.0[..]
	}
}

impl CryptoType for Signature {
	#[cfg(feature = "full_crypto")]
	type Pair = Pair;
}

/// The raw secret seed, which can be used to recreate the `Pair`.
#[cfg(feature = "full_crypto")]
type Seed = [u8; SEED_SERIALIZED_LEN];

use bandersnatch_vrfs::Transcript;

/// DAVXY TODO: DOCS
#[cfg(feature = "full_crypto")]
#[derive(Clone)]
pub struct Pair(SecretKey);

#[cfg(feature = "full_crypto")]
impl TraitPair for Pair {
	type Seed = Seed;
	type Public = Public;
	type Signature = Signature;

	/// Make a new key pair from secret seed material.
	///
	/// The slice must be 64 bytes long or it will return an error.
	fn from_seed_slice(seed_slice: &[u8]) -> Result<Pair, SecretStringError> {
		if seed_slice.len() != SEED_SERIALIZED_LEN {
			return Err(SecretStringError::InvalidSeedLength)
		}
		let mut seed_raw = [0; SEED_SERIALIZED_LEN];
		seed_raw.copy_from_slice(seed_slice);
		let secret = SecretKey::from_seed(&seed_raw);
		Ok(Pair(secret))
	}

	/// Derive a child key from a series of given (hard) junctions.
	///
	/// Soft junctions are not supported.
	fn derive<Iter: Iterator<Item = DeriveJunction>>(
		&self,
		path: Iter,
		_seed: Option<Seed>,
	) -> Result<(Pair, Option<Seed>), DeriveError> {
		// TODO DAVXY: is this good?
		let derive_hard_junction = |secret_seed, cc| -> Seed {
			("bandersnatch-vrf-HDKD", secret_seed, cc).using_encoded(sp_core_hashing::blake2_256)
		};

		let mut acc = [0; SEED_SERIALIZED_LEN];
		for j in path {
			match j {
				DeriveJunction::Soft(_cc) => return Err(DeriveError::SoftKeyInPath),
				DeriveJunction::Hard(cc) => acc = derive_hard_junction(acc, cc),
			}
		}
		Ok((Self::from_seed(&acc), Some(acc)))
	}

	/// Get the public key.
	fn public(&self) -> Public {
		let public = self.0.to_public();
		let mut raw = [0; PUBLIC_SERIALIZED_LEN];
		public.0.serialize(raw.as_mut_slice()).expect("key buffer length is good; qed");
		Public::unchecked_from(raw)
	}

	/// Sign a message.
	fn sign(&self, message: &[u8]) -> Signature {
		let mut t = Transcript::new(b"SigningContext");
		t.append_slice(message);
		// // TODO DAVXY: looks like we require to clone to call sign... is this required?
		let sign: ThinVrfSignature<0> = self.0.clone().sign_thin_vrf(t, &[]);
		let mut raw = [0; SIGNATURE_SERIALIZED_LEN];
		sign.serialize_compressed(raw.as_mut_slice());
		Signature(raw)
	}

	/// Verify a signature on a message. Returns true if the signature is good.
	fn verify<M: AsRef<[u8]>>(sig: &Self::Signature, message: M, pubkey: &Self::Public) -> bool {
		// match sig.recover(message) {
		// 	Some(actual) => actual == *pubkey,
		// 	None => false,
		// }
		// DAVXY TODO
		false
	}

	/// Verify a signature on a message. Returns true if the signature is good.
	///
	/// This doesn't use the type system to ensure that `sig` and `pubkey` are the correct
	/// size. Use it only if you're coming from byte buffers and need the speed.
	fn verify_weak<P: AsRef<[u8]>, M: AsRef<[u8]>>(sig: &[u8], message: M, pubkey: P) -> bool {
		// match Signature::from_slice(sig).and_then(|sig| sig.recover(message)) {
		// 	Some(actual) => actual.as_ref() == pubkey.as_ref(),
		// 	None => false,
		// }
		// DAVXY TODO
		false
	}

	/// Return a vec filled with seed raw data.
	fn to_raw_vec(&self) -> Vec<u8> {
		// DAVXY TODO: should we maintain the seed here?
		// Can't we extract it from inner secret key somehow? Maybe not...
		vec![]
	}
}

#[cfg(feature = "full_crypto")]
impl CryptoType for Pair {
	type Pair = Pair;
}

// use ark_serialize::CanonicalSerialize;

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn assumptions_check() {
		let pair = SecretKey::from_seed(&[0; SEED_SERIALIZED_LEN]);
		let public = pair.to_public();
		assert_eq!(public.0.size_of_serialized(), PUBLIC_SERIALIZED_LEN);
	}

	#[test]
	fn tmp_construct_public() {
		let pair = Pair::from_seed(&[0; SEED_SERIALIZED_LEN]);
		let public = pair.public();
		let raw = public.to_vec();
		println!("{:?}", raw);
	}

	#[test]
	fn sign_verify() {
		let pair = Pair::from_seed(&[0; SEED_SERIALIZED_LEN]);
		let public = pair.public();

		let signature = pair.sign(b"hello");

		println!("{:?}", signature.0);
	}
}
