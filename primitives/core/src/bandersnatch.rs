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
use bandersnatch_vrfs::{
	CanonicalDeserialize, CanonicalSerialize, IntoVrfInput, PublicKey, SecretKey, ThinVrfSignature,
	Transcript, VrfInput, VrfPreOut,
};
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

const SIGNING_CTX: &[u8] = b"SigningContext";

const SEED_SERIALIZED_LEN: usize = 32;
const PUBLIC_SERIALIZED_LEN: usize = 32;
const SIGNATURE_SERIALIZED_LEN: usize = 64;

/// XXX.
#[cfg_attr(feature = "full_crypto", derive(Hash))]
#[derive(
	Clone,
	Copy,
	PartialEq,
	Eq,
	PartialOrd,
	Ord,
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

impl ByteArray for Public {
	const LEN: usize = PUBLIC_SERIALIZED_LEN;
}

impl TraitPublic for Public {}

impl CryptoType for Public {
	#[cfg(feature = "full_crypto")]
	type Pair = Pair;
}

impl Derive for Public {}

impl sp_std::fmt::Debug for Public {
	#[cfg(feature = "std")]
	fn fmt(&self, f: &mut sp_std::fmt::Formatter) -> sp_std::fmt::Result {
		let s = self.to_ss58check();
		write!(f, "{} ({}...)", crate::hexdisplay::HexDisplay::from(&self.0), &s[0..8])
	}

	#[cfg(not(feature = "std"))]
	fn fmt(&self, _: &mut sp_std::fmt::Formatter) -> sp_std::fmt::Result {
		Ok(())
	}
}

/// TODO davxy: DOCS
#[cfg_attr(feature = "full_crypto", derive(Hash))]
#[derive(Clone, Copy, PartialEq, Eq, Encode, Decode, PassByInner, MaxEncodedLen, TypeInfo)]
pub struct Signature([u8; SIGNATURE_SERIALIZED_LEN]);

impl UncheckedFrom<[u8; SIGNATURE_SERIALIZED_LEN]> for Signature {
	fn unchecked_from(raw: [u8; SIGNATURE_SERIALIZED_LEN]) -> Self {
		Signature(raw)
	}
}

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

impl TryFrom<&[u8]> for Signature {
	type Error = ();

	fn try_from(data: &[u8]) -> Result<Self, Self::Error> {
		if data.len() != SIGNATURE_SERIALIZED_LEN {
			return Err(())
		}
		let mut r = [0u8; SIGNATURE_SERIALIZED_LEN];
		r.copy_from_slice(data);
		Ok(Self::unchecked_from(r))
	}
}

impl ByteArray for Signature {
	const LEN: usize = SIGNATURE_SERIALIZED_LEN;
}

impl CryptoType for Signature {
	#[cfg(feature = "full_crypto")]
	type Pair = Pair;
}

impl sp_std::fmt::Debug for Signature {
	#[cfg(feature = "std")]
	fn fmt(&self, f: &mut sp_std::fmt::Formatter) -> sp_std::fmt::Result {
		write!(f, "{}", crate::hexdisplay::HexDisplay::from(&self.0))
	}

	#[cfg(not(feature = "std"))]
	fn fmt(&self, _: &mut sp_std::fmt::Formatter) -> sp_std::fmt::Result {
		Ok(())
	}
}

/// The raw secret seed, which can be used to recreate the `Pair`.
#[cfg(feature = "full_crypto")]
type Seed = [u8; SEED_SERIALIZED_LEN];

/// TODO davxy: DOCS
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
		// TODO davxy is this good?
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
		let mut transcript = Transcript::new(SIGNING_CTX);
		transcript.append_slice(message);
		let sign: ThinVrfSignature<0> = self.0.sign_thin_vrf(transcript, &[]);
		let mut raw = [0; SIGNATURE_SERIALIZED_LEN];
		sign.serialize_compressed(raw.as_mut_slice());
		Signature(raw)
	}

	/// Verify a signature on a message.
	///
	/// Returns true if the signature is good.
	fn verify<M: AsRef<[u8]>>(
		signature: &Self::Signature,
		message: M,
		public: &Self::Public,
	) -> bool {
		let Ok(public) = PublicKey::deserialize_compressed(public.as_ref()) else {
			return false
		};
		let Ok(signature) = ThinVrfSignature::<0>::deserialize_compressed(signature.as_ref()) else {
			return false
		};
		let mut transcript = Transcript::new(SIGNING_CTX);
		transcript.append_slice(message.as_ref());

		let inputs: Vec<VrfInput> = Vec::new();
		match signature.verify_thin_vrf(transcript, inputs, &public) {
			Ok(ios) => true,
			Err(e) => false,
		}
	}

	/// Verify a signature on a message. Returns true if the signature is good.
	///
	/// This doesn't use the type system to ensure that `sig` and `public` are the correct
	/// size. Use it only if you're coming from byte buffers and need the speed.
	fn verify_weak<P: AsRef<[u8]>, M: AsRef<[u8]>>(sig: &[u8], message: M, public: P) -> bool {
		// TODO davxy : makes sense???
		unimplemented!()
		false
	}

	/// Return a vec filled with seed raw data.
	fn to_raw_vec(&self) -> Vec<u8> {
		// TODO davxy: makes sense???
		unimplemented!()
	}
}

#[cfg(feature = "full_crypto")]
impl CryptoType for Pair {
	type Pair = Pair;
}

/// VRF related types and operations.
pub mod vrf {
	use super::*;
	#[cfg(feature = "full_crypto")]
	use crate::crypto::VrfSigner;
	use crate::crypto::{VrfCrypto, VrfVerifier};

	/// VRF transcript ready to be used for VRF sign/verify operations.
	pub struct VrfTranscript(Transcript);

	impl VrfTranscript {
		/// Build a new transcript ready to be used by a VRF signer/verifier.
		pub fn new(label: &'static [u8], data: &[&[u8]]) -> Self {
			let mut transcript = Transcript::new(label);
			data.iter().for_each(|b| transcript.append_slice(b));
			VrfTranscript(transcript)
		}
	}

	/// TODO davxy: docs
	pub type VrfSignature = super::Signature;

	#[cfg(feature = "full_crypto")]
	impl VrfCrypto for Pair {
		type VrfSignature = VrfSignature;
		type VrfInput = VrfTranscript;
	}

	#[cfg(feature = "full_crypto")]
	impl VrfSigner for Pair {
		fn vrf_sign(&self, transcript: &Self::VrfInput) -> Self::VrfSignature {
			let sign: ThinVrfSignature<0> = self.0.sign_thin_vrf(transcript.0.clone(), &[]);
			let mut raw = [0; SIGNATURE_SERIALIZED_LEN];
			sign.serialize_compressed(raw.as_mut_slice());
			Signature(raw)
		}
	}

	impl VrfCrypto for Public {
		type VrfSignature = VrfSignature;
		type VrfInput = VrfTranscript;
	}

	impl VrfVerifier for Public {
		fn vrf_verify(&self, transcript: &Self::VrfInput, signature: &Self::VrfSignature) -> bool {
			let Ok(public) = PublicKey::deserialize_compressed(self.as_ref()) else {
				return false
			};
			let Ok(signature) = ThinVrfSignature::<0>::deserialize_compressed(signature.as_ref()) else {
				return false
			};

			let inputs: Vec<VrfInput> = Vec::new();
			match signature.verify_thin_vrf(transcript.0.clone(), inputs, &public) {
				Ok(ios) => true,
				Err(e) => false,
			}
		}
	}

	#[cfg(feature = "full_crypto")]
	impl Pair {
		/// Generate bytes from the given VRF configuration.
		pub fn make_bytes<B: Default + AsMut<[u8]>>(
			&self,
			_context: &[u8],
			_transcript: &VrfTranscript,
		) -> B {
			// TODO davxy: the following is for schnorrkel
			// let inout = self.0.vrf_create_hash(transcript.0.clone());
			// inout.make_bytes::<B>(context)
			B::default()
		}
	}

	impl Public {
		/// Generate bytes from the given VRF configuration.
		pub fn make_bytes<B: Default + AsMut<[u8]>>(
			&self,
			_context: &[u8],
			_transcript: &VrfTranscript,
			_output: &VrfPreOut,
		) -> Result<B, codec::Error> {
			// TODO davxy: the following is for schnorrkel
			// let pubkey = schnorrkel::PublicKey::from_bytes(&self.0).map_err(convert_error)?;
			// let inout = output
			// 	.0
			// 	.attach_input_hash(&pubkey, transcript.0.clone())
			// 	.map_err(convert_error)?;
			// Ok(inout.make_bytes::<B>(context))
			Ok(B::default())
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::crypto::DEV_PHRASE;
	const DEV_SEED: &[u8; SEED_SERIALIZED_LEN] = &[0; SEED_SERIALIZED_LEN];

	fn b2h(bytes: &[u8]) -> String {
		array_bytes::bytes2hex("", bytes)
	}

	fn h2b(hex: &str) -> Vec<u8> {
		array_bytes::hex2bytes_unchecked(hex)
	}

	#[test]
	fn backend_assumptions_check() {
		let pair = SecretKey::from_seed(DEV_SEED);
		let public = pair.to_public();

		assert_eq!(public.0.size_of_serialized(), PUBLIC_SERIALIZED_LEN);
	}

	#[test]
	fn derive_hard_known_pair() {
		let pair = Pair::from_string(&format!("{}//Alice", DEV_PHRASE), None).unwrap();
		// known address of DEV_PHRASE with 1.1
		let known = h2b("b0d3648bd5a3542afa16c06fee04cba37cc55c83a8894d36d87897bda0c65eec");
		assert_eq!(pair.public().as_ref(), known);
	}

	#[test]
	fn verify_known_signature() {
		let pair = Pair::from_seed(DEV_SEED);
		let public = pair.public();

		let signature_raw =
	h2b("524b0cbc4eb9579e2cd115fe55e2625e8265b3ea599ac903e67b08c2c669780cf43ca9c1e0a8a63c1dba121a606f95d3466cfe1880acc502c2792775125a7fcc"
	);
		let signature = Signature::from_slice(&signature_raw).unwrap();

		assert!(Pair::verify(&signature, b"hello", &public));
	}

	#[test]
	fn sign_verify() {
		let pair = Pair::from_seed(DEV_SEED);
		let public = pair.public();
		let msg = b"hello";

		let signature = pair.sign(msg);
		assert!(Pair::verify(&signature, msg, &public));
	}

	#[test]
	fn vrf_sign_verify() {
		use super::vrf::*;
		use crate::crypto::{VrfSigner, VrfVerifier};

		let pair = Pair::from_seed(DEV_SEED);
		let public = pair.public();
		let transcript = VrfTranscript::new(b"test", &[b"foo", b"bar"]);

		let signature = pair.vrf_sign(&transcript);

		println!("{}", b2h(signature.as_ref()));

		assert!(public.vrf_verify(&transcript, &signature));
	}

	// #[test]
	// fn vrf_make_bytes_matches() {
	// 	use super::vrf::*;
	// 	use crate::crypto::VrfSigner;
	// 	let pair = Pair::from_seed(DEV_SEED);
	// 	let public = pair.public();
	// 	let transcript = VrfTranscript::new(b"test", &[b"foo", b"bar"]);

	// 	let ctx = b"randbytes";
	// 	let b1 = pair.make_bytes::<[u8; 32]>(ctx, &transcript);
	// }
}
