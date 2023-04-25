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

// #![allow(unused)]

#[cfg(feature = "std")]
use crate::crypto::Ss58Codec;
use crate::crypto::{
	ByteArray, CryptoType, CryptoTypeId, Derive, Public as TraitPublic, UncheckedFrom, VrfVerifier,
};
#[cfg(feature = "full_crypto")]
use crate::crypto::{DeriveError, DeriveJunction, Pair as TraitPair, SecretStringError, VrfSigner};

#[cfg(feature = "full_crypto")]
use bandersnatch_vrfs::SecretKey;
use codec::{Decode, Encode, MaxEncodedLen};
use scale_info::TypeInfo;

use sp_runtime_interface::pass_by::PassByInner;
use sp_std::{boxed::Box, vec::Vec};

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

	/// Sign raw data.
	fn sign(&self, data: &[u8]) -> Signature {
		let input = vrf::VrfInput::new(SIGNING_CTX, &[data], &[])
			.expect("less than max input messages; qed");
		self.vrf_sign(&input).signature
	}

	/// Verify a signature on a message.
	///
	/// Returns true if the signature is good.
	fn verify<M: AsRef<[u8]>>(signature: &Self::Signature, data: M, public: &Self::Public) -> bool {
		let input = vrf::VrfInput::new(SIGNING_CTX, &[data.as_ref()], &[])
			.expect("less than max input messages; qed");
		let signature = vrf::VrfSignature { signature: signature.clone(), preouts: Box::new([]) };
		public.vrf_verify(&input, &signature)
	}

	/// Return a vec filled with seed raw data.
	fn to_raw_vec(&self) -> Vec<u8> {
		// TODO davxy: makes sense??? Should we returne the seed or serialized secret key?
		// If we return the serialized secret there is no method to reconstruct if ...
		// unimplemented!()
		panic!()
	}
}

#[cfg(feature = "full_crypto")]
impl CryptoType for Pair {
	type Pair = Pair;
}

/// VRF related types and operations.
pub mod vrf {
	use super::*;
	use crate::crypto::VrfCrypto;
	#[cfg(feature = "full_crypto")]
	use bandersnatch_vrfs::CanonicalSerialize;
	use bandersnatch_vrfs::{
		CanonicalDeserialize, IntoVrfInput, PublicKey, ThinVrfSignature, Transcript,
	};

	const MAX_VRF_INPUT_MESSAGES: usize = 3;

	/// Input to be used for VRF sign and verify operations.
	pub struct VrfInput {
		/// Associated Fiat-Shamir transcript
		pub(super) transcript: Transcript,
		/// VRF input messages
		pub(super) messages: Box<[bandersnatch_vrfs::VrfInput]>,
	}

	impl VrfInput {
		/// Build a new VRF input ready to be used by VRF sign and verify operations.
		///
		/// Returns `None` if `messages.len() > MAX_VRF_INPUT_MESSAGES`.
		pub fn new(
			label: &'static [u8],
			transcript_data: &[&[u8]],
			messages: &[(&[u8], &[u8])],
		) -> Option<Self> {
			if messages.len() > MAX_VRF_INPUT_MESSAGES {
				return None
			}
			let mut transcript = Transcript::new(label);
			transcript_data.iter().for_each(|b| transcript.append_slice(b));
			let messages = messages
				.into_iter()
				.map(|(domain, message)| {
					bandersnatch_vrfs::Message { domain, message }.into_vrf_input()
				})
				.collect();
			Some(VrfInput { transcript, messages })
		}
	}

	/// TODO davxy: docs
	pub struct VrfSignature {
		/// VRF signature
		pub(super) signature: Signature,
		/// VRF pre-outputs
		pub(super) preouts: Box<[bandersnatch_vrfs::VrfPreOut]>,
	}

	#[cfg(feature = "full_crypto")]
	impl VrfCrypto for Pair {
		type VrfSignature = VrfSignature;
		type VrfInput = VrfInput;
	}

	#[cfg(feature = "full_crypto")]
	impl VrfSigner for Pair {
		fn vrf_sign(&self, input: &Self::VrfInput) -> Self::VrfSignature {
			// Hack used because backend signature type is generic over the number of ios
			// @burdges can we provide a vec or boxed version?
			match input.messages.len() {
				0 => self.vrf_sign_gen::<0>(input),
				1 => self.vrf_sign_gen::<1>(input),
				2 => self.vrf_sign_gen::<2>(input),
				3 => self.vrf_sign_gen::<3>(input),
				_ => panic!("Max VRF input messages is set to: {}", MAX_VRF_INPUT_MESSAGES),
			}
		}
	}

	impl VrfCrypto for Public {
		type VrfSignature = VrfSignature;
		type VrfInput = VrfInput;
	}

	impl VrfVerifier for Public {
		fn vrf_verify(&self, input: &Self::VrfInput, signature: &Self::VrfSignature) -> bool {
			let preouts_len = signature.preouts.len();
			if preouts_len != input.messages.len() {
				return false
			}
			// Hack used because backend signature type is generic over the number of ios
			// @burdges can we provide a vec or boxed version?
			match preouts_len {
				0 => self.vrf_verify_gen::<0>(input, signature),
				1 => self.vrf_verify_gen::<1>(input, signature),
				2 => self.vrf_verify_gen::<2>(input, signature),
				3 => self.vrf_verify_gen::<3>(input, signature),
				_ => panic!("Max VRF input messages is set to: {}", MAX_VRF_INPUT_MESSAGES),
			}
		}
	}

	#[cfg(feature = "full_crypto")]
	impl Pair {
		fn vrf_sign_gen<const N: usize>(&self, input: &VrfInput) -> VrfSignature {
			let ios: Vec<_> =
				input.messages.iter().map(|i| self.0.clone().0.vrf_inout(i.clone())).collect();

			let sign: ThinVrfSignature<N> =
				self.0.sign_thin_vrf(input.transcript.clone(), ios.as_slice());

			let mut sign_bytes = [0; SIGNATURE_SERIALIZED_LEN];
			// TODO davxy: use ark-scale???
			sign.signature
				.serialize_compressed(sign_bytes.as_mut_slice())
				.expect("serialization can't fail");
			VrfSignature { signature: Signature(sign_bytes), preouts: Box::new(sign.preoutputs) }
		}

		/// Generate output bytes from the given VRF input.
		///
		/// Index is relative to one of the `VrfInput` messages used during construction.
		pub fn output_bytes<const N: usize>(
			&self,
			input: &VrfInput,
			index: usize,
		) -> Option<[u8; N]> {
			let msg = input.messages.get(index)?.clone();
			let inout = self.0.clone().0.vrf_inout(msg);
			let bytes = inout.vrf_output_bytes(input.transcript.clone());
			Some(bytes)
		}
	}

	impl Public {
		fn vrf_verify_gen<const N: usize>(
			&self,
			input: &VrfInput,
			signature: &VrfSignature,
		) -> bool {
			let Ok(public) = PublicKey::deserialize_compressed(self.as_ref()) else {
				return false
			};

			let Ok(preouts) = signature
				.preouts
				.iter()
				.map(|o| o.clone())
				.collect::<arrayvec::ArrayVec<bandersnatch_vrfs::VrfPreOut, N>>()
				.into_inner() else {
					return false
				};

			// Deserialize only the proof, the rest has already been deserialized
			// This is another hack used because backend signature type is generic over the number
			// of ios. @burdges can we provide a vec or boxed version?
			let Ok(signature) = ThinVrfSignature::<0>::deserialize_compressed(signature.signature.as_ref()).map(|s| s.signature) else {
				return false
			};
			let signature = ThinVrfSignature { signature, preoutputs: preouts };

			let inputs = input.messages.clone().into_vec();

			signature.verify_thin_vrf(input.transcript.clone(), inputs, &public).is_ok()
		}
	}

	impl VrfSignature {
		/// Generate output bytes for the given VRF input.
		pub fn output_bytes<const N: usize>(
			&self,
			input: &VrfInput,
			index: usize,
		) -> Option<[u8; N]> {
			let inout = bandersnatch_vrfs::VrfInOut {
				input: input.messages.get(index)?.clone().into_vrf_input(),
				preoutput: self.preouts.get(index)?.clone(),
			};
			let bytes = inout.vrf_output_bytes(input.transcript.clone());
			Some(bytes)
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
		// let input = VrfInput::new(b"test", &[b"foo", b"bar"], &[]);
		let input = VrfInput::new(b"test", &[b"foo", b"bar"], &[(b"msg1", b"hello")]).unwrap();

		let signature = pair.vrf_sign(&input);

		assert!(public.vrf_verify(&input, &signature));
	}

	#[test]
	fn vrf_sign_verify_bad_inputs() {
		use super::vrf::*;
		use crate::crypto::{VrfSigner, VrfVerifier};

		let pair = Pair::from_seed(DEV_SEED);
		let public = pair.public();

		let input = VrfInput::new(b"test", &[b"foo", b"bar"], &[(b"msg1", b"hello")]).unwrap();

		let signature = pair.vrf_sign(&input);

		let input = VrfInput::new(b"test", &[b"foo", b"bar"], &[]).unwrap();
		assert!(!public.vrf_verify(&input, &signature));
	}

	#[test]
	fn vrf_make_bytes_matches() {
		use super::vrf::*;
		let pair = Pair::from_seed(DEV_SEED);

		let input = VrfInput::new(
			b"test",
			&[b"proto", b"foo"],
			&[(b"dom1", b"dat1"), (b"dom2", b"dat2"), (b"dom3", b"dat3")],
		)
		.unwrap();

		let sign = pair.vrf_sign(&input);

		let out0 = pair.output_bytes::<32>(&input, 0).unwrap();
		let out1 = sign.output_bytes::<32>(&input, 0).unwrap();
		assert_eq!(out0, out1);

		let out0 = pair.output_bytes::<48>(&input, 1).unwrap();
		let out1 = sign.output_bytes::<48>(&input, 1).unwrap();
		assert_eq!(out0, out1);

		let out0 = pair.output_bytes::<64>(&input, 2).unwrap();
		let out1 = sign.output_bytes::<64>(&input, 2).unwrap();
		assert_eq!(out0, out1);

		assert!(pair.output_bytes::<8>(&input, 3).is_none());
		assert!(sign.output_bytes::<8>(&input, 3).is_none());
	}
}
