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

//! Simple sr25519 (Schnorr-Ristretto) API.
//!
//! Note: `CHAIN_CODE_LENGTH` must be equal to `crate::crypto::JUNCTION_ID_LEN`
//! for this to work.

#[cfg(feature = "std")]
use crate::crypto::Ss58Codec;
#[cfg(feature = "full_crypto")]
use crate::crypto::{DeriveError, DeriveJunction, Pair as TraitPair, SecretStringError};
#[cfg(feature = "full_crypto")]
use schnorrkel::{
	derive::{ChainCode, Derivation, CHAIN_CODE_LENGTH},
	signing_context, ExpansionMode, Keypair, MiniSecretKey, PublicKey, SecretKey,
};
use sp_std::vec::Vec;

use crate::{
	crypto::{ByteArray, CryptoType, CryptoTypeId, Derive, Public as TraitPublic, UncheckedFrom},
	hash::{H256, H512},
};
use codec::{Decode, Encode, MaxEncodedLen};
use scale_info::TypeInfo;
use sp_std::ops::Deref;

#[cfg(feature = "full_crypto")]
use schnorrkel::keys::{MINI_SECRET_KEY_LENGTH, SECRET_KEY_LENGTH};
#[cfg(feature = "std")]
use serde::{de, Deserialize, Deserializer, Serialize, Serializer};
use sp_runtime_interface::pass_by::PassByInner;

// signing context
#[cfg(feature = "full_crypto")]
const SIGNING_CTX: &[u8] = b"substrate";

/// An identifier used to match public keys against sr25519 keys
pub const CRYPTO_ID: CryptoTypeId = CryptoTypeId(*b"sr25");

/// An Schnorrkel/Ristretto x25519 ("sr25519") public key.
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
pub struct Public(pub [u8; 32]);

/// An Schnorrkel/Ristretto x25519 ("sr25519") key pair.
#[cfg(feature = "full_crypto")]
pub struct Pair(Keypair);

#[cfg(feature = "full_crypto")]
impl Clone for Pair {
	fn clone(&self) -> Self {
		Pair(schnorrkel::Keypair {
			public: self.0.public,
			secret: schnorrkel::SecretKey::from_bytes(&self.0.secret.to_bytes()[..])
				.expect("key is always the correct size; qed"),
		})
	}
}

impl AsRef<[u8; 32]> for Public {
	fn as_ref(&self) -> &[u8; 32] {
		&self.0
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

impl Deref for Public {
	type Target = [u8];

	fn deref(&self) -> &Self::Target {
		&self.0
	}
}

impl From<Public> for [u8; 32] {
	fn from(x: Public) -> [u8; 32] {
		x.0
	}
}

impl From<Public> for H256 {
	fn from(x: Public) -> H256 {
		x.0.into()
	}
}

#[cfg(feature = "std")]
impl std::str::FromStr for Public {
	type Err = crate::crypto::PublicError;

	fn from_str(s: &str) -> Result<Self, Self::Err> {
		Self::from_ss58check(s)
	}
}

impl TryFrom<&[u8]> for Public {
	type Error = ();

	fn try_from(data: &[u8]) -> Result<Self, Self::Error> {
		if data.len() != Self::LEN {
			return Err(())
		}
		let mut r = [0u8; 32];
		r.copy_from_slice(data);
		Ok(Self::unchecked_from(r))
	}
}

impl UncheckedFrom<[u8; 32]> for Public {
	fn unchecked_from(x: [u8; 32]) -> Self {
		Public::from_raw(x)
	}
}

impl UncheckedFrom<H256> for Public {
	fn unchecked_from(x: H256) -> Self {
		Public::from_h256(x)
	}
}

#[cfg(feature = "std")]
impl std::fmt::Display for Public {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		write!(f, "{}", self.to_ss58check())
	}
}

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

#[cfg(feature = "std")]
impl Serialize for Public {
	fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
	where
		S: Serializer,
	{
		serializer.serialize_str(&self.to_ss58check())
	}
}

#[cfg(feature = "std")]
impl<'de> Deserialize<'de> for Public {
	fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
	where
		D: Deserializer<'de>,
	{
		Public::from_ss58check(&String::deserialize(deserializer)?)
			.map_err(|e| de::Error::custom(format!("{:?}", e)))
	}
}

/// An Schnorrkel/Ristretto x25519 ("sr25519") signature.
#[cfg_attr(feature = "full_crypto", derive(Hash))]
#[derive(Encode, Decode, MaxEncodedLen, PassByInner, TypeInfo, PartialEq, Eq)]
pub struct Signature(pub [u8; 64]);

impl TryFrom<&[u8]> for Signature {
	type Error = ();

	fn try_from(data: &[u8]) -> Result<Self, Self::Error> {
		if data.len() == 64 {
			let mut inner = [0u8; 64];
			inner.copy_from_slice(data);
			Ok(Signature(inner))
		} else {
			Err(())
		}
	}
}

#[cfg(feature = "std")]
impl Serialize for Signature {
	fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
	where
		S: Serializer,
	{
		serializer.serialize_str(&array_bytes::bytes2hex("", self.as_ref()))
	}
}

#[cfg(feature = "std")]
impl<'de> Deserialize<'de> for Signature {
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

impl Clone for Signature {
	fn clone(&self) -> Self {
		let mut r = [0u8; 64];
		r.copy_from_slice(&self.0[..]);
		Signature(r)
	}
}

impl From<Signature> for [u8; 64] {
	fn from(v: Signature) -> [u8; 64] {
		v.0
	}
}

impl From<Signature> for H512 {
	fn from(v: Signature) -> H512 {
		H512::from(v.0)
	}
}

impl AsRef<[u8; 64]> for Signature {
	fn as_ref(&self) -> &[u8; 64] {
		&self.0
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

#[cfg(feature = "full_crypto")]
impl From<schnorrkel::Signature> for Signature {
	fn from(s: schnorrkel::Signature) -> Signature {
		Signature(s.to_bytes())
	}
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

impl UncheckedFrom<[u8; 64]> for Signature {
	fn unchecked_from(data: [u8; 64]) -> Signature {
		Signature(data)
	}
}

impl Signature {
	/// A new instance from the given 64-byte `data`.
	///
	/// NOTE: No checking goes on to ensure this is a real signature. Only use
	/// it if you are certain that the array actually is a signature, or if you
	/// immediately verify the signature.  All functions that verify signatures
	/// will fail if the `Signature` is not actually a valid signature.
	pub fn from_raw(data: [u8; 64]) -> Signature {
		Signature(data)
	}

	/// A new instance from the given slice that should be 64 bytes long.
	///
	/// NOTE: No checking goes on to ensure this is a real signature. Only use it if
	/// you are certain that the array actually is a signature. GIGO!
	pub fn from_slice(data: &[u8]) -> Option<Self> {
		if data.len() != 64 {
			return None
		}
		let mut r = [0u8; 64];
		r.copy_from_slice(data);
		Some(Signature(r))
	}

	/// A new instance from an H512.
	///
	/// NOTE: No checking goes on to ensure this is a real signature. Only use it if
	/// you are certain that the array actually is a signature. GIGO!
	pub fn from_h512(v: H512) -> Signature {
		Signature(v.into())
	}
}

impl Derive for Public {
	/// Derive a child key from a series of given junctions.
	///
	/// `None` if there are any hard junctions in there.
	#[cfg(feature = "std")]
	fn derive<Iter: Iterator<Item = DeriveJunction>>(&self, path: Iter) -> Option<Public> {
		let mut acc = PublicKey::from_bytes(self.as_ref()).ok()?;
		for j in path {
			match j {
				DeriveJunction::Soft(cc) => acc = acc.derived_key_simple(ChainCode(cc), &[]).0,
				DeriveJunction::Hard(_cc) => return None,
			}
		}
		Some(Self(acc.to_bytes()))
	}
}

impl Public {
	/// A new instance from the given 32-byte `data`.
	///
	/// NOTE: No checking goes on to ensure this is a real public key. Only use it if
	/// you are certain that the array actually is a pubkey. GIGO!
	pub fn from_raw(data: [u8; 32]) -> Self {
		Public(data)
	}

	/// A new instance from an H256.
	///
	/// NOTE: No checking goes on to ensure this is a real public key. Only use it if
	/// you are certain that the array actually is a pubkey. GIGO!
	pub fn from_h256(x: H256) -> Self {
		Public(x.into())
	}

	/// Return a slice filled with raw data.
	pub fn as_array_ref(&self) -> &[u8; 32] {
		self.as_ref()
	}
}

impl ByteArray for Public {
	const LEN: usize = 32;
}

impl TraitPublic for Public {}

#[cfg(feature = "std")]
impl From<MiniSecretKey> for Pair {
	fn from(sec: MiniSecretKey) -> Pair {
		Pair(sec.expand_to_keypair(ExpansionMode::Ed25519))
	}
}

#[cfg(feature = "std")]
impl From<SecretKey> for Pair {
	fn from(sec: SecretKey) -> Pair {
		Pair(Keypair::from(sec))
	}
}

#[cfg(feature = "full_crypto")]
impl From<schnorrkel::Keypair> for Pair {
	fn from(p: schnorrkel::Keypair) -> Pair {
		Pair(p)
	}
}

#[cfg(feature = "full_crypto")]
impl From<Pair> for schnorrkel::Keypair {
	fn from(p: Pair) -> schnorrkel::Keypair {
		p.0
	}
}

#[cfg(feature = "full_crypto")]
impl AsRef<schnorrkel::Keypair> for Pair {
	fn as_ref(&self) -> &schnorrkel::Keypair {
		&self.0
	}
}

/// Derive a single hard junction.
#[cfg(feature = "full_crypto")]
fn derive_hard_junction(secret: &SecretKey, cc: &[u8; CHAIN_CODE_LENGTH]) -> MiniSecretKey {
	secret.hard_derive_mini_secret_key(Some(ChainCode(*cc)), b"").0
}

/// The raw secret seed, which can be used to recreate the `Pair`.
#[cfg(feature = "full_crypto")]
type Seed = [u8; MINI_SECRET_KEY_LENGTH];

#[cfg(feature = "full_crypto")]
impl TraitPair for Pair {
	type Public = Public;
	type Seed = Seed;
	type Signature = Signature;

	/// Get the public key.
	fn public(&self) -> Public {
		let mut pk = [0u8; 32];
		pk.copy_from_slice(&self.0.public.to_bytes());
		Public(pk)
	}

	/// Make a new key pair from raw secret seed material.
	///
	/// This is generated using schnorrkel's Mini-Secret-Keys.
	///
	/// A `MiniSecretKey` is literally what Ed25519 calls a `SecretKey`, which is just 32 random
	/// bytes.
	fn from_seed_slice(seed: &[u8]) -> Result<Pair, SecretStringError> {
		match seed.len() {
			MINI_SECRET_KEY_LENGTH => Ok(Pair(
				MiniSecretKey::from_bytes(seed)
					.map_err(|_| SecretStringError::InvalidSeed)?
					.expand_to_keypair(ExpansionMode::Ed25519),
			)),
			SECRET_KEY_LENGTH => Ok(Pair(
				SecretKey::from_bytes(seed)
					.map_err(|_| SecretStringError::InvalidSeed)?
					.to_keypair(),
			)),
			_ => Err(SecretStringError::InvalidSeedLength),
		}
	}

	fn derive<Iter: Iterator<Item = DeriveJunction>>(
		&self,
		path: Iter,
		seed: Option<Seed>,
	) -> Result<(Pair, Option<Seed>), DeriveError> {
		let seed = seed
			.and_then(|s| MiniSecretKey::from_bytes(&s).ok())
			.filter(|msk| msk.expand(ExpansionMode::Ed25519) == self.0.secret);

		let init = self.0.secret.clone();
		let (result, seed) = path.fold((init, seed), |(acc, acc_seed), j| match (j, acc_seed) {
			(DeriveJunction::Soft(cc), _) => (acc.derived_key_simple(ChainCode(cc), &[]).0, None),
			(DeriveJunction::Hard(cc), maybe_seed) => {
				let seed = derive_hard_junction(&acc, &cc);
				(seed.expand(ExpansionMode::Ed25519), maybe_seed.map(|_| seed))
			},
		});
		Ok((Self(result.into()), seed.map(|s| MiniSecretKey::to_bytes(&s))))
	}

	fn sign(&self, message: &[u8]) -> Signature {
		let context = signing_context(SIGNING_CTX);
		self.0.sign(context.bytes(message)).into()
	}

	fn verify<M: AsRef<[u8]>>(sig: &Self::Signature, message: M, pubkey: &Self::Public) -> bool {
		let Ok(signature) = schnorrkel::Signature::from_bytes(sig.as_ref()) else {
			return false
		};
		let Ok(public) = PublicKey::from_bytes(pubkey.as_ref()) else {
			return false
		};
		public.verify_simple(SIGNING_CTX, message.as_ref(), &signature).is_ok()
	}

	fn to_raw_vec(&self) -> Vec<u8> {
		self.0.secret.to_bytes().to_vec()
	}
}

#[cfg(feature = "std")]
impl Pair {
	/// Verify a signature on a message. Returns `true` if the signature is good.
	/// Supports old 0.1.1 deprecated signatures and should be used only for backward
	/// compatibility.
	pub fn verify_deprecated<M: AsRef<[u8]>>(sig: &Signature, message: M, pubkey: &Public) -> bool {
		// Match both schnorrkel 0.1.1 and 0.8.0+ signatures, supporting both wallets
		// that have not been upgraded and those that have.
		match PublicKey::from_bytes(pubkey.as_ref()) {
			Ok(pk) => pk
				.verify_simple_preaudit_deprecated(SIGNING_CTX, message.as_ref(), &sig.0[..])
				.is_ok(),
			Err(_) => false,
		}
	}
}

impl CryptoType for Public {
	#[cfg(feature = "full_crypto")]
	type Pair = Pair;
}

impl CryptoType for Signature {
	#[cfg(feature = "full_crypto")]
	type Pair = Pair;
}

#[cfg(feature = "full_crypto")]
impl CryptoType for Pair {
	type Pair = Pair;
}

/// Schnorrkel VRF related types and operations.
pub mod vrf {
	use super::*;
	#[cfg(feature = "full_crypto")]
	use crate::crypto::VrfSigner;
	use crate::crypto::{VrfCrypto, VrfVerifier};
	use schnorrkel::{
		errors::MultiSignatureStage,
		vrf::{VRF_OUTPUT_LENGTH, VRF_PROOF_LENGTH},
		SignatureError,
	};

	/// VRF transcript ready to be used for VRF sign/verify operations.
	pub struct VrfTranscript(pub merlin::Transcript);

	impl VrfTranscript {
		/// Build a new transcript ready to be used by a VRF signer/verifier.
		pub fn new(label: &'static [u8], data: &[(&'static [u8], &[u8])]) -> Self {
			let mut transcript = merlin::Transcript::new(label);
			data.iter().for_each(|(l, b)| transcript.append_message(l, b));
			VrfTranscript(transcript)
		}
	}

	/// VRF signature data
	#[derive(Clone, Debug, PartialEq, Eq, Encode, Decode, MaxEncodedLen, TypeInfo)]
	pub struct VrfSignature {
		/// The initial VRF configuration
		pub output: VrfOutput,
		/// The calculated VRF proof
		pub proof: VrfProof,
	}

	/// VRF output type suitable for schnorrkel operations.
	#[derive(Clone, Debug, PartialEq, Eq)]
	pub struct VrfOutput(pub schnorrkel::vrf::VRFOutput);

	impl Encode for VrfOutput {
		fn encode(&self) -> Vec<u8> {
			self.0.as_bytes().encode()
		}
	}

	impl Decode for VrfOutput {
		fn decode<R: codec::Input>(i: &mut R) -> Result<Self, codec::Error> {
			let decoded = <[u8; VRF_OUTPUT_LENGTH]>::decode(i)?;
			Ok(Self(schnorrkel::vrf::VRFOutput::from_bytes(&decoded).map_err(convert_error)?))
		}
	}

	impl MaxEncodedLen for VrfOutput {
		fn max_encoded_len() -> usize {
			<[u8; VRF_OUTPUT_LENGTH]>::max_encoded_len()
		}
	}

	impl TypeInfo for VrfOutput {
		type Identity = [u8; VRF_OUTPUT_LENGTH];

		fn type_info() -> scale_info::Type {
			Self::Identity::type_info()
		}
	}

	/// VRF proof type suitable for schnorrkel operations.
	#[derive(Clone, Debug, PartialEq, Eq)]
	pub struct VrfProof(pub schnorrkel::vrf::VRFProof);

	impl Encode for VrfProof {
		fn encode(&self) -> Vec<u8> {
			self.0.to_bytes().encode()
		}
	}

	impl Decode for VrfProof {
		fn decode<R: codec::Input>(i: &mut R) -> Result<Self, codec::Error> {
			let decoded = <[u8; VRF_PROOF_LENGTH]>::decode(i)?;
			Ok(Self(schnorrkel::vrf::VRFProof::from_bytes(&decoded).map_err(convert_error)?))
		}
	}

	impl MaxEncodedLen for VrfProof {
		fn max_encoded_len() -> usize {
			<[u8; VRF_PROOF_LENGTH]>::max_encoded_len()
		}
	}

	impl TypeInfo for VrfProof {
		type Identity = [u8; VRF_PROOF_LENGTH];

		fn type_info() -> scale_info::Type {
			Self::Identity::type_info()
		}
	}

	#[cfg(feature = "full_crypto")]
	impl VrfCrypto for Pair {
		type VrfSignature = VrfSignature;
		type VrfInput = VrfTranscript;
	}

	#[cfg(feature = "full_crypto")]
	impl VrfSigner for Pair {
		fn vrf_sign(&self, transcript: &Self::VrfInput) -> Self::VrfSignature {
			let (inout, proof, _) = self.0.vrf_sign(transcript.0.clone());
			VrfSignature { output: VrfOutput(inout.to_output()), proof: VrfProof(proof) }
		}
	}

	impl VrfCrypto for Public {
		type VrfSignature = VrfSignature;
		type VrfInput = VrfTranscript;
	}

	impl VrfVerifier for Public {
		fn vrf_verify(&self, transcript: &Self::VrfInput, signature: &Self::VrfSignature) -> bool {
			schnorrkel::PublicKey::from_bytes(self)
				.and_then(|public| {
					public.vrf_verify(transcript.0.clone(), &signature.output.0, &signature.proof.0)
				})
				.is_ok()
		}
	}

	fn convert_error(e: SignatureError) -> codec::Error {
		use MultiSignatureStage::*;
		use SignatureError::*;
		match e {
			EquationFalse => "Signature error: `EquationFalse`".into(),
			PointDecompressionError => "Signature error: `PointDecompressionError`".into(),
			ScalarFormatError => "Signature error: `ScalarFormatError`".into(),
			NotMarkedSchnorrkel => "Signature error: `NotMarkedSchnorrkel`".into(),
			BytesLengthError { .. } => "Signature error: `BytesLengthError`".into(),
			MuSigAbsent { musig_stage: Commitment } =>
				"Signature error: `MuSigAbsent` at stage `Commitment`".into(),
			MuSigAbsent { musig_stage: Reveal } =>
				"Signature error: `MuSigAbsent` at stage `Reveal`".into(),
			MuSigAbsent { musig_stage: Cosignature } =>
				"Signature error: `MuSigAbsent` at stage `Commitment`".into(),
			MuSigInconsistent { musig_stage: Commitment, duplicate: true } =>
				"Signature error: `MuSigInconsistent` at stage `Commitment` on duplicate".into(),
			MuSigInconsistent { musig_stage: Commitment, duplicate: false } =>
				"Signature error: `MuSigInconsistent` at stage `Commitment` on not duplicate".into(),
			MuSigInconsistent { musig_stage: Reveal, duplicate: true } =>
				"Signature error: `MuSigInconsistent` at stage `Reveal` on duplicate".into(),
			MuSigInconsistent { musig_stage: Reveal, duplicate: false } =>
				"Signature error: `MuSigInconsistent` at stage `Reveal` on not duplicate".into(),
			MuSigInconsistent { musig_stage: Cosignature, duplicate: true } =>
				"Signature error: `MuSigInconsistent` at stage `Cosignature` on duplicate".into(),
			MuSigInconsistent { musig_stage: Cosignature, duplicate: false } =>
				"Signature error: `MuSigInconsistent` at stage `Cosignature` on not duplicate"
					.into(),
		}
	}

	#[cfg(feature = "full_crypto")]
	impl Pair {
		/// Generate bytes from the given VRF configuration.
		pub fn make_bytes<B: Default + AsMut<[u8]>>(
			&self,
			context: &[u8],
			transcript: &VrfTranscript,
		) -> B {
			let inout = self.0.vrf_create_hash(transcript.0.clone());
			inout.make_bytes::<B>(context)
		}
	}

	impl Public {
		/// Generate bytes from the given VRF configuration.
		pub fn make_bytes<B: Default + AsMut<[u8]>>(
			&self,
			context: &[u8],
			transcript: &VrfTranscript,
			output: &VrfOutput,
		) -> Result<B, codec::Error> {
			let pubkey = schnorrkel::PublicKey::from_bytes(&self.0).map_err(convert_error)?;
			let inout = output
				.0
				.attach_input_hash(&pubkey, transcript.0.clone())
				.map_err(convert_error)?;
			Ok(inout.make_bytes::<B>(context))
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::crypto::{Ss58Codec, DEV_ADDRESS, DEV_PHRASE};
	use serde_json;

	#[test]
	fn derive_soft_known_pair_should_work() {
		let pair = Pair::from_string(&format!("{}/Alice", DEV_PHRASE), None).unwrap();
		// known address of DEV_PHRASE with 1.1
		let known = array_bytes::hex2bytes_unchecked(
			"d6c71059dbbe9ad2b0ed3f289738b800836eb425544ce694825285b958ca755e",
		);
		assert_eq!(pair.public().to_raw_vec(), known);
	}

	#[test]
	fn derive_hard_known_pair_should_work() {
		let pair = Pair::from_string(&format!("{}//Alice", DEV_PHRASE), None).unwrap();
		// known address of DEV_PHRASE with 1.1
		let known = array_bytes::hex2bytes_unchecked(
			"d43593c715fdd31c61141abd04a99fd6822c8558854ccde39a5684e7a56da27d",
		);
		assert_eq!(pair.public().to_raw_vec(), known);
	}

	#[test]
	fn verify_known_old_message_should_work() {
		let public = Public::from_raw(array_bytes::hex2array_unchecked(
			"b4bfa1f7a5166695eb75299fd1c4c03ea212871c342f2c5dfea0902b2c246918",
		));
		// signature generated by the 1.1 version with the same ^^ public key.
		let signature = Signature::from_raw(array_bytes::hex2array_unchecked(
			"5a9755f069939f45d96aaf125cf5ce7ba1db998686f87f2fb3cbdea922078741a73891ba265f70c31436e18a9acd14d189d73c12317ab6c313285cd938453202"
		));
		let message = b"Verifying that I am the owner of 5G9hQLdsKQswNPgB499DeA5PkFBbgkLPJWkkS6FAM6xGQ8xD. Hash: 221455a3\n";
		assert!(Pair::verify_deprecated(&signature, &message[..], &public));
		assert!(!Pair::verify(&signature, &message[..], &public));
	}

	#[test]
	fn default_phrase_should_be_used() {
		assert_eq!(
			Pair::from_string("//Alice///password", None).unwrap().public(),
			Pair::from_string(&format!("{}//Alice", DEV_PHRASE), Some("password"))
				.unwrap()
				.public(),
		);
		assert_eq!(
			Pair::from_string(&format!("{}/Alice", DEV_PHRASE), None)
				.as_ref()
				.map(Pair::public),
			Pair::from_string("/Alice", None).as_ref().map(Pair::public)
		);
	}

	#[test]
	fn default_address_should_be_used() {
		assert_eq!(
			Public::from_string(&format!("{}/Alice", DEV_ADDRESS)),
			Public::from_string("/Alice")
		);
	}

	#[test]
	fn default_phrase_should_correspond_to_default_address() {
		assert_eq!(
			Pair::from_string(&format!("{}/Alice", DEV_PHRASE), None).unwrap().public(),
			Public::from_string(&format!("{}/Alice", DEV_ADDRESS)).unwrap(),
		);
		assert_eq!(
			Pair::from_string("/Alice", None).unwrap().public(),
			Public::from_string("/Alice").unwrap()
		);
	}

	#[test]
	fn derive_soft_should_work() {
		let pair = Pair::from_seed(&array_bytes::hex2array_unchecked(
			"9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60",
		));
		let derive_1 = pair.derive(Some(DeriveJunction::soft(1)).into_iter(), None).unwrap().0;
		let derive_1b = pair.derive(Some(DeriveJunction::soft(1)).into_iter(), None).unwrap().0;
		let derive_2 = pair.derive(Some(DeriveJunction::soft(2)).into_iter(), None).unwrap().0;
		assert_eq!(derive_1.public(), derive_1b.public());
		assert_ne!(derive_1.public(), derive_2.public());
	}

	#[test]
	fn derive_hard_should_work() {
		let pair = Pair::from_seed(&array_bytes::hex2array_unchecked(
			"9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60",
		));
		let derive_1 = pair.derive(Some(DeriveJunction::hard(1)).into_iter(), None).unwrap().0;
		let derive_1b = pair.derive(Some(DeriveJunction::hard(1)).into_iter(), None).unwrap().0;
		let derive_2 = pair.derive(Some(DeriveJunction::hard(2)).into_iter(), None).unwrap().0;
		assert_eq!(derive_1.public(), derive_1b.public());
		assert_ne!(derive_1.public(), derive_2.public());
	}

	#[test]
	fn derive_soft_public_should_work() {
		let pair = Pair::from_seed(&array_bytes::hex2array_unchecked(
			"9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60",
		));
		let path = Some(DeriveJunction::soft(1));
		let pair_1 = pair.derive(path.into_iter(), None).unwrap().0;
		let public_1 = pair.public().derive(path.into_iter()).unwrap();
		assert_eq!(pair_1.public(), public_1);
	}

	#[test]
	fn derive_hard_public_should_fail() {
		let pair = Pair::from_seed(&array_bytes::hex2array_unchecked(
			"9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60",
		));
		let path = Some(DeriveJunction::hard(1));
		assert!(pair.public().derive(path.into_iter()).is_none());
	}

	#[test]
	fn sr_test_vector_should_work() {
		let pair = Pair::from_seed(&array_bytes::hex2array_unchecked(
			"9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60",
		));
		let public = pair.public();
		assert_eq!(
			public,
			Public::from_raw(array_bytes::hex2array_unchecked(
				"44a996beb1eef7bdcab976ab6d2ca26104834164ecf28fb375600576fcc6eb0f"
			))
		);
		let message = b"";
		let signature = pair.sign(message);
		assert!(Pair::verify(&signature, &message[..], &public));
	}

	#[test]
	fn generated_pair_should_work() {
		let (pair, _) = Pair::generate();
		let public = pair.public();
		let message = b"Something important";
		let signature = pair.sign(&message[..]);
		assert!(Pair::verify(&signature, &message[..], &public));
	}

	#[test]
	fn messed_signature_should_not_work() {
		let (pair, _) = Pair::generate();
		let public = pair.public();
		let message = b"Signed payload";
		let Signature(mut bytes) = pair.sign(&message[..]);
		bytes[0] = !bytes[0];
		bytes[2] = !bytes[2];
		let signature = Signature(bytes);
		assert!(!Pair::verify(&signature, &message[..], &public));
	}

	#[test]
	fn messed_message_should_not_work() {
		let (pair, _) = Pair::generate();
		let public = pair.public();
		let message = b"Something important";
		let signature = pair.sign(&message[..]);
		assert!(!Pair::verify(&signature, &b"Something unimportant", &public));
	}

	#[test]
	fn seeded_pair_should_work() {
		let pair = Pair::from_seed(b"12345678901234567890123456789012");
		let public = pair.public();
		assert_eq!(
			public,
			Public::from_raw(array_bytes::hex2array_unchecked(
				"741c08a06f41c596608f6774259bd9043304adfa5d3eea62760bd9be97634d63"
			))
		);
		let message = array_bytes::hex2bytes_unchecked("2f8c6129d816cf51c374bc7f08c3e63ed156cf78aefb4a6550d97b87997977ee00000000000000000200d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a4500000000000000");
		let signature = pair.sign(&message[..]);
		assert!(Pair::verify(&signature, &message[..], &public));
	}

	#[test]
	fn ss58check_roundtrip_works() {
		let (pair, _) = Pair::generate();
		let public = pair.public();
		let s = public.to_ss58check();
		println!("Correct: {}", s);
		let cmp = Public::from_ss58check(&s).unwrap();
		assert_eq!(cmp, public);
	}

	#[test]
	fn verify_from_old_wasm_works() {
		// The values in this test case are compared to the output of `node-test.js` in
		// schnorrkel-js.
		//
		// This is to make sure that the wasm library is compatible.
		let pk = Pair::from_seed(&array_bytes::hex2array_unchecked(
			"0000000000000000000000000000000000000000000000000000000000000000",
		));
		let public = pk.public();
		let js_signature = Signature::from_raw(array_bytes::hex2array_unchecked(
			"28a854d54903e056f89581c691c1f7d2ff39f8f896c9e9c22475e60902cc2b3547199e0e91fa32902028f2ca2355e8cdd16cfe19ba5e8b658c94aa80f3b81a00"
		));
		assert!(Pair::verify_deprecated(&js_signature, b"SUBSTRATE", &public));
		assert!(!Pair::verify(&js_signature, b"SUBSTRATE", &public));
	}

	#[test]
	fn signature_serialization_works() {
		let pair = Pair::from_seed(b"12345678901234567890123456789012");
		let message = b"Something important";
		let signature = pair.sign(&message[..]);
		let serialized_signature = serde_json::to_string(&signature).unwrap();
		// Signature is 64 bytes, so 128 chars + 2 quote chars
		assert_eq!(serialized_signature.len(), 130);
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

	#[test]
	fn vrf_make_bytes_matches() {
		use super::vrf::*;
		use crate::crypto::VrfSigner;
		let pair = Pair::from_seed(b"12345678901234567890123456789012");
		let public = pair.public();
		let transcript = VrfTranscript::new(b"test", &[(b"foo", b"bar")]);

		let signature = pair.vrf_sign(&transcript);

		let ctx = b"randbytes";
		let b1 = pair.make_bytes::<[u8; 32]>(ctx, &transcript);
		let b2 = public.make_bytes::<[u8; 32]>(ctx, &transcript, &signature.output).unwrap();
		assert_eq!(b1, b2);
	}
}
