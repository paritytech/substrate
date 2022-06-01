// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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

// tag::description[]
//! Simple BLS (Boneh–Lynn–Shacham) Signature API.
// end::description[]

#[cfg(feature = "full_crypto")]
use sp_std::vec::Vec;

use crate::{
	crypto::ByteArray,
	hash::{H384, H768},
};
use codec::{Decode, Encode, MaxEncodedLen};
use scale_info::TypeInfo;

#[cfg(feature = "std")]
use crate::crypto::Ss58Codec;
use crate::crypto::{
	CryptoType, CryptoTypeId, CryptoTypePublicPair, Derive, Public as TraitPublic, UncheckedFrom,
};
#[cfg(feature = "full_crypto")]
use crate::crypto::{DeriveJunction, Pair as TraitPair, SecretStringError};
#[cfg(feature = "std")]
use bip39::{Language, Mnemonic, MnemonicType};
#[cfg(feature = "full_crypto")]
use core::convert::TryFrom;
#[cfg(feature = "full_crypto")]
use bls_like::{
    BLS377, EngineBLS, Keypair, Message, Signature as BLSSignature, pop::{ProofOfPossessionGenerator, ProofOfPossessionVerifier}, pop::BatchAssumingProofsOfPossession, SecretKey, SerializableToBytes
};
#[cfg(feature = "std")]
use serde::{de, Deserialize, Deserializer, Serialize, Serializer};
use sp_runtime_interface::pass_by::PassByInner;
use sp_std::ops::Deref;
#[cfg(feature = "std")]
use substrate_bip39::seed_from_entropy;

/// An identifier used to match public keys against bls377 keys
pub const CRYPTO_ID: CryptoTypeId = CryptoTypeId(*b"bls7");

/// A secret seed. It's not called a "secret key" because ring doesn't expose the secret keys
/// of the key pair (yeah, dumb); as such we're forced to remember the seed manually if we
/// will need it later (such as for HDKD).
#[cfg(feature = "full_crypto")]
type Seed = [u8; BLS377::SECRET_KEY_SIZE];

/// A public key.
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
pub struct Public(pub [u8; BLS377::PUBLICKEY_SERIALIZED_SIZE]);

/// A key pair.
#[cfg(feature = "full_crypto")]
pub struct Pair(Keypair<BLS377>);

#[cfg(feature = "full_crypto")]
impl Clone for Pair {
	fn clone(&self) -> Self {
		Pair(self.0.clone())
	}
}

impl AsRef<[u8; BLS377::PUBLICKEY_SERIALIZED_SIZE]> for Public {
	fn as_ref(&self) -> &[u8; BLS377::PUBLICKEY_SERIALIZED_SIZE] {
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

impl sp_std::convert::TryFrom<&[u8]> for Public {
	type Error = ();

	fn try_from(data: &[u8]) -> Result<Self, Self::Error> {
		if data.len() != Self::LEN {
			return Err(())
		}
		let mut r = [0u8; Self::LEN];
		r.copy_from_slice(data);
		Ok(Self::unchecked_from(r))
	}
}

impl From<Public> for [u8; BLS377::PUBLICKEY_SERIALIZED_SIZE] {
	fn from(x: Public) -> Self {
		x.0
	}
}

#[cfg(feature = "full_crypto")]
impl From<Pair> for Public {
	fn from(x: Pair) -> Self {
		x.public()
	}
}

impl From<Public> for H384 {
	fn from(x: Public) -> Self {
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

impl UncheckedFrom<[u8; BLS377::PUBLICKEY_SERIALIZED_SIZE]> for Public {
	fn unchecked_from(x: [u8; BLS377::PUBLICKEY_SERIALIZED_SIZE]) -> Self {
		Public::from_raw(x)
	}
}

impl UncheckedFrom<H384> for Public {
	fn unchecked_from(x: H384) -> Self {
		Public::from_h384(x)
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

/// A signature (a 512-bit value).
#[cfg_attr(feature = "full_crypto", derive(Hash))]
#[derive(Encode, Decode, MaxEncodedLen, PassByInner, TypeInfo, PartialEq, Eq)]
pub struct Signature(pub [u8; BLS377::SIGNATURE_SERIALIZED_SIZE]);

impl sp_std::convert::TryFrom<&[u8]> for Signature {
	type Error = ();

	fn try_from(data: &[u8]) -> Result<Self, Self::Error> {
		if data.len() ==  BLS377::SIGNATURE_SERIALIZED_SIZE {
			let mut inner = [0u8; BLS377::SIGNATURE_SERIALIZED_SIZE];
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
		serializer.serialize_str(&hex::encode(self))
	}
}

#[cfg(feature = "std")]
impl<'de> Deserialize<'de> for Signature {
	fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
	where
		D: Deserializer<'de>,
	{
		let signature_hex = hex::decode(&String::deserialize(deserializer)?)
			.map_err(|e| de::Error::custom(format!("{:?}", e)))?;
		Signature::try_from(signature_hex.as_ref())
			.map_err(|e| de::Error::custom(format!("{:?}", e)))
	}
}

impl Clone for Signature {
	fn clone(&self) -> Self {
		let mut r = [0u8; BLS377::SIGNATURE_SERIALIZED_SIZE];
		r.copy_from_slice(&self.0[..]);
		Signature(r)
	}
}

impl From<Signature> for H768 {
	fn from(v: Signature) -> H768 {
		H768::from(v.0)
	}
}

impl From<Signature> for [u8; BLS377::SIGNATURE_SERIALIZED_SIZE] {
	fn from(v: Signature) -> [u8; BLS377::SIGNATURE_SERIALIZED_SIZE] {
		v.0
	}
}

impl AsRef<[u8; BLS377::SIGNATURE_SERIALIZED_SIZE]> for Signature {
	fn as_ref(&self) -> &[u8; BLS377::SIGNATURE_SERIALIZED_SIZE] {
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

impl UncheckedFrom<[u8; BLS377::SIGNATURE_SERIALIZED_SIZE]> for Signature {
	fn unchecked_from(data: [u8; BLS377::SIGNATURE_SERIALIZED_SIZE]) -> Signature {
		Signature(data)
	}
}

impl Signature {
	/// A new instance from the given BLS377::SIGNATURE_SERIALIZED_SIZE-byte `data`.
	///
	/// NOTE: No checking goes on to ensure this is a real signature. Only use it if
	/// you are certain that the array actually is a signature. GIGO!
	pub fn from_raw(data: [u8; BLS377::SIGNATURE_SERIALIZED_SIZE]) -> Signature {
		Signature(data)
	}

	/// A new instance from the given slice that should be 64 bytes long.
	///
	/// NOTE: No checking goes on to ensure this is a real signature. Only use it if
	/// you are certain that the array actually is a signature. GIGO!
	pub fn from_slice(data: &[u8]) -> Self {
		let mut r = [0u8; BLS377::SIGNATURE_SERIALIZED_SIZE];
		r.copy_from_slice(data);
		Signature(r)
	}

	/// A new instance from an H512.
	///
	/// NOTE: No checking goes on to ensure this is a real signature. Only use it if
	/// you are certain that the array actually is a signature. GIGO!
	pub fn from_h512(v: H768) -> Signature {
		Signature(v.into())
	}
}

/// A localized signature also contains sender information.
#[cfg(feature = "std")]
#[derive(PartialEq, Eq, Clone, Debug, Encode, Decode)]
pub struct LocalizedSignature {
	/// The signer of the signature.
	pub signer: Public,
	/// The signature itself.
	pub signature: Signature,
}

impl Public {
	/// A new instance from the given BLS377::PUBLICKEY_SERIALIZED_SIZE-byte `data`.
	///
	/// NOTE: No checking goes on to ensure this is a real public key. Only use it if
	/// you are certain that the array actually is a pubkey. GIGO!
	pub fn from_raw(data: [u8; BLS377::PUBLICKEY_SERIALIZED_SIZE]) -> Self {
		Public(data)
	}

	/// A new instance from an H384.
	///
	/// NOTE: No checking goes on to ensure this is a real public key. Only use it if
	/// you are certain that the array actually is a pubkey. GIGO!
	pub fn from_h384(x: H384) -> Self {
		Public(x.into())
	}

	/// Return a slice filled with raw data.
	pub fn as_array_ref(&self) -> &[u8; BLS377::PUBLICKEY_SERIALIZED_SIZE] {
		self.as_ref()
	}
}

impl ByteArray for Public {
	const LEN: usize = BLS377::PUBLICKEY_SERIALIZED_SIZE;
}

impl TraitPublic for Public {
	fn to_public_crypto_pair(&self) -> CryptoTypePublicPair {
		CryptoTypePublicPair(CRYPTO_ID, self.to_raw_vec())
	}
}

impl Derive for Public {}

impl From<Public> for CryptoTypePublicPair {
	fn from(key: Public) -> Self {
		(&key).into()
	}
}

impl From<&Public> for CryptoTypePublicPair {
	fn from(key: &Public) -> Self {
		CryptoTypePublicPair(CRYPTO_ID, key.to_raw_vec())
	}
}

///???
///What is HDKD? What is hard junction? should seed be 48bytes
/// Derive a single hard junction.
#[cfg(feature = "full_crypto")]
fn derive_hard_junction(secret_seed: &Seed, cc: &[u8; 32]) -> Seed {
	("BLS12377HDKD", secret_seed, cc).using_encoded(|data| {
		let mut res = [0u8; BLS377::SECRET_KEY_SIZE];
		res.copy_from_slice(blake2_rfc::blake2b::blake2b(BLS377::SECRET_KEY_SIZE, &[], data).as_bytes());
		res
	})
}

/// An error when deriving a key.
#[cfg(feature = "full_crypto")]
pub enum DeriveError {
	/// A soft key was found in the path (and is unsupported).
	SoftKeyInPath,
}

#[cfg(feature = "full_crypto")]
impl TraitPair for Pair {
	type Public = Public;
	type Seed = Seed;
	type Signature = Signature;
	type DeriveError = DeriveError;

	/// Generate new secure (random) key pair and provide the recovery phrase.
	///
	/// You can recover the same key later with `from_phrase`.
	#[cfg(feature = "std")]
	fn generate_with_phrase(password: Option<&str>) -> (Pair, String, Seed) {
		let mnemonic = Mnemonic::new(MnemonicType::Words12, Language::English);
		let phrase = mnemonic.phrase();
		let (pair, seed) = Self::from_phrase(phrase, password)
			.expect("All phrases generated by Mnemonic are valid; qed");
		(pair, phrase.to_owned(), seed)
	}

	/// Generate key pair from given recovery phrase and password.
	#[cfg(feature = "std")]
	fn from_phrase(
		phrase: &str,
		password: Option<&str>,
	) -> Result<(Pair, Seed), SecretStringError> {
		let big_seed = seed_from_entropy(
			Mnemonic::from_phrase(phrase, Language::English)
				.map_err(|_| SecretStringError::InvalidPhrase)?
				.entropy(),
			password.unwrap_or(""),
		)
		.map_err(|_| SecretStringError::InvalidSeed)?;
		let mut seed = Seed::default();
		seed.copy_from_slice(&big_seed[0..32]);
		Self::from_seed_slice(&big_seed[0..32]).map(|x| (x, seed))
	}

	/// Make a new key pair from secret seed material.
	///
	/// You should never need to use this; generate(), generate_with_phrase
	fn from_seed(seed: &Seed) -> Pair {
		Self::from_seed_slice(&seed[..]).expect("seed has valid length; qed")
	}

	/// Make a new key pair from secret seed material. The slice must be 32 bytes long or it
	/// will return `None`.
	///
	/// You should never need to use this; generate(), generate_with_phrase
	fn from_seed_slice(seed_slice: &[u8]) -> Result<Pair, SecretStringError> {
        if seed_slice.len() != BLS377::SECRET_KEY_SIZE {
            return Err(SecretStringError::InvalidSeedLength);
        }        
		let secret = bls_like::SecretKey::from_seed(seed_slice);
		let public = secret.into_public();
		Ok(Pair(bls_like::Keypair { secret, public }))
	}

	/// Derive a child key from a series of given junctions.
	fn derive<Iter: Iterator<Item = DeriveJunction>>(
		&self,
		path: Iter,
		_seed: Option<Seed>,
	) -> Result<(Pair, Option<Seed>), DeriveError> {
		let mut acc = self.0.secret.to_bytes();
		for j in path {
			match j {
				DeriveJunction::Soft(_cc) => return Err(DeriveError::SoftKeyInPath),
				DeriveJunction::Hard(cc) => acc = derive_hard_junction(&acc, &cc),
			}
		}
		Ok((Self::from_seed(&acc), Some(acc)))
	}

	/// Get the public key.
	fn public(&self) -> Public {
		let mut r = [0u8; BLS377::PUBLICKEY_SERIALIZED_SIZE];
		let pk = self.0.public.to_bytes();
		r.copy_from_slice(pk.as_slice());
		Public(r)
	}

	/// Sign a message.
	fn sign(&self, message: &[u8]) -> Signature {
        let mut mutable_self = self.clone();
		let r = mutable_self.0.sign(Message::new(b"", message)).to_bytes();
		Signature::from_raw(r)
	}

	/// Verify a signature on a message. Returns true if the signature is good.
	fn verify<M: AsRef<[u8]>>(sig: &Self::Signature, message: M, pubkey: &Self::Public) -> bool {
		Self::verify_weak(&sig.0[..], message.as_ref(), pubkey)
	}

	/// Verify a signature on a message. Returns true if the signature is good.
	///
	/// This doesn't use the type system to ensure that `sig` and `pubkey` are the correct
	/// size. Use it only if you're coming from byte buffers and need the speed.
	fn verify_weak<P: AsRef<[u8]>, M: AsRef<[u8]>>(sig: &[u8], message: M, pubkey: P) -> bool {
        let pubkey_array : [u8; BLS377::PUBLICKEY_SERIALIZED_SIZE]  = match pubkey.as_ref().try_into() {
			Ok(pk) => pk,
			Err(_) => return false,
        };        
		let public_key = match bls_like::PublicKey::<BLS377>::from_bytes(&pubkey_array) {
			Ok(pk) => pk,
			Err(_) => return false,
		};
        
        let sig_array  = match sig.try_into() {
			Ok(s) => s,
			Err(_) => return false,
		};
		let sig = match bls_like::Signature::from_bytes(sig_array) {
			Ok(s) => s,
			Err(_) => return false,
		};

		sig.verify(Message::new(b"", message.as_ref()), &public_key)
	}

	/// Return a vec filled with raw data.
	fn to_raw_vec(&self) -> Vec<u8> {
		self.seed().to_vec()
	}
}

#[cfg(feature = "full_crypto")]
impl Pair {
	/// Get the seed for this key.
	pub fn seed(&self) -> Seed {
        self.0.secret.to_bytes()
	}

	/// Exactly as `from_string` except that if no matches are found then, the the first 32
	/// characters are taken (padded with spaces as necessary) and used as the MiniSecretKey.
	#[cfg(feature = "std")]
	pub fn from_legacy_string(s: &str, password_override: Option<&str>) -> Pair {
		Self::from_string(s, password_override).unwrap_or_else(|_| {
			let mut padded_seed: Seed = [b' '; 32];
			let len = s.len().min(32);
			padded_seed[..len].copy_from_slice(&s.as_bytes()[..len]);
			Self::from_seed(&padded_seed)
		})
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

#[cfg(test)]
mod test {
	use super::*;
	use crate::crypto::DEV_PHRASE;
	use hex_literal::hex;
	use serde_json;

	#[test]
	fn default_phrase_should_be_used() {
		assert_eq!(
			Pair::from_string("//Alice///password", None).unwrap().public(),
			Pair::from_string(&format!("{}//Alice", DEV_PHRASE), Some("password"))
				.unwrap()
				.public(),
		);
	}

    //only passes if the seed = seed (mod ScalarField)
	#[test]
	fn seed_and_derive_should_work() {
		let seed = hex!("9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f00"); 
		let pair = Pair::from_seed(&seed);
        // we are using hash to field so this is not going to work
		// assert_eq!(pair.seed(), seed);
		let path = vec![DeriveJunction::Hard([0u8; 32])];
		let derived = pair.derive(path.into_iter(), None).ok().unwrap().0;
		assert_eq!(
			derived.seed(),
			hex!("a4f2269333b3e87c577aa00c4a2cd650b3b30b2e8c286a47c251279ff3a26e0d")
		);
	}

	#[test]
	fn test_vector_should_work() {
		let pair = Pair::from_seed(&hex!(
			"9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60"
		));
		let public = pair.public();
		assert_eq!(
			public,
			Public::from_raw(hex!(
				"7a84ca8ce4c37c93c95ecee6a3c0c9a7b9c225093cf2f12dc4f69cbfb847ef9424a18f5755d5a742247d386ff2aabb80"
			))
		);
		let message = b"";
		let signature = hex!("cb12ab70f52b7c955a49ff30488fe7d612561e1a4d2903d0e0823b59201cd25e26bf6c145726f6519c2c989f2c2d5501ed973296de6c4e15bee5dc975ced74495fc38afac70e8cc60184f734ffd42b90718c393f82fa8c1b5403d686c33a9000");
		let signature = Signature::from_raw(signature);
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
			Public::from_raw(hex!(
				"6dc6be608fab3c6bd894a606be86db346cc170db85c733853a371f3db54ae1b12052c0888d472760c81b537572a26f00"
			))
		);
		let message = b"";
		let signature = hex!("300b1ef3d3c8d7afd275c035241331dee228a502c3d210657a12eb735d3f5c17827d61b5071a71cb23c24f351d6f7600e61b41c0789bbb839946c654b7dee43174dc1aed6179062cfb00c0fab461fbdb9e15dbb849b31c285b60bfc44f9d9901");
		let signature = Signature::from_raw(signature);
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
		let pair = Pair::from_seed(b"12345678901234567890123456789012");
		let public = pair.public();
		assert_eq!(
			public,
			Public::from_raw(hex!(
				"754d2f2bbfa67df54d7e0e951979a18a1e0f45948857752cc2bac6bbb0b1d05e8e48bcc453920bf0c4bbd59932124801")
			)
		);
		let message = hex!("2f8c6129d816cf51c374bc7f08c3e63ed156cf78aefb4a6550d97b87997977ee00000000000000000200d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a4500000000000000");
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
		let pair = Pair::from_seed(b"12345678901234567890123456789012");
		let public = pair.public();
		let s = public.to_ss58check();
		println!("Correct: {}", s);
		let cmp = Public::from_ss58check(&s).unwrap();
		assert_eq!(cmp, public);
	}

	#[test]
	fn signature_serialization_works() {
		let pair = Pair::from_seed(b"12345678901234567890123456789012");
		let message = b"Something important";
		let signature = pair.sign(&message[..]);
		let serialized_signature = serde_json::to_string(&signature).unwrap();
		// Signature is 96 bytes, so 192 chars + 2 quote chars
		assert_eq!(serialized_signature.len(), 194);
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
