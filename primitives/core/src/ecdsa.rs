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

//! Simple ECDSA secp256k1 API.

use codec::{Decode, Encode, MaxEncodedLen};
use scale_info::TypeInfo;
use sp_runtime_interface::pass_by::PassByInner;

#[cfg(feature = "serde")]
use crate::crypto::Ss58Codec;
use crate::crypto::{
	ByteArray, CryptoType, CryptoTypeId, Derive, Public as TraitPublic, UncheckedFrom,
};
#[cfg(feature = "full_crypto")]
use crate::{
	crypto::{DeriveError, DeriveJunction, Pair as TraitPair, SecretStringError},
	hashing::blake2_256,
};
#[cfg(all(feature = "full_crypto", not(feature = "std")))]
use secp256k1::Secp256k1;
#[cfg(feature = "std")]
use secp256k1::SECP256K1;
#[cfg(feature = "full_crypto")]
use secp256k1::{
	ecdsa::{RecoverableSignature, RecoveryId},
	Message, PublicKey, SecretKey,
};
#[cfg(feature = "serde")]
use serde::{de, Deserialize, Deserializer, Serialize, Serializer};
#[cfg(all(not(feature = "std"), feature = "serde"))]
use sp_std::alloc::{format, string::String};
#[cfg(feature = "full_crypto")]
use sp_std::vec::Vec;

/// An identifier used to match public keys against ecdsa keys
pub const CRYPTO_ID: CryptoTypeId = CryptoTypeId(*b"ecds");

/// A secret seed (which is bytewise essentially equivalent to a SecretKey).
///
/// We need it as a different type because `Seed` is expected to be AsRef<[u8]>.
#[cfg(feature = "full_crypto")]
type Seed = [u8; 32];

/// The ECDSA compressed public key.
#[cfg_attr(feature = "full_crypto", derive(Hash))]
#[derive(
	Clone,
	Copy,
	Encode,
	Decode,
	PassByInner,
	MaxEncodedLen,
	TypeInfo,
	Eq,
	PartialEq,
	PartialOrd,
	Ord,
)]
pub struct Public(pub [u8; 33]);

impl Public {
	/// A new instance from the given 33-byte `data`.
	///
	/// NOTE: No checking goes on to ensure this is a real public key. Only use it if
	/// you are certain that the array actually is a pubkey. GIGO!
	pub fn from_raw(data: [u8; 33]) -> Self {
		Self(data)
	}

	/// Create a new instance from the given full public key.
	///
	/// This will convert the full public key into the compressed format.
	#[cfg(feature = "std")]
	pub fn from_full(full: &[u8]) -> Result<Self, ()> {
		let pubkey = if full.len() == 64 {
			// Tag it as uncompressed public key.
			let mut tagged_full = [0u8; 65];
			tagged_full[0] = 0x04;
			tagged_full[1..].copy_from_slice(full);
			secp256k1::PublicKey::from_slice(&tagged_full)
		} else {
			secp256k1::PublicKey::from_slice(full)
		};
		pubkey.map(|k| Self(k.serialize())).map_err(|_| ())
	}
}

impl ByteArray for Public {
	const LEN: usize = 33;
}

impl TraitPublic for Public {}

impl Derive for Public {}

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
		if data.len() != Self::LEN {
			return Err(())
		}
		let mut r = [0u8; Self::LEN];
		r.copy_from_slice(data);
		Ok(Self::unchecked_from(r))
	}
}

#[cfg(feature = "full_crypto")]
impl From<Pair> for Public {
	fn from(x: Pair) -> Self {
		x.public()
	}
}

impl UncheckedFrom<[u8; 33]> for Public {
	fn unchecked_from(x: [u8; 33]) -> Self {
		Public(x)
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
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		let s = self.to_ss58check();
		write!(f, "{} ({}...)", crate::hexdisplay::HexDisplay::from(&self.as_ref()), &s[0..8])
	}

	#[cfg(not(feature = "std"))]
	fn fmt(&self, _: &mut sp_std::fmt::Formatter) -> sp_std::fmt::Result {
		Ok(())
	}
}

#[cfg(feature = "serde")]
impl Serialize for Public {
	fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
	where
		S: Serializer,
	{
		serializer.serialize_str(&self.to_ss58check())
	}
}

#[cfg(feature = "serde")]
impl<'de> Deserialize<'de> for Public {
	fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
	where
		D: Deserializer<'de>,
	{
		Public::from_ss58check(&String::deserialize(deserializer)?)
			.map_err(|e| de::Error::custom(format!("{:?}", e)))
	}
}

/// A signature (a 512-bit value, plus 8 bits for recovery ID).
#[cfg_attr(feature = "full_crypto", derive(Hash))]
#[derive(Encode, Decode, MaxEncodedLen, PassByInner, TypeInfo, PartialEq, Eq)]
pub struct Signature(pub [u8; 65]);

impl TryFrom<&[u8]> for Signature {
	type Error = ();

	fn try_from(data: &[u8]) -> Result<Self, Self::Error> {
		if data.len() == 65 {
			let mut inner = [0u8; 65];
			inner.copy_from_slice(data);
			Ok(Signature(inner))
		} else {
			Err(())
		}
	}
}

#[cfg(feature = "serde")]
impl Serialize for Signature {
	fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
	where
		S: Serializer,
	{
		serializer.serialize_str(&array_bytes::bytes2hex("", self.as_ref()))
	}
}

#[cfg(feature = "serde")]
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
		let mut r = [0u8; 65];
		r.copy_from_slice(&self.0[..]);
		Signature(r)
	}
}

impl Default for Signature {
	fn default() -> Self {
		Signature([0u8; 65])
	}
}

impl From<Signature> for [u8; 65] {
	fn from(v: Signature) -> [u8; 65] {
		v.0
	}
}

impl AsRef<[u8; 65]> for Signature {
	fn as_ref(&self) -> &[u8; 65] {
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

impl UncheckedFrom<[u8; 65]> for Signature {
	fn unchecked_from(data: [u8; 65]) -> Signature {
		Signature(data)
	}
}

impl Signature {
	/// A new instance from the given 65-byte `data`.
	///
	/// NOTE: No checking goes on to ensure this is a real signature. Only use it if
	/// you are certain that the array actually is a signature. GIGO!
	pub fn from_raw(data: [u8; 65]) -> Signature {
		Signature(data)
	}

	/// A new instance from the given slice that should be 65 bytes long.
	///
	/// NOTE: No checking goes on to ensure this is a real signature. Only use it if
	/// you are certain that the array actually is a signature. GIGO!
	pub fn from_slice(data: &[u8]) -> Option<Self> {
		if data.len() != 65 {
			return None
		}
		let mut r = [0u8; 65];
		r.copy_from_slice(data);
		Some(Signature(r))
	}

	/// Recover the public key from this signature and a message.
	#[cfg(feature = "full_crypto")]
	pub fn recover<M: AsRef<[u8]>>(&self, message: M) -> Option<Public> {
		self.recover_prehashed(&blake2_256(message.as_ref()))
	}

	/// Recover the public key from this signature and a pre-hashed message.
	#[cfg(feature = "full_crypto")]
	pub fn recover_prehashed(&self, message: &[u8; 32]) -> Option<Public> {
		let rid = RecoveryId::from_i32(self.0[64] as i32).ok()?;
		let sig = RecoverableSignature::from_compact(&self.0[..64], rid).ok()?;
		let message = Message::from_slice(message).expect("Message is 32 bytes; qed");

		#[cfg(feature = "std")]
		let context = SECP256K1;
		#[cfg(not(feature = "std"))]
		let context = Secp256k1::verification_only();

		context
			.recover_ecdsa(&message, &sig)
			.ok()
			.map(|pubkey| Public(pubkey.serialize()))
	}
}

#[cfg(feature = "full_crypto")]
impl From<RecoverableSignature> for Signature {
	fn from(recsig: RecoverableSignature) -> Signature {
		let mut r = Self::default();
		let (recid, sig) = recsig.serialize_compact();
		r.0[..64].copy_from_slice(&sig);
		// This is safe due to the limited range of possible valid ids.
		r.0[64] = recid.to_i32() as u8;
		r
	}
}

/// Derive a single hard junction.
#[cfg(feature = "full_crypto")]
fn derive_hard_junction(secret_seed: &Seed, cc: &[u8; 32]) -> Seed {
	("Secp256k1HDKD", secret_seed, cc).using_encoded(sp_core_hashing::blake2_256)
}

/// A key pair.
#[cfg(feature = "full_crypto")]
#[derive(Clone)]
pub struct Pair {
	public: Public,
	secret: SecretKey,
}

#[cfg(feature = "full_crypto")]
impl TraitPair for Pair {
	type Public = Public;
	type Seed = Seed;
	type Signature = Signature;

	/// Make a new key pair from secret seed material. The slice must be 32 bytes long or it
	/// will return `None`.
	///
	/// You should never need to use this; generate(), generate_with_phrase
	fn from_seed_slice(seed_slice: &[u8]) -> Result<Pair, SecretStringError> {
		let secret =
			SecretKey::from_slice(seed_slice).map_err(|_| SecretStringError::InvalidSeedLength)?;

		#[cfg(feature = "std")]
		let context = SECP256K1;
		#[cfg(not(feature = "std"))]
		let context = Secp256k1::signing_only();

		let public = PublicKey::from_secret_key(&context, &secret);
		let public = Public(public.serialize());
		Ok(Pair { public, secret })
	}

	/// Derive a child key from a series of given junctions.
	fn derive<Iter: Iterator<Item = DeriveJunction>>(
		&self,
		path: Iter,
		_seed: Option<Seed>,
	) -> Result<(Pair, Option<Seed>), DeriveError> {
		let mut acc = self.seed();
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
		self.public
	}

	/// Sign a message.
	fn sign(&self, message: &[u8]) -> Signature {
		self.sign_prehashed(&blake2_256(message))
	}

	/// Verify a signature on a message. Returns true if the signature is good.
	fn verify<M: AsRef<[u8]>>(sig: &Self::Signature, message: M, public: &Self::Public) -> bool {
		sig.recover(message).map(|actual| actual == *public).unwrap_or_default()
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
		self.secret.secret_bytes()
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

	/// Sign a pre-hashed message
	pub fn sign_prehashed(&self, message: &[u8; 32]) -> Signature {
		let message = Message::from_slice(message).expect("Message is 32 bytes; qed");

		#[cfg(feature = "std")]
		let context = SECP256K1;
		#[cfg(not(feature = "std"))]
		let context = Secp256k1::signing_only();

		context.sign_ecdsa_recoverable(&message, &self.secret).into()
	}

	/// Verify a signature on a pre-hashed message. Return `true` if the signature is valid
	/// and thus matches the given `public` key.
	pub fn verify_prehashed(sig: &Signature, message: &[u8; 32], public: &Public) -> bool {
		match sig.recover_prehashed(message) {
			Some(actual) => actual == *public,
			None => false,
		}
	}

	/// Verify a signature on a message. Returns true if the signature is good.
	/// Parses Signature using parse_overflowing_slice.
	#[deprecated(note = "please use `verify` instead")]
	pub fn verify_deprecated<M: AsRef<[u8]>>(sig: &Signature, message: M, pubkey: &Public) -> bool {
		let message = libsecp256k1::Message::parse(&blake2_256(message.as_ref()));

		let parse_signature_overflowing = |x: [u8; 65]| {
			let sig = libsecp256k1::Signature::parse_overflowing_slice(&x[..64]).ok()?;
			let rid = libsecp256k1::RecoveryId::parse(x[64]).ok()?;
			Some((sig, rid))
		};

		let (sig, rid) = match parse_signature_overflowing(sig.0) {
			Some(sigri) => sigri,
			_ => return false,
		};
		match libsecp256k1::recover(&message, &sig, &rid) {
			Ok(actual) => pubkey.0 == actual.serialize_compressed(),
			_ => false,
		}
	}
}

// The `secp256k1` backend doesn't implement cleanup for their private keys.
// Currently we should take care of wiping the secret from memory.
// NOTE: this solution is not effective when `Pair` is moved around memory.
// The very same problem affects other cryptographic backends that are just using
// `zeroize`for their secrets.
#[cfg(feature = "full_crypto")]
impl Drop for Pair {
	fn drop(&mut self) {
		let ptr = self.secret.as_mut_ptr();
		for off in 0..self.secret.len() {
			unsafe {
				core::ptr::write_volatile(ptr.add(off), 0);
			}
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

#[cfg(test)]
mod test {
	use super::*;
	use crate::crypto::{
		set_default_ss58_version, PublicError, Ss58AddressFormat, Ss58AddressFormatRegistry,
		DEV_PHRASE,
	};
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

	#[test]
	fn seed_and_derive_should_work() {
		let seed = array_bytes::hex2array_unchecked(
			"9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60",
		);
		let pair = Pair::from_seed(&seed);
		assert_eq!(pair.seed(), seed);
		let path = vec![DeriveJunction::Hard([0u8; 32])];
		let derived = pair.derive(path.into_iter(), None).ok().unwrap();
		assert_eq!(
			derived.0.seed(),
			array_bytes::hex2array_unchecked::<32>(
				"b8eefc4937200a8382d00050e050ced2d4ab72cc2ef1b061477afb51564fdd61"
			)
		);
	}

	#[test]
	fn test_vector_should_work() {
		let pair = Pair::from_seed(&array_bytes::hex2array_unchecked(
			"9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60",
		));
		let public = pair.public();
		assert_eq!(
			public,
			Public::from_full(
				&array_bytes::hex2bytes_unchecked("8db55b05db86c0b1786ca49f095d76344c9e6056b2f02701a7e7f3c20aabfd913ebbe148dd17c56551a52952371071a6c604b3f3abe8f2c8fa742158ea6dd7d4"),
			).unwrap(),
		);
		let message = b"";
		let signature = array_bytes::hex2array_unchecked("3dde91174bd9359027be59a428b8146513df80a2a3c7eda2194f64de04a69ab97b753169e94db6ffd50921a2668a48b94ca11e3d32c1ff19cfe88890aa7e8f3c00");
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
			Public::from_full(
				&array_bytes::hex2bytes_unchecked("8db55b05db86c0b1786ca49f095d76344c9e6056b2f02701a7e7f3c20aabfd913ebbe148dd17c56551a52952371071a6c604b3f3abe8f2c8fa742158ea6dd7d4"),
			).unwrap(),
		);
		let message = b"";
		let signature = array_bytes::hex2array_unchecked("3dde91174bd9359027be59a428b8146513df80a2a3c7eda2194f64de04a69ab97b753169e94db6ffd50921a2668a48b94ca11e3d32c1ff19cfe88890aa7e8f3c00");
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
			Public::from_full(
				&array_bytes::hex2bytes_unchecked("5676109c54b9a16d271abeb4954316a40a32bcce023ac14c8e26e958aa68fba995840f3de562156558efbfdac3f16af0065e5f66795f4dd8262a228ef8c6d813"),
			).unwrap(),
		);
		let message = array_bytes::hex2bytes_unchecked("2f8c6129d816cf51c374bc7f08c3e63ed156cf78aefb4a6550d97b87997977ee00000000000000000200d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a4500000000000000");
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
	fn ss58check_format_check_works() {
		let pair = Pair::from_seed(b"12345678901234567890123456789012");
		let public = pair.public();
		let format = Ss58AddressFormatRegistry::Reserved46Account.into();
		let s = public.to_ss58check_with_version(format);
		assert_eq!(Public::from_ss58check_with_version(&s), Err(PublicError::FormatNotAllowed));
	}

	#[test]
	fn ss58check_full_roundtrip_works() {
		let pair = Pair::from_seed(b"12345678901234567890123456789012");
		let public = pair.public();
		let format = Ss58AddressFormatRegistry::PolkadotAccount.into();
		let s = public.to_ss58check_with_version(format);
		let (k, f) = Public::from_ss58check_with_version(&s).unwrap();
		assert_eq!(k, public);
		assert_eq!(f, format);

		let format = Ss58AddressFormat::custom(64);
		let s = public.to_ss58check_with_version(format);
		let (k, f) = Public::from_ss58check_with_version(&s).unwrap();
		assert_eq!(k, public);
		assert_eq!(f, format);
	}

	#[test]
	fn ss58check_custom_format_works() {
		// We need to run this test in its own process to not interfere with other tests running in
		// parallel and also relying on the ss58 version.
		if std::env::var("RUN_CUSTOM_FORMAT_TEST") == Ok("1".into()) {
			use crate::crypto::Ss58AddressFormat;
			// temp save default format version
			let default_format = crate::crypto::default_ss58_version();
			// set current ss58 version is custom "200" `Ss58AddressFormat::Custom(200)`

			set_default_ss58_version(Ss58AddressFormat::custom(200));
			// custom addr encoded by version 200
			let addr = "4pbsSkWcBaYoFHrKJZp5fDVUKbqSYD9dhZZGvpp3vQ5ysVs5ybV";
			Public::from_ss58check(addr).unwrap();

			set_default_ss58_version(default_format);
			// set current ss58 version to default version
			let addr = "KWAfgC2aRG5UVD6CpbPQXCx4YZZUhvWqqAJE6qcYc9Rtr6g5C";
			Public::from_ss58check(addr).unwrap();

			println!("CUSTOM_FORMAT_SUCCESSFUL");
		} else {
			let executable = std::env::current_exe().unwrap();
			let output = std::process::Command::new(executable)
				.env("RUN_CUSTOM_FORMAT_TEST", "1")
				.args(&["--nocapture", "ss58check_custom_format_works"])
				.output()
				.unwrap();

			let output = String::from_utf8(output.stdout).unwrap();
			assert!(output.contains("CUSTOM_FORMAT_SUCCESSFUL"));
		}
	}

	#[test]
	fn signature_serialization_works() {
		let pair = Pair::from_seed(b"12345678901234567890123456789012");
		let message = b"Something important";
		let signature = pair.sign(&message[..]);
		let serialized_signature = serde_json::to_string(&signature).unwrap();
		// Signature is 65 bytes, so 130 chars + 2 quote chars
		assert_eq!(serialized_signature.len(), 132);
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
	fn sign_prehashed_works() {
		let (pair, _, _) = Pair::generate_with_phrase(Some("password"));

		// `msg` shouldn't be mangled
		let msg = [0u8; 32];
		let sig1 = pair.sign_prehashed(&msg);
		let sig2: Signature = {
			let message = Message::from_slice(&msg).unwrap();
			SECP256K1.sign_ecdsa_recoverable(&message, &pair.secret).into()
		};
		assert_eq!(sig1, sig2);

		// signature is actually different
		let sig2 = pair.sign(&msg);
		assert_ne!(sig1, sig2);

		// using pre-hashed `msg` works
		let msg = b"this should be hashed";
		let sig1 = pair.sign_prehashed(&blake2_256(msg));
		let sig2 = pair.sign(msg);
		assert_eq!(sig1, sig2);
	}

	#[test]
	fn verify_prehashed_works() {
		let (pair, _, _) = Pair::generate_with_phrase(Some("password"));

		// `msg` and `sig` match
		let msg = blake2_256(b"this should be hashed");
		let sig = pair.sign_prehashed(&msg);
		assert!(Pair::verify_prehashed(&sig, &msg, &pair.public()));

		// `msg` and `sig` don't match
		let msg = blake2_256(b"this is a different message");
		assert!(!Pair::verify_prehashed(&sig, &msg, &pair.public()));
	}

	#[test]
	fn recover_prehashed_works() {
		let (pair, _, _) = Pair::generate_with_phrase(Some("password"));

		// recovered key matches signing key
		let msg = blake2_256(b"this should be hashed");
		let sig = pair.sign_prehashed(&msg);
		let key = sig.recover_prehashed(&msg).unwrap();
		assert_eq!(pair.public(), key);

		// recovered key is useable
		assert!(Pair::verify_prehashed(&sig, &msg, &key));

		// recovered key and signing key don't match
		let msg = blake2_256(b"this is a different message");
		let key = sig.recover_prehashed(&msg).unwrap();
		assert_ne!(pair.public(), key);
	}
}
