// Copyright 2017-2019 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

// tag::description[]
//! Simple Ed25519 API.
// end::description[]


use crate::{hash::H256, hash::H512};
use parity_codec::{Encode, Decode};

#[cfg(feature = "std")]
use blake2_rfc;
#[cfg(feature = "std")]
use substrate_bip39::seed_from_entropy;
#[cfg(feature = "std")]
use bip39::{Mnemonic, Language, MnemonicType};
#[cfg(feature = "std")]
use rand::Rng;
#[cfg(feature = "std")]
use crate::crypto::{Pair as TraitPair, DeriveJunction, SecretStringError, Derive, Ss58Codec};
#[cfg(feature = "std")]
use serde::{de, Serializer, Serialize, Deserializer, Deserialize};
use crate::crypto::UncheckedFrom;

/// A secret seed. It's not called a "secret key" because ring doesn't expose the secret keys
/// of the key pair (yeah, dumb); as such we're forced to remember the seed manually if we
/// will need it later (such as for HDKD).
#[cfg(feature = "std")]
type Seed = [u8; 32];

/// A public key.
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Encode, Decode, Default)]
pub struct Public(pub [u8; 32]);

/// A key pair.
#[cfg(feature = "std")]
pub struct Pair(ed25519_dalek::Keypair);

#[cfg(feature = "std")]
impl Clone for Pair {
	fn clone(&self) -> Self {
		Pair(ed25519_dalek::Keypair {
			public: self.0.public.clone(),
			secret: ed25519_dalek::SecretKey::from_bytes(self.0.secret.as_bytes())
				.expect("key is always the correct size; qed")
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

impl From<Public> for [u8; 32] {
	fn from(x: Public) -> Self {
		x.0
	}
}

#[cfg(feature = "std")]
impl From<Pair> for Public {
	fn from(x: Pair) -> Self {
		x.public()
	}
}

impl AsRef<Public> for Public {
	fn as_ref(&self) -> &Public {
		&self
	}
}

impl From<Public> for H256 {
	fn from(x: Public) -> Self {
		x.0.into()
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
impl ::std::fmt::Display for Public {
	fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
		write!(f, "{}", self.to_ss58check())
	}
}

#[cfg(feature = "std")]
impl ::std::fmt::Debug for Public {
	fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
		let s = self.to_ss58check();
		write!(f, "{} ({}...)", crate::hexdisplay::HexDisplay::from(&self.0), &s[0..8])
	}
}

#[cfg(feature = "std")]
impl Serialize for Public {
	fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error> where S: Serializer {
		serializer.serialize_str(&self.to_ss58check())
	}
}

#[cfg(feature = "std")]
impl<'de> Deserialize<'de> for Public {
	fn deserialize<D>(deserializer: D) -> Result<Self, D::Error> where D: Deserializer<'de> {
		Public::from_ss58check(&String::deserialize(deserializer)?)
			.map_err(|e| de::Error::custom(format!("{:?}", e)))
	}
}

#[cfg(feature = "std")]
impl ::std::hash::Hash for Public {
	fn hash<H: ::std::hash::Hasher>(&self, state: &mut H) {
		self.0.hash(state);
	}
}

/// A signature (a 512-bit value).
#[derive(Encode, Decode)]
pub struct Signature(pub [u8; 64]);

impl Clone for Signature {
	fn clone(&self) -> Self {
		let mut r = [0u8; 64];
		r.copy_from_slice(&self.0[..]);
		Signature(r)
	}
}

impl Default for Signature {
	fn default() -> Self {
		Signature([0u8; 64])
	}
}

impl PartialEq for Signature {
	fn eq(&self, b: &Self) -> bool {
		&self.0[..] == &b.0[..]
	}
}

impl Eq for Signature {}

impl From<Signature> for H512 {
	fn from(v: Signature) -> H512 {
		H512::from(v.0)
	}
}

impl From<Signature> for [u8; 64] {
	fn from(v: Signature) -> [u8; 64] {
		v.0
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

#[cfg(feature = "std")]
impl ::std::fmt::Debug for Signature {
	fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
		write!(f, "{}", crate::hexdisplay::HexDisplay::from(&self.0))
	}
}

#[cfg(feature = "std")]
impl ::std::hash::Hash for Signature {
	fn hash<H: ::std::hash::Hasher>(&self, state: &mut H) {
		::std::hash::Hash::hash(&self.0[..], state);
	}
}

impl Signature {
	/// A new instance from the given 64-byte `data`.
	///
	/// NOTE: No checking goes on to ensure this is a real signature. Only use it if
	/// you are certain that the array actually is a signature. GIGO!
	pub fn from_raw(data: [u8; 64]) -> Signature {
		Signature(data)
	}

	/// A new instance from the given slice that should be 64 bytes long.
	///
	/// NOTE: No checking goes on to ensure this is a real signature. Only use it if
	/// you are certain that the array actually is a signature. GIGO!
	pub fn from_slice(data: &[u8]) -> Self {
		let mut r = [0u8; 64];
		r.copy_from_slice(data);
		Signature(r)
	}

	/// A new instance from an H512.
	///
	/// NOTE: No checking goes on to ensure this is a real signature. Only use it if
	/// you are certain that the array actually is a signature. GIGO!
	pub fn from_h512(v: H512) -> Signature {
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

/// An error type for SS58 decoding.
#[cfg(feature = "std")]
#[derive(Clone, Copy, Eq, PartialEq, Debug)]
pub enum PublicError {
	/// Bad alphabet.
	BadBase58,
	/// Bad length.
	BadLength,
	/// Unknown version.
	UnknownVersion,
	/// Invalid checksum.
	InvalidChecksum,
}

impl Public {
	/// A new instance from the given 32-byte `data`.
	///
	/// NOTE: No checking goes on to ensure this is a real public key. Only use it if
	/// you are certain that the array actually is a pubkey. GIGO!
	pub fn from_raw(data: [u8; 32]) -> Self {
		Public(data)
	}

	/// A new instance from the given slice that should be 32 bytes long.
	///
	/// NOTE: No checking goes on to ensure this is a real public key. Only use it if
	/// you are certain that the array actually is a pubkey. GIGO!
	pub fn from_slice(data: &[u8]) -> Self {
		let mut r = [0u8; 32];
		r.copy_from_slice(data);
		Public(r)
	}

	/// A new instance from an H256.
	///
	/// NOTE: No checking goes on to ensure this is a real public key. Only use it if
	/// you are certain that the array actually is a pubkey. GIGO!
	pub fn from_h256(x: H256) -> Self {
		Public(x.into())
	}

	/// Return a `Vec<u8>` filled with raw data.
	#[cfg(feature = "std")]
	pub fn to_raw_vec(self) -> Vec<u8> {
		let r: &[u8; 32] = self.as_ref();
		r.to_vec()
	}

	/// Return a slice filled with raw data.
	pub fn as_slice(&self) -> &[u8] {
		let r: &[u8; 32] = self.as_ref();
		&r[..]
	}

	/// Return a slice filled with raw data.
	pub fn as_array_ref(&self) -> &[u8; 32] {
		self.as_ref()
	}
}

#[cfg(feature = "std")]
impl Derive for Public {}

#[cfg(feature = "std")]
impl AsRef<Pair> for Pair {
	fn as_ref(&self) -> &Pair {
		&self
	}
}

/// Derive a single hard junction.
#[cfg(feature = "std")]
fn derive_hard_junction(secret_seed: &Seed, cc: &[u8; 32]) -> Seed {
	("Ed25519HDKD", secret_seed, cc).using_encoded(|data| {
		let mut res = [0u8; 32];
		res.copy_from_slice(blake2_rfc::blake2b::blake2b(32, &[], data).as_bytes());
		res
	})
}

/// An error when deriving a key.
#[cfg(feature = "std")]
pub enum DeriveError {
	/// A soft key was found in the path (and is unsupported).
	SoftKeyInPath,
}

#[cfg(feature = "std")]
impl TraitPair for Pair {
	type Public = Public;
	type Seed = Seed;
	type Signature = Signature;
	type DeriveError = DeriveError;

	/// Generate new secure (random) key pair.
	///
	/// This is only for ephemeral keys really, since you won't have access to the secret key
	/// for storage. If you want a persistent key pair, use `generate_with_phrase` instead.
	fn generate() -> Pair {
		let mut seed: Seed = Default::default();
		rand::rngs::EntropyRng::new().fill(seed.as_mut());
		Self::from_seed(seed)
	}

	/// Generate new secure (random) key pair and provide the recovery phrase.
	///
	/// You can recover the same key later with `from_phrase`.
	fn generate_with_phrase(password: Option<&str>) -> (Pair, String) {
		let mnemonic = Mnemonic::new(MnemonicType::Words12, Language::English);
		let phrase = mnemonic.phrase();
		(
			Self::from_phrase(phrase, password).expect("All phrases generated by Mnemonic are valid; qed"),
			phrase.to_owned(),
		)
	}

	/// Generate key pair from given recovery phrase and password.
	fn from_phrase(phrase: &str, password: Option<&str>) -> Result<Pair, SecretStringError> {
		let big_seed = seed_from_entropy(
			Mnemonic::from_phrase(phrase, Language::English)
				.map_err(|_| SecretStringError::InvalidPhrase)?.entropy(),
			password.unwrap_or(""),
		).map_err(|_| SecretStringError::InvalidSeed)?;
		Self::from_seed_slice(&big_seed[0..32])
	}

	/// Make a new key pair from secret seed material.
	///
	/// You should never need to use this; generate(), generate_with_phrasee
	fn from_seed(seed: Seed) -> Pair {
		let secret = ed25519_dalek::SecretKey::from_bytes(&seed[..])
			.expect("seed has valid length; qed");
		let public = ed25519_dalek::PublicKey::from(&secret);
		Pair(ed25519_dalek::Keypair { secret, public })
	}

	/// Make a new key pair from secret seed material. The slice must be 32 bytes long or it
	/// will return `None`.
	///
	/// You should never need to use this; generate(), generate_with_phrase
	fn from_seed_slice(seed_slice: &[u8]) -> Result<Pair, SecretStringError> {
		if seed_slice.len() != 32 {
			Err(SecretStringError::InvalidSeedLength)
		} else {
			let mut seed = [0u8; 32];
			seed.copy_from_slice(&seed_slice);
			Ok(Self::from_seed(seed))
		}
	}

	/// Derive a child key from a series of given junctions.
	fn derive<Iter: Iterator<Item=DeriveJunction>>(&self, path: Iter) -> Result<Pair, DeriveError> {
		let mut acc = self.0.secret.to_bytes();
		for j in path {
			match j {
				DeriveJunction::Soft(_cc) => return Err(DeriveError::SoftKeyInPath),
				DeriveJunction::Hard(cc) => acc = derive_hard_junction(&acc, &cc),
			}
		}
		Ok(Self::from_seed(acc))
	}

	/// Generate a key from the phrase, password and derivation path.
	fn from_standard_components<I: Iterator<Item=DeriveJunction>>(phrase: &str, password: Option<&str>, path: I) -> Result<Pair, SecretStringError> {
		Self::from_phrase(phrase, password)?.derive(path).map_err(|_| SecretStringError::InvalidPath)
	}

	/// Get the public key.
	fn public(&self) -> Public {
		let mut r = [0u8; 32];
		let pk = self.0.public.as_bytes();
		r.copy_from_slice(pk);
		Public(r)
	}

	/// Sign a message.
	fn sign(&self, message: &[u8]) -> Signature {
		let r = self.0.sign(message).to_bytes();
		Signature::from_raw(r)
	}

	/// Verify a signature on a message. Returns true if the signature is good.
	fn verify<P: AsRef<Self::Public>, M: AsRef<[u8]>>(sig: &Self::Signature, message: M, pubkey: P) -> bool {
		Self::verify_weak(&sig.0[..], message.as_ref(), &pubkey.as_ref().0[..])
	}

	/// Verify a signature on a message. Returns true if the signature is good.
	///
	/// This doesn't use the type system to ensure that `sig` and `pubkey` are the correct
	/// size. Use it only if you're coming from byte buffers and need the speed.
	fn verify_weak<P: AsRef<[u8]>, M: AsRef<[u8]>>(sig: &[u8], message: M, pubkey: P) -> bool {
		let public_key = match ed25519_dalek::PublicKey::from_bytes(pubkey.as_ref()) {
			Ok(pk) => pk,
			Err(_) => return false,
		};

		let sig = match ed25519_dalek::Signature::from_bytes(sig) {
			Ok(s) => s,
			Err(_) => return false
		};

		match public_key.verify(message.as_ref(), &sig) {
			Ok(_) => true,
			_ => false,
		}
	}
}

#[cfg(feature = "std")]
impl Pair {
	/// Get the seed for this key.
	pub fn seed(&self) -> &Seed {
		self.0.secret.as_bytes()
	}

	/// Exactly as `from_string` except that if no matches are found then, the the first 32
	/// characters are taken (padded with spaces as necessary) and used as the MiniSecretKey.
	pub fn from_legacy_string(s: &str, password_override: Option<&str>) -> Pair {
		Self::from_string(s, password_override).unwrap_or_else(|_| {
			let mut padded_seed: Seed = [' ' as u8; 32];
			let len = s.len().min(32);
			padded_seed[..len].copy_from_slice(&s.as_bytes()[..len]);
			Self::from_seed(padded_seed)
		})
	}
}

#[cfg(test)]
mod test {
	use super::*;
	use hex_literal::hex;
	use crate::crypto::DEV_PHRASE;

	#[test]
	fn default_phrase_should_be_used() {
		assert_eq!(
			Pair::from_string("//Alice///password", None).unwrap().public(),
			Pair::from_string(&format!("{}//Alice", DEV_PHRASE), Some("password")).unwrap().public(),
		);
	}

	#[test]
	fn seed_and_derive_should_work() {
		let seed = hex!("9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60");
		let pair = Pair::from_seed(seed);
		assert_eq!(pair.seed(), &seed);
		let path = vec![DeriveJunction::Hard([0u8; 32])];
		let derived = pair.derive(path.into_iter()).ok().unwrap();
		assert_eq!(derived.seed(), &hex!("ede3354e133f9c8e337ddd6ee5415ed4b4ffe5fc7d21e933f4930a3730e5b21c"));
	}

	#[test]
	fn test_vector_should_work() {
		let pair: Pair = Pair::from_seed(hex!("9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60"));
		let public = pair.public();
		assert_eq!(public, Public::from_raw(hex!("d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a")));
		let message = b"";
		let signature = Signature::from_raw(hex!("e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b"));
		assert!(&pair.sign(&message[..]) == &signature);
		assert!(Pair::verify(&signature, &message[..], &public));
	}

	#[test]
	fn test_vector_by_string_should_work() {
		let pair: Pair = Pair::from_string("0x9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60", None).unwrap();
		let public = pair.public();
		assert_eq!(public, Public::from_raw(hex!("d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a")));
		let message = b"";
		let signature = Signature::from_raw(hex!("e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b"));
		assert!(&pair.sign(&message[..]) == &signature);
		assert!(Pair::verify(&signature, &message[..], &public));
	}

	#[test]
	fn generated_pair_should_work() {
		let pair = Pair::generate();
		let public = pair.public();
		let message = b"Something important";
		let signature = pair.sign(&message[..]);
		assert!(Pair::verify(&signature, &message[..], &public));
		assert!(!Pair::verify(&signature, b"Something else", &public));
	}

	#[test]
	fn seeded_pair_should_work() {
		let pair = Pair::from_seed(*b"12345678901234567890123456789012");
		let public = pair.public();
		assert_eq!(public, Public::from_raw(hex!("2f8c6129d816cf51c374bc7f08c3e63ed156cf78aefb4a6550d97b87997977ee")));
		let message = hex!("2f8c6129d816cf51c374bc7f08c3e63ed156cf78aefb4a6550d97b87997977ee00000000000000000200d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a4500000000000000");
		let signature = pair.sign(&message[..]);
		println!("Correct signature: {:?}", signature);
		assert!(Pair::verify(&signature, &message[..], &public));
		assert!(!Pair::verify(&signature, "Other message", &public));
	}

	#[test]
	fn generate_with_phrase_recovery_possible() {
		let (pair1, phrase) = Pair::generate_with_phrase(None);
		let pair2 = Pair::from_phrase(&phrase, None).unwrap();

		assert_eq!(pair1.public(), pair2.public());
	}

	#[test]
	fn generate_with_password_phrase_recovery_possible() {
		let (pair1, phrase) = Pair::generate_with_phrase(Some("password"));
		let pair2 = Pair::from_phrase(&phrase, Some("password")).unwrap();

		assert_eq!(pair1.public(), pair2.public());
	}

	#[test]
	fn password_does_something() {
		let (pair1, phrase) = Pair::generate_with_phrase(Some("password"));
		let pair2 = Pair::from_phrase(&phrase, None).unwrap();

		assert_ne!(pair1.public(), pair2.public());
	}

	#[test]
	fn ss58check_roundtrip_works() {
		let pair = Pair::from_seed(*b"12345678901234567890123456789012");
		let public = pair.public();
		let s = public.to_ss58check();
		println!("Correct: {}", s);
		let cmp = Public::from_ss58check(&s).unwrap();
		assert_eq!(cmp, public);
	}
}
