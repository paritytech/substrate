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
//! Simple sr25519 (Schnorr-Ristretto) API.
//!
//! Note: `CHAIN_CODE_LENGTH` must be equal to `crate::crypto::JUNCTION_ID_LEN`
//! for this to work.
// end::description[]

#[cfg(feature = "std")]
use rand::rngs::OsRng;
#[cfg(feature = "std")]
use schnorrkel::{signing_context, Keypair, SecretKey, MiniSecretKey, PublicKey,
	derive::{Derivation, ChainCode, CHAIN_CODE_LENGTH}
};
#[cfg(feature = "std")]
use substrate_bip39::mini_secret_from_entropy;
#[cfg(feature = "std")]
use bip39::{Mnemonic, Language, MnemonicType};
#[cfg(feature = "std")]
use crate::crypto::{Pair as TraitPair, DeriveJunction, Infallible, SecretStringError, Derive, Ss58Codec};
use crate::{hash::{H256, H512}, crypto::UncheckedFrom};
use parity_codec::{Encode, Decode};

#[cfg(feature = "std")]
use serde::{de, Deserialize, Deserializer, Serialize, Serializer};
#[cfg(feature = "std")]
use schnorrkel::keys::MINI_SECRET_KEY_LENGTH;

// signing context
#[cfg(feature = "std")]
const SIGNING_CTX: &[u8] = b"substrate";

/// An Schnorrkel/Ristretto x25519 ("sr25519") public key.
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Encode, Decode, Default)]
pub struct Public(pub [u8; 32]);

/// An Schnorrkel/Ristretto x25519 ("sr25519") key pair.
#[cfg(feature = "std")]
pub struct Pair(Keypair);

impl AsRef<Public> for Public {
	fn as_ref(&self) -> &Public {
		&self
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
	fn from(x: Public) -> [u8; 32] {
		x.0
	}
}

impl From<Public> for H256 {
	fn from(x: Public) -> H256 {
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

/// An Schnorrkel/Ristretto x25519 ("sr25519") signature.
///
/// Instead of importing it for the local module, alias it to be available as a public type
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

#[cfg(feature = "std")]
impl From<schnorrkel::Signature> for Signature {
	fn from(s: schnorrkel::Signature) -> Signature {
		Signature(s.to_bytes())
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

/// A localized signature also contains sender information.
/// NOTE: Encode and Decode traits are supported in ed25519 but not possible for now here.
#[cfg(feature = "std")]
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct LocalizedSignature {
	/// The signer of the signature.
	pub signer: Public,
	/// The signature itself.
	pub signature: Signature,
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

#[cfg(feature = "std")]
impl Derive for Public {
	/// Derive a child key from a series of given junctions.
	///
	/// `None` if there are any hard junctions in there.
	fn derive<Iter: Iterator<Item=DeriveJunction>>(&self, path: Iter) -> Option<Public> {
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
impl AsRef<Pair> for Pair {
	fn as_ref(&self) -> &Pair {
		&self
	}
}

#[cfg(feature = "std")]
impl From<MiniSecretKey> for Pair {
	fn from(sec: MiniSecretKey) -> Pair {
		Pair(sec.expand_to_keypair())
	}
}

#[cfg(feature = "std")]
impl From<SecretKey> for Pair {
	fn from(sec: SecretKey) -> Pair {
		Pair(Keypair::from(sec))
	}
}

#[cfg(feature = "std")]
impl From<schnorrkel::Keypair> for Pair {
	fn from(p: schnorrkel::Keypair) -> Pair {
		Pair(p)
	}
}

#[cfg(feature = "std")]
impl From<Pair> for schnorrkel::Keypair {
	fn from(p: Pair) -> schnorrkel::Keypair {
		p.0
	}
}

#[cfg(feature = "std")]
impl AsRef<schnorrkel::Keypair> for Pair {
	fn as_ref(&self) -> &schnorrkel::Keypair {
		&self.0
	}
}

/// Derive a single hard junction.
#[cfg(feature = "std")]
fn derive_hard_junction(secret: &SecretKey, cc: &[u8; CHAIN_CODE_LENGTH]) -> SecretKey {
	secret.hard_derive_mini_secret_key(Some(ChainCode(cc.clone())), b"").0.expand()
}

#[cfg(feature = "std")]
type Seed = [u8; MINI_SECRET_KEY_LENGTH];

#[cfg(feature = "std")]
impl TraitPair for Pair {
	type Public = Public;
	type Seed = Seed;
	type Signature = Signature;
	type DeriveError = Infallible;

	/// Generate new secure (random) key pair.
	fn generate() -> Pair {
		let mut csprng: OsRng = OsRng::new().expect("os random generator works; qed");
		let key_pair: Keypair = Keypair::generate(&mut csprng);
		Pair(key_pair)
	}

	/// Make a new key pair from raw secret seed material.
	///
	/// This is generated using schnorrkel's Mini-Secret-Keys.
	///
	/// A MiniSecretKey is literally what Ed25519 calls a SecretKey, which is just 32 random bytes.
	fn from_seed(seed: Seed) -> Pair {
		let mini_key: MiniSecretKey = MiniSecretKey::from_bytes(&seed[..])
			.expect("32 bytes can always build a key; qed");
		let kp = mini_key.expand_to_keypair();
		Pair(kp)
	}

	/// Get the public key.
	fn public(&self) -> Public {
		let mut pk = [0u8; 32];
		pk.copy_from_slice(&self.0.public.to_bytes());
		Public(pk)
	}

	/// Make a new key pair from secret seed material. The slice must be 32 bytes long or it
	/// will return `None`.
	///
	/// You should never need to use this; generate(), generate_with_phrase(), from_phrase()
	fn from_seed_slice(seed: &[u8]) -> Result<Pair, SecretStringError> {
		if seed.len() != MINI_SECRET_KEY_LENGTH {
			Err(SecretStringError::InvalidSeedLength)
		} else {
			Ok(Pair(
				MiniSecretKey::from_bytes(seed)
					.map_err(|_| SecretStringError::InvalidSeed)?
					.expand_to_keypair()
			))
		}
	}

	/// Generate a key from the phrase, password and derivation path.
	fn from_standard_components<I: Iterator<Item=DeriveJunction>>(phrase: &str, password: Option<&str>, path: I) -> Result<Pair, SecretStringError> {
		Self::from_phrase(phrase, password)?
			.derive(path)
			.map_err(|_| SecretStringError::InvalidPath)
	}

	fn generate_with_phrase(password: Option<&str>) -> (Pair, String) {
		let mnemonic = Mnemonic::new(MnemonicType::Words12, Language::English);
		let phrase = mnemonic.phrase();
		(
			Self::from_phrase(phrase, password).expect("All phrases generated by Mnemonic are valid; qed"),
			phrase.to_owned(),
		)
	}

	fn from_phrase(phrase: &str, password: Option<&str>) -> Result<Pair, SecretStringError> {
		Mnemonic::from_phrase(phrase, Language::English)
			.map_err(|_| SecretStringError::InvalidPhrase)
			.map(|m| Self::from_entropy(m.entropy(), password))
	}

	fn derive<Iter: Iterator<Item=DeriveJunction>>(&self, path: Iter) -> Result<Pair, Self::DeriveError> {
		let init = self.0.secret.clone();
		let result = path.fold(init, |acc, j| match j {
			DeriveJunction::Soft(cc) => acc.derived_key_simple(ChainCode(cc), &[]).0,
			DeriveJunction::Hard(cc) => derive_hard_junction(&acc, &cc),
		});
		Ok(Self(result.into()))
	}

	fn sign(&self, message: &[u8]) -> Signature {
		let context = signing_context(SIGNING_CTX);
		self.0.sign(context.bytes(message)).into()
	}

	/// Verify a signature on a message. Returns true if the signature is good.
	fn verify<P: AsRef<Self::Public>, M: AsRef<[u8]>>(sig: &Self::Signature, message: M, pubkey: P) -> bool {
		let signature: schnorrkel::Signature = match schnorrkel::Signature::from_bytes(&sig.as_ref()) {
			Ok(some_signature) => some_signature,
			Err(_) => return false
		};
		match PublicKey::from_bytes(pubkey.as_ref().as_slice()) {
			Ok(pk) => pk.verify(
				signing_context(SIGNING_CTX).bytes(message.as_ref()), &signature
			),
			Err(_) => false,
		}
	}

	/// Verify a signature on a message. Returns true if the signature is good.
	fn verify_weak<P: AsRef<[u8]>, M: AsRef<[u8]>>(sig: &[u8], message: M, pubkey: P) -> bool {
		let signature: schnorrkel::Signature = match schnorrkel::Signature::from_bytes(sig) {
			Ok(some_signature) => some_signature,
			Err(_) => return false
		};
		match PublicKey::from_bytes(pubkey.as_ref()) {
			Ok(pk) => pk.verify(
				signing_context(SIGNING_CTX).bytes(message.as_ref()), &signature
			),
			Err(_) => false,
		}
	}
}

#[cfg(feature = "std")]
impl Pair {
	/// Make a new key pair from binary data derived from a valid seed phrase.
	///
	/// This uses a key derivation function to convert the entropy into a seed, then returns
	/// the pair generated from it.
	pub fn from_entropy(entropy: &[u8], password: Option<&str>) -> Pair {
		let mini_key: MiniSecretKey = mini_secret_from_entropy(entropy, password.unwrap_or(""))
			.expect("32 bytes can always build a key; qed");
		let kp = mini_key.expand_to_keypair();
		Pair(kp)
	}
}

#[cfg(test)]
mod test {
	use super::*;
	use crate::crypto::{Ss58Codec, DEV_PHRASE, DEV_ADDRESS};
	use hex_literal::hex;

	#[test]
	fn default_phrase_should_be_used() {
		assert_eq!(
			Pair::from_string("//Alice///password", None).unwrap().public(),
			Pair::from_string(&format!("{}//Alice", DEV_PHRASE), Some("password")).unwrap().public(),
		);
		assert_eq!(
			Pair::from_string(&format!("{}/Alice", DEV_PHRASE), None).as_ref().map(Pair::public),
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
		let pair: Pair = Pair::from_seed(hex!(
			"9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60"
		));
		let derive_1 = pair.derive(Some(DeriveJunction::soft(1)).into_iter()).unwrap();
		let derive_1b = pair.derive(Some(DeriveJunction::soft(1)).into_iter()).unwrap();
		let derive_2 = pair.derive(Some(DeriveJunction::soft(2)).into_iter()).unwrap();
		assert_eq!(derive_1.public(), derive_1b.public());
		assert_ne!(derive_1.public(), derive_2.public());
	}

	#[test]
	fn derive_hard_should_work() {
		let pair: Pair = Pair::from_seed(hex!(
			"9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60"
		));
		let derive_1 = pair.derive(Some(DeriveJunction::hard(1)).into_iter()).unwrap();
		let derive_1b = pair.derive(Some(DeriveJunction::hard(1)).into_iter()).unwrap();
		let derive_2 = pair.derive(Some(DeriveJunction::hard(2)).into_iter()).unwrap();
		assert_eq!(derive_1.public(), derive_1b.public());
		assert_ne!(derive_1.public(), derive_2.public());
	}

	#[test]
	fn derive_soft_public_should_work() {
		let pair: Pair = Pair::from_seed(hex!(
			"9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60"
		));
		let path = Some(DeriveJunction::soft(1));
		let pair_1 = pair.derive(path.clone().into_iter()).unwrap();
		let public_1 = pair.public().derive(path.into_iter()).unwrap();
		assert_eq!(pair_1.public(), public_1);
	}

	#[test]
	fn derive_hard_public_should_fail() {
		let pair: Pair = Pair::from_seed(hex!(
			"9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60"
		));
		let path = Some(DeriveJunction::hard(1));
		assert!(pair.public().derive(path.into_iter()).is_none());
	}

	#[test]
	fn sr_test_vector_should_work() {
		let pair: Pair = Pair::from_seed(hex!(
			"9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60"
		));
		let public = pair.public();
		assert_eq!(
			public,
			Public::from_raw(hex!(
				"44a996beb1eef7bdcab976ab6d2ca26104834164ecf28fb375600576fcc6eb0f"
			))
		);
		let message = b"";
		let signature = pair.sign(message);
		assert!(Pair::verify(&signature, &message[..], &public));
	}

	#[test]
	fn generated_pair_should_work() {
		let pair = Pair::generate();
		let public = pair.public();
		let message = b"Something important";
		let signature = pair.sign(&message[..]);
		assert!(Pair::verify(&signature, &message[..], &public));
	}

	#[test]
	fn seeded_pair_should_work() {

		let pair = Pair::from_seed(*b"12345678901234567890123456789012");
		let public = pair.public();
		assert_eq!(
			public,
			Public::from_raw(hex!(
				"741c08a06f41c596608f6774259bd9043304adfa5d3eea62760bd9be97634d63"
			))
		);
		let message = hex!("2f8c6129d816cf51c374bc7f08c3e63ed156cf78aefb4a6550d97b87997977ee00000000000000000200d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a4500000000000000");
		let signature = pair.sign(&message[..]);
		assert!(Pair::verify(&signature, &message[..], &public));
	}

	#[test]
	fn ss58check_roundtrip_works() {
		let pair = Pair::generate();
		let public = pair.public();
		let s = public.to_ss58check();
		println!("Correct: {}", s);
		let cmp = Public::from_ss58check(&s).unwrap();
		assert_eq!(cmp, public);
	}

	#[test]
	fn verify_from_wasm_works() {
		// The values in this test case are compared to the output of `node-test.js` in schnorrkel-js.
		// 
		// This is to make sure that the wasm library is compatible.
		let pk = Pair::from_seed(hex!("0000000000000000000000000000000000000000000000000000000000000000"));
		let public = pk.public();
		let js_signature = Signature::from_raw(hex!("28a854d54903e056f89581c691c1f7d2ff39f8f896c9e9c22475e60902cc2b3547199e0e91fa32902028f2ca2355e8cdd16cfe19ba5e8b658c94aa80f3b81a00"));
		assert!(Pair::verify(&js_signature, b"SUBSTRATE", public));
	}
}
