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
// end::description[]

use base58::{FromBase58, ToBase58};
use blake2_rfc;
use rand::rngs::OsRng;
use schnorrkel::{signing_context, Keypair, SecretKey, MiniSecretKey, PublicKey,
	derive::{Derivation, ChainCode, CHAIN_CODE_LENGTH}
};
use substrate_bip39::mini_secret_from_entropy;
//use sha2::Sha512;
use parity_codec::{Encode, Decode};
use crate::hash::H512;
use bip39::{Mnemonic, Language};

#[cfg(feature = "std")]
use serde::{de, Deserialize, Deserializer, Serializer};

// signing context
const SIGNING_CTX: &'static [u8] = b"substrate transaction";

/// An Schnorrkel/Ristretto x25519 ("sr25519") signature.
///
/// Instead of importing it for the local module, alias it to be available as a public type
pub type Signature = H512;

/// A localized signature also contains sender information.
/// NOTE: Encode and Decode traits are supported in ed25519 but not possible for now here.
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct LocalizedSignature {
	/// The signer of the signature.
	pub signer: Public,
	/// The signature itself.
	pub signature: Signature,
}

/// An Schnorrkel/Ristretto x25519 ("sr25519") public key.
#[derive(PartialEq, Eq, Clone, Encode, Decode)]
pub struct Public(pub [u8; 32]);

/// An Schnorrkel/Ristretto x25519 ("sr25519") key pair.
pub struct Pair(Keypair);

impl ::std::hash::Hash for Public {
	fn hash<H: ::std::hash::Hasher>(&self, state: &mut H) {
		self.0.hash(state);
	}
}

/// An error type for SS58 decoding.
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
	pub fn from_raw(data: [u8; 32]) -> Self {
		Public(data)
	}

	/// A new instance from the given slice that should be 32 bytes long.
	pub fn from_slice(data: &[u8]) -> Self {
		let mut r = [0u8; 32];
		r.copy_from_slice(data);
		Public(r)
	}

	/// Some if the string is a properly encoded SS58Check address.
	pub fn from_ss58check(s: &str) -> Result<Self, PublicError> {
		let d = s.from_base58().map_err(|_| PublicError::BadBase58)?; // failure here would be invalid encoding.
		if d.len() != 35 {
			// Invalid length.
			return Err(PublicError::BadLength);
		}
		if d[0] != 42 {
			// Invalid version.
			return Err(PublicError::UnknownVersion);
		}
		if d[33..35] != blake2_rfc::blake2b::blake2b(64, &[], &d[0..33]).as_bytes()[0..2] {
			// Invalid checksum.
			return Err(PublicError::InvalidChecksum);
		}
		Ok(Self::from_slice(&d[1..33]))
	}

	/// Return a `Vec<u8>` filled with raw data.
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

	/// Return the ss58-check string for this key.
	pub fn to_ss58check(&self) -> String {
		let mut v = vec![42u8];
		v.extend(self.as_slice());
		let r = blake2_rfc::blake2b::blake2b(64, &[], &v);
		v.extend(&r.as_bytes()[0..2]);
		v.to_base58()
	}

	/// Derive a child key from a series of given junctions.
	///
	/// `None` if there are any hard junctions in there.
	pub fn derive<Iter: Iterator<Item=DeriveJunction>>(&self, mut path: Iter) -> Option<Public> {
		let mut acc = PublicKey::from_bytes(self.as_ref()).ok()?;
		for j in path {
			match j {
				DeriveJunction::Soft(cc) => acc = acc.derived_key_simple(ChainCode(cc), &[]).0,
				DeriveJunction::Hard(cc) => return None,
			}
		}
		Some(Self(acc.to_bytes()))
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

impl Into<[u8; 32]> for Public {
	fn into(self) -> [u8; 32] {
		self.0
	}
}

impl AsRef<Public> for Public {
	fn as_ref(&self) -> &Public {
		&self
	}
}

impl AsRef<Pair> for Pair {
	fn as_ref(&self) -> &Pair {
		&self
	}
}

impl From<MiniSecretKey> for Pair {
	fn from(sec: MiniSecretKey) -> Pair {
		Pair(sec.expand_to_keypair())
	}
}

impl From<SecretKey> for Pair {
	fn from(sec: SecretKey) -> Pair {
		Pair(Keypair::from(sec))
	}
}

impl From<schnorrkel::Keypair> for Pair {
	fn from(p: schnorrkel::Keypair) -> Pair {
		Pair(p)
	}
}

impl From<Pair> for schnorrkel::Keypair {
	fn from(p: Pair) -> schnorrkel::Keypair {
		p.0
	}
}

impl AsRef<schnorrkel::Keypair> for Pair {
	fn as_ref(&self) -> &schnorrkel::Keypair {
		&self.0
	}
}

impl ::std::fmt::Display for Public {
	fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
		write!(f, "{}", self.to_ss58check())
	}
}

impl ::std::fmt::Debug for Public {
	fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
		let s = self.to_ss58check();
		write!(f, "{} ({}...)", crate::hexdisplay::HexDisplay::from(&self.0), &s[0..8])
	}
}

/// A since derivation junction description. It is the single parameter used when creating
/// a new secret key from an existing secret key and, in the case of `SoftRaw` and `SoftIndex`
/// a new public key from an existing public key.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug, Encode, Decode)]
pub enum DeriveJunction {
	/// Soft (vanilla) derivation. Public keys have a correspondent derivation.
	Soft([u8; CHAIN_CODE_LENGTH]),
	/// Hard ("hardened") derivation. Public keys do not have a correspondent derivation.
	Hard([u8; CHAIN_CODE_LENGTH]),
}

impl DeriveJunction {
	/// Consume self to return a soft derive junction with the same chain code.
	pub fn soften(self) -> Self { DeriveJunction::Soft(self.unwrap_inner()) }

	/// Consume self to return a hard derive junction with the same chain code.
	pub fn harden(self) -> Self { DeriveJunction::Hard(self.unwrap_inner()) }

	/// Create a new soft (vanilla) DeriveJunction from a given, encodable, value.
	///
	/// If you need a hard junction, use `hard()`.
	pub fn soft<T: Encode>(index: T) -> Self {
		let mut cc: [u8; CHAIN_CODE_LENGTH] = Default::default();
		index.using_encoded(|data| if data.len() > CHAIN_CODE_LENGTH {
			let hash_result = blake2_rfc::blake2b::blake2b(CHAIN_CODE_LENGTH, &[], data);
			let hash = hash_result.as_bytes();
			cc.copy_from_slice(hash);
		} else {
			cc[0..data.len()].copy_from_slice(data);
		});
		DeriveJunction::Soft(cc)
	}

	/// Create a new hard (hardened) DeriveJunction from a given, encodable, value.
	///
	/// If you need a soft junction, use `soft()`.
	pub fn hard<T: Encode>(index: T) -> Self {
		Self::soft(index).harden()
	}

	/// Consume self to return the chain code.
	pub fn unwrap_inner(self) -> [u8; CHAIN_CODE_LENGTH] {
		match self {
			DeriveJunction::Hard(c) | DeriveJunction::Soft(c) => c,
		}
	}

	/// Consume self to return the chain code.
	pub fn unwrap_chain_code(self) -> ChainCode {
		ChainCode(self.unwrap_inner())
	}

	/// Return a reference to the chain code.
	pub fn chain_code(&self) -> ChainCode {
		self.clone().unwrap_chain_code()
	}

	/// Return `true` if the junction is soft.
	pub fn is_soft(&self) -> bool {
		match *self {
			DeriveJunction::Soft(_) => true,
			_ => false,
		}
	}

	/// Return `true` if the junction is hard.
	pub fn is_hard(&self) -> bool {
		match *self {
			DeriveJunction::Hard(_) => true,
			_ => false,
		}
	}
}

/// Derive a single hard junction.
fn derive_hard_junction(secret: &SecretKey, cc: &[u8; CHAIN_CODE_LENGTH]) -> SecretKey {
	("SchnorrRistrettoHDKD", &secret.to_bytes()[..], cc).using_encoded(|data|
		MiniSecretKey::from_bytes(blake2_rfc::blake2b::blake2b(32, &[], data).as_bytes())
			.expect("all 32-byte crypto-hash results are valid MiniSecretKeys; qed")
			.expand()
	)
}

impl Pair {
	/// Generate new secure (random) key pair.
	pub fn generate() -> Pair {
		let mut csprng: OsRng = OsRng::new().expect("os random generator works; qed");
		let key_pair: Keypair = Keypair::generate(&mut csprng);
		Pair(key_pair)
	}

	/// Make a new key pair from a seed phrase.
	/// This is generated using schnorrkel's Mini-Secret-Keys.
	/// A MiniSecretKey is literally what Ed25519 calls a SecretKey, which is just 32 random bytes.
	pub fn from_seed(seed: &[u8; 32]) -> Pair {
		let mini_key: MiniSecretKey = MiniSecretKey::from_bytes(seed)
			.expect("32 bytes can always build a key; qed");
		let kp = mini_key.expand_to_keypair();
		Pair(kp)
	}

	/// Make a new key pair from a seed phrase.
	/// This is generated using schnorrkel's Mini-Secret-Keys.
	/// A MiniSecretKey is literally what Ed25519 calls a SecretKey, which is just 32 random bytes.
	pub fn from_entropy(entropy: &[u8], password: Option<&str>) -> Pair {
		let mini_key: MiniSecretKey = mini_secret_from_entropy(entropy, password.unwrap_or(""))
			.expect("32 bytes can always build a key; qed");
		let kp = mini_key.expand_to_keypair();
		Pair(kp)
	}

	/// Returns the KeyPair from the English BIP39 seed `phrase`, or `None` if it's invalid.
	pub fn from_phrase(phrase: &str, password: Option<&str>) -> Option<Pair> {
		Mnemonic::from_phrase(phrase, Language::English)
			.ok()
			.map(|m| Self::from_entropy(m.entropy(), password))
	}

	/// Derive a child key from a series of given junctions.
	pub fn derive<Iter: Iterator<Item=DeriveJunction>>(&self, mut path: Iter) -> Pair {
		let init = self.0.secret.clone();
		let result = path.fold(init, |acc, j| match j {
			DeriveJunction::Soft(cc) => acc.derived_key_simple(ChainCode(cc), &[]).0,
			DeriveJunction::Hard(cc) => derive_hard_junction(&acc, &cc),
		});
		Self(result.into())
	}

	/// Sign a message.
	pub fn sign(&self, message: &[u8]) -> Signature {
		let context = signing_context(SIGNING_CTX);
		Signature::from(self.0.sign(context.bytes(message)).to_bytes())
	}

	/// Get the public key.
	pub fn public(&self) -> Public {
		let mut pk = [0u8; 32];
		pk.copy_from_slice(&self.0.public.to_bytes());
		Public(pk)
	}
}

/// Verify a signature on a message. Returns true if the signature is good.
pub fn verify_strong<P: AsRef<Public>>(sig: &Signature, message: &[u8], pubkey: P) -> bool {
	let signature: schnorrkel::Signature = match schnorrkel::Signature::from_bytes(&sig[..]) {
		Ok(some_signature) => some_signature,
		Err(_) => return false
	};
	match PublicKey::from_bytes(pubkey.as_ref().as_slice()) {
		Ok(pk) => pk.verify(signing_context(SIGNING_CTX).bytes(message), &signature),
		Err(_) => false,
	}
}

/// Verify a message without type checking the parameters' types for the right size.
/// Returns true if both the pubkey and the signature is good.
pub fn verify<P: AsRef<[u8]>>(sig: &[u8], message: &[u8], pubkey: P) -> bool {
	let signature = match schnorrkel::Signature::from_bytes(&sig[..]) {
		Ok(sig) => sig,
		Err(_) => return false,
	};
	match PublicKey::from_bytes(pubkey.as_ref()) {
		Ok(pk) => pk.verify_simple(SIGNING_CTX, message, &signature),
		Err(_) => false,
	}
}

/// Something that acts as a signature allowing a message to be verified.
pub trait Verifiable {
	/// Verify something that acts like a signature.
	fn verify<P: AsRef<Public>>(&self, message: &[u8], pubkey: P) -> bool;
}

impl Verifiable for Signature {
	/// Verify something that acts like a signature.
	fn verify<P: AsRef<Public>>(&self, message: &[u8], pubkey: P) -> bool {
		verify_strong(&self, message, pubkey)
	}
}

impl Verifiable for LocalizedSignature {
	fn verify<P: AsRef<Public>>(&self, message: &[u8], pubkey: P) -> bool {
		pubkey.as_ref() == &self.signer && self.signature.verify(message, pubkey)
	}
}

/// Deserialize from `ss58` into something that can be constructed from `[u8; 32]`.
#[cfg(feature = "std")]
pub fn deserialize<'de, D, T: From<[u8; 32]>>(deserializer: D) -> Result<T, D::Error>
where
	D: Deserializer<'de>,
{
	let ss58 = String::deserialize(deserializer)?;
	Public::from_ss58check(&ss58)
		.map_err(|e| de::Error::custom(format!("{:?}", e)))
		.map(|v| v.0.into())
}

/// Serializes something that implements `AsRef<[u8; 32]>` into `ss58`.
#[cfg(feature = "std")]
pub fn serialize<S, T: AsRef<[u8; 32]>>(data: &T, serializer: S) -> Result<S::Ok, S::Error>
where
	S: Serializer,
{
	serializer.serialize_str(&Public(*data.as_ref()).to_ss58check())
}

#[cfg(test)]
mod test {
	use super::*;
	use hex_literal::{hex, hex_impl};

	#[test]
	fn derive_soft_should_work() {
		let pair: Pair = Pair::from_seed(&hex!(
			"9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60"
		));
		let derive_1 = pair.derive(Some(DeriveJunction::soft(1)).into_iter());
		let derive_1b = pair.derive(Some(DeriveJunction::soft(1)).into_iter());
		let derive_2 = pair.derive(Some(DeriveJunction::soft(2)).into_iter());
		assert_eq!(derive_1.public(), derive_1b.public());
		assert_ne!(derive_1.public(), derive_2.public());
	}

	#[test]
	fn derive_hard_should_work() {
		let pair: Pair = Pair::from_seed(&hex!(
			"9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60"
		));
		let derive_1 = pair.derive(Some(DeriveJunction::hard(1)).into_iter());
		let derive_1b = pair.derive(Some(DeriveJunction::hard(1)).into_iter());
		let derive_2 = pair.derive(Some(DeriveJunction::hard(2)).into_iter());
		assert_eq!(derive_1.public(), derive_1b.public());
		assert_ne!(derive_1.public(), derive_2.public());
	}

	#[test]
	fn derive_soft_public_should_work() {
		let pair: Pair = Pair::from_seed(&hex!(
			"9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60"
		));
		let path = Some(DeriveJunction::soft(1));
		let pair_1 = pair.derive(path.clone().into_iter());
		let public_1 = pair.public().derive(path.into_iter()).unwrap();
		assert_eq!(pair_1.public(), public_1);
	}

	#[test]
	fn derive_hard_public_should_fail() {
		let pair: Pair = Pair::from_seed(&hex!(
			"9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60"
		));
		let path = Some(DeriveJunction::hard(1));
		assert!(pair.public().derive(path.into_iter()).is_none());
	}

	#[test]
	fn sr_test_vector_should_work() {
		let pair: Pair = Pair::from_seed(&hex!(
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
		assert!(verify(&signature[..], message, &public.0));
		assert!(verify_strong(&signature, &message[..], &public));
	}

	#[test]
	fn generated_pair_should_work() {
		let pair = Pair::generate();
		let public = pair.public();
		let message = b"Something important";
		let signature = pair.sign(&message[..]);
		assert!(verify_strong(&signature, &message[..], &public));
	}

	#[test]
	fn seeded_pair_should_work() {

		let pair = Pair::from_seed(b"12345678901234567890123456789012");
		let public = pair.public();
		assert_eq!(
			public,
			Public::from_raw(hex!(
				"741c08a06f41c596608f6774259bd9043304adfa5d3eea62760bd9be97634d63"
			))
		);
		let message = hex!("2f8c6129d816cf51c374bc7f08c3e63ed156cf78aefb4a6550d97b87997977ee00000000000000000200d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a4500000000000000");
		let signature = pair.sign(&message[..]);
		assert!(verify_strong(&signature, &message[..], &public));
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
	fn ss58check_known_works() {
		let k = "5CGavy93sZgPPjHyziRohwVumxiHXMGmQLyuqQP4ZFx5vRU9";
		let enc = hex!["090fa15cb5b1666222fff584b4cc2b1761fe1e238346b340491b37e25ea183ff"];
		assert_eq!(Public::from_ss58check(k).unwrap(), Public::from_raw(enc));
	}
}
