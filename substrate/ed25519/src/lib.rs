// Copyright 2017 Parity Technologies (UK) Ltd.
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

//! Simple Ed25519 API.

extern crate ring;
extern crate substrate_primitives as primitives;
extern crate untrusted;

use ring::{rand, signature};
use primitives::hash::H512;

#[cfg(test)]
#[macro_use]
extern crate hex_literal;

/// Alias to 512-bit hash when used in the context of a signature on the relay chain.
pub type Signature = H512;

/// Length of the PKCS#8 encoding of the key.
pub const PKCS_LEN: usize = 85;

/// A localized signature also contains sender information.
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct LocalizedSignature {
	/// The signer of the signature.
	pub signer: Public,
	/// The signature itself.
	pub signature: Signature,
}

/// Verify a message without type checking the parameters' types for the right size.
pub fn verify(sig: &[u8], message: &[u8], public: &[u8]) -> bool {
	let public_key = untrusted::Input::from(public);
	let msg = untrusted::Input::from(message);
	let sig = untrusted::Input::from(sig);

	match signature::verify(&signature::ED25519, public_key, msg, sig) {
		Ok(_) => true,
		_ => false,
	}
}

/// A public key.
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct Public(pub [u8; 32]);

/// A key pair.
pub struct Pair(signature::Ed25519KeyPair);

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

impl Pair {
	/// Generate new secure (random) key pair, yielding it and the corresponding pkcs#8 bytes.
	pub fn generate_with_pkcs8() -> (Self, [u8; PKCS_LEN]) {
		let rng = rand::SystemRandom::new();
		let pkcs8_bytes = signature::Ed25519KeyPair::generate_pkcs8(&rng).expect("system randomness is available; qed");
		let pair = Self::from_pkcs8(&pkcs8_bytes).expect("just-generated pkcs#8 data is valid; qed");

		(pair, pkcs8_bytes)
	}

	/// Generate new secure (random) key pair.
	pub fn generate() -> Pair {
		let (pair, _) = Self::generate_with_pkcs8();
		pair
	}

	/// Generate from pkcs#8 bytes.
	pub fn from_pkcs8(pkcs8_bytes: &[u8]) -> Result<Self, ::ring::error::Unspecified> {
		signature::Ed25519KeyPair::from_pkcs8(untrusted::Input::from(&pkcs8_bytes)).map(Pair)
	}

	/// Make a new key pair from a seed phrase.
	/// NOTE: prefer pkcs#8 unless security doesn't matter -- this is used primarily for tests.
	pub fn from_seed(seed: &[u8; 32]) -> Pair {
		let key = signature::Ed25519KeyPair::from_seed_unchecked(untrusted::Input::from(&seed[..]))
			.expect("seed has valid length; qed");

		Pair(key)
	}

	/// Sign a message.
	pub fn sign(&self, message: &[u8]) -> Signature {
		let mut r = [0u8; 64];
		r.copy_from_slice(self.0.sign(message).as_ref());
		Signature::from(r)
	}

	/// Get the public key.
	pub fn public(&self) -> Public {
		let mut r = [0u8; 32];
		let pk = self.0.public_key_bytes();
		r.copy_from_slice(pk);
		Public(r)
	}

	/// Derive a child key. Probably unsafe and broken.
	// TODO: proper HD derivation https://cardanolaunch.com/assets/Ed25519_BIP.pdf
	pub fn derive_child_probably_bad(&self, chain_data: &[u8]) -> Pair {
		let sig = self.sign(chain_data);
		let mut seed = [0u8; 32];
		seed.copy_from_slice(&sig.0[..32]);

		Pair::from_seed(&seed)
	}
}

/// Verify a signature on a message.
pub fn verify_strong(sig: &Signature, message: &[u8], pubkey: &Public) -> bool {
	let public_key = untrusted::Input::from(&pubkey.0[..]);
	let msg = untrusted::Input::from(message);
	let sig = untrusted::Input::from(&sig.0[..]);

	match signature::verify(&signature::ED25519, public_key, msg, sig) {
		Ok(_) => true,
		_ => false,
	}
}

pub trait Verifiable {
	/// Verify something that acts like a signature.
	fn verify(&self, message: &[u8], pubkey: &Public) -> bool;
}

impl Verifiable for Signature {
	/// Verify something that acts like a signature.
	fn verify(&self, message: &[u8], pubkey: &Public) -> bool {
		verify_strong(&self, message, pubkey)
	}
}

impl Verifiable for LocalizedSignature {
	fn verify(&self, message: &[u8], pubkey: &Public) -> bool {
		pubkey == &self.signer && self.signature.verify(message, pubkey)
	}
}

#[cfg(test)]
mod test {
	use super::*;

	fn _test_primitives_signature_and_local_the_same() {
		fn takes_two<T>(_: T, _: T) { }
		takes_two(Signature::default(), primitives::Signature::default())
	}

	#[test]
	fn test_vector_should_work() {
		let pair: Pair = Pair::from_seed(&hex!("9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60"));
		let public = pair.public();
		assert_eq!(public, Public::from_raw(hex!("d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a")));
		let message = b"";
		let signature: Signature = hex!("e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b").into();
		assert!(&pair.sign(&message[..]) == &signature);
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
		use primitives::hexdisplay::HexDisplay;

		let pair = Pair::from_seed(b"12345678901234567890123456789012");
		let public = pair.public();
		assert_eq!(public, Public::from_raw(hex!("2f8c6129d816cf51c374bc7f08c3e63ed156cf78aefb4a6550d97b87997977ee")));
		let message = hex!("2f8c6129d816cf51c374bc7f08c3e63ed156cf78aefb4a6550d97b87997977ee00000000000000002228000000d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a4500000000000000");
		let signature = pair.sign(&message[..]);
		println!("Correct signature: {}", HexDisplay::from(&signature.0));
		assert!(verify_strong(&signature, &message[..], &public));
	}

	#[test]
	fn generate_with_pkcs8_recovery_possible() {
		let (pair1, pkcs8) = Pair::generate_with_pkcs8();
		let pair2 = Pair::from_pkcs8(&pkcs8).unwrap();

		assert_eq!(pair1.public(), pair2.public());
	}

	#[test]
	fn derive_child() {
		let pair = Pair::generate();
		let _pair2 = pair.derive_child_probably_bad(b"session_1234");
	}
}
