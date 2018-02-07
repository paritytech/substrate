// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! Simple Ed25519 API.

extern crate ring;
extern crate polkadot_primitives as primitives;
extern crate untrusted;
extern crate rustc_hex;

use ring::{rand, signature};
use primitives::hash::H512;
use rustc_hex::FromHex;

/// Alias to 520-bit hash when used in the context of a signature on the relay chain.
pub type Signature = H512;

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
#[derive(PartialEq, Clone, Debug)]
pub struct Public ([u8; 32]);

/// A key pair.
pub struct Pair(signature::Ed25519KeyPair);

impl Public {
	/// A new instance from the given 32-byte `data`.
	pub fn from(data: [u8; 32]) -> Self {
		Public(data)
	}

	/// A new instance from the given slice that should be 32 bytes long.
	pub fn from_slice(data: &[u8]) -> Self {
		let mut r = [0u8; 32];
		r.copy_from_slice(data);
		Public(r)
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

impl Pair {
	/// Generate new secure (random) key pair.
	pub fn new() -> Pair {
		let rng = rand::SystemRandom::new();
		let pkcs8_bytes = signature::Ed25519KeyPair::generate_pkcs8(&rng).unwrap();
		Pair(signature::Ed25519KeyPair::from_pkcs8(untrusted::Input::from(&pkcs8_bytes)).unwrap())
	}
	/// Make a new key pair from a seed phrase.
	pub fn from_seed(seed: &[u8; 32]) -> Pair {
		Pair(signature::Ed25519KeyPair::from_seed_unchecked(untrusted::Input::from(&seed[..])).unwrap())
	}
	/// Make a new key pair from the raw secret.
	pub fn from_secret(secret: &[u8; 32]) -> Pair {
		let mut pkcs8_bytes: Vec<_> = FromHex::from_hex("302e020100300506032b657004220420").unwrap();
		pkcs8_bytes.extend_from_slice(&secret[..]);
		Pair(signature::Ed25519KeyPair::from_pkcs8_maybe_unchecked(untrusted::Input::from(&pkcs8_bytes)).unwrap())
	}
	/// Make a new key pair from the raw secret and public key (it will check to make sure
	/// they correspond to each other).
	pub fn from_both(secret_public: &[u8; 64]) -> Option<Pair> {
		let mut pkcs8_bytes: Vec<_> = FromHex::from_hex("3053020101300506032b657004220420").unwrap();
		pkcs8_bytes.extend_from_slice(&secret_public[0..32]);
		pkcs8_bytes.extend_from_slice(&[0xa1u8, 0x23, 0x03, 0x21, 0x00]);
		pkcs8_bytes.extend_from_slice(&secret_public[32..64]);
		signature::Ed25519KeyPair::from_pkcs8_maybe_unchecked(untrusted::Input::from(&pkcs8_bytes)).ok().map(Pair)
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

impl From<&'static str> for Public {
	fn from(hex: &'static str) -> Self {
		let mut r = [0u8; 32];
		let v: Vec<_> = FromHex::from_hex(hex).unwrap();
		r.copy_from_slice(&v[0..32]);
		Public(r)
	}
}
impl From<&'static str> for Pair {
	fn from(hex: &'static str) -> Self {
		let data: Vec<_> = FromHex::from_hex(hex).expect("Key pair given is static so hex should be good.");
		match data.len() {
			32 => {
				let mut r = [0u8; 32];
				r.copy_from_slice(&data[0..32]);
				Pair::from_secret(&r)
			}
			64 => {
				let mut r = [0u8; 64];
				r.copy_from_slice(&data[0..64]);
				Pair::from_both(&r).expect("Key pair given is static so should be good.")
			}
			_ => {
				panic!("Key pair given is static so should be correct length.");
			}
		}
	}
}

#[cfg(test)]
mod test {
	use super::*;

	#[test]
	fn test_vector_should_work() {
		let pair: Pair = "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60".into();
		let public = pair.public();
		assert_eq!(public, "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a".into());
		let message = b"";
		let signature: Signature = "e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b".into();
		assert!(&pair.sign(&message[..]) == &signature);
		assert!(verify_strong(&signature, &message[..], &public));
	}

	#[test]
	fn generated_pair_should_work() {
		let pair = Pair::new();
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
		assert_eq!(public, "2f8c6129d816cf51c374bc7f08c3e63ed156cf78aefb4a6550d97b87997977ee".into());
		let message: Vec<_> = FromHex::from_hex("2f8c6129d816cf51c374bc7f08c3e63ed156cf78aefb4a6550d97b87997977ee00000000000000002228000000d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a4500000000000000").unwrap();
		let signature = pair.sign(&message[..]);
		println!("Correct signature: {}", HexDisplay::from(&signature.0));
		assert!(verify_strong(&signature, &message[..], &public));
	}
}
