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

//! Shareable Polkadot types.

#![warn(missing_docs)]

extern crate rustc_hex;
extern crate serde;
extern crate tiny_keccak;
extern crate crypto;

#[macro_use]
extern crate crunchy;
#[macro_use]
extern crate fixed_hash;
#[macro_use]
extern crate serde_derive;
#[macro_use]
extern crate uint as uint_crate;

#[cfg(feature="std")]
extern crate core;
#[cfg(test)]
extern crate polkadot_serializer;
#[cfg(test)]
#[macro_use]
extern crate pretty_assertions;

mod bytes;
pub mod block;
pub mod contract;
pub mod hash;
pub mod parachain;
pub mod uint;
pub mod validator;

/// Alias to 160-bit hash when used in the context of an account address.
pub type Address = hash::H160;
/// Alias to 520-bit hash when used in the context of a signature.
pub type Signature = hash::H520;

pub use self::hash::{H160, H256};
pub use self::uint::{U256, U512};

/// A hash function.
pub fn hash(data: &[u8]) -> hash::H256 {
	tiny_keccak::keccak256(data).into()
}

/// Cool module.
pub mod ed25519 {
	use crypto;
	use rustc_hex::FromHex;

	#[derive(PartialEq, Clone)]
	struct Public ([u8; 32]);
	#[derive(Clone)]
	struct Pair ([u8; 64]);
	#[derive(Clone)]
	struct Signature ([u8; 64]);
	impl Pair {
		pub fn from_seed(seed: &[u8]) -> Pair {
			let (secret_public, public) = crypto::ed25519::keypair(seed);
			assert_eq!(&secret_public[32..64], &public[0..32]);
			Pair(secret_public)
		}
		pub fn sign(&self, message: &[u8]) -> Signature {
			Signature(crypto::ed25519::signature(message, &self.0))
		}
		pub fn public(&self) -> Public {
			let mut r = [0u8; 32];
			r.copy_from_slice(&self.0[32..64]);
			Public(r)
		}
	}
	impl From<&'static str> for Public {
		fn from(hex: &'static str) -> Self {
			let mut r = [0u8; 32];
			r.copy_from_slice(&FromHex::from_hex(hex).unwrap()[0..32]);
			Public(r)
		}
	}
	impl From<&'static str> for Pair {
		fn from(hex: &'static str) -> Self {
			let mut r = [0u8; 64];
			r.copy_from_slice(&FromHex::from_hex(hex).unwrap()[0..64]);
			Pair(r)
		}
	}
	impl From<&'static str> for Signature {
		fn from(hex: &'static str) -> Self {
			let mut r = [0u8; 64];
			r.copy_from_slice(&FromHex::from_hex(hex).unwrap()[0..64]);
			Signature(r)
		}
	}

	impl PartialEq for Signature {
		fn eq(&self, other: &Signature) -> bool {
			self.0.iter().eq(other.0.iter())
		}
	}

	impl PartialEq for Pair {
		fn eq(&self, other: &Pair) -> bool {
			self.0.iter().eq(other.0.iter())
		}
	}

	impl Signature {
		fn verify(&self, message: &[u8], public: &Public) -> bool {
			crypto::ed25519::verify(message, &public.0, &self.0)
		}
	}

	#[cfg(test)]
	mod test {
		use super::*;

		#[test]
		fn test_vector_should_work() {
			let pair: Pair = "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a".into();
			let public = pair.public();
			let message = b"";
			let signature: Signature = "e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b".into();
			assert!(&pair.sign(&message[..]) == &signature);
			assert!(signature.verify(&message[..], &public));
		}

		#[test]
		fn generated_pair_should_work() {
			let pair = Pair::from_seed(b"test");
			let public = pair.public();
			let message = b"Something important";
			let signature = pair.sign(&message[..]);
			assert!(signature.verify(&message[..], &public));
		}
	}
}
