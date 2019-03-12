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
//! Cryptographic utilities.
// end::description[]

use parity_codec::{Encode, Decode};
use regex::Regex;

/// The infallible type.
#[derive(Debug)]
pub enum Infallible {}

/// The length of the junction identifier. Note that this is also referred to as the
/// `CHAIN_CODE_LENGTH` in the context of Schnorrkel.
pub const JUNCTION_ID_LEN: usize = 32;

/// A since derivation junction description. It is the single parameter used when creating
/// a new secret key from an existing secret key and, in the case of `SoftRaw` and `SoftIndex`
/// a new public key from an existing public key.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug, Encode, Decode)]
pub enum DeriveJunction {
	/// Soft (vanilla) derivation. Public keys have a correspondent derivation.
	Soft([u8; JUNCTION_ID_LEN]),
	/// Hard ("hardened") derivation. Public keys do not have a correspondent derivation.
	Hard([u8; JUNCTION_ID_LEN]),
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
		let mut cc: [u8; JUNCTION_ID_LEN] = Default::default();
		index.using_encoded(|data| if data.len() > JUNCTION_ID_LEN {
			let hash_result = blake2_rfc::blake2b::blake2b(JUNCTION_ID_LEN, &[], data);
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
	pub fn unwrap_inner(self) -> [u8; JUNCTION_ID_LEN] {
		match self {
			DeriveJunction::Hard(c) | DeriveJunction::Soft(c) => c,
		}
	}

	/// Get a reference to the inner junction id.
	pub fn inner(&self) -> &[u8; JUNCTION_ID_LEN] {
		match self {
			DeriveJunction::Hard(ref c) | DeriveJunction::Soft(ref c) => c,
		}
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

impl<'a> From<&'a str> for DeriveJunction {
	fn from(j: &'a str) -> DeriveJunction {
		let (code, hard) = if j.starts_with("/") {
			(&j[1..], true)
		} else {
			(j, false)
		};

		let res = if let Ok(n) = str::parse::<u64>(code) {
			// number
			DeriveJunction::soft(n)
		} else {
			// something else
			DeriveJunction::soft(code)
		};

		if hard {
			res.harden()
		} else {
			res
		}
	}
}

/// Trait suitable for typical cryptographic PKI key pair type.
///
/// For now it just specifies how to create a key from a phrase and derivation path.
pub trait Pair: Sized {
	/// TThe type which is used to encode a public key.
	type Public;

	/// The type used to (minimally) encode the data required to securely create
	/// a new key pair.
	type Seed;

	/// The type used to represent a signature. Can be created from a key pair and a message
	/// and verified with the message and a public key.
	type Signature;

	/// Error returned from the `derive` function.
	type DeriveError;

	/// Generate new secure (random) key pair.
	///
	/// This is only for ephemeral keys really, since you won't have access to the secret key
	/// for storage. If you want a persistent key pair, use `generate_with_phrase` instead.
	fn generate() -> Self;

	/// Generate new secure (random) key pair and provide the recovery phrase.
	///
	/// You can recover the same key later with `from_phrase`.
	///
	/// This is generally slower than `generate()`, so prefer that unless you need to persist
	/// the key from the current session.
	fn generate_with_phrase(password: Option<&str>) -> (Self, String);

	/// Returns the KeyPair from the English BIP39 seed `phrase`, or `None` if it's invalid.
	fn from_phrase(phrase: &str, password: Option<&str>) -> Option<Self>;

	/// Derive a child key from a series of given junctions.
	fn derive<Iter: Iterator<Item=DeriveJunction>>(&self, path: Iter) -> Result<Self, Self::DeriveError>;

	/// Generate new key pair from the provided `seed`.
	///
	/// @WARNING: THIS WILL ONLY BE SECURE IF THE `seed` IS SECURE. If it can be guessed
	/// by an attacker then they can also derive your key.
	fn from_seed(seed: Self::Seed) -> Self;

	/// Make a new key pair from secret seed material. The slice must be the correct size or
	/// it will return `None`.
	///
	/// @WARNING: THIS WILL ONLY BE SECURE IF THE `seed` IS SECURE. If it can be guessed
	/// by an attacker then they can also derive your key.
	fn from_seed_slice(seed: &[u8]) -> Option<Self>;

	/// Construct a key from a phrase, password and path.
	fn from_standard_components<
		I: Iterator<Item=DeriveJunction>
	>(phrase: &str, password: Option<&str>, path: I) -> Option<Self>;

	/// Sign a message.
	fn sign(&self, message: &[u8]) -> Self::Signature;

	/// Verify a signature on a message. Returns true if the signature is good.
	fn verify<P: AsRef<Self::Public>, M: AsRef<[u8]>>(sig: &Self::Signature, message: M, pubkey: P) -> bool;

	/// Verify a signature on a message. Returns true if the signature is good.
	fn verify_weak<P: AsRef<[u8]>, M: AsRef<[u8]>>(sig: &[u8], message: M, pubkey: P) -> bool;

	/// Get the public key.
	fn public(&self) -> Self::Public;

	/// Interprets the string `s` in order to generate a key Pair.
	///
	/// This takes a helper function to do the key generation from a phrase, password and
	/// junction iterator.
	///
	/// - If `s` is a possibly `0x` prefixed 64-digit hex string, then it will be interpreted
	/// directly as a `MiniSecretKey` (aka "seed" in `subkey`).
	/// - If `s` is a valid BIP-39 key phrase of 12, 15, 18, 21 or 24 words, then the key will
	/// be derived from it. In this case:
	///   - the phrase may be followed by one or more items delimited by `/` characters.
	///   - the path may be followed by `///`, in which case everything after the `///` is treated
	/// as a password.
	/// In this case they are interpreted as HDKD junctions; purely numeric items are interpreted as
	/// integers, non-numeric items as strings. Junctions prefixed with `/` are interpreted as soft
	/// junctions, and with `//` as hard junctions.
	///
	/// There is no correspondence mapping between SURI strings and the keys they represent.
	/// Two different non-identical strings can actually lead to the same secret being derived.
	/// Notably, integer junction indices may be legally prefixed with arbitrary number of zeros.
	/// Similarly an empty password (ending the SURI with `///`) is perfectly valid and will generally
	/// be equivalent to no password at all.
	///
	/// `None` is returned if no matches are found.
	/// TODO: should return Result that includes InvalidPhrase, InvalidPassword and InvalidSeed.
	fn from_string(s: &str, password_override: Option<&str>) -> Option<Self> {
		let hex_seed = if s.starts_with("0x") {
			&s[2..]
		} else {
			s
		};

		if let Ok(d) = hex::decode(hex_seed) {
			if let Some(r) = Self::from_seed_slice(&d) {
				return Some(r)
			}
		}

		let re = Regex::new(r"^(?P<phrase>\w+( \w+)*)(?P<path>(//?[^/]+)*)(///(?P<password>.*))?$")
			.expect("constructed from known-good static value; qed");
		let cap = re.captures(s)?;
		let re_junction = Regex::new(r"/(/?)([^/]+)")
			.expect("constructed from known-good static value; qed");
		let path = re_junction.captures_iter(&cap["path"])
			.map(|f| {
				let j = if let Ok(n) = str::parse::<u64>(&f[2]) {
					DeriveJunction::soft(n)
				} else {
					DeriveJunction::soft(&f[2])
				};
				if f[1].is_empty() { j } else { j.harden() }
			});
		Self::from_standard_components(
			&cap["phrase"],
			password_override.or_else(|| cap.name("password").map(|m| m.as_str())),
			path,
		)
	}
}

#[cfg(test)]
mod tests {
	use crate::DeriveJunction;
	use hex_literal::{hex, hex_impl};
	use super::*;

	#[derive(Eq, PartialEq, Debug)]
	enum TestPair {
		Generated,
		GeneratedWithPhrase,
		GeneratedFromPhrase{phrase: String, password: Option<String>},
		Standard{phrase: String, password: Option<String>, path: Vec<DeriveJunction>},
		Seed(Vec<u8>),
	}

	impl Pair for TestPair {
		type Public = ();
		type Seed = ();
		type Signature = ();
		type DeriveError = ();

		fn generate() -> Self { TestPair::Generated }
		fn generate_with_phrase(_password: Option<&str>) -> (Self, String) { (TestPair::GeneratedWithPhrase, "".into()) }
		fn from_phrase(phrase: &str, password: Option<&str>) -> Option<Self> {
			Some(TestPair::GeneratedFromPhrase{ phrase: phrase.to_owned(), password: password.map(Into::into) })
		}
		fn derive<Iter: Iterator<Item=DeriveJunction>>(&self, _path: Iter) -> Result<Self, Self::DeriveError> {
			Err(())
		}
		fn from_seed(_seed: Self::Seed) -> Self { TestPair::Seed(vec![]) }
		fn sign(&self, _message: &[u8]) -> Self::Signature { () }
		fn verify<P: AsRef<Self::Public>, M: AsRef<[u8]>>(_sig: &Self::Signature, _message: M, _pubkey: P) -> bool { true }
		fn verify_weak<P: AsRef<[u8]>, M: AsRef<[u8]>>(_sig: &[u8], _message: M, _pubkey: P) -> bool { true }
		fn public(&self) -> Self::Public { () }
		fn from_standard_components<I: Iterator<Item=DeriveJunction>>(phrase: &str, password: Option<&str>, path: I) -> Option<Self> {
			Some(TestPair::Standard { phrase: phrase.to_owned(), password: password.map(ToOwned::to_owned), path: path.collect() })
		}
		fn from_seed_slice(seed: &[u8]) -> Option<Self> {
			Some(TestPair::Seed(seed.to_owned()))
		}
	}

	#[test]
	fn interpret_std_seed_should_work() {
		assert_eq!(
			TestPair::from_string("0x0123456789abcdef", None),
			Some(TestPair::Seed(hex!["0123456789abcdef"][..].to_owned()))
		);
		assert_eq!(
			TestPair::from_string("0123456789abcdef", None),
			Some(TestPair::Seed(hex!["0123456789abcdef"][..].to_owned()))
		);
	}

	#[test]
	fn password_override_should_work() {
		assert_eq!(
			TestPair::from_string("hello world///password", None),
			TestPair::from_string("hello world", Some("password")),
		);
		assert_eq!(
			TestPair::from_string("hello world///password", None),
			TestPair::from_string("hello world///other password", Some("password")),
		);
	}

	#[test]
	fn interpret_std_secret_string_should_work() {
		assert_eq!(
			TestPair::from_string("hello world", None),
			Some(TestPair::Standard{phrase: "hello world".to_owned(), password: None, path: vec![]})
		);
		assert_eq!(
			TestPair::from_string("hello world/1", None),
			Some(TestPair::Standard{phrase: "hello world".to_owned(), password: None, path: vec![DeriveJunction::soft(1)]})
		);
		assert_eq!(
			TestPair::from_string("hello world/DOT", None),
			Some(TestPair::Standard{phrase: "hello world".to_owned(), password: None, path: vec![DeriveJunction::soft("DOT")]})
		);
		assert_eq!(
			TestPair::from_string("hello world//1", None),
			Some(TestPair::Standard{phrase: "hello world".to_owned(), password: None, path: vec![DeriveJunction::hard(1)]})
		);
		assert_eq!(
			TestPair::from_string("hello world//DOT", None),
			Some(TestPair::Standard{phrase: "hello world".to_owned(), password: None, path: vec![DeriveJunction::hard("DOT")]})
		);
		assert_eq!(
			TestPair::from_string("hello world//1/DOT", None),
			Some(TestPair::Standard{phrase: "hello world".to_owned(), password: None, path: vec![DeriveJunction::hard(1), DeriveJunction::soft("DOT")]})
		);
		assert_eq!(
			TestPair::from_string("hello world//DOT/1", None),
			Some(TestPair::Standard{phrase: "hello world".to_owned(), password: None, path: vec![DeriveJunction::hard("DOT"), DeriveJunction::soft(1)]})
		);
		assert_eq!(
			TestPair::from_string("hello world///password", None),
			Some(TestPair::Standard{phrase: "hello world".to_owned(), password: Some("password".to_owned()), path: vec![]})
		);
		assert_eq!(
			TestPair::from_string("hello world//1/DOT///password", None),
			Some(TestPair::Standard{phrase: "hello world".to_owned(), password: Some("password".to_owned()), path: vec![DeriveJunction::hard(1), DeriveJunction::soft("DOT")]})
		);
		assert_eq!(
			TestPair::from_string("hello world/1//DOT///password", None),
			Some(TestPair::Standard{phrase: "hello world".to_owned(), password: Some("password".to_owned()), path: vec![DeriveJunction::soft(1), DeriveJunction::hard("DOT")]})
		);
	}
}
