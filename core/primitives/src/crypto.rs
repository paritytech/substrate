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

#[cfg(feature = "std")]
use rand::{RngCore, rngs::OsRng};
#[cfg(feature = "std")]
use parity_codec::{Encode, Decode};
#[cfg(feature = "std")]
use regex::Regex;
#[cfg(feature = "std")]
use base58::{FromBase58, ToBase58};

/// The root phrase for our publicly known keys.
pub const DEV_PHRASE: &str = "bottom drive obey lake curtain smoke basket hold race lonely fit walk";

/// The address of the associated root phrase for our publicly known keys.
pub const DEV_ADDRESS: &str = "5DfhGyQdFobKM8NsWvEeAKk5EQQgYe9AydgJ7rMB6E1EqRzV";

/// The infallible type.
#[derive(Debug)]
pub enum Infallible {}

/// The length of the junction identifier. Note that this is also referred to as the
/// `CHAIN_CODE_LENGTH` in the context of Schnorrkel.
#[cfg(feature = "std")]
pub const JUNCTION_ID_LEN: usize = 32;

/// Similar to `From`, except that the onus is on the part of the caller to ensure
/// that data passed in makes sense. Basically, you're not guaranteed to get anything
/// sensible out.
pub trait UncheckedFrom<T> {
	/// Convert from an instance of `T` to Self. This is not guaranteed to be
	/// whatever counts as a valid instance of `T` and it's up to the caller to
	/// ensure that it makes sense.
	fn unchecked_from(t: T) -> Self;
}

/// The counterpart to `UncheckedFrom`.
pub trait UncheckedInto<T> {
	/// The counterpart to `unchecked_from`.
	fn unchecked_into(self) -> T;
}

impl<S, T: UncheckedFrom<S>> UncheckedInto<T> for S {
	fn unchecked_into(self) -> T {
		T::unchecked_from(self)
	}
}

/// An error with the interpretation of a secret.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg(feature = "std")]
pub enum SecretStringError {
	/// The overall format was invalid (e.g. the seed phrase contained symbols).
	InvalidFormat,
	/// The seed phrase provided is not a valid BIP39 phrase.
	InvalidPhrase,
	/// The supplied password was invalid.
	InvalidPassword,
	/// The seed is invalid (bad content).
	InvalidSeed,
	/// The seed has an invalid length.
	InvalidSeedLength,
	/// The derivation path was invalid (e.g. contains soft junctions when they are not supported).
	InvalidPath,
}

/// A since derivation junction description. It is the single parameter used when creating
/// a new secret key from an existing secret key and, in the case of `SoftRaw` and `SoftIndex`
/// a new public key from an existing public key.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug, Encode, Decode)]
#[cfg(feature = "std")]
pub enum DeriveJunction {
	/// Soft (vanilla) derivation. Public keys have a correspondent derivation.
	Soft([u8; JUNCTION_ID_LEN]),
	/// Hard ("hardened") derivation. Public keys do not have a correspondent derivation.
	Hard([u8; JUNCTION_ID_LEN]),
}

#[cfg(feature = "std")]
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

#[cfg(feature = "std")]
impl<T: AsRef<str>> From<T> for DeriveJunction {
	fn from(j: T) -> DeriveJunction {
		let j = j.as_ref();
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
	/// Invalid format.
	InvalidFormat,
	/// Invalid derivation path.
	InvalidPath,
}

/// Key that can be encoded to/from SS58.
#[cfg(feature = "std")]
pub trait Ss58Codec: Sized {
	/// Some if the string is a properly encoded SS58Check address.
	fn from_ss58check(s: &str) -> Result<Self, PublicError>;
	/// Some if the string is a properly encoded SS58Check address, optionally with
	/// a derivation path following.
	fn from_string(s: &str) -> Result<Self, PublicError> { Self::from_ss58check(s) }
	/// Return the ss58-check string for this key.
	fn to_ss58check(&self) -> String;
}

#[cfg(feature = "std")]
/// Derivable key trait.
pub trait Derive: Sized {
	/// Derive a child key from a series of given junctions.
	///
	/// Will be `None` for public keys if there are any hard junctions in there.
	fn derive<Iter: Iterator<Item=DeriveJunction>>(&self, _path: Iter) -> Option<Self> {
		None
	}
}

#[cfg(feature = "std")]
const PREFIX: &[u8] = b"SS58PRE";

#[cfg(feature = "std")]
fn ss58hash(data: &[u8]) -> blake2_rfc::blake2b::Blake2bResult {
	let mut context = blake2_rfc::blake2b::Blake2b::new(64);
	context.update(PREFIX);
	context.update(data);
	context.finalize()
}

#[cfg(feature = "std")]
impl<T: AsMut<[u8]> + AsRef<[u8]> + Default + Derive> Ss58Codec for T {
	fn from_ss58check(s: &str) -> Result<Self, PublicError> {
		let mut res = T::default();
		let len = res.as_mut().len();
		let d = s.from_base58().map_err(|_| PublicError::BadBase58)?; // failure here would be invalid encoding.
		if d.len() != len + 3 {
			// Invalid length.
			return Err(PublicError::BadLength);
		}
		if d[0] != 42 {
			// Invalid version.
			return Err(PublicError::UnknownVersion);
		}

		if d[len+1..len+3] != ss58hash(&d[0..len+1]).as_bytes()[0..2] {
			// Invalid checksum.
			return Err(PublicError::InvalidChecksum);
		}
		res.as_mut().copy_from_slice(&d[1..len+1]);
		Ok(res)
	}

	fn to_ss58check(&self) -> String {
		let mut v = vec![42u8];
		v.extend(self.as_ref());
		let r = ss58hash(&v);
		v.extend(&r.as_bytes()[0..2]);
		v.to_base58()
	}

	fn from_string(s: &str) -> Result<Self, PublicError> {
		let re = Regex::new(r"^(?P<ss58>[\w\d]+)?(?P<path>(//?[^/]+)*)$")
			.expect("constructed from known-good static value; qed");
		let cap = re.captures(s).ok_or(PublicError::InvalidFormat)?;
		let re_junction = Regex::new(r"/(/?[^/]+)")
			.expect("constructed from known-good static value; qed");
		let addr = Self::from_ss58check(
			cap.name("ss58")
				.map(|r| r.as_str())
				.unwrap_or(DEV_ADDRESS)
		)?;
		if cap["path"].is_empty() {
			Ok(addr)
		} else {
			let path = re_junction.captures_iter(&cap["path"])
				.map(|f| DeriveJunction::from(&f[1]));
			addr.derive(path)
				.ok_or(PublicError::InvalidPath)
		}
	}
}

/// Trait suitable for typical cryptographic PKI key pair type.
///
/// For now it just specifies how to create a key from a phrase and derivation path.
#[cfg(feature = "std")]
pub trait Pair: Sized + 'static {
	/// TThe type which is used to encode a public key.
	type Public;

	/// The type used to (minimally) encode the data required to securely create
	/// a new key pair.
	type Seed: Default + AsRef<[u8]> + AsMut<[u8]> + Clone;

	/// The type used to represent a signature. Can be created from a key pair and a message
	/// and verified with the message and a public key.
	type Signature;

	/// Error returned from the `derive` function.
	type DeriveError;

	/// Generate new secure (random) key pair.
	///
	/// This is only for ephemeral keys really, since you won't have access to the secret key
	/// for storage. If you want a persistent key pair, use `generate_with_phrase` instead.
	fn generate() -> (Self, Self::Seed) {
		let mut csprng: OsRng = OsRng::new().expect("OS random generator works; qed");
		let mut seed = Self::Seed::default();
		csprng.fill_bytes(seed.as_mut());
		(Self::from_seed(&seed), seed)
	}

	/// Generate new secure (random) key pair and provide the recovery phrase.
	///
	/// You can recover the same key later with `from_phrase`.
	///
	/// This is generally slower than `generate()`, so prefer that unless you need to persist
	/// the key from the current session.
	fn generate_with_phrase(password: Option<&str>) -> (Self, String, Self::Seed);

	/// Returns the KeyPair from the English BIP39 seed `phrase`, or `None` if it's invalid.
	fn from_phrase(phrase: &str, password: Option<&str>) -> Result<(Self, Self::Seed), SecretStringError>;

	/// Derive a child key from a series of given junctions.
	fn derive<Iter: Iterator<Item=DeriveJunction>>(&self, path: Iter) -> Result<Self, Self::DeriveError>;

	/// Generate new key pair from the provided `seed`.
	///
	/// @WARNING: THIS WILL ONLY BE SECURE IF THE `seed` IS SECURE. If it can be guessed
	/// by an attacker then they can also derive your key.
	fn from_seed(seed: &Self::Seed) -> Self;

	/// Make a new key pair from secret seed material. The slice must be the correct size or
	/// it will return `None`.
	///
	/// @WARNING: THIS WILL ONLY BE SECURE IF THE `seed` IS SECURE. If it can be guessed
	/// by an attacker then they can also derive your key.
	fn from_seed_slice(seed: &[u8]) -> Result<Self, SecretStringError>;

	/// Construct a key from a phrase, password and path.
	fn from_standard_components<
		I: Iterator<Item=DeriveJunction>
	>(phrase: &str, password: Option<&str>, path: I) -> Result<Self, SecretStringError>;

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
	/// - If `s` begins with a `/` character it is prefixed with the Substrate public `DEV_PHRASE` and
	/// interpreted as above.
	///
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
	fn from_string(s: &str, password_override: Option<&str>) -> Result<Self, SecretStringError> {
		let hex_seed = if s.starts_with("0x") {
			&s[2..]
		} else {
			s
		};

		if let Ok(d) = hex::decode(hex_seed) {
			if let Ok(r) = Self::from_seed_slice(&d) {
				return Ok(r)
			}
		}

		let re = Regex::new(r"^(?P<phrase>\w+( \w+)*)?(?P<path>(//?[^/]+)*)(///(?P<password>.*))?$")
			.expect("constructed from known-good static value; qed");
		let cap = re.captures(s).ok_or(SecretStringError::InvalidFormat)?;
		let re_junction = Regex::new(r"/(/?[^/]+)")
			.expect("constructed from known-good static value; qed");
		let path = re_junction.captures_iter(&cap["path"])
			.map(|f| DeriveJunction::from(&f[1]));
		Self::from_standard_components(
			cap.name("phrase").map(|r| r.as_str()).unwrap_or(DEV_PHRASE),
			password_override.or_else(|| cap.name("password").map(|m| m.as_str())),
			path,
		)
	}
}

#[cfg(test)]
mod tests {
	use crate::DeriveJunction;
	use hex_literal::hex;
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
		type Seed = [u8; 0];
		type Signature = ();
		type DeriveError = ();

		fn generate() -> (Self, <Self as Pair>::Seed) { (TestPair::Generated, []) }
		fn generate_with_phrase(_password: Option<&str>) -> (Self, String, <Self as Pair>::Seed) {
			(TestPair::GeneratedWithPhrase, "".into(), [])
		}
		fn from_phrase(phrase: &str, password: Option<&str>)
			-> Result<(Self, <Self as Pair>::Seed), SecretStringError>
		{
			Ok((TestPair::GeneratedFromPhrase {
				phrase: phrase.to_owned(),
				password: password.map(Into::into)
			}, []))
		}
		fn derive<Iter: Iterator<Item=DeriveJunction>>(&self, _path: Iter)
			-> Result<Self, Self::DeriveError>
		{
			Err(())
		}
		fn from_seed(_seed: &<TestPair as Pair>::Seed) -> Self { TestPair::Seed(vec![]) }
		fn sign(&self, _message: &[u8]) -> Self::Signature { () }
		fn verify<P: AsRef<Self::Public>, M: AsRef<[u8]>>(
			_sig: &Self::Signature,
			_message: M,
			_pubkey: P
		) -> bool { true }
		fn verify_weak<P: AsRef<[u8]>, M: AsRef<[u8]>>(
			_sig: &[u8],
			_message: M,
			_pubkey: P
		) -> bool { true }
		fn public(&self) -> Self::Public { () }
		fn from_standard_components<I: Iterator<Item=DeriveJunction>>(
			phrase: &str,
			password: Option<&str>,
			path: I
		) -> Result<Self, SecretStringError> {
			Ok(TestPair::Standard {
				phrase: phrase.to_owned(),
				password: password.map(ToOwned::to_owned),
				path: path.collect()
			})
		}
		fn from_seed_slice(seed: &[u8])
			-> Result<Self, SecretStringError>
		{
			Ok(TestPair::Seed(seed.to_owned()))
		}
	}

	#[test]
	fn interpret_std_seed_should_work() {
		assert_eq!(
			TestPair::from_string("0x0123456789abcdef", None),
			Ok(TestPair::Seed(hex!["0123456789abcdef"][..].to_owned()))
		);
		assert_eq!(
			TestPair::from_string("0123456789abcdef", None),
			Ok(TestPair::Seed(hex!["0123456789abcdef"][..].to_owned()))
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
			Ok(TestPair::Standard{phrase: "hello world".to_owned(), password: None, path: vec![]})
		);
		assert_eq!(
			TestPair::from_string("hello world/1", None),
			Ok(TestPair::Standard{phrase: "hello world".to_owned(), password: None, path: vec![DeriveJunction::soft(1)]})
		);
		assert_eq!(
			TestPair::from_string("hello world/DOT", None),
			Ok(TestPair::Standard{phrase: "hello world".to_owned(), password: None, path: vec![DeriveJunction::soft("DOT")]})
		);
		assert_eq!(
			TestPair::from_string("hello world//1", None),
			Ok(TestPair::Standard{phrase: "hello world".to_owned(), password: None, path: vec![DeriveJunction::hard(1)]})
		);
		assert_eq!(
			TestPair::from_string("hello world//DOT", None),
			Ok(TestPair::Standard{phrase: "hello world".to_owned(), password: None, path: vec![DeriveJunction::hard("DOT")]})
		);
		assert_eq!(
			TestPair::from_string("hello world//1/DOT", None),
			Ok(TestPair::Standard{phrase: "hello world".to_owned(), password: None, path: vec![DeriveJunction::hard(1), DeriveJunction::soft("DOT")]})
		);
		assert_eq!(
			TestPair::from_string("hello world//DOT/1", None),
			Ok(TestPair::Standard{phrase: "hello world".to_owned(), password: None, path: vec![DeriveJunction::hard("DOT"), DeriveJunction::soft(1)]})
		);
		assert_eq!(
			TestPair::from_string("hello world///password", None),
			Ok(TestPair::Standard{phrase: "hello world".to_owned(), password: Some("password".to_owned()), path: vec![]})
		);
		assert_eq!(
			TestPair::from_string("hello world//1/DOT///password", None),
			Ok(TestPair::Standard{phrase: "hello world".to_owned(), password: Some("password".to_owned()), path: vec![DeriveJunction::hard(1), DeriveJunction::soft("DOT")]})
		);
		assert_eq!(
			TestPair::from_string("hello world/1//DOT///password", None),
			Ok(TestPair::Standard{phrase: "hello world".to_owned(), password: Some("password".to_owned()), path: vec![DeriveJunction::soft(1), DeriveJunction::hard("DOT")]})
		);
	}
}
