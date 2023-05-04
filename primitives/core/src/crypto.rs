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

// tag::description[]
//! Cryptographic utilities.
// end::description[]

use crate::{ed25519, sr25519};
#[cfg(feature = "std")]
use bip39::{Language, Mnemonic, MnemonicType};
use codec::{Decode, Encode, MaxEncodedLen};
#[cfg(feature = "std")]
use rand::{rngs::OsRng, RngCore};
#[cfg(feature = "std")]
use regex::Regex;
use scale_info::TypeInfo;
#[cfg(feature = "std")]
pub use secrecy::{ExposeSecret, SecretString};
use sp_runtime_interface::pass_by::PassByInner;
#[doc(hidden)]
pub use sp_std::ops::Deref;
use sp_std::{hash::Hash, str, vec::Vec};
/// Trait to zeroize a memory buffer.
pub use zeroize::Zeroize;

#[cfg(feature = "full_crypto")]
pub use ss58_registry::{from_known_address_format, Ss58AddressFormat, Ss58AddressFormatRegistry};

/// The root phrase for our publicly known keys.
pub const DEV_PHRASE: &str =
	"bottom drive obey lake curtain smoke basket hold race lonely fit walk";

/// The address of the associated root phrase for our publicly known keys.
pub const DEV_ADDRESS: &str = "5DfhGyQdFobKM8NsWvEeAKk5EQQgYe9AydgJ7rMB6E1EqRzV";

/// The length of the junction identifier. Note that this is also referred to as the
/// `CHAIN_CODE_LENGTH` in the context of Schnorrkel.
#[cfg(feature = "full_crypto")]
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
#[cfg_attr(feature = "std", derive(thiserror::Error))]
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg(feature = "full_crypto")]
pub enum SecretStringError {
	/// The overall format was invalid (e.g. the seed phrase contained symbols).
	#[cfg_attr(feature = "std", error("Invalid format"))]
	InvalidFormat,
	/// The seed phrase provided is not a valid BIP39 phrase.
	#[cfg_attr(feature = "std", error("Invalid phrase"))]
	InvalidPhrase,
	/// The supplied password was invalid.
	#[cfg_attr(feature = "std", error("Invalid password"))]
	InvalidPassword,
	/// The seed is invalid (bad content).
	#[cfg_attr(feature = "std", error("Invalid seed"))]
	InvalidSeed,
	/// The seed has an invalid length.
	#[cfg_attr(feature = "std", error("Invalid seed length"))]
	InvalidSeedLength,
	/// The derivation path was invalid (e.g. contains soft junctions when they are not supported).
	#[cfg_attr(feature = "std", error("Invalid path"))]
	InvalidPath,
}

/// An error when deriving a key.
#[cfg_attr(feature = "std", derive(thiserror::Error))]
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg(feature = "full_crypto")]
pub enum DeriveError {
	/// A soft key was found in the path (and is unsupported).
	#[cfg_attr(feature = "std", error("Soft key in path"))]
	SoftKeyInPath,
}

/// A since derivation junction description. It is the single parameter used when creating
/// a new secret key from an existing secret key and, in the case of `SoftRaw` and `SoftIndex`
/// a new public key from an existing public key.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug, Encode, Decode)]
#[cfg(feature = "full_crypto")]
pub enum DeriveJunction {
	/// Soft (vanilla) derivation. Public keys have a correspondent derivation.
	Soft([u8; JUNCTION_ID_LEN]),
	/// Hard ("hardened") derivation. Public keys do not have a correspondent derivation.
	Hard([u8; JUNCTION_ID_LEN]),
}

#[cfg(feature = "full_crypto")]
impl DeriveJunction {
	/// Consume self to return a soft derive junction with the same chain code.
	pub fn soften(self) -> Self {
		DeriveJunction::Soft(self.unwrap_inner())
	}

	/// Consume self to return a hard derive junction with the same chain code.
	pub fn harden(self) -> Self {
		DeriveJunction::Hard(self.unwrap_inner())
	}

	/// Create a new soft (vanilla) DeriveJunction from a given, encodable, value.
	///
	/// If you need a hard junction, use `hard()`.
	pub fn soft<T: Encode>(index: T) -> Self {
		let mut cc: [u8; JUNCTION_ID_LEN] = Default::default();
		index.using_encoded(|data| {
			if data.len() > JUNCTION_ID_LEN {
				cc.copy_from_slice(&sp_core_hashing::blake2_256(data));
			} else {
				cc[0..data.len()].copy_from_slice(data);
			}
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
		matches!(*self, DeriveJunction::Soft(_))
	}

	/// Return `true` if the junction is hard.
	pub fn is_hard(&self) -> bool {
		matches!(*self, DeriveJunction::Hard(_))
	}
}

#[cfg(feature = "full_crypto")]
impl<T: AsRef<str>> From<T> for DeriveJunction {
	fn from(j: T) -> DeriveJunction {
		let j = j.as_ref();
		let (code, hard) =
			if let Some(stripped) = j.strip_prefix('/') { (stripped, true) } else { (j, false) };

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
#[cfg_attr(feature = "std", derive(thiserror::Error))]
#[cfg_attr(not(feature = "std"), derive(Debug))]
#[derive(Clone, Copy, Eq, PartialEq)]
#[allow(missing_docs)]
#[cfg(feature = "full_crypto")]
pub enum PublicError {
	#[cfg_attr(feature = "std", error("Base 58 requirement is violated"))]
	BadBase58,
	#[cfg_attr(feature = "std", error("Length is bad"))]
	BadLength,
	#[cfg_attr(
		feature = "std",
		error(
			"Unknown SS58 address format `{}`. ` \
		`To support this address format, you need to call `set_default_ss58_version` at node start up.",
			_0
		)
	)]
	UnknownSs58AddressFormat(Ss58AddressFormat),
	#[cfg_attr(feature = "std", error("Invalid checksum"))]
	InvalidChecksum,
	#[cfg_attr(feature = "std", error("Invalid SS58 prefix byte."))]
	InvalidPrefix,
	#[cfg_attr(feature = "std", error("Invalid SS58 format."))]
	InvalidFormat,
	#[cfg_attr(feature = "std", error("Invalid derivation path."))]
	InvalidPath,
	#[cfg_attr(feature = "std", error("Disallowed SS58 Address Format for this datatype."))]
	FormatNotAllowed,
}

#[cfg(feature = "std")]
impl sp_std::fmt::Debug for PublicError {
	fn fmt(&self, f: &mut sp_std::fmt::Formatter<'_>) -> sp_std::fmt::Result {
		// Just use the `Display` implementation
		write!(f, "{}", self)
	}
}

/// Key that can be encoded to/from SS58.
///
/// See <https://docs.substrate.io/v3/advanced/ss58/>
/// for information on the codec.
#[cfg(feature = "full_crypto")]
pub trait Ss58Codec: Sized + AsMut<[u8]> + AsRef<[u8]> + ByteArray {
	/// A format filterer, can be used to ensure that `from_ss58check` family only decode for
	/// allowed identifiers. By default just refuses the two reserved identifiers.
	fn format_is_allowed(f: Ss58AddressFormat) -> bool {
		!f.is_reserved()
	}

	/// Some if the string is a properly encoded SS58Check address.
	#[cfg(feature = "std")]
	fn from_ss58check(s: &str) -> Result<Self, PublicError> {
		Self::from_ss58check_with_version(s).and_then(|(r, v)| match v {
			v if !v.is_custom() => Ok(r),
			v if v == default_ss58_version() => Ok(r),
			v => Err(PublicError::UnknownSs58AddressFormat(v)),
		})
	}

	/// Some if the string is a properly encoded SS58Check address.
	#[cfg(feature = "std")]
	fn from_ss58check_with_version(s: &str) -> Result<(Self, Ss58AddressFormat), PublicError> {
		const CHECKSUM_LEN: usize = 2;
		let body_len = Self::LEN;

		let data = bs58::decode(s).into_vec().map_err(|_| PublicError::BadBase58)?;
		if data.len() < 2 {
			return Err(PublicError::BadLength)
		}
		let (prefix_len, ident) = match data[0] {
			0..=63 => (1, data[0] as u16),
			64..=127 => {
				// weird bit manipulation owing to the combination of LE encoding and missing two
				// bits from the left.
				// d[0] d[1] are: 01aaaaaa bbcccccc
				// they make the LE-encoded 16-bit value: aaaaaabb 00cccccc
				// so the lower byte is formed of aaaaaabb and the higher byte is 00cccccc
				let lower = (data[0] << 2) | (data[1] >> 6);
				let upper = data[1] & 0b00111111;
				(2, (lower as u16) | ((upper as u16) << 8))
			},
			_ => return Err(PublicError::InvalidPrefix),
		};
		if data.len() != prefix_len + body_len + CHECKSUM_LEN {
			return Err(PublicError::BadLength)
		}
		let format = ident.into();
		if !Self::format_is_allowed(format) {
			return Err(PublicError::FormatNotAllowed)
		}

		let hash = ss58hash(&data[0..body_len + prefix_len]);
		let checksum = &hash[0..CHECKSUM_LEN];
		if data[body_len + prefix_len..body_len + prefix_len + CHECKSUM_LEN] != *checksum {
			// Invalid checksum.
			return Err(PublicError::InvalidChecksum)
		}

		let result = Self::from_slice(&data[prefix_len..body_len + prefix_len])
			.map_err(|()| PublicError::BadLength)?;
		Ok((result, format))
	}

	/// Some if the string is a properly encoded SS58Check address, optionally with
	/// a derivation path following.
	#[cfg(feature = "std")]
	fn from_string(s: &str) -> Result<Self, PublicError> {
		Self::from_string_with_version(s).and_then(|(r, v)| match v {
			v if !v.is_custom() => Ok(r),
			v if v == default_ss58_version() => Ok(r),
			v => Err(PublicError::UnknownSs58AddressFormat(v)),
		})
	}

	/// Return the ss58-check string for this key.
	#[cfg(feature = "std")]
	fn to_ss58check_with_version(&self, version: Ss58AddressFormat) -> String {
		// We mask out the upper two bits of the ident - SS58 Prefix currently only supports 14-bits
		let ident: u16 = u16::from(version) & 0b0011_1111_1111_1111;
		let mut v = match ident {
			0..=63 => vec![ident as u8],
			64..=16_383 => {
				// upper six bits of the lower byte(!)
				let first = ((ident & 0b0000_0000_1111_1100) as u8) >> 2;
				// lower two bits of the lower byte in the high pos,
				// lower bits of the upper byte in the low pos
				let second = ((ident >> 8) as u8) | ((ident & 0b0000_0000_0000_0011) as u8) << 6;
				vec![first | 0b01000000, second]
			},
			_ => unreachable!("masked out the upper two bits; qed"),
		};
		v.extend(self.as_ref());
		let r = ss58hash(&v);
		v.extend(&r[0..2]);
		bs58::encode(v).into_string()
	}

	/// Return the ss58-check string for this key.
	#[cfg(feature = "std")]
	fn to_ss58check(&self) -> String {
		self.to_ss58check_with_version(default_ss58_version())
	}

	/// Some if the string is a properly encoded SS58Check address, optionally with
	/// a derivation path following.
	#[cfg(feature = "std")]
	fn from_string_with_version(s: &str) -> Result<(Self, Ss58AddressFormat), PublicError> {
		Self::from_ss58check_with_version(s)
	}
}

/// Derivable key trait.
pub trait Derive: Sized {
	/// Derive a child key from a series of given junctions.
	///
	/// Will be `None` for public keys if there are any hard junctions in there.
	#[cfg(feature = "std")]
	fn derive<Iter: Iterator<Item = DeriveJunction>>(&self, _path: Iter) -> Option<Self> {
		None
	}
}

#[cfg(feature = "std")]
const PREFIX: &[u8] = b"SS58PRE";

#[cfg(feature = "std")]
fn ss58hash(data: &[u8]) -> Vec<u8> {
	use blake2::{Blake2b512, Digest};

	let mut ctx = Blake2b512::new();
	ctx.update(PREFIX);
	ctx.update(data);
	ctx.finalize().to_vec()
}

/// Default prefix number
#[cfg(feature = "std")]
static DEFAULT_VERSION: core::sync::atomic::AtomicU16 = std::sync::atomic::AtomicU16::new(
	from_known_address_format(Ss58AddressFormatRegistry::SubstrateAccount),
);

/// Returns default SS58 format used by the current active process.
#[cfg(feature = "std")]
pub fn default_ss58_version() -> Ss58AddressFormat {
	DEFAULT_VERSION.load(std::sync::atomic::Ordering::Relaxed).into()
}

/// Returns either the input address format or the default.
#[cfg(feature = "std")]
pub fn unwrap_or_default_ss58_version(network: Option<Ss58AddressFormat>) -> Ss58AddressFormat {
	network.unwrap_or_else(default_ss58_version)
}

/// Set the default SS58 "version".
///
/// This SS58 version/format will be used when encoding/decoding SS58 addresses.
///
/// If you want to support a custom SS58 prefix (that isn't yet registered in the `ss58-registry`),
/// you are required to call this function with your desired prefix [`Ss58AddressFormat::custom`].
/// This will enable the node to decode ss58 addresses with this prefix.
///
/// This SS58 version/format is also only used by the node and not by the runtime.
#[cfg(feature = "std")]
pub fn set_default_ss58_version(new_default: Ss58AddressFormat) {
	DEFAULT_VERSION.store(new_default.into(), std::sync::atomic::Ordering::Relaxed);
}

#[cfg(feature = "std")]
lazy_static::lazy_static! {
	static ref SS58_REGEX: Regex = Regex::new(r"^(?P<ss58>[\w\d ]+)?(?P<path>(//?[^/]+)*)$")
		.expect("constructed from known-good static value; qed");
	static ref SECRET_PHRASE_REGEX: Regex = Regex::new(r"^(?P<phrase>[\d\w ]+)?(?P<path>(//?[^/]+)*)(///(?P<password>.*))?$")
		.expect("constructed from known-good static value; qed");
	static ref JUNCTION_REGEX: Regex = Regex::new(r"/(/?[^/]+)")
		.expect("constructed from known-good static value; qed");
}

#[cfg(feature = "std")]
impl<T: Sized + AsMut<[u8]> + AsRef<[u8]> + Public + Derive> Ss58Codec for T {
	fn from_string(s: &str) -> Result<Self, PublicError> {
		let cap = SS58_REGEX.captures(s).ok_or(PublicError::InvalidFormat)?;
		let s = cap.name("ss58").map(|r| r.as_str()).unwrap_or(DEV_ADDRESS);
		let addr = if let Some(stripped) = s.strip_prefix("0x") {
			let d = array_bytes::hex2bytes(stripped).map_err(|_| PublicError::InvalidFormat)?;
			Self::from_slice(&d).map_err(|()| PublicError::BadLength)?
		} else {
			Self::from_ss58check(s)?
		};
		if cap["path"].is_empty() {
			Ok(addr)
		} else {
			let path =
				JUNCTION_REGEX.captures_iter(&cap["path"]).map(|f| DeriveJunction::from(&f[1]));
			addr.derive(path).ok_or(PublicError::InvalidPath)
		}
	}

	fn from_string_with_version(s: &str) -> Result<(Self, Ss58AddressFormat), PublicError> {
		let cap = SS58_REGEX.captures(s).ok_or(PublicError::InvalidFormat)?;
		let (addr, v) = Self::from_ss58check_with_version(
			cap.name("ss58").map(|r| r.as_str()).unwrap_or(DEV_ADDRESS),
		)?;
		if cap["path"].is_empty() {
			Ok((addr, v))
		} else {
			let path =
				JUNCTION_REGEX.captures_iter(&cap["path"]).map(|f| DeriveJunction::from(&f[1]));
			addr.derive(path).ok_or(PublicError::InvalidPath).map(|a| (a, v))
		}
	}
}

/// Trait used for types that are really just a fixed-length array.
pub trait ByteArray: AsRef<[u8]> + AsMut<[u8]> + for<'a> TryFrom<&'a [u8], Error = ()> {
	/// The "length" of the values of this type, which is always the same.
	const LEN: usize;

	/// A new instance from the given slice that should be `Self::LEN` bytes long.
	fn from_slice(data: &[u8]) -> Result<Self, ()> {
		Self::try_from(data)
	}

	/// Return a `Vec<u8>` filled with raw data.
	fn to_raw_vec(&self) -> Vec<u8> {
		self.as_slice().to_vec()
	}

	/// Return a slice filled with raw data.
	fn as_slice(&self) -> &[u8] {
		self.as_ref()
	}
}

/// Trait suitable for typical cryptographic key public type.
pub trait Public: ByteArray + Derive + CryptoType + PartialEq + Eq + Clone + Send + Sync {}

/// An opaque 32-byte cryptographic identifier.
#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Encode, Decode, MaxEncodedLen, TypeInfo)]
#[cfg_attr(feature = "std", derive(Hash))]
pub struct AccountId32([u8; 32]);

impl AccountId32 {
	/// Create a new instance from its raw inner byte value.
	///
	/// Equivalent to this types `From<[u8; 32]>` implementation. For the lack of const
	/// support in traits we have this constructor.
	pub const fn new(inner: [u8; 32]) -> Self {
		Self(inner)
	}
}

impl UncheckedFrom<crate::hash::H256> for AccountId32 {
	fn unchecked_from(h: crate::hash::H256) -> Self {
		AccountId32(h.into())
	}
}

impl ByteArray for AccountId32 {
	const LEN: usize = 32;
}

#[cfg(feature = "std")]
impl Ss58Codec for AccountId32 {}

impl AsRef<[u8]> for AccountId32 {
	fn as_ref(&self) -> &[u8] {
		&self.0[..]
	}
}

impl AsMut<[u8]> for AccountId32 {
	fn as_mut(&mut self) -> &mut [u8] {
		&mut self.0[..]
	}
}

impl AsRef<[u8; 32]> for AccountId32 {
	fn as_ref(&self) -> &[u8; 32] {
		&self.0
	}
}

impl AsMut<[u8; 32]> for AccountId32 {
	fn as_mut(&mut self) -> &mut [u8; 32] {
		&mut self.0
	}
}

impl From<[u8; 32]> for AccountId32 {
	fn from(x: [u8; 32]) -> Self {
		Self::new(x)
	}
}

impl<'a> TryFrom<&'a [u8]> for AccountId32 {
	type Error = ();
	fn try_from(x: &'a [u8]) -> Result<AccountId32, ()> {
		if x.len() == 32 {
			let mut data = [0; 32];
			data.copy_from_slice(x);
			Ok(AccountId32(data))
		} else {
			Err(())
		}
	}
}

impl From<AccountId32> for [u8; 32] {
	fn from(x: AccountId32) -> [u8; 32] {
		x.0
	}
}

impl From<sr25519::Public> for AccountId32 {
	fn from(k: sr25519::Public) -> Self {
		k.0.into()
	}
}

impl From<ed25519::Public> for AccountId32 {
	fn from(k: ed25519::Public) -> Self {
		k.0.into()
	}
}

#[cfg(feature = "std")]
impl std::fmt::Display for AccountId32 {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		write!(f, "{}", self.to_ss58check())
	}
}

impl sp_std::fmt::Debug for AccountId32 {
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
impl serde::Serialize for AccountId32 {
	fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
	where
		S: serde::Serializer,
	{
		serializer.serialize_str(&self.to_ss58check())
	}
}

#[cfg(feature = "std")]
impl<'de> serde::Deserialize<'de> for AccountId32 {
	fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
	where
		D: serde::Deserializer<'de>,
	{
		Ss58Codec::from_ss58check(&String::deserialize(deserializer)?)
			.map_err(|e| serde::de::Error::custom(format!("{:?}", e)))
	}
}

#[cfg(feature = "std")]
impl sp_std::str::FromStr for AccountId32 {
	type Err = &'static str;

	fn from_str(s: &str) -> Result<Self, Self::Err> {
		let hex_or_ss58_without_prefix = s.trim_start_matches("0x");
		if hex_or_ss58_without_prefix.len() == 64 {
			array_bytes::hex_n_into(hex_or_ss58_without_prefix).map_err(|_| "invalid hex address.")
		} else {
			Self::from_ss58check(s).map_err(|_| "invalid ss58 address.")
		}
	}
}

#[cfg(feature = "std")]
pub use self::dummy::*;

#[cfg(feature = "std")]
mod dummy {
	use super::*;

	/// Dummy cryptography. Doesn't do anything.
	#[derive(Clone, Hash, Default, Eq, PartialEq)]
	pub struct Dummy;

	impl AsRef<[u8]> for Dummy {
		fn as_ref(&self) -> &[u8] {
			&b""[..]
		}
	}

	impl AsMut<[u8]> for Dummy {
		fn as_mut(&mut self) -> &mut [u8] {
			unsafe {
				#[allow(mutable_transmutes)]
				sp_std::mem::transmute::<_, &'static mut [u8]>(&b""[..])
			}
		}
	}

	impl<'a> TryFrom<&'a [u8]> for Dummy {
		type Error = ();

		fn try_from(_: &'a [u8]) -> Result<Self, ()> {
			Ok(Self)
		}
	}

	impl CryptoType for Dummy {
		type Pair = Dummy;
	}

	impl Derive for Dummy {}

	impl ByteArray for Dummy {
		const LEN: usize = 0;
		fn from_slice(_: &[u8]) -> Result<Self, ()> {
			Ok(Self)
		}
		#[cfg(feature = "std")]
		fn to_raw_vec(&self) -> Vec<u8> {
			vec![]
		}
		fn as_slice(&self) -> &[u8] {
			b""
		}
	}
	impl Public for Dummy {}

	impl Pair for Dummy {
		type Public = Dummy;
		type Seed = Dummy;
		type Signature = Dummy;

		#[cfg(feature = "std")]
		fn generate_with_phrase(_: Option<&str>) -> (Self, String, Self::Seed) {
			Default::default()
		}

		#[cfg(feature = "std")]
		fn from_phrase(_: &str, _: Option<&str>) -> Result<(Self, Self::Seed), SecretStringError> {
			Ok(Default::default())
		}

		fn derive<Iter: Iterator<Item = DeriveJunction>>(
			&self,
			_: Iter,
			_: Option<Dummy>,
		) -> Result<(Self, Option<Dummy>), DeriveError> {
			Ok((Self, None))
		}

		fn from_seed_slice(_: &[u8]) -> Result<Self, SecretStringError> {
			Ok(Self)
		}

		fn sign(&self, _: &[u8]) -> Self::Signature {
			Self
		}

		fn verify<M: AsRef<[u8]>>(_: &Self::Signature, _: M, _: &Self::Public) -> bool {
			true
		}

		fn public(&self) -> Self::Public {
			Self
		}

		fn to_raw_vec(&self) -> Vec<u8> {
			vec![]
		}
	}
}

/// A secret uri (`SURI`) that can be used to generate a key pair.
///
/// The `SURI` can be parsed from a string. The string is interpreted in the following way:
///
/// - If `string` is a possibly `0x` prefixed 64-digit hex string, then it will be interpreted
/// directly as a `MiniSecretKey` (aka "seed" in `subkey`).
/// - If `string` is a valid BIP-39 key phrase of 12, 15, 18, 21 or 24 words, then the key will
/// be derived from it. In this case:
///   - the phrase may be followed by one or more items delimited by `/` characters.
///   - the path may be followed by `///`, in which case everything after the `///` is treated
/// as a password.
/// - If `string` begins with a `/` character it is prefixed with the Substrate public `DEV_PHRASE`
///   and interpreted as above.
///
/// In this case they are interpreted as HDKD junctions; purely numeric items are interpreted as
/// integers, non-numeric items as strings. Junctions prefixed with `/` are interpreted as soft
/// junctions, and with `//` as hard junctions.
///
/// There is no correspondence mapping between `SURI` strings and the keys they represent.
/// Two different non-identical strings can actually lead to the same secret being derived.
/// Notably, integer junction indices may be legally prefixed with arbitrary number of zeros.
/// Similarly an empty password (ending the `SURI` with `///`) is perfectly valid and will
/// generally be equivalent to no password at all.
///
/// # Example
///
/// Parse [`DEV_PHRASE`] secret uri with junction:
///
/// ```
/// # use sp_core::crypto::{SecretUri, DeriveJunction, DEV_PHRASE, ExposeSecret};
/// # use std::str::FromStr;
/// let suri = SecretUri::from_str("//Alice").expect("Parse SURI");
///
/// assert_eq!(vec![DeriveJunction::from("Alice").harden()], suri.junctions);
/// assert_eq!(DEV_PHRASE, suri.phrase.expose_secret());
/// assert!(suri.password.is_none());
/// ```
///
/// Parse [`DEV_PHRASE`] secret ui with junction and password:
///
/// ```
/// # use sp_core::crypto::{SecretUri, DeriveJunction, DEV_PHRASE, ExposeSecret};
/// # use std::str::FromStr;
/// let suri = SecretUri::from_str("//Alice///SECRET_PASSWORD").expect("Parse SURI");
///
/// assert_eq!(vec![DeriveJunction::from("Alice").harden()], suri.junctions);
/// assert_eq!(DEV_PHRASE, suri.phrase.expose_secret());
/// assert_eq!("SECRET_PASSWORD", suri.password.unwrap().expose_secret());
/// ```
///
/// Parse [`DEV_PHRASE`] secret ui with hex phrase and junction:
///
/// ```
/// # use sp_core::crypto::{SecretUri, DeriveJunction, DEV_PHRASE, ExposeSecret};
/// # use std::str::FromStr;
/// let suri = SecretUri::from_str("0xe5be9a5092b81bca64be81d212e7f2f9eba183bb7a90954f7b76361f6edb5c0a//Alice").expect("Parse SURI");
///
/// assert_eq!(vec![DeriveJunction::from("Alice").harden()], suri.junctions);
/// assert_eq!("0xe5be9a5092b81bca64be81d212e7f2f9eba183bb7a90954f7b76361f6edb5c0a", suri.phrase.expose_secret());
/// assert!(suri.password.is_none());
/// ```
#[cfg(feature = "std")]
pub struct SecretUri {
	/// The phrase to derive the private key.
	///
	/// This can either be a 64-bit hex string or a BIP-39 key phrase.
	pub phrase: SecretString,
	/// Optional password as given as part of the uri.
	pub password: Option<SecretString>,
	/// The junctions as part of the uri.
	pub junctions: Vec<DeriveJunction>,
}

#[cfg(feature = "std")]
impl sp_std::str::FromStr for SecretUri {
	type Err = SecretStringError;

	fn from_str(s: &str) -> Result<Self, Self::Err> {
		let cap = SECRET_PHRASE_REGEX.captures(s).ok_or(SecretStringError::InvalidFormat)?;

		let junctions = JUNCTION_REGEX
			.captures_iter(&cap["path"])
			.map(|f| DeriveJunction::from(&f[1]))
			.collect::<Vec<_>>();

		let phrase = cap.name("phrase").map(|r| r.as_str()).unwrap_or(DEV_PHRASE);
		let password = cap.name("password");

		Ok(Self {
			phrase: SecretString::from_str(phrase).expect("Returns infallible error; qed"),
			password: password.map(|v| {
				SecretString::from_str(v.as_str()).expect("Returns infallible error; qed")
			}),
			junctions,
		})
	}
}

/// Trait suitable for typical cryptographic PKI key pair type.
///
/// For now it just specifies how to create a key from a phrase and derivation path.
#[cfg(feature = "full_crypto")]
pub trait Pair: CryptoType + Sized + Clone + Send + Sync + 'static {
	/// The type which is used to encode a public key.
	type Public: Public + Hash;

	/// The type used to (minimally) encode the data required to securely create
	/// a new key pair.
	type Seed: Default + AsRef<[u8]> + AsMut<[u8]> + Clone;

	/// The type used to represent a signature. Can be created from a key pair and a message
	/// and verified with the message and a public key.
	type Signature: AsRef<[u8]>;

	/// Generate new secure (random) key pair.
	///
	/// This is only for ephemeral keys really, since you won't have access to the secret key
	/// for storage. If you want a persistent key pair, use `generate_with_phrase` instead.
	#[cfg(feature = "std")]
	fn generate() -> (Self, Self::Seed) {
		let mut seed = Self::Seed::default();
		OsRng.fill_bytes(seed.as_mut());
		(Self::from_seed(&seed), seed)
	}

	/// Generate new secure (random) key pair and provide the recovery phrase.
	///
	/// You can recover the same key later with `from_phrase`.
	///
	/// This is generally slower than `generate()`, so prefer that unless you need to persist
	/// the key from the current session.
	#[cfg(feature = "std")]
	fn generate_with_phrase(password: Option<&str>) -> (Self, String, Self::Seed) {
		let mnemonic = Mnemonic::new(MnemonicType::Words12, Language::English);
		let phrase = mnemonic.phrase();
		let (pair, seed) = Self::from_phrase(phrase, password)
			.expect("All phrases generated by Mnemonic are valid; qed");
		(pair, phrase.to_owned(), seed)
	}

	/// Returns the KeyPair from the English BIP39 seed `phrase`, or `None` if it's invalid.
	#[cfg(feature = "std")]
	fn from_phrase(
		phrase: &str,
		password: Option<&str>,
	) -> Result<(Self, Self::Seed), SecretStringError> {
		let mnemonic = Mnemonic::from_phrase(phrase, Language::English)
			.map_err(|_| SecretStringError::InvalidPhrase)?;
		let big_seed =
			substrate_bip39::seed_from_entropy(mnemonic.entropy(), password.unwrap_or(""))
				.map_err(|_| SecretStringError::InvalidSeed)?;
		let mut seed = Self::Seed::default();
		let seed_slice = seed.as_mut();
		let seed_len = seed_slice.len();
		debug_assert!(seed_len <= big_seed.len());
		seed_slice[..seed_len].copy_from_slice(&big_seed[..seed_len]);
		Self::from_seed_slice(seed_slice).map(|x| (x, seed))
	}

	/// Derive a child key from a series of given junctions.
	fn derive<Iter: Iterator<Item = DeriveJunction>>(
		&self,
		path: Iter,
		seed: Option<Self::Seed>,
	) -> Result<(Self, Option<Self::Seed>), DeriveError>;

	/// Generate new key pair from the provided `seed`.
	///
	/// @WARNING: THIS WILL ONLY BE SECURE IF THE `seed` IS SECURE. If it can be guessed
	/// by an attacker then they can also derive your key.
	fn from_seed(seed: &Self::Seed) -> Self {
		Self::from_seed_slice(seed.as_ref()).expect("seed has valid length; qed")
	}

	/// Make a new key pair from secret seed material. The slice must be the correct size or
	/// it will return `None`.
	///
	/// @WARNING: THIS WILL ONLY BE SECURE IF THE `seed` IS SECURE. If it can be guessed
	/// by an attacker then they can also derive your key.
	fn from_seed_slice(seed: &[u8]) -> Result<Self, SecretStringError>;

	/// Sign a message.
	fn sign(&self, message: &[u8]) -> Self::Signature;

	/// Verify a signature on a message. Returns true if the signature is good.
	fn verify<M: AsRef<[u8]>>(sig: &Self::Signature, message: M, pubkey: &Self::Public) -> bool;

	/// Get the public key.
	fn public(&self) -> Self::Public;

	/// Interprets the string `s` in order to generate a key Pair. Returns both the pair and an
	/// optional seed, in the case that the pair can be expressed as a direct derivation from a seed
	/// (some cases, such as Sr25519 derivations with path components, cannot).
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
	/// - If `s` begins with a `/` character it is prefixed with the Substrate public `DEV_PHRASE`
	///   and
	/// interpreted as above.
	///
	/// In this case they are interpreted as HDKD junctions; purely numeric items are interpreted as
	/// integers, non-numeric items as strings. Junctions prefixed with `/` are interpreted as soft
	/// junctions, and with `//` as hard junctions.
	///
	/// There is no correspondence mapping between SURI strings and the keys they represent.
	/// Two different non-identical strings can actually lead to the same secret being derived.
	/// Notably, integer junction indices may be legally prefixed with arbitrary number of zeros.
	/// Similarly an empty password (ending the SURI with `///`) is perfectly valid and will
	/// generally be equivalent to no password at all.
	///
	/// `None` is returned if no matches are found.
	#[cfg(feature = "std")]
	fn from_string_with_seed(
		s: &str,
		password_override: Option<&str>,
	) -> Result<(Self, Option<Self::Seed>), SecretStringError> {
		use sp_std::str::FromStr;
		let SecretUri { junctions, phrase, password } = SecretUri::from_str(s)?;
		let password =
			password_override.or_else(|| password.as_ref().map(|p| p.expose_secret().as_str()));

		let (root, seed) = if let Some(stripped) = phrase.expose_secret().strip_prefix("0x") {
			array_bytes::hex2bytes(stripped)
				.ok()
				.and_then(|seed_vec| {
					let mut seed = Self::Seed::default();
					if seed.as_ref().len() == seed_vec.len() {
						seed.as_mut().copy_from_slice(&seed_vec);
						Some((Self::from_seed(&seed), seed))
					} else {
						None
					}
				})
				.ok_or(SecretStringError::InvalidSeed)?
		} else {
			Self::from_phrase(phrase.expose_secret().as_str(), password)
				.map_err(|_| SecretStringError::InvalidPhrase)?
		};
		root.derive(junctions.into_iter(), Some(seed))
			.map_err(|_| SecretStringError::InvalidPath)
	}

	/// Interprets the string `s` in order to generate a key pair.
	///
	/// See [`from_string_with_seed`](Pair::from_string_with_seed) for more extensive documentation.
	#[cfg(feature = "std")]
	fn from_string(s: &str, password_override: Option<&str>) -> Result<Self, SecretStringError> {
		Self::from_string_with_seed(s, password_override).map(|x| x.0)
	}

	/// Return a vec filled with raw data.
	fn to_raw_vec(&self) -> Vec<u8>;
}

/// One type is wrapped by another.
pub trait IsWrappedBy<Outer>: From<Outer> + Into<Outer> {
	/// Get a reference to the inner from the outer.
	fn from_ref(outer: &Outer) -> &Self;
	/// Get a mutable reference to the inner from the outer.
	fn from_mut(outer: &mut Outer) -> &mut Self;
}

/// Opposite of `IsWrappedBy` - denotes a type which is a simple wrapper around another type.
pub trait Wraps: Sized {
	/// The inner type it is wrapping.
	type Inner: IsWrappedBy<Self>;

	/// Get a reference to the inner type that is wrapped.
	fn as_inner_ref(&self) -> &Self::Inner {
		Self::Inner::from_ref(self)
	}
}

impl<T, Outer> IsWrappedBy<Outer> for T
where
	Outer: AsRef<Self> + AsMut<Self> + From<Self>,
	T: From<Outer>,
{
	/// Get a reference to the inner from the outer.
	fn from_ref(outer: &Outer) -> &Self {
		outer.as_ref()
	}

	/// Get a mutable reference to the inner from the outer.
	fn from_mut(outer: &mut Outer) -> &mut Self {
		outer.as_mut()
	}
}

impl<Inner, Outer, T> UncheckedFrom<T> for Outer
where
	Outer: Wraps<Inner = Inner>,
	Inner: IsWrappedBy<Outer> + UncheckedFrom<T>,
{
	fn unchecked_from(t: T) -> Self {
		let inner: Inner = t.unchecked_into();
		inner.into()
	}
}

/// Type which has a particular kind of crypto associated with it.
pub trait CryptoType {
	/// The pair key type of this crypto.
	#[cfg(feature = "full_crypto")]
	type Pair: Pair;
}

/// An identifier for a type of cryptographic key.
///
/// To avoid clashes with other modules when distributing your module publicly, register your
/// `KeyTypeId` on the list here by making a PR.
///
/// Values whose first character is `_` are reserved for private use and won't conflict with any
/// public modules.
#[derive(
	Copy,
	Clone,
	Default,
	PartialEq,
	Eq,
	PartialOrd,
	Ord,
	Hash,
	Encode,
	Decode,
	PassByInner,
	crate::RuntimeDebug,
	TypeInfo,
)]
#[cfg_attr(feature = "std", derive(serde::Serialize, serde::Deserialize))]
pub struct KeyTypeId(pub [u8; 4]);

impl From<u32> for KeyTypeId {
	fn from(x: u32) -> Self {
		Self(x.to_le_bytes())
	}
}

impl From<KeyTypeId> for u32 {
	fn from(x: KeyTypeId) -> Self {
		u32::from_le_bytes(x.0)
	}
}

impl<'a> TryFrom<&'a str> for KeyTypeId {
	type Error = ();

	fn try_from(x: &'a str) -> Result<Self, ()> {
		let b = x.as_bytes();
		if b.len() != 4 {
			return Err(())
		}
		let mut res = KeyTypeId::default();
		res.0.copy_from_slice(&b[0..4]);
		Ok(res)
	}
}

/// Trait grouping types shared by a VRF signer and verifiers.
pub trait VrfCrypto {
	/// Associated signature type.
	type VrfSignature;

	/// Vrf input data. Generally some form of transcript.
	type VrfInput;
}

/// VRF Signer.
pub trait VrfSigner: VrfCrypto {
	/// Sign input data.
	fn vrf_sign(&self, data: &Self::VrfInput) -> Self::VrfSignature;
}

/// VRF Verifier.
pub trait VrfVerifier: VrfCrypto {
	/// Verify input data signature.
	fn vrf_verify(&self, data: &Self::VrfInput, signature: &Self::VrfSignature) -> bool;
}

/// An identifier for a specific cryptographic algorithm used by a key pair
#[derive(Debug, Copy, Clone, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Encode, Decode)]
#[cfg_attr(feature = "std", derive(serde::Serialize, serde::Deserialize))]
pub struct CryptoTypeId(pub [u8; 4]);

/// Known key types; this also functions as a global registry of key types for projects wishing to
/// avoid collisions with each other.
///
/// It's not universal in the sense that *all* key types need to be mentioned here, it's just a
/// handy place to put common key types.
pub mod key_types {
	use super::KeyTypeId;

	/// Key type for Babe module, built-in. Identified as `babe`.
	pub const BABE: KeyTypeId = KeyTypeId(*b"babe");
	/// Key type for Grandpa module, built-in. Identified as `gran`.
	pub const GRANDPA: KeyTypeId = KeyTypeId(*b"gran");
	/// Key type for controlling an account in a Substrate runtime, built-in. Identified as `acco`.
	pub const ACCOUNT: KeyTypeId = KeyTypeId(*b"acco");
	/// Key type for Aura module, built-in. Identified as `aura`.
	pub const AURA: KeyTypeId = KeyTypeId(*b"aura");
	/// Key type for ImOnline module, built-in. Identified as `imon`.
	pub const IM_ONLINE: KeyTypeId = KeyTypeId(*b"imon");
	/// Key type for AuthorityDiscovery module, built-in. Identified as `audi`.
	pub const AUTHORITY_DISCOVERY: KeyTypeId = KeyTypeId(*b"audi");
	/// Key type for staking, built-in. Identified as `stak`.
	pub const STAKING: KeyTypeId = KeyTypeId(*b"stak");
	/// A key type for signing statements
	pub const STATEMENT: KeyTypeId = KeyTypeId(*b"stmt");
	/// A key type ID useful for tests.
	pub const DUMMY: KeyTypeId = KeyTypeId(*b"dumy");
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::DeriveJunction;

	#[derive(Clone, Eq, PartialEq, Debug)]
	enum TestPair {
		Generated,
		GeneratedWithPhrase,
		GeneratedFromPhrase { phrase: String, password: Option<String> },
		Standard { phrase: String, password: Option<String>, path: Vec<DeriveJunction> },
		Seed(Vec<u8>),
	}
	impl Default for TestPair {
		fn default() -> Self {
			TestPair::Generated
		}
	}
	impl CryptoType for TestPair {
		type Pair = Self;
	}

	#[derive(Clone, PartialEq, Eq, Hash, Default)]
	struct TestPublic;
	impl AsRef<[u8]> for TestPublic {
		fn as_ref(&self) -> &[u8] {
			&[]
		}
	}
	impl AsMut<[u8]> for TestPublic {
		fn as_mut(&mut self) -> &mut [u8] {
			&mut []
		}
	}
	impl<'a> TryFrom<&'a [u8]> for TestPublic {
		type Error = ();

		fn try_from(data: &'a [u8]) -> Result<Self, ()> {
			Self::from_slice(data)
		}
	}
	impl CryptoType for TestPublic {
		type Pair = TestPair;
	}
	impl Derive for TestPublic {}
	impl ByteArray for TestPublic {
		const LEN: usize = 0;
		fn from_slice(bytes: &[u8]) -> Result<Self, ()> {
			if bytes.is_empty() {
				Ok(Self)
			} else {
				Err(())
			}
		}
		fn as_slice(&self) -> &[u8] {
			&[]
		}
		fn to_raw_vec(&self) -> Vec<u8> {
			vec![]
		}
	}
	impl Public for TestPublic {}
	impl Pair for TestPair {
		type Public = TestPublic;
		type Seed = [u8; 8];
		type Signature = [u8; 0];

		fn generate() -> (Self, <Self as Pair>::Seed) {
			(TestPair::Generated, [0u8; 8])
		}

		fn generate_with_phrase(_password: Option<&str>) -> (Self, String, <Self as Pair>::Seed) {
			(TestPair::GeneratedWithPhrase, "".into(), [0u8; 8])
		}

		fn from_phrase(
			phrase: &str,
			password: Option<&str>,
		) -> Result<(Self, <Self as Pair>::Seed), SecretStringError> {
			Ok((
				TestPair::GeneratedFromPhrase {
					phrase: phrase.to_owned(),
					password: password.map(Into::into),
				},
				[0u8; 8],
			))
		}

		fn derive<Iter: Iterator<Item = DeriveJunction>>(
			&self,
			path_iter: Iter,
			_: Option<[u8; 8]>,
		) -> Result<(Self, Option<[u8; 8]>), DeriveError> {
			Ok((
				match self.clone() {
					TestPair::Standard { phrase, password, path } => TestPair::Standard {
						phrase,
						password,
						path: path.into_iter().chain(path_iter).collect(),
					},
					TestPair::GeneratedFromPhrase { phrase, password } =>
						TestPair::Standard { phrase, password, path: path_iter.collect() },
					x =>
						if path_iter.count() == 0 {
							x
						} else {
							return Err(DeriveError::SoftKeyInPath)
						},
				},
				None,
			))
		}

		fn sign(&self, _message: &[u8]) -> Self::Signature {
			[]
		}

		fn verify<M: AsRef<[u8]>>(_: &Self::Signature, _: M, _: &Self::Public) -> bool {
			true
		}

		fn public(&self) -> Self::Public {
			TestPublic
		}

		fn from_seed_slice(seed: &[u8]) -> Result<Self, SecretStringError> {
			Ok(TestPair::Seed(seed.to_owned()))
		}

		fn to_raw_vec(&self) -> Vec<u8> {
			vec![]
		}
	}

	#[test]
	fn interpret_std_seed_should_work() {
		assert_eq!(
			TestPair::from_string("0x0123456789abcdef", None),
			Ok(TestPair::Seed(array_bytes::hex2bytes_unchecked("0123456789abcdef")))
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
			Ok(TestPair::Standard {
				phrase: "hello world".to_owned(),
				password: None,
				path: vec![]
			})
		);
		assert_eq!(
			TestPair::from_string("hello world/1", None),
			Ok(TestPair::Standard {
				phrase: "hello world".to_owned(),
				password: None,
				path: vec![DeriveJunction::soft(1)]
			})
		);
		assert_eq!(
			TestPair::from_string("hello world/DOT", None),
			Ok(TestPair::Standard {
				phrase: "hello world".to_owned(),
				password: None,
				path: vec![DeriveJunction::soft("DOT")]
			})
		);
		assert_eq!(
			TestPair::from_string("hello world/0123456789012345678901234567890123456789", None),
			Ok(TestPair::Standard {
				phrase: "hello world".to_owned(),
				password: None,
				path: vec![DeriveJunction::soft("0123456789012345678901234567890123456789")]
			})
		);
		assert_eq!(
			TestPair::from_string("hello world//1", None),
			Ok(TestPair::Standard {
				phrase: "hello world".to_owned(),
				password: None,
				path: vec![DeriveJunction::hard(1)]
			})
		);
		assert_eq!(
			TestPair::from_string("hello world//DOT", None),
			Ok(TestPair::Standard {
				phrase: "hello world".to_owned(),
				password: None,
				path: vec![DeriveJunction::hard("DOT")]
			})
		);
		assert_eq!(
			TestPair::from_string("hello world//0123456789012345678901234567890123456789", None),
			Ok(TestPair::Standard {
				phrase: "hello world".to_owned(),
				password: None,
				path: vec![DeriveJunction::hard("0123456789012345678901234567890123456789")]
			})
		);
		assert_eq!(
			TestPair::from_string("hello world//1/DOT", None),
			Ok(TestPair::Standard {
				phrase: "hello world".to_owned(),
				password: None,
				path: vec![DeriveJunction::hard(1), DeriveJunction::soft("DOT")]
			})
		);
		assert_eq!(
			TestPair::from_string("hello world//DOT/1", None),
			Ok(TestPair::Standard {
				phrase: "hello world".to_owned(),
				password: None,
				path: vec![DeriveJunction::hard("DOT"), DeriveJunction::soft(1)]
			})
		);
		assert_eq!(
			TestPair::from_string("hello world///password", None),
			Ok(TestPair::Standard {
				phrase: "hello world".to_owned(),
				password: Some("password".to_owned()),
				path: vec![]
			})
		);
		assert_eq!(
			TestPair::from_string("hello world//1/DOT///password", None),
			Ok(TestPair::Standard {
				phrase: "hello world".to_owned(),
				password: Some("password".to_owned()),
				path: vec![DeriveJunction::hard(1), DeriveJunction::soft("DOT")]
			})
		);
		assert_eq!(
			TestPair::from_string("hello world/1//DOT///password", None),
			Ok(TestPair::Standard {
				phrase: "hello world".to_owned(),
				password: Some("password".to_owned()),
				path: vec![DeriveJunction::soft(1), DeriveJunction::hard("DOT")]
			})
		);
	}

	#[test]
	fn accountid_32_from_str_works() {
		use std::str::FromStr;
		assert!(AccountId32::from_str("5G9VdMwXvzza9pS8qE8ZHJk3CheHW9uucBn9ngW4C1gmmzpv").is_ok());
		assert!(AccountId32::from_str(
			"5c55177d67b064bb5d189a3e1ddad9bc6646e02e64d6e308f5acbb1533ac430d"
		)
		.is_ok());
		assert!(AccountId32::from_str(
			"0x5c55177d67b064bb5d189a3e1ddad9bc6646e02e64d6e308f5acbb1533ac430d"
		)
		.is_ok());

		assert_eq!(
			AccountId32::from_str("99G9VdMwXvzza9pS8qE8ZHJk3CheHW9uucBn9ngW4C1gmmzpv").unwrap_err(),
			"invalid ss58 address.",
		);
		assert_eq!(
			AccountId32::from_str(
				"gc55177d67b064bb5d189a3e1ddad9bc6646e02e64d6e308f5acbb1533ac430d"
			)
			.unwrap_err(),
			"invalid hex address.",
		);
		assert_eq!(
			AccountId32::from_str(
				"0xgc55177d67b064bb5d189a3e1ddad9bc6646e02e64d6e308f5acbb1533ac430d"
			)
			.unwrap_err(),
			"invalid hex address.",
		);

		// valid hex but invalid length will be treated as ss58.
		assert_eq!(
			AccountId32::from_str(
				"55c55177d67b064bb5d189a3e1ddad9bc6646e02e64d6e308f5acbb1533ac430d"
			)
			.unwrap_err(),
			"invalid ss58 address.",
		);
	}
}
