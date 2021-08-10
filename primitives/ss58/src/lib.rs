// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
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

#![cfg_attr(not(feature = "full"), no_std)]

use arrayvec::{ArrayString, ArrayVec};
use core::{
	convert::{TryFrom, TryInto},
	fmt,
	hash::Hash,
	str,
};
#[cfg(feature = "full")]
use parking_lot::Mutex;
#[cfg(feature = "full")]
use regex::Regex;

/// The address of the associated root phrase for our publicly known keys.
pub const DEV_ADDRESS: &str = "5DfhGyQdFobKM8NsWvEeAKk5EQQgYe9AydgJ7rMB6E1EqRzV";
/// The length of the junction identifier. Note that this is also referred to as the
/// `CHAIN_CODE_LENGTH` in the context of Schnorrkel.
pub const JUNCTION_ID_LEN: usize = 32;

// Address will never have more than 64 bytes.
const ADDRESS_UPPER_BOUND: usize = 64;

/// A since derivation junction description. It is the single parameter used when creating
/// a new secret key from an existing secret key and, in the case of `SoftRaw` and `SoftIndex`
/// a new public key from an existing public key.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
#[cfg_attr(
	feature = "with-parity-scale-codec",
	derive(parity_scale_codec::Decode, parity_scale_codec::Encode)
)]
pub enum DeriveJunction {
	/// Soft (vanilla) derivation. Public keys have a correspondent derivation.
	Soft([u8; JUNCTION_ID_LEN]),
	/// Hard ("hardened") derivation. Public keys do not have a correspondent derivation.
	Hard([u8; JUNCTION_ID_LEN]),
}

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
	#[cfg(feature = "with-parity-scale-codec")]
	pub fn soft<T: parity_scale_codec::Encode>(index: T) -> Self {
		let mut cc: [u8; JUNCTION_ID_LEN] = Default::default();
		index.using_encoded(|data| {
			if data.len() > JUNCTION_ID_LEN {
				let hash_result = blake2_rfc::blake2b::blake2b(JUNCTION_ID_LEN, &[], data);
				let hash = hash_result.as_bytes();
				cc.copy_from_slice(hash);
			} else {
				cc[0..data.len()].copy_from_slice(data);
			}
		});
		DeriveJunction::Soft(cc)
	}

	/// Create a new hard (hardened) DeriveJunction from a given, encodable, value.
	///
	/// If you need a soft junction, use `soft()`.
	#[cfg(feature = "with-parity-scale-codec")]
	pub fn hard<T: parity_scale_codec::Encode>(index: T) -> Self {
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

#[cfg(feature = "with-parity-scale-codec")]
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
#[derive(Clone, Copy, Eq, PartialEq, Debug)]
pub enum PublicError {
	/// Bad alphabet.
	BadBase58,
	/// Bad length.
	BadLength,
	/// Unknown identifier for the encoding.
	UnknownVersion,
	/// Invalid checksum.
	InvalidChecksum,
	/// Invalid format.
	InvalidFormat,
	/// Invalid derivation path.
	InvalidPath,
	/// Disallowed SS58 Address Format for this datatype.
	FormatNotAllowed,
}

/// Key that can be encoded to/from SS58.
///
/// See <https://github.com/paritytech/substrate/wiki/External-Address-Format-(SS58)#address-type>
/// for information on the codec.
pub trait Ss58Codec: Sized + AsMut<[u8]> + AsRef<[u8]> + Default {
	/// A format filterer, can be used to ensure that `from_ss58check` family only decode for
	/// allowed identifiers. By default just refuses the two reserved identifiers.
	fn format_is_allowed(f: Ss58AddressFormat) -> bool {
		!matches!(f, Ss58AddressFormat::Reserved46 | Ss58AddressFormat::Reserved47)
	}

	/// Some if the string is a properly encoded SS58Check address.
	#[cfg(feature = "full")]
	fn from_ss58check(s: &str) -> Result<Self, PublicError> {
		Self::from_ss58check_with_version(s).and_then(|(r, v)| match v {
			v if !v.is_custom() => Ok(r),
			v if v == *DEFAULT_VERSION.lock() => Ok(r),
			_ => Err(PublicError::UnknownVersion),
		})
	}

	/// Some if the string is a properly encoded SS58Check address.
	fn from_ss58check_with_version(s: &str) -> Result<(Self, Ss58AddressFormat), PublicError> {
		const CHECKSUM_LEN: usize = 2;

		let mut res = Self::default();

		// Must decode to our type.
		let body_len = res.as_mut().len();

		let mut data = ArrayVec::from([0u8; ADDRESS_UPPER_BOUND]);
		let len = bs58::decode(s).into(&mut data).map_err(|_| PublicError::BadBase58)?;
		data.truncate(len);

		if data.len() < 2 {
			return Err(PublicError::BadLength)
		}
		let (prefix_len, ident) = match data[0] {
			0..=63 => (1, data[0] as u16),
			64..=127 => {
				// weird bit manipulation owing to the combination of LE encoding and missing two bits
				// from the left.
				// d[0] d[1] are: 01aaaaaa bbcccccc
				// they make the LE-encoded 16-bit value: aaaaaabb 00cccccc
				// so the lower byte is formed of aaaaaabb and the higher byte is 00cccccc
				let lower = (data[0] << 2) | (data[1] >> 6);
				let upper = data[1] & 0b00111111;
				(2, (lower as u16) | ((upper as u16) << 8))
			},
			_ => return Err(PublicError::UnknownVersion),
		};
		if data.len() != prefix_len + body_len + CHECKSUM_LEN {
			return Err(PublicError::BadLength)
		}
		let format = ident.try_into().map_err(|_: ()| PublicError::UnknownVersion)?;
		if !Self::format_is_allowed(format) {
			return Err(PublicError::FormatNotAllowed)
		}

		let hash = ss58hash(&data[0..body_len + prefix_len]);
		let checksum = &hash.as_bytes()[0..CHECKSUM_LEN];
		if data[body_len + prefix_len..body_len + prefix_len + CHECKSUM_LEN] != *checksum {
			// Invalid checksum.
			return Err(PublicError::InvalidChecksum)
		}
		res.as_mut().copy_from_slice(&data[prefix_len..body_len + prefix_len]);
		Ok((res, format))
	}

	/// Some if the string is a properly encoded SS58Check address, optionally with
	/// a derivation path following.
	#[cfg(feature = "full")]
	fn from_string(s: &str) -> Result<Self, PublicError> {
		Self::from_string_with_version(s).and_then(|(r, v)| match v {
			v if !v.is_custom() => Ok(r),
			v if v == *DEFAULT_VERSION.lock() => Ok(r),
			_ => Err(PublicError::UnknownVersion),
		})
	}

	/// Return the ss58-check string for this key.
	fn to_ss58check_with_version(
		&self,
		version: Ss58AddressFormat,
	) -> ArrayString<ADDRESS_UPPER_BOUND> {
		// We mask out the upper two bits of the ident - SS58 Prefix currently only supports 14-bits
		let ident: u16 = u16::from(version) & 0b0011_1111_1111_1111;
		let mut v = ArrayVec::<u8, ADDRESS_UPPER_BOUND>::new();
		match ident {
			0..=63 => v.push(ident as u8),
			64..=16_383 => {
				// upper six bits of the lower byte(!)
				let first = ((ident & 0b0000_0000_1111_1100) as u8) >> 2;
				// lower two bits of the lower byte in the high pos,
				// lower bits of the upper byte in the low pos
				let second = ((ident >> 8) as u8) | ((ident & 0b0000_0000_0000_0011) as u8) << 6;
				v.push(first | 0b01000000);
				v.push(second);
			},
			_ => unreachable!("masked out the upper two bits; qed"),
		};
		v.extend(self.as_ref().iter().copied());
		let r = ss58hash(&v);
		v.extend(r.as_bytes().iter().take(2).copied());
		// ' ' is valid utf-8
		let mut rslt = ArrayString::from_byte_string(&[b' '; ADDRESS_UPPER_BOUND]).unwrap();
		// `rslt` is large enough but be careful when tweaking `ADDRESS_UPPER_BOUND`. Besides, this
		// `to_ss58check_with_version` method is not fallible
		let len = bs58::encode(v).into(&mut rslt[..]).unwrap();
		rslt.truncate(len);
		rslt
	}

	/// Return the ss58-check string for this key.
	#[cfg(feature = "full")]
	fn to_ss58check(&self) -> ArrayString<ADDRESS_UPPER_BOUND> {
		self.to_ss58check_with_version(*DEFAULT_VERSION.lock())
	}

	/// Some if the string is a properly encoded SS58Check address, optionally with
	/// a derivation path following.
	#[cfg(feature = "full")]
	fn from_string_with_version(s: &str) -> Result<(Self, Ss58AddressFormat), PublicError> {
		Self::from_ss58check_with_version(s)
	}
}

/// Derivable key trait.
pub trait Derive: Sized {
	/// Derive a child key from a series of given junctions.
	///
	/// Will be `None` for public keys if there are any hard junctions in there.
	fn derive<Iter: Iterator<Item = DeriveJunction>>(&self, _path: Iter) -> Option<Self> {
		None
	}
}

fn ss58hash(data: &[u8]) -> blake2_rfc::blake2b::Blake2bResult {
	const PREFIX: &[u8] = b"SS58PRE";

	let mut context = blake2_rfc::blake2b::Blake2b::new(64);
	context.update(PREFIX);
	context.update(data);
	context.finalize()
}

#[cfg(feature = "full")]
lazy_static::lazy_static! {
	static ref DEFAULT_VERSION: Mutex<Ss58AddressFormat>
		= Mutex::new(Ss58AddressFormat::SubstrateAccount);
}

macro_rules! ss58_address_format {
	( $( $identifier:tt => ($number:expr, $name:expr, $desc:tt) )* ) => (
		/// A known address (sub)format/network ID for SS58.
		#[derive(Copy, Clone, PartialEq, Eq)]
        #[cfg_attr(feature = "with-sp-debug-derive", derive(sp_debug_derive::RuntimeDebug))]
		pub enum Ss58AddressFormat {
			$(#[doc = $desc] $identifier),*,
			/// Use a manually provided numeric value as a standard identifier
			Custom(u16),
		}

		impl fmt::Display for Ss58AddressFormat {
			fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
				match self {
					$(
						Ss58AddressFormat::$identifier => write!(f, "{}", $name),
					)*
					Ss58AddressFormat::Custom(x) => write!(f, "{}", x),
				}

			}
		}

		static ALL_SS58_ADDRESS_FORMATS: [Ss58AddressFormat; 0 $(+ { let _ = $number; 1})*] = [
			$(Ss58AddressFormat::$identifier),*,
		];

		impl Ss58AddressFormat {
			/// names of all address formats
			pub fn all_names() -> &'static [&'static str] {
				&[
					$($name),*,
				]
			}
			/// All known address formats.
			pub fn all() -> &'static [Ss58AddressFormat] {
				&ALL_SS58_ADDRESS_FORMATS
			}

			/// Whether the address is custom.
			pub fn is_custom(&self) -> bool {
				matches!(self, Self::Custom(_))
			}
		}

		impl TryFrom<u8> for Ss58AddressFormat {
			type Error = ();

			fn try_from(x: u8) -> Result<Ss58AddressFormat, ()> {
				Ss58AddressFormat::try_from(x as u16)
			}
		}

		impl From<Ss58AddressFormat> for u16 {
			fn from(x: Ss58AddressFormat) -> u16 {
				match x {
					$(Ss58AddressFormat::$identifier => $number),*,
					Ss58AddressFormat::Custom(n) => n,
				}
			}
		}

		impl TryFrom<u16> for Ss58AddressFormat {
			type Error = ();

			fn try_from(x: u16) -> Result<Ss58AddressFormat, ()> {
				match x {
					$($number => Ok(Ss58AddressFormat::$identifier)),*,
					_ => Ok(Ss58AddressFormat::Custom(x)),
				}
			}
		}

		/// Error encountered while parsing `Ss58AddressFormat` from &'_ str
		/// unit struct for now.
        #[cfg_attr(feature = "with-sp-debug-derive", derive(sp_debug_derive::RuntimeDebug))]
		#[derive(Copy, Clone, PartialEq, Eq)]
		pub struct ParseError;

		impl<'a> TryFrom<&'a str> for Ss58AddressFormat {
			type Error = ParseError;

			fn try_from(x: &'a str) -> Result<Ss58AddressFormat, Self::Error> {
				match x {
					$($name => Ok(Ss58AddressFormat::$identifier)),*,
					a => a.parse::<u16>().map(Ss58AddressFormat::Custom).map_err(|_| ParseError),
				}
			}
		}

		impl str::FromStr for Ss58AddressFormat {
			type Err = ParseError;

			fn from_str(data: &str) -> Result<Self, Self::Err> {
				Self::try_from(data)
			}
		}

		impl fmt::Display for ParseError {
			fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
				write!(f, "failed to parse network value as u8")
			}
		}

		#[cfg(feature = "full")]
		impl Default for Ss58AddressFormat {
			fn default() -> Self {
				*DEFAULT_VERSION.lock()
			}
		}
	)
}

ss58_address_format!(
	PolkadotAccount =>
		(0, "polkadot", "Polkadot Relay-chain, standard account (*25519).")
	BareSr25519 =>
		(1, "sr25519", "Bare 32-bit Schnorr/Ristretto 25519 (S/R 25519) key.")
	KusamaAccount =>
		(2, "kusama", "Kusama Relay-chain, standard account (*25519).")
	BareEd25519 =>
		(3, "ed25519", "Bare 32-bit Edwards Ed25519 key.")
	KatalChainAccount =>
		(4, "katalchain", "Katal Chain, standard account (*25519).")
	PlasmAccount =>
		(5, "plasm", "Plasm Network, standard account (*25519).")
	BifrostAccount =>
		(6, "bifrost", "Bifrost mainnet, direct checksum, standard account (*25519).")
	EdgewareAccount =>
		(7, "edgeware", "Edgeware mainnet, standard account (*25519).")
	KaruraAccount =>
		(8, "karura", "Acala Karura canary network, standard account (*25519).")
	ReynoldsAccount =>
		(9, "reynolds", "Laminar Reynolds canary network, standard account (*25519).")
	AcalaAccount =>
		(10, "acala", "Acala mainnet, standard account (*25519).")
	LaminarAccount =>
		(11, "laminar", "Laminar mainnet, standard account (*25519).")
	PolymathAccount =>
		(12, "polymath", "Polymath network, standard account (*25519).")
	SubstraTeeAccount =>
		(13, "substratee", "Any SubstraTEE off-chain network private account (*25519).")
	TotemAccount =>
		(14, "totem", "Any Totem Live Accounting network standard account (*25519).")
	SynesthesiaAccount =>
		(15, "synesthesia", "Synesthesia mainnet, standard account (*25519).")
	KulupuAccount =>
		(16, "kulupu", "Kulupu mainnet, standard account (*25519).")
	DarkAccount =>
		(17, "dark", "Dark mainnet, standard account (*25519).")
	DarwiniaAccount =>
		(18, "darwinia", "Darwinia Chain mainnet, standard account (*25519).")
	GeekAccount =>
		(19, "geek", "GeekCash mainnet, standard account (*25519).")
	StafiAccount =>
		(20, "stafi", "Stafi mainnet, standard account (*25519).")
	DockTestAccount =>
		(21, "dock-testnet", "Dock testnet, standard account (*25519).")
	DockMainAccount =>
		(22, "dock-mainnet", "Dock mainnet, standard account (*25519).")
	ShiftNrg =>
		(23, "shift", "ShiftNrg mainnet, standard account (*25519).")
	ZeroAccount =>
		(24, "zero", "ZERO mainnet, standard account (*25519).")
	AlphavilleAccount =>
		(25, "alphaville", "ZERO testnet, standard account (*25519).")
	JupiterAccount =>
		(26, "jupiter", "Jupiter testnet, standard account (*25519).")
	SubsocialAccount =>
		(28, "subsocial", "Subsocial network, standard account (*25519).")
	DhiwayAccount =>
		(29, "cord", "Dhiway CORD network, standard account (*25519).")
	PhalaAccount =>
		(30, "phala", "Phala Network, standard account (*25519).")
	LitentryAccount =>
		(31, "litentry", "Litentry Network, standard account (*25519).")
	RobonomicsAccount =>
		(32, "robonomics", "Any Robonomics network standard account (*25519).")
	DataHighwayAccount =>
		(33, "datahighway", "DataHighway mainnet, standard account (*25519).")
	AresAccount =>
		(34, "ares", "Ares Protocol, standard account (*25519).")
	ValiuAccount =>
		(35, "vln", "Valiu Liquidity Network mainnet, standard account (*25519).")
	CentrifugeAccount =>
		(36, "centrifuge", "Centrifuge Chain mainnet, standard account (*25519).")
	NodleAccount =>
		(37, "nodle", "Nodle Chain mainnet, standard account (*25519).")
	KiltAccount =>
		(38, "kilt", "KILT Chain mainnet, standard account (*25519).")
	PolimecAccount =>
		(41, "poli", "Polimec Chain mainnet, standard account (*25519).")
	SubstrateAccount =>
		(42, "substrate", "Any Substrate network, standard account (*25519).")
	BareSecp256k1 =>
		(43, "secp256k1", "Bare ECDSA SECP256k1 key.")
	ChainXAccount =>
		(44, "chainx", "ChainX mainnet, standard account (*25519).")
	UniartsAccount =>
		(45, "uniarts", "UniArts Chain mainnet, standard account (*25519).")
	Reserved46 =>
		(46, "reserved46", "Reserved for future use (46).")
	Reserved47 =>
		(47, "reserved47", "Reserved for future use (47).")
	NeatcoinAccount =>
		(48, "neatcoin", "Neatcoin mainnet, standard account (*25519).")
	HydraDXAccount =>
		(63, "hydradx", "HydraDX standard account (*25519).")
	AventusAccount =>
		(65, "aventus", "Aventus Chain mainnet, standard account (*25519).")
	CrustAccount =>
		(66, "crust", "Crust Network, standard account (*25519).")
	EquilibriumAccount =>
		(67, "equilibrium", "Equilibrium Network, standard account (*25519).")
	SoraAccount =>
		(69, "sora", "SORA Network, standard account (*25519).")
  ZeitgeistAccount =>
		(73, "zeitgeist", "Zeitgeist network, standard account (*25519).")
	MantaAccount =>
		(77, "manta", "Manta Network, standard account (*25519).")
	CalamariAccount =>
		(78, "calamari", "Manta Canary Network, standard account (*25519).")
	PolkaSmith =>
		(98, "polkasmith", "PolkaSmith Canary Network, standard account (*25519).")
	PolkaFoundry =>
		(99, "polkafoundry", "PolkaFoundry Network, standard account (*25519).")
  OriginTrailAccount =>
		(101, "origintrail-parachain", "OriginTrail Parachain, ethereumm account (ECDSA).")
	HeikoAccount =>
		(110, "heiko", "Heiko, session key (*25519).")
	ParallelAccount =>
		(172, "parallel", "Parallel, session key (*25519).")
	SocialAccount =>
		(252, "social-network", "Social Network, standard account (*25519).")
	Moonbeam =>
		(1284, "moonbeam", "Moonbeam, session key (*25519).")
	Moonriver =>
		(1285, "moonriver", "Moonriver, session key (*25519).")
	BasiliskAccount =>
		(10041, "basilisk", "Basilisk standard account (*25519).")

	// Note: 16384 and above are reserved.
);

/// Set the default "version" (actually, this is a bit of a misnomer and the version byte is
/// typically used not just to encode format/version but also network identity) that is used for
/// encoding and decoding SS58 addresses. If an unknown version is provided then it fails.
///
/// See `ss58_address_format!` for all current known "versions".
#[cfg(feature = "full")]
pub fn set_default_ss58_version(version: Ss58AddressFormat) {
	*DEFAULT_VERSION.lock() = version
}

#[cfg(feature = "full")]
lazy_static::lazy_static! {
	pub static ref JUNCTION_REGEX: Regex = Regex::new(r"/(/?[^/]+)")
		.expect("constructed from known-good static value; qed");
	static ref SS58_REGEX: Regex = Regex::new(r"^(?P<ss58>[\w\d ]+)?(?P<path>(//?[^/]+)*)$")
		.expect("constructed from known-good static value; qed");
}

#[cfg(feature = "full")]
impl<T: Sized + AsMut<[u8]> + AsRef<[u8]> + Default + Derive> Ss58Codec for T {
	fn from_string(s: &str) -> Result<Self, PublicError> {
		let cap = SS58_REGEX.captures(s).ok_or(PublicError::InvalidFormat)?;
		let s = cap.name("ss58").map(|r| r.as_str()).unwrap_or(DEV_ADDRESS);
		let addr = if let Some(stripped) = s.strip_prefix("0x") {
			let mut d = ArrayVec::from([0u8; ADDRESS_UPPER_BOUND]);
			d.truncate(stripped.len() / 2);
			hex::decode_to_slice(stripped, &mut d).map_err(|_| PublicError::InvalidFormat)?;
			let mut r = Self::default();
			if d.len() == r.as_ref().len() {
				r.as_mut().copy_from_slice(&d);
				r
			} else {
				return Err(PublicError::BadLength)
			}
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
