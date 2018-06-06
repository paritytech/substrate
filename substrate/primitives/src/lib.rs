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

#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(not(feature = "std"), feature(alloc))]

extern crate rustc_hex;
extern crate byteorder;
#[macro_use]
extern crate crunchy;
#[macro_use]
extern crate fixed_hash;
#[macro_use]
extern crate uint as uint_crate;
extern crate substrate_codec as codec;

#[cfg(feature = "std")]
extern crate serde;
#[cfg(feature = "std")]
extern crate twox_hash;
#[cfg(feature = "std")]
extern crate blake2_rfc;
#[cfg(feature = "std")]
#[macro_use]
extern crate serde_derive;
#[cfg(feature = "std")]
extern crate core;
#[cfg(feature = "std")]
extern crate wasmi;

extern crate substrate_runtime_std as rstd;

#[cfg(test)]
extern crate substrate_serializer;

#[cfg(test)]
#[macro_use]
extern crate pretty_assertions;

#[macro_export]
macro_rules! map {
	($( $name:expr => $value:expr ),*) => (
		vec![ $( ( $name, $value ) ),* ].into_iter().collect()
	)
}


#[cfg(feature = "std")]
pub mod bytes;
#[cfg(feature = "std")]
pub mod hashing;
#[cfg(feature = "std")]
pub use hashing::{blake2_256, twox_128, twox_256};
#[cfg(feature = "std")]
pub mod hexdisplay;

pub mod hash;
pub mod sandbox;
pub mod storage;
pub mod uint;

#[cfg(test)]
mod tests;

pub use self::hash::{H160, H256, H512};
pub use self::uint::{U256, U512};

/// An identifier for an authority in the consensus algorithm. The same as ed25519::Public.
pub type AuthorityId = [u8; 32];

/// A 512-bit value interpreted as a signature.
pub type Signature = hash::H512;
