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
extern crate ring;
extern crate untrusted;

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
pub mod ed25519;

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
