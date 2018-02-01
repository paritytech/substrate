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
extern crate serde;
extern crate ring;
extern crate untrusted;
extern crate twox_hash;
extern crate byteorder;
extern crate blake2_rfc;

#[macro_use]
extern crate crunchy;
#[macro_use]
extern crate fixed_hash;
#[macro_use]
extern crate serde_derive;
#[macro_use]
extern crate uint as uint_crate;

#[cfg(feature = "std")]
extern crate core;
#[cfg(test)]
extern crate polkadot_serializer;
#[cfg(test)]
#[macro_use]
extern crate pretty_assertions;

#[cfg(not(feature = "std"))]
#[macro_use]
extern crate alloc;

mod bytes;
pub mod block;
pub mod contract;
pub mod ed25519;
pub mod hash;
pub mod hashing;
pub mod hexdisplay;
pub mod parachain;
pub mod proposal;
pub mod runtime_function;
pub mod transaction;
pub mod uint;
pub mod validator;

pub use self::hash::{H160, H256};
pub use self::uint::{U256, U512};
pub use hashing::{blake2_256, twox_128, twox_256};

/// Virtual account ID that represents the idea of a dispatch/statement being signed by everybody
/// (who matters). Essentially this means that a majority of validators have decided it is
/// "correct".
pub const EVERYBODY: AccountId = [255u8; 32];

/// Alias to Ed25519 pubkey that identifies an account.
pub type AccountId = [u8; 32];

/// The Ed25519 pub key of an session that belongs to an authority. This is used as what the
/// external environment/consensus algorithm calls an "authority".
pub type SessionKey = AccountId;

/// Indentifier for a chain.
pub type ChainID = u64;

/// Index of a block in the chain.
pub type BlockNumber = u64;

/// Index of a transaction.
pub type TxOrder = u64;

/// A hash of some data.
pub type Hash = [u8; 32];

/// Alias to 520-bit hash when used in the context of a signature.
pub type Signature = hash::H512;

/// A hash function.
pub fn hash(data: &[u8]) -> hash::H256 {
	blake2_256(data).into()
}
