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

#[cfg(feature = "std")]
#[macro_use]
extern crate serde_derive;
#[cfg(feature = "std")]
extern crate serde;

extern crate substrate_runtime_std as rstd;
extern crate substrate_primitives as primitives;
extern crate substrate_runtime_primitives as runtime_primitives;
#[cfg(test)]
extern crate substrate_serializer;

extern crate substrate_codec as codec;

pub mod parachain;

/// Virtual account ID that represents the idea of a dispatch/statement being signed by everybody
/// (who matters). Essentially this means that a majority of validators have decided it is
/// "correct".
pub const EVERYBODY: AccountId = [255u8; 32];

/// Something that identifies a block.
pub use primitives::block::Id as BlockId;

/// The type of digest item.
pub use primitives::block::Log as Log;

/// An index to a block.
/// 32-bits will allow for 136 years of blocks assuming 1 block per second.
/// TODO: switch to u32
pub type BlockNumber = u64;

/// Alias to Ed25519 pubkey that identifies an account on the relay chain. This will almost
/// certainly continue to be the same as the substrate's `AuthorityId`.
pub type AccountId = primitives::AuthorityId;

/// The Ed25519 pub key of an session that belongs to an authority of the relay chain. This is
/// exactly equivalent to what the substrate calls an "authority".
pub type SessionKey = primitives::AuthorityId;

/// Indentifier for a chain. 32-bit should be plenty.
pub type ChainId = u32;

/// Index of a transaction in the relay chain. 32-bit should be plenty.
pub type Index = u32;

/// A hash of some data used by the relay chain.
pub type Hash = primitives::H256;

/// Alias to 512-bit hash when used in the context of a signature on the relay chain.
pub type Signature = runtime_primitives::Ed25519Signature;

/// A timestamp: seconds since the unix epoch.
pub type Timestamp = u64;

/// The balance of an account.
/// 128-bits (or 38 significant decimal figures) will allow for 10m currency (10^7) at a resolution
/// to all for one second's worth of an annualised 50% reward be paid to a unit holder (10^11 unit
/// denomination), or 10^18 total atomic units, to grow at 50%/year for 51 years (10^9 multiplier)
/// for an eventual total of 10^27 units (27 significant decimal figures).
/// We round denomination to 10^12 (12 sdf), and leave the other redundancy at the upper end so
/// that 32 bits may be multiplied with a balance in 128 bits without worrying about overflow.
pub type Balance = runtime_primitives::U128;
