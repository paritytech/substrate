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

extern crate substrate_codec as codec;
extern crate substrate_primitives as primitives;
extern crate substrate_runtime_primitives as runtime_primitives;
extern crate substrate_runtime_std as rstd;

#[cfg(test)]
extern crate substrate_serializer;

#[macro_use]
extern crate substrate_codec_derive;

#[cfg(feature = "std")]
#[macro_use]
extern crate serde_derive;

#[cfg(feature = "std")]
extern crate serde;

#[cfg(feature = "std")]
use primitives::bytes;

use rstd::prelude::*;
use runtime_primitives::traits::BlakeTwo256;
use runtime_primitives::generic;

pub mod parachain;

/// Block header type as expected by this runtime.
pub type Header = generic::Header<BlockNumber, BlakeTwo256, Log>;

/// Opaque, encoded, unchecked extrinsic.
pub type UncheckedExtrinsic = Vec<u8>;

/// A "future-proof" block type for Polkadot. This will be resilient to upgrades in transaction
/// format, because it doesn't attempt to decode extrinsics.
///
/// Specialized code needs to link to (at least one version of) the runtime directly
/// in order to handle the extrinsics within.
pub type Block = generic::Block<Header, UncheckedExtrinsic>;

/// An index to a block.
/// 32-bits will allow for 136 years of blocks assuming 1 block per second.
/// TODO: switch to u32
pub type BlockNumber = u64;

/// Alias to Ed25519 pubkey that identifies an account on the relay chain.
pub type AccountId = primitives::hash::H256;

/// The type for looking up accounts. We don't expect more than 4 billion of them, but you
/// never know...
pub type AccountIndex = u64;

/// The Ed25519 pub key of an session that belongs to an authority of the relay chain. This is
/// exactly equivalent to what the substrate calls an "authority".
pub type SessionKey = primitives::AuthorityId;

/// Indentifier for a chain. 32-bit should be plenty.
pub type ChainId = u32;

/// A hash of some data used by the relay chain.
pub type Hash = primitives::H256;

/// Index of a transaction in the relay chain. 32-bit should be plenty.
pub type Index = u32;

/// Alias to 512-bit hash when used in the context of a signature on the relay chain.
/// Equipped with logic for possibly "unsigned" messages.
pub type Signature = runtime_primitives::MaybeUnsigned<runtime_primitives::Ed25519Signature>;

/// A timestamp: seconds since the unix epoch.
pub type Timestamp = u64;

/// The balance of an account.
/// 128-bits (or 38 significant decimal figures) will allow for 10m currency (10^7) at a resolution
/// to all for one second's worth of an annualised 50% reward be paid to a unit holder (10^11 unit
/// denomination), or 10^18 total atomic units, to grow at 50%/year for 51 years (10^9 multiplier)
/// for an eventual total of 10^27 units (27 significant decimal figures).
/// We round denomination to 10^12 (12 sdf), and leave the other redundancy at the upper end so
/// that 32 bits may be multiplied with a balance in 128 bits without worrying about overflow.
pub type Balance = u128;

/// "generic" block ID for the future-proof block type.
// TODO: parameterize blockid only as necessary.
pub type BlockId = generic::BlockId<Block>;

/// A log entry in the block.
#[derive(PartialEq, Eq, Clone, Default, Encode, Decode)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug))]
pub struct Log(#[cfg_attr(feature = "std", serde(with="bytes"))] pub Vec<u8>);

/// Inherent data to include in a block.
#[derive(Encode, Decode)]
pub struct InherentData {
	/// Current timestamp.
	pub timestamp: Timestamp,
	/// Parachain heads update.
	pub parachain_heads: Vec<::parachain::CandidateReceipt>,
	/// Indices of offline validators.
	pub offline_indices: Vec<u32>,
}
