// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Substrate Demo.

// Substrate Demo is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate Demo is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate Demo.  If not, see <http://www.gnu.org/licenses/>.

//! Low-level types used throughout the Substrate Demo code.

#![warn(missing_docs)]

#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(not(feature = "std"), feature(alloc))]

#[cfg(feature = "std")]
extern crate serde;

#[cfg(feature = "std")]
#[macro_use]
extern crate serde_derive;

#[macro_use]
extern crate substrate_runtime_support;

extern crate substrate_runtime_std as rstd;
extern crate substrate_runtime_primitives as runtime_primitives;
extern crate substrate_primitives as primitives;
extern crate substrate_codec as codec;

use rstd::prelude::*;
use runtime_primitives::traits::BlakeTwo256;
use runtime_primitives::generic;
use codec::{Input, Output, Encode, Decode};

#[cfg(feature = "std")]
use primitives::bytes;

/// An index to a block.
pub type BlockNumber = u64;

/// Alias to Ed25519 pubkey that identifies an account on the relay chain. This will almost
/// certainly continue to be the same as the substrate's `AuthorityId`.
pub type AccountId = primitives::hash::H256;

/// Node id within the Blitz network
pub type NodeId = primitives::hash::H256;

/// Chain Transaction Hash is used in a Blitz consensus
pub type CTH = primitives::hash::H256;

/// The type for looking up accounts. We don't expect more than 4 billion of them, but you
/// never know...
pub type AccountIndex = u64;

/// Balance of an account.
pub type Balance = u64;

/// The Ed25519 pub key of an session that belongs to an authority of the relay chain. This is
/// exactly equivalent to what the substrate calls an "authority".
pub type SessionKey = primitives::AuthorityId;

/// Index of a transaction in the relay chain.
pub type Index = u64;

/// A hash of some data used by the relay chain.
pub type Hash = primitives::H256;

/// Alias to 512-bit hash when used in the context of a signature on the relay chain.
/// Equipped with logic for possibly "unsigned" messages.
pub type Signature = runtime_primitives::MaybeUnsigned<runtime_primitives::Ed25519Signature>;

/// Round id of the Blitz protocol
pub type RoundId = u64;

/// Public key of an entity within a Blitz network
pub type PublicKey = primitives::AuthorityId;

/// Timestamp within the Blitz network
pub type Timestamp = u64;

/// Amount of funds to be transfered
pub type Amount = u64;

/// Address of an account within the Blitz network
pub type AccountAddress = Hash;

/// Block header type as expected by this runtime.
pub type Header = generic::Header<BlockNumber, BlakeTwo256, Log>;

/// Opaque, encoded, unchecked extrinsic.
pub type UncheckedExtrinsic = Vec<u8>;

/// A "future-proof" block type for Blitz. This will be resilient to upgrades in transaction
/// format, because it doesn't attempt to decode extrinsics.
///
/// Specialized code needs to link to (at least one version of) the runtime directly
/// in order to handle the extrinsics within.
pub type Block = generic::Block<Header, UncheckedExtrinsic>;

/// "generic" block ID for the future-proof block type.
// TODO: parameterize blockid only as necessary.
pub type BlockId = generic::BlockId<Block>;

/// A log entry in the block.
#[derive(PartialEq, Eq, Clone, Default)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug))]
pub struct Log(#[cfg_attr(feature = "std", serde(with="bytes"))] pub Vec<u8>);


impl Decode for Log {
	fn decode<I: Input>(input: &mut I) -> Option<Self> {
		Vec::<u8>::decode(input).map(Log)
	}
}

impl Encode for Log {
	fn encode_to<T: Output>(&self, dest: &mut T) {
		self.0.encode_to(dest)
	}
}
