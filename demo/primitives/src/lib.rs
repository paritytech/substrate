// Copyright 2018 Parity Technologies (UK) Ltd.
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
extern crate substrate_codec_derive;

extern crate substrate_runtime_std as rstd;
extern crate substrate_runtime_primitives as runtime_primitives;
extern crate substrate_primitives as primitives;
extern crate substrate_codec as codec;

use rstd::prelude::*;
use runtime_primitives::generic;
#[cfg(feature = "std")]
use primitives::bytes;
use runtime_primitives::traits::BlakeTwo256;

/// An index to a block.
pub type BlockNumber = u64;

/// Alias to Ed25519 pubkey that identifies an account on the chain. This will almost
/// certainly continue to be the same as the substrate's `AuthorityId`.
pub type AccountId = ::primitives::H256;

/// The type for looking up accounts. We don't expect more than 4 billion of them, but you
/// never know...
pub type AccountIndex = u32;

/// Balance of an account.
pub type Balance = u64;

/// The Ed25519 pub key of an session that belongs to an authority of the chain. This is
/// exactly equivalent to what the substrate calls an "authority".
pub type SessionKey = primitives::AuthorityId;

/// Index of a transaction in the chain.
pub type Index = u64;

/// A hash of some data used by the chain.
pub type Hash = primitives::H256;

/// Alias to 512-bit hash when used in the context of a signature on the chain.
pub type Signature = runtime_primitives::Ed25519Signature;

/// A timestamp: seconds since the unix epoch.
pub type Timestamp = u64;

/// Header type.
pub type Header = generic::Header<BlockNumber, BlakeTwo256, generic::DigestItem<()>>;
/// Block type.
pub type Block = generic::Block<Header, UncheckedExtrinsic>;
/// Block ID.
pub type BlockId = generic::BlockId<Block>;

/// Opaque, encoded, unchecked extrinsic.
#[derive(PartialEq, Eq, Clone, Default, Encode, Decode)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug))]
pub struct UncheckedExtrinsic(#[cfg_attr(feature = "std", serde(with="bytes"))] pub Vec<u8>);
///
/// Inherent data to include in a block.
#[derive(Encode, Decode)]
pub struct InherentData {
	/// Current timestamp.
	pub timestamp: Timestamp,
	/// Indices of offline validators.
	pub offline_indices: Vec<u32>,
}
