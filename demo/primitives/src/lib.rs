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
#[cfg(test)]
extern crate substrate_serializer;

extern crate substrate_codec as codec;

macro_rules! try_opt {
	($e: expr) => {
		match $e {
			Some(x) => x,
			None => return None,
		}
	}
}

pub mod block;
pub mod transaction;

pub use self::block::{Header, Block, Log, Digest};
pub use self::block::Number as BlockNumber;
pub use self::transaction::{Transaction, UncheckedTransaction, Function, Proposal};

/// Alias to Ed25519 pubkey that identifies an account on the relay chain. This will almost
/// certainly continue to be the same as the substrate's `AuthorityId`.
pub type AccountId = primitives::AuthorityId;

/// The Ed25519 pub key of an session that belongs to an authority of the relay chain. This is
/// exactly equivalent to what the substrate calls an "authority".
pub type SessionKey = primitives::AuthorityId;

/// Index of a transaction in the relay chain.
pub type TxOrder = u64;

/// A hash of some data used by the relay chain.
pub type Hash = primitives::H256;

/// Alias to 520-bit hash when used in the context of a signature on the relay chain.
pub type Signature = primitives::hash::H512;
