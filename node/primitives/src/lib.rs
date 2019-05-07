// Copyright 2018-2019 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Low-level types used throughout the Substrate code.

#![warn(missing_docs)]

#![cfg_attr(not(feature = "std"), no_std)]

use runtime_primitives::{
	generic, traits::{Verify, BlakeTwo256}, OpaqueExtrinsic, AnySignature
};

/// An index to a block.
pub type BlockNumber = u64;

/// Alias to 512-bit hash when used in the context of a transaction signature on the chain.
pub type Signature = AnySignature;

/// Some way of identifying an account on the chain. We intentionally make it equivalent
/// to the public key of our transaction signing scheme.
pub type AccountId = <Signature as Verify>::Signer;

/// The type for looking up accounts. We don't expect more than 4 billion of them, but you
/// never know...
pub type AccountIndex = u32;

/// Balance of an account.
pub type Balance = u128;

/// The Ed25519 pub key of an session that belongs to an authority of the chain. This is
/// exactly equivalent to what the substrate calls an "authority".
pub type AuthorityId = <AuthoritySignature as Verify>::Signer;

/// Alias to 512-bit hash when used in the context of a session signature on the chain.
pub type AuthoritySignature = primitives::ed25519::Signature;

/// Index of a transaction in the chain.
pub type Index = u64;

/// A hash of some data used by the chain.
pub type Hash = primitives::H256;

/// A timestamp: seconds since the unix epoch.
pub type Timestamp = u64;

/// Header type.
/// 
pub type Header = generic::Header<BlockNumber, BlakeTwo256, generic::DigestItem<Hash, AuthorityId, AuthoritySignature>>;
/// Block type.
pub type Block = generic::Block<Header, UncheckedExtrinsic>;
/// Block ID.
pub type BlockId = generic::BlockId<Block>;

/// Opaque, encoded, unchecked extrinsic.
pub type UncheckedExtrinsic = OpaqueExtrinsic;
