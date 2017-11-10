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

//! Block and header type definitions.

use hash::H256;

/// Hash used to refer to a block hash.
pub type HeaderHash = H256;
/// Hash used to refer to proof of block header.
pub type ProofHash = H256;

/// Unique identifier of a parachain.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub struct ParachainId(u64);

impl From<ParachainId> for u64 {
	fn from(x: ParachainId) -> Self { x.0 }
}

impl From<u64> for ParachainId {
	fn from(x: u64) -> Self { ParachainId(x) }
}

/// A parachain block proposal.
#[derive(Debug, PartialEq, Eq)]
pub struct ParachainProposal {
	/// The ID of the parachain this is a proposal for.
	pub parachain: ParachainId,
	/// Parachain block header bytes.
	pub header: Vec<u8>,
	/// Hash of data necessary to prove validity of the header.
	pub proof_hash: ProofHash,
}

/// A relay chain block header.
#[derive(Debug, PartialEq, Eq)]
pub struct Header {
	/// Block parent's hash.
    pub parent_hash: HeaderHash,
	/// State root after this transition.
    pub state_root: H256,
	/// Unix time at which this header was produced.
    pub timestamp: u64,
	/// Block number.
	pub number: u64,
}

/// A relay chain block body.
///
/// Included candidates should be sorted by parachain ID, and without duplicate
/// IDs.
#[derive(Debug, PartialEq, Eq)]
pub struct Body {
	/// Parachain proposal blocks.
    pub para_blocks: Vec<ParachainProposal>,
}
