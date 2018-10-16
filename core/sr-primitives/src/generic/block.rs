// Copyright 2017-2018 Parity Technologies (UK) Ltd.
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

//! Generic implementation of a block and associated items.

#[cfg(feature = "std")]
use std::fmt;

use rstd::prelude::*;
use codec::Codec;
use traits::{self, Member, Block as BlockT, Header as HeaderT, DigestItemFor};
use ::Justification;

/// Something to identify a block.
#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Debug, Serialize))]
#[cfg_attr(feature = "std", serde(rename_all = "camelCase"))]
#[cfg_attr(feature = "std", serde(deny_unknown_fields))]
pub enum BlockId<Block: BlockT> {
	/// Identify by block header hash.
	Hash(<<Block as BlockT>::Header as HeaderT>::Hash),
	/// Identify by block number.
	Number(<<Block as BlockT>::Header as HeaderT>::Number),
}

impl<Block: BlockT> BlockId<Block> {
	/// Create a block ID from a hash.
	pub fn hash(hash: Block::Hash) -> Self {
		BlockId::Hash(hash)
	}

	/// Create a block ID from a number.
	pub fn number(number: <Block::Header as HeaderT>::Number) -> Self {
		BlockId::Number(number)
	}
}

impl<Block: BlockT> Copy for BlockId<Block> {}

#[cfg(feature = "std")]
impl<Block: BlockT> fmt::Display for BlockId<Block> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "{:?}", self)
	}
}

/// Abstraction over a substrate block.
#[derive(PartialEq, Eq, Clone, Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
#[cfg_attr(feature = "std", serde(rename_all = "camelCase"))]
#[cfg_attr(feature = "std", serde(deny_unknown_fields))]
pub struct Block<Header, Extrinsic> {
	/// The block header.
	pub header: Header,
	/// The accompanying extrinsics.
	pub extrinsics: Vec<Extrinsic>,
}

impl<Header, Extrinsic> traits::Block for Block<Header, Extrinsic>
where
	Header: HeaderT,
	Extrinsic: Member + Codec + traits::Extrinsic,
{
	type Extrinsic = Extrinsic;
	type Header = Header;
	type Hash = <Self::Header as traits::Header>::Hash;

	fn header(&self) -> &Self::Header {
		&self.header
	}
	fn extrinsics(&self) -> &[Self::Extrinsic] {
		&self.extrinsics[..]
	}
	fn deconstruct(self) -> (Self::Header, Vec<Self::Extrinsic>) {
		(self.header, self.extrinsics)
	}
	fn new(header: Self::Header, extrinsics: Vec<Self::Extrinsic>) -> Self {
		Block { header, extrinsics }
	}
}

/// Abstraction over a substrate block and justification.
#[derive(PartialEq, Eq, Clone, Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
#[cfg_attr(feature = "std", serde(rename_all = "camelCase"))]
#[cfg_attr(feature = "std", serde(deny_unknown_fields))]
pub struct SignedBlock<H, E> {
	/// Full block.
	pub block: Block<H, E>,
	/// Block justification.
	pub justification: Justification,
}

/// Block import result.
#[derive(Debug)]
pub enum ImportResult {
	/// Added to the import queue.
	Queued,
	/// Already in the import queue.
	AlreadyQueued,
	/// Already in the blockchain.
	AlreadyInChain,
	/// Block or parent is known to be bad.
	KnownBad,
	/// Block parent is not in the chain.
	UnknownParent,
}

/// Block data origin.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum BlockOrigin {
	/// Genesis block built into the client.
	Genesis,
	/// Block is part of the initial sync with the network.
	NetworkInitialSync,
	/// Block was broadcasted on the network.
	NetworkBroadcast,
	/// Block that was received from the network and validated in the consensus process.
	ConsensusBroadcast,
	/// Block that was collated by this node.
	Own,
	/// Block was imported from a file.
	File,
}

/// Data required to import a Block
pub struct ImportBlock<Block: BlockT> {
	/// Origin of the Block
	pub origin: BlockOrigin,
	/// The header, without consensus post-digests applied. This should be in the same
	/// state as it comes out of the runtime.
	///
	/// Consensus engines which alter the header (by adding post-runtime digests)
	/// should strip those off in the initial verification process and pass them
	/// via the `post_runtime_digests` field. During block authorship, they should
	/// not be pushed to the header directly.
	///
	/// The reason for this distinction is so the header can be directly
	/// re-executed in a runtime that checks digest equivalence -- the
	/// post-runtime digests are pushed back on after.
	pub header: Block::Header,
	/// Justification provided for this block from the outside:.
	pub external_justification: Justification,
	/// Digest items that have been added after the runtime for external
	/// work, like a consensus signature.
	pub post_runtime_digests: Vec<DigestItemFor<Block>>,
	/// Block's body
	pub body: Option<Vec<Block::Extrinsic>>,
	/// Is this block finalized already?
	/// `true` implies instant finality.
	pub finalized: bool,
	/// Auxiliary consensus data produced by the block.
	/// Contains a list of key-value pairs. If values are `None`, the keys
	/// will be deleted.
	pub auxiliary: Vec<(Vec<u8>, Option<Vec<u8>>)>,
}

impl<Block: BlockT> ImportBlock<Block> {
	/// Deconstruct the justified header into parts.
	pub fn into_inner(self)
		-> (
			BlockOrigin,
			<Block as BlockT>::Header,
			Justification,
			Vec<DigestItemFor<Block>>,
			Option<Vec<<Block as BlockT>::Extrinsic>>,
			bool,
			Vec<(Vec<u8>, Option<Vec<u8>>)>,
		) {
		(
			self.origin,
			self.header,
			self.external_justification,
			self.post_runtime_digests,
			self.body,
			self.finalized,
			self.auxiliary,
		)
	}
}