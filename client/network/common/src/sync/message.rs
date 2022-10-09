// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! Network packet message types. These get serialized and put into the lower level protocol
//! payload.

use bitflags::bitflags;
use codec::{Decode, Encode, Error, Input, Output};
pub use generic::{BlockAnnounce, FromBlock};
use sp_runtime::traits::{Block as BlockT, Header as HeaderT};

/// Type alias for using the block request type using block type parameters.
pub type BlockRequest<B> =
	generic::BlockRequest<<B as BlockT>::Hash, <<B as BlockT>::Header as HeaderT>::Number>;

/// Type alias for using the BlockData type using block type parameters.
pub type BlockData<B> =
	generic::BlockData<<B as BlockT>::Header, <B as BlockT>::Hash, <B as BlockT>::Extrinsic>;

/// Type alias for using the BlockResponse type using block type parameters.
pub type BlockResponse<B> =
	generic::BlockResponse<<B as BlockT>::Header, <B as BlockT>::Hash, <B as BlockT>::Extrinsic>;

// Bits of block data and associated artifacts to request.
bitflags! {
	/// Node roles bitmask.
	pub struct BlockAttributes: u8 {
		/// Include block header.
		const HEADER = 0b00000001;
		/// Include block body.
		const BODY = 0b00000010;
		/// Include block receipt.
		const RECEIPT = 0b00000100;
		/// Include block message queue.
		const MESSAGE_QUEUE = 0b00001000;
		/// Include a justification for the block.
		const JUSTIFICATION = 0b00010000;
		/// Include indexed transactions for a block.
		const INDEXED_BODY = 0b00100000;
	}
}

impl BlockAttributes {
	/// Encodes attributes as big endian u32, compatible with SCALE-encoding (i.e the
	/// significant byte has zero index).
	pub fn to_be_u32(&self) -> u32 {
		u32::from_be_bytes([self.bits(), 0, 0, 0])
	}

	/// Decodes attributes, encoded with the `encode_to_be_u32()` call.
	pub fn from_be_u32(encoded: u32) -> Result<Self, Error> {
		Self::from_bits(encoded.to_be_bytes()[0])
			.ok_or_else(|| Error::from("Invalid BlockAttributes"))
	}
}

impl Encode for BlockAttributes {
	fn encode_to<T: Output + ?Sized>(&self, dest: &mut T) {
		dest.push_byte(self.bits())
	}
}

impl codec::EncodeLike for BlockAttributes {}

impl Decode for BlockAttributes {
	fn decode<I: Input>(input: &mut I) -> Result<Self, Error> {
		Self::from_bits(input.read_byte()?).ok_or_else(|| Error::from("Invalid bytes"))
	}
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Encode, Decode)]
/// Block enumeration direction.
pub enum Direction {
	/// Enumerate in ascending order (from child to parent).
	Ascending = 0,
	/// Enumerate in descending order (from parent to canonical child).
	Descending = 1,
}

/// Block state in the chain.
#[derive(Debug, PartialEq, Eq, Clone, Copy, Encode, Decode)]
pub enum BlockState {
	/// Block is not part of the best chain.
	Normal,
	/// Latest best block.
	Best,
}

/// Announcement summary used for debug logging.
#[derive(Debug)]
pub struct AnnouncementSummary<H: HeaderT> {
	pub block_hash: H::Hash,
	pub number: H::Number,
	pub parent_hash: H::Hash,
	pub state: Option<BlockState>,
}

impl<H: HeaderT> BlockAnnounce<H> {
	pub fn summary(&self) -> AnnouncementSummary<H> {
		AnnouncementSummary {
			block_hash: self.header.hash(),
			number: *self.header.number(),
			parent_hash: *self.header.parent_hash(),
			state: self.state,
		}
	}
}

/// Generic types.
pub mod generic {
	use super::{BlockAttributes, BlockState, Direction};
	use crate::message::RequestId;
	use codec::{Decode, Encode, Input, Output};
	use sp_runtime::{EncodedJustification, Justifications};

	/// Block data sent in the response.
	#[derive(Debug, PartialEq, Eq, Clone, Encode, Decode)]
	pub struct BlockData<Header, Hash, Extrinsic> {
		/// Block header hash.
		pub hash: Hash,
		/// Block header if requested.
		pub header: Option<Header>,
		/// Block body if requested.
		pub body: Option<Vec<Extrinsic>>,
		/// Block body indexed transactions if requested.
		pub indexed_body: Option<Vec<Vec<u8>>>,
		/// Block receipt if requested.
		pub receipt: Option<Vec<u8>>,
		/// Block message queue if requested.
		pub message_queue: Option<Vec<u8>>,
		/// Justification if requested.
		pub justification: Option<EncodedJustification>,
		/// Justifications if requested.
		pub justifications: Option<Justifications>,
	}

	/// Request block data from a peer.
	#[derive(Debug, PartialEq, Eq, Clone, Encode, Decode)]
	pub struct BlockRequest<Hash, Number> {
		/// Unique request id.
		pub id: RequestId,
		/// Bits of block data to request.
		pub fields: BlockAttributes,
		/// Start from this block.
		pub from: FromBlock<Hash, Number>,
		/// Sequence direction.
		pub direction: Direction,
		/// Maximum number of blocks to return. An implementation defined maximum is used when
		/// unspecified.
		pub max: Option<u32>,
	}

	/// Identifies starting point of a block sequence.
	#[derive(Debug, PartialEq, Eq, Clone, Encode, Decode)]
	pub enum FromBlock<Hash, Number> {
		/// Start with given hash.
		Hash(Hash),
		/// Start with given block number.
		Number(Number),
	}

	/// Response to `BlockRequest`
	#[derive(Debug, PartialEq, Eq, Clone, Encode, Decode)]
	pub struct BlockResponse<Header, Hash, Extrinsic> {
		/// Id of a request this response was made for.
		pub id: RequestId,
		/// Block data for the requested sequence.
		pub blocks: Vec<BlockData<Header, Hash, Extrinsic>>,
	}

	/// Announce a new complete relay chain block on the network.
	#[derive(Debug, PartialEq, Eq, Clone)]
	pub struct BlockAnnounce<H> {
		/// New block header.
		pub header: H,
		/// Block state. TODO: Remove `Option` and custom encoding when v4 becomes common.
		pub state: Option<BlockState>,
		/// Data associated with this block announcement, e.g. a candidate message.
		pub data: Option<Vec<u8>>,
	}

	// Custom Encode/Decode impl to maintain backwards compatibility with v3.
	// This assumes that the packet contains nothing but the announcement message.
	// TODO: Get rid of it once protocol v4 is common.
	impl<H: Encode> Encode for BlockAnnounce<H> {
		fn encode_to<T: Output + ?Sized>(&self, dest: &mut T) {
			self.header.encode_to(dest);
			if let Some(state) = &self.state {
				state.encode_to(dest);
			}
			if let Some(data) = &self.data {
				data.encode_to(dest)
			}
		}
	}

	impl<H: Decode> Decode for BlockAnnounce<H> {
		fn decode<I: Input>(input: &mut I) -> Result<Self, codec::Error> {
			let header = H::decode(input)?;
			let state = BlockState::decode(input).ok();
			let data = Vec::decode(input).ok();
			Ok(Self { header, state, data })
		}
	}
}
