// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

//! Network packet message types. These get serialized and put into the lower level protocol payload.

use bitflags::bitflags;
use runtime_primitives::{ConsensusEngineId, traits::{Block as BlockT, Header as HeaderT}};
use parity_codec::{Encode, Decode, Input, Output};
pub use self::generic::{
	BlockAnnounce, RemoteCallRequest, RemoteReadRequest,
	RemoteHeaderRequest, RemoteHeaderResponse,
	RemoteChangesRequest, RemoteChangesResponse,
	FromBlock, RemoteReadChildRequest,
};

/// A unique ID of a request.
pub type RequestId = u64;

/// Type alias for using the message type using block type parameters.
pub type Message<B> = generic::Message<
	<B as BlockT>::Header,
	<B as BlockT>::Hash,
	<<B as BlockT>::Header as HeaderT>::Number,
	<B as BlockT>::Extrinsic,
>;

/// Type alias for using the status type using block type parameters.
pub type Status<B> = generic::Status<
	<B as BlockT>::Hash,
	<<B as BlockT>::Header as HeaderT>::Number,
>;

/// Type alias for using the block request type using block type parameters.
pub type BlockRequest<B> = generic::BlockRequest<
	<B as BlockT>::Hash,
	<<B as BlockT>::Header as HeaderT>::Number,
>;

/// Type alias for using the BlockData type using block type parameters.
pub type BlockData<B> = generic::BlockData<
	<B as BlockT>::Header,
	<B as BlockT>::Hash,
	<B as BlockT>::Extrinsic,
>;

/// Type alias for using the BlockResponse type using block type parameters.
pub type BlockResponse<B> = generic::BlockResponse<
	<B as BlockT>::Header,
	<B as BlockT>::Hash,
	<B as BlockT>::Extrinsic,
>;

/// A set of transactions.
pub type Transactions<E> = Vec<E>;

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
	}
}

impl Encode for BlockAttributes {
	fn encode_to<T: Output>(&self, dest: &mut T) {
		dest.push_byte(self.bits())
	}
}

impl Decode for BlockAttributes {
	fn decode<I: Input>(input: &mut I) -> Option<Self> {
		Self::from_bits(input.read_byte()?)
	}
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Encode, Decode)]
/// Block enumeration direction.
pub enum Direction {
	/// Enumerate in ascending order (from child to parent).
	Ascending = 0,
	/// Enumerate in descendfing order (from parent to canonical child).
	Descending = 1,
}

/// Remote call response.
#[derive(Debug, PartialEq, Eq, Clone, Encode, Decode)]
pub struct RemoteCallResponse {
	/// Id of a request this response was made for.
	pub id: RequestId,
	/// Execution proof.
	pub proof: Vec<Vec<u8>>,
}

#[derive(Debug, PartialEq, Eq, Clone, Encode, Decode)]
/// Remote read response.
pub struct RemoteReadResponse {
	/// Id of a request this response was made for.
	pub id: RequestId,
	/// Read proof.
	pub proof: Vec<Vec<u8>>,
}

/// Generic types.
pub mod generic {
	use parity_codec::{Encode, Decode};
	use network_libp2p::CustomMessage;
	use runtime_primitives::Justification;
	use crate::config::Roles;
	use super::{
		RemoteReadResponse, Transactions, Direction,
		RequestId, BlockAttributes, RemoteCallResponse, ConsensusEngineId,
	};
	/// Consensus is mostly opaque to us
	#[derive(Debug, PartialEq, Eq, Clone, Encode, Decode)]
	pub struct ConsensusMessage {
		/// Identifies consensus engine.
		pub engine_id: ConsensusEngineId,
		/// Message payload.
		pub data: Vec<u8>,
	}

	/// Block data sent in the response.
	#[derive(Debug, PartialEq, Eq, Clone, Encode, Decode)]
	pub struct BlockData<Header, Hash, Extrinsic> {
		/// Block header hash.
		pub hash: Hash,
		/// Block header if requested.
		pub header: Option<Header>,
		/// Block body if requested.
		pub body: Option<Vec<Extrinsic>>,
		/// Block receipt if requested.
		pub receipt: Option<Vec<u8>>,
		/// Block message queue if requested.
		pub message_queue: Option<Vec<u8>>,
		/// Justification if requested.
		pub justification: Option<Justification>,
	}

	/// Identifies starting point of a block sequence.
	#[derive(Debug, PartialEq, Eq, Clone, Encode, Decode)]
	pub enum FromBlock<Hash, Number> {
		/// Start with given hash.
		Hash(Hash),
		/// Start with given block number.
		Number(Number),
	}

	/// A network message.
	#[derive(Debug, PartialEq, Eq, Clone, Encode, Decode)]
	pub enum Message<Header, Hash, Number, Extrinsic> {
		/// Status packet.
		Status(Status<Hash, Number>),
		/// Block request.
		BlockRequest(BlockRequest<Hash, Number>),
		/// Block response.
		BlockResponse(BlockResponse<Header, Hash, Extrinsic>),
		/// Block announce.
		BlockAnnounce(BlockAnnounce<Header>),
		/// Transactions.
		Transactions(Transactions<Extrinsic>),
		/// Consensus protocol message.
		Consensus(ConsensusMessage),
		/// Remote method call request.
		RemoteCallRequest(RemoteCallRequest<Hash>),
		/// Remote method call response.
		RemoteCallResponse(RemoteCallResponse),
		/// Remote storage read request.
		RemoteReadRequest(RemoteReadRequest<Hash>),
		/// Remote storage read response.
		RemoteReadResponse(RemoteReadResponse),
		/// Remote header request.
		RemoteHeaderRequest(RemoteHeaderRequest<Number>),
		/// Remote header response.
		RemoteHeaderResponse(RemoteHeaderResponse<Header>),
		/// Remote changes request.
		RemoteChangesRequest(RemoteChangesRequest<Hash>),
		/// Remote changes reponse.
		RemoteChangesResponse(RemoteChangesResponse<Number, Hash>),
		/// Remote child storage read request.
		RemoteReadChildRequest(RemoteReadChildRequest<Hash>),
		/// Chain-specific message
		#[codec(index = "255")]
		ChainSpecific(Vec<u8>),
	}

	impl<Header, Hash, Number, Extrinsic> CustomMessage for Message<Header, Hash, Number, Extrinsic>
		where Self: Decode + Encode
	{
		fn into_bytes(self) -> Vec<u8> {
			self.encode()
		}

		fn from_bytes(bytes: &[u8]) -> Result<Self, ()> {
			Decode::decode(&mut &bytes[..]).ok_or(())
		}
	}

	/// Status sent on connection.
	#[derive(Debug, PartialEq, Eq, Clone, Encode, Decode)]
	pub struct Status<Hash, Number> {
		/// Protocol version.
		pub version: u32,
		/// Minimum supported version.
		pub min_supported_version: u32,
		/// Supported roles.
		pub roles: Roles,
		/// Best block number.
		pub best_number: Number,
		/// Best block hash.
		pub best_hash: Hash,
		/// Genesis block hash.
		pub genesis_hash: Hash,
		/// Chain-specific status.
		pub chain_status: Vec<u8>,
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
		/// End at this block. An implementation defined maximum is used when unspecified.
		pub to: Option<Hash>,
		/// Sequence direction.
		pub direction: Direction,
		/// Maximum number of blocks to return. An implementation defined maximum is used when unspecified.
		pub max: Option<u32>,
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
	#[derive(Debug, PartialEq, Eq, Clone, Encode, Decode)]
	pub struct BlockAnnounce<H> {
		/// New block header.
		pub header: H,
	}

	#[derive(Debug, PartialEq, Eq, Clone, Encode, Decode)]
	/// Remote call request.
	pub struct RemoteCallRequest<H> {
		/// Unique request id.
		pub id: RequestId,
		/// Block at which to perform call.
		pub block: H,
		/// Method name.
		pub method: String,
		/// Call data.
		pub data: Vec<u8>,
	}

	#[derive(Debug, PartialEq, Eq, Clone, Encode, Decode)]
	/// Remote storage read request.
	pub struct RemoteReadRequest<H> {
		/// Unique request id.
		pub id: RequestId,
		/// Block at which to perform call.
		pub block: H,
		/// Storage key.
		pub key: Vec<u8>,
	}

	#[derive(Debug, PartialEq, Eq, Clone, Encode, Decode)]
	/// Remote storage read child request.
	pub struct RemoteReadChildRequest<H> {
		/// Unique request id.
		pub id: RequestId,
		/// Block at which to perform call.
		pub block: H,
		/// Child Storage key.
		pub storage_key: Vec<u8>,
		/// Storage key.
		pub key: Vec<u8>,
	}

	#[derive(Debug, PartialEq, Eq, Clone, Encode, Decode)]
	/// Remote header request.
	pub struct RemoteHeaderRequest<N> {
		/// Unique request id.
		pub id: RequestId,
		/// Block number to request header for.
		pub block: N,
	}

	#[derive(Debug, PartialEq, Eq, Clone, Encode, Decode)]
	/// Remote header response.
	pub struct RemoteHeaderResponse<Header> {
		/// Id of a request this response was made for.
		pub id: RequestId,
		/// Header. None if proof generation has failed (e.g. header is unknown).
		pub header: Option<Header>,
		/// Header proof.
		pub proof: Vec<Vec<u8>>,
	}

	#[derive(Debug, PartialEq, Eq, Clone, Encode, Decode)]
	/// Remote changes request.
	pub struct RemoteChangesRequest<H> {
		/// Unique request id.
		pub id: RequestId,
		/// Hash of the first block of the range (including first) where changes are requested.
		pub first: H,
		/// Hash of the last block of the range (including last) where changes are requested.
		pub last: H,
		/// Hash of the first block for which the requester has the changes trie root. All other
		/// affected roots must be proved.
		pub min: H,
		/// Hash of the last block that we can use when querying changes.
		pub max: H,
		/// Storage key which changes are requested.
		pub key: Vec<u8>,
	}

	#[derive(Debug, PartialEq, Eq, Clone, Encode, Decode)]
	/// Remote changes response.
	pub struct RemoteChangesResponse<N, H> {
		/// Id of a request this response was made for.
		pub id: RequestId,
		/// Proof has been generated using block with this number as a max block. Should be
		/// less than or equal to the RemoteChangesRequest::max block number.
		pub max: N,
		/// Changes proof.
		pub proof: Vec<Vec<u8>>,
		/// Changes tries roots missing on the requester' node.
		pub roots: Vec<(N, H)>,
		/// Missing changes tries roots proof.
		pub roots_proof: Vec<Vec<u8>>,
	}
}
