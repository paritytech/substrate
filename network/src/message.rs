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
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.?

//! Network packet message types. These get serialized and put into the lower level protocol payload.

use std::borrow::Borrow;
use primitives::parachain::Id as ParachainId;
use primitives::Address;
use primitives::block::{Number as BlockNumber, HeaderHash, Header, Body};
use service::Role as RoleFlags;

pub type RequestId = u64;
type Bytes = Vec<u8>;

type Signature = ::primitives::hash::H256; //TODO:

/// Configured node role.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Role {
	/// Full relay chain client with no additional responsibilities.
	Full,
	/// Relay chain light client.
	Light,
	/// Parachain validator.
	Validator,
	/// Parachain collator.
	Collator,
}

impl<T> From<T> for RoleFlags where T: Borrow<[Role]> {
	fn from(roles: T) -> RoleFlags {
		let mut flags = RoleFlags::NONE;
		let roles: &[Role] = roles.borrow();
		for r in roles {
			match *r {
				Role::Full => flags = flags | RoleFlags::FULL,
				Role::Light => flags = flags | RoleFlags::LIGHT,
				Role::Validator => flags = flags | RoleFlags::VALIDATOR,
				Role::Collator => flags = flags | RoleFlags::COLLATOR,
			}
		}
		flags
	}
}

impl From<RoleFlags> for Vec<Role> where {
	fn from(flags: RoleFlags) -> Vec<Role> {
		let mut roles = Vec::new();
		if !(flags & RoleFlags::FULL).is_empty() {
			roles.push(Role::Full);
		}
		if !(flags & RoleFlags::LIGHT).is_empty() {
			roles.push(Role::Light);
		}
		if !(flags & RoleFlags::VALIDATOR).is_empty() {
			roles.push(Role::Validator);
		}
		if !(flags & RoleFlags::COLLATOR).is_empty() {
			roles.push(Role::Collator);
		}
		roles
	}
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize, Copy, Clone)]
/// Bits of block data and associated artefacts to request.
pub enum BlockAttribute {
	/// Include block header.
	Header,
	/// Include block body.
	Body,
	/// Include block receipt.
	Receipt,
	/// Include block message queue.
	MessageQueue,
}

#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize)]
/// Block data sent in the response.
pub struct BlockData {
	/// Block header hash.
	pub hash: HeaderHash,
	/// Block header if requested.
	pub header: Option<Header>,
	/// Block body if requested.
	pub body: Option<Body>,
	/// Block receipt if requested.
	pub receipt: Option<Bytes>,
	/// Block message queue if requested.
	pub message_queue: Option<Bytes>,
}

#[serde(untagged)]
#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize)]
/// Identifies starting point of a block sequence.
pub enum FromBlock {
	/// Start with given hash.
	Hash(HeaderHash),
	/// Start with given block number.
	Number(BlockNumber),
}

#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize)]
/// Block enumeration direction.
pub enum Direction {
	/// Enumerate in ascending order (from child to parent).
	Ascending,
	/// Enumerate in descendfing order (from parent to canonical child).
	Descending,
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
/// A network message.
pub enum Message {
	/// Status packet.
	Status(Status),
	/// Block request.
	BlockRequest(BlockRequest),
	/// Block response.
	BlockResponse(BlockResponse),
	/// Block announce.
	BlockAnnounce(BlockAnnounce),
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Status {
	/// Protocol version.
	pub version: u32,
	/// Supported roles.
	pub roles: Vec<Role>,
	/// Best block number.
	pub best_number: BlockNumber,
	/// Best block hash.
	pub best_hash: HeaderHash,
	/// Genesis block hash.
	pub genesis_hash: HeaderHash,
	/// Signatue of `best_hash` made with validator address. Required for the validator role.
	pub validator_signature: Option<Signature>,
	/// Validator address. Required for the validator role.
	pub validator_id: Option<Address>,
	/// Parachain id. Required for the collator role.
	pub parachain_id: Option<ParachainId>,
}

#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize)]
/// Request block data from a peer.
pub struct BlockRequest {
	/// Unique request id.
	pub id: RequestId,
	/// Bits of block data to request.
	pub fields: Vec<BlockAttribute>,
	/// Start from this block.
	pub from: FromBlock,
	/// End at this block. An implementation defined maximum is used when unspecified.
	pub to: Option<HeaderHash>,
	/// Sequence direction.
	pub direction: Direction,
	/// Maximum number of block to return. An implementation defined maximum is used when unspecified.
	pub max: Option<u32>,
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
/// Response to `BlockRequest`
pub struct BlockResponse {
	/// Id of a request this response was made for.
	pub id: RequestId,
	/// Block data for the requested sequence.
	pub blocks: Vec<BlockData>,
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
/// Announce a new complete relay chain block on the network.
pub struct BlockAnnounce {
	/// New block header.
	pub header: Header,
}
