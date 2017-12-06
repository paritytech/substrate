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

use std::borrow::Borrow;
use primitives::parachain::Id as ParachainId;
use primitives::Address;
use primitives::block::{Number as BlockNumber, HeaderHash, Header, Body};
use service::Role as RoleFlags;

pub type RequestId = u64;
type Bytes = Vec<u8>;

type Signature = ::primitives::hash::H256; //TODO:

// Auxilary types

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Role {
	Full,
	Light,
	Validator,
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
pub enum BlockAttribute {
	Header,
	Body,
	Receipt,
	MessageQueue,
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BlockData {
	pub hash: HeaderHash,
	pub header: Option<Header>,
	pub body: Option<Body>,
	pub receipt: Option<Bytes>,
	pub message: Option<Bytes>,
}

#[serde(untagged)]
#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize)]
pub enum FromBlock {
	Hash(HeaderHash),
	Number(BlockNumber),
}

#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize)]
pub enum Direction {
	Ascending,
	Descending,
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Message {
	Status(Status),
	BlockRequest(BlockRequest),
	BlockResponse(BlockResponse),
	BlockAnnounce(BlockAnnounce),
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Status {
	pub version: u32,
	pub roles: Vec<Role>,
	pub best_number: BlockNumber,
	pub best_hash: HeaderHash,
	pub genesis_hash: HeaderHash,
	pub validator_signature: Option<Signature>,
	pub validator_id: Option<Address>,
	pub parachain_id: Option<ParachainId>,
}

#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize)]
pub struct BlockRequest {
	pub id: RequestId,
	pub fields: Vec<BlockAttribute>,
	pub from: FromBlock,
	pub to: Option<HeaderHash>,
	pub direction: Option<Direction>,
	pub max: Option<u32>,
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BlockResponse {
	pub id: RequestId,
	pub blocks: Vec<BlockData>,
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BlockAnnounce {
	pub header: Header,
}
