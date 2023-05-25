// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Generic implementation of a block and associated items.

#[cfg(feature = "std")]
use std::fmt;

#[cfg(feature = "std")]
use serde::{Deserialize, Serialize};

use crate::{
	codec::{Codec, Decode, Encode},
	traits::{self, Block as BlockT, Header as HeaderT, MaybeSerialize, Member, NumberFor},
	Justifications,
};
use sp_core::RuntimeDebug;
use sp_std::prelude::*;

/// Something to identify a block.
#[derive(PartialEq, Eq, Clone, Encode, Decode, RuntimeDebug)]
pub enum BlockId<Block: BlockT> {
	/// Identify by block header hash.
	Hash(Block::Hash),
	/// Identify by block number.
	Number(NumberFor<Block>),
}

impl<Block: BlockT> BlockId<Block> {
	/// Create a block ID from a hash.
	pub const fn hash(hash: Block::Hash) -> Self {
		BlockId::Hash(hash)
	}

	/// Create a block ID from a number.
	pub const fn number(number: NumberFor<Block>) -> Self {
		BlockId::Number(number)
	}

	/// Check if this block ID refers to the pre-genesis state.
	pub fn is_pre_genesis(&self) -> bool {
		match self {
			BlockId::Hash(hash) => hash == &Default::default(),
			BlockId::Number(_) => false,
		}
	}

	/// Create a block ID for a pre-genesis state.
	pub fn pre_genesis() -> Self {
		BlockId::Hash(Default::default())
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
#[derive(PartialEq, Eq, Clone, Encode, Decode, RuntimeDebug, scale_info::TypeInfo)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
#[cfg_attr(feature = "std", serde(rename_all = "camelCase"))]
#[cfg_attr(feature = "std", serde(deny_unknown_fields))]
pub struct Block<Header, Extrinsic: MaybeSerialize> {
	/// The block header.
	pub header: Header,
	/// The accompanying extrinsics.
	pub extrinsics: Vec<Extrinsic>,
}

impl<Header, Extrinsic: MaybeSerialize> traits::Block for Block<Header, Extrinsic>
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
	fn encode_from(header: &Self::Header, extrinsics: &[Self::Extrinsic]) -> Vec<u8> {
		(header, extrinsics).encode()
	}
}

/// Abstraction over a substrate block and justification.
#[derive(PartialEq, Eq, Clone, Encode, Decode, RuntimeDebug)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
#[cfg_attr(feature = "std", serde(rename_all = "camelCase"))]
#[cfg_attr(feature = "std", serde(deny_unknown_fields))]
pub struct SignedBlock<Block> {
	/// Full block.
	pub block: Block,
	/// Block justification.
	pub justifications: Option<Justifications>,
}
