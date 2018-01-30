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

//! Polkadot blockchain trait

use std::fmt::{Display, Formatter, Error as FmtError};
use primitives::block;
use error::Result;

/// Block indentification.
#[derive(Debug, Clone, Copy)]
pub enum BlockId {
	/// Identify by block header hash.
	Hash(block::HeaderHash),
	/// Identify by block number.
	Number(block::Number),
}

impl Display for BlockId {
	fn fmt(&self, f: &mut Formatter) -> ::std::result::Result<(), FmtError> {
		match *self {
			BlockId::Hash(h) => h.fmt(f),
			BlockId::Number(n) => n.fmt(f),
		}
	}
}

/// Blockchain database backend. Does not perform any validation.
pub trait Backend: Send + Sync {
	/// Get block header. Returns `None` if block is not found.
	fn header(&self, id: BlockId) -> Result<Option<block::Header>>;
	/// Get block body. Returns `None` if block is not found.
	fn body(&self, id: BlockId) -> Result<Option<block::Body>>;
	/// Get blockchain info.
	fn info(&self) -> Result<Info>;
	/// Get block status.
	fn status(&self, id: BlockId) -> Result<BlockStatus>;
	/// Get block hash by number. Returns `None` if the header is not in the chain.
	fn hash(&self, number: block::Number) -> Result<Option<block::HeaderHash>>;
}

/// Block import outcome
pub enum ImportResult<E> {
	/// Imported successfully.
	Imported,
	/// Block already exists, skippped.
	AlreadyInChain,
	/// Unknown parent.
	UnknownParent,
	/// Other errror.
	Err(E),
}

/// Blockchain info
#[derive(Debug)]
pub struct Info {
	/// Best block hash.
	pub best_hash: block::HeaderHash,
	/// Best block number.
	pub best_number: block::Number,
	/// Genesis block hash.
	pub genesis_hash: block::HeaderHash,
}

/// Block status.
#[derive(Debug, PartialEq, Eq)]
pub enum BlockStatus {
	/// Already in the blockchain.
	InChain,
	/// Not in the queue or the blockchain.
	Unknown,
}

