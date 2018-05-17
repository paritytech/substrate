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

use runtime_primitives::traits::Block as BlockT;
use runtime_primitives::generic::BlockId;
use primitives::bft::Justification;

use error::Result;

/// Blockchain database backend. Does not perform any validation.
pub trait Backend: Send + Sync {
	type Block: BlockT;

	/// Get block header. Returns `None` if block is not found.
	fn header(&self, id: BlockId<Self::Block>) -> Result<Option<Self::Block::Header>>;
	/// Get block body. Returns `None` if block is not found.
	fn body(&self, id: BlockId<Self::Block>) -> Result<Option<Vec<Self::Block::Extrinsic>>>;
	/// Get block justification. Returns `None` if justification does not exist.
	fn justification(&self, id: BlockId<Self::Block>) -> Result<Option<Justification>>;
	/// Get blockchain info.
	fn info(&self) -> Result<Info<Self::Block>>;
	/// Get block status.
	fn status(&self, id: BlockId<Self::Block>) -> Result<BlockStatus>;
	/// Get block hash by number. Returns `None` if the header is not in the chain.
	fn hash(&self, number: Self::Block::Header::Number) -> Result<Option<Self::Block::Header::Hash>>;
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
pub struct Info<Hash, Number> {
	/// Best block hash.
	pub best_hash: Hash,
	/// Best block number.
	pub best_number: Number,
	/// Genesis block hash.
	pub genesis_hash: HeaderHash,
}

/// Block status.
#[derive(Debug, PartialEq, Eq)]
pub enum BlockStatus {
	/// Already in the blockchain.
	InChain,
	/// Not in the queue or the blockchain.
	Unknown,
}
