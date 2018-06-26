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

use primitives::AuthorityId;
use runtime_primitives::traits::{Block as BlockT, Header as HeaderT};
use runtime_primitives::generic::BlockId;
use runtime_primitives::bft::Justification;

use error::Result;

/// Blockchain database header backend. Does not perform any validation.
pub trait HeaderBackend<Block: BlockT>: Send + Sync {
	/// Get block header. Returns `None` if block is not found.
	fn header(&self, id: BlockId<Block>) -> Result<Option<<Block as BlockT>::Header>>;
	/// Get blockchain info.
	fn info(&self) -> Result<Info<Block>>;
	/// Get block status.
	fn status(&self, id: BlockId<Block>) -> Result<BlockStatus>;
	/// Get block hash by number. Returns `None` if the header is not in the chain.
	fn hash(&self, number: <<Block as BlockT>::Header as HeaderT>::Number) -> Result<Option<<<Block as BlockT>::Header as HeaderT>::Hash>>;
}

/// Blockchain database backend. Does not perform any validation.
pub trait Backend<Block: BlockT>: HeaderBackend<Block> {
	/// Get block body. Returns `None` if block is not found.
	fn body(&self, id: BlockId<Block>) -> Result<Option<Vec<<Block as BlockT>::Extrinsic>>>;
	/// Get block justification. Returns `None` if justification does not exist.
	fn justification(&self, id: BlockId<Block>) -> Result<Option<Justification<Block::Hash>>>;

	/// Returns data cache reference, if it is enabled on this backend.
	fn cache(&self) -> Option<&Cache<Block>>;
}

/// Blockchain optional data cache.
pub trait Cache<Block: BlockT>: Send + Sync {
	/// Returns the set of authorities, that was active at given block or None if there's no entry in the cache.
	fn authorities_at(&self, block: BlockId<Block>) -> Option<Vec<AuthorityId>>;
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
pub struct Info<Block: BlockT> {
	/// Best block hash.
	pub best_hash: <<Block as BlockT>::Header as HeaderT>::Hash,
	/// Best block number.
	pub best_number: <<Block as BlockT>::Header as HeaderT>::Number,
	/// Genesis block hash.
	pub genesis_hash: <<Block as BlockT>::Header as HeaderT>::Hash,
}

/// Block status.
#[derive(Debug, PartialEq, Eq)]
pub enum BlockStatus {
	/// Already in the blockchain.
	InChain,
	/// Not in the queue or the blockchain.
	Unknown,
}
