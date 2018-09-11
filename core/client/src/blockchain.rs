// Copyright 2017 Parity Technologies (UK) Ltd.
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

//! Polkadot blockchain trait

use primitives::AuthorityId;
use runtime_primitives::traits::{Block as BlockT, Chain, Header as HeaderT, 
	Consensus as ConsensusT, NumberFor};
use runtime_primitives::generic::BlockId;

use error::{ErrorKind, Result};

/// Blockchain database header backend. Does not perform any validation.
pub trait HeaderBackend<Ch: Chain>: Send + Sync {
	/// Get block header. Returns `None` if block is not found.
	fn header(&self, id: BlockId<Ch::Block>) -> Result<Option<<Ch::Block as BlockT>::Header>>;
	/// Get blockchain info.
	fn info(&self) -> Result<Info<Ch::Block>>;
	/// Get block status.
	fn status(&self, id: BlockId<Ch::Block>) -> Result<BlockStatus>;
	/// Get block number by hash. Returns `None` if the header is not in the chain.
	fn number(&self, hash: <Ch::Block as BlockT>::Hash) -> Result<Option<<<Ch::Block as BlockT>::Header as HeaderT>::Number>>;
	/// Get block hash by number. Returns `None` if the header is not in the chain.
	fn hash(&self, number: NumberFor<Ch::Block>) -> Result<Option<<Ch::Block as BlockT>::Hash>>;

	/// Get block header. Returns `UnknownBlock` error if block is not found.
	fn expect_header(&self, id: BlockId<Ch::Block>) -> Result<<Ch::Block as BlockT>::Header> {
		self.header(id)?.ok_or_else(|| ErrorKind::UnknownBlock(format!("{}", id)).into())
	}
}

/// Blockchain database backend. Does not perform any validation.
pub trait Backend<Ch: Chain>: HeaderBackend<Ch> {
	/// Get block body. Returns `None` if block is not found.
	fn body(&self, id: BlockId<Ch::Block>) -> Result<Option<Vec<<Ch::Block as BlockT>::Extrinsic>>>;
	/// Get block justification. Returns `None` if justification does not exist.
	fn justification(&self, id: BlockId<Ch::Block>) -> Result<Option<<Ch::Consensus as ConsensusT>::Signature>>;

	/// Returns data cache reference, if it is enabled on this backend.
	fn cache(&self) -> Option<&Cache<Ch::Block>>;
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
