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

use primitives::block::{self, Id as BlockId};
use primitives::{self, AuthorityId};
use error::Result;

/// Blockchain database header backend. Does not perform any validation.
pub trait HeaderBackend: Send + Sync {
	/// Get block header. Returns `None` if block is not found.
	fn header(&self, id: BlockId) -> Result<Option<block::Header>>;
	/// Get blockchain info.
	fn info(&self) -> Result<Info>;
	/// Get block status.
	fn status(&self, id: BlockId) -> Result<BlockStatus>;
	/// Get block hash by number. Returns `None` if the header is not in the chain.
	fn hash(&self, number: block::Number) -> Result<Option<block::HeaderHash>>;
}

/// Blockchain database backend. Does not perform any validation.
pub trait Backend: HeaderBackend {
	/// Get block body. Returns `None` if block is not found.
	fn body(&self, id: BlockId) -> Result<Option<block::Body>>;
	/// Get block justification. Returns `None` if justification does not exist.
	fn justification(&self, id: BlockId) -> Result<Option<primitives::bft::Justification>>;

	/// Returns data cache reference, if it is enabled on this backend.
	fn cache(&self) -> Option<&Cache>;
}

/// Blockchain optional data cache.
pub trait Cache: Send + Sync {
	/// Returns the code that was active at given block or None if there's no entry in the cache.
	fn code_at(&self, block: BlockId) -> Option<Vec<u8>>;
	/// Returns the set of authorities, that was active at given block or None if there's no entry in the cache.
	fn authorities_at(&self, block: BlockId) -> Option<Vec<AuthorityId>>;
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
