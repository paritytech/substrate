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

use std;
use primitives::block;

/// Blockchain access
pub trait Blockchain : Send + Sync {
	/// Error Type
	type Error: std::error::Error + Send + 'static;

	/// Returns the hash of latest block.
	fn latest_hash(&self) -> Result<block::HeaderHash, Self::Error>;

	/// Given a hash return a header
	fn header(&self, hash: &block::HeaderHash) -> Result<Option<block::Header>, Self::Error>;

	/// Given a hash return a header
	fn import(&self, header: block::Header, body: Option<block::Body>) -> ImportResult<Self::Error>;

	/// Get blockchain info.
	fn info(&self) -> Result<ChainInfo, Self::Error>;

	/// Get block hash by number.
	fn hash(&self, block_number: block::Number) -> Result<Option<block::HeaderHash>, Self::Error>;
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
pub struct ChainInfo {
	/// Best block hash.
	pub best_hash: block::HeaderHash,
	/// Best block number.
	pub best_number: block::Number,
	/// Genesis block hash.
	pub genesis_hash: block::HeaderHash,
}

