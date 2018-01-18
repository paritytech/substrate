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

//! Blockchain access trait

use client::{self, Client as PolkadotClient, ImportResult, ClientInfo, BlockStatus};
use client::error::Error;
use state_machine;
use primitives::block;

pub trait Client : Send + Sync {
	/// Given a hash return a header
	fn import(&self, header: block::Header, body: Option<block::Body>) -> Result<ImportResult, Error>;

	/// Get blockchain info.
	fn info(&self) -> Result<ClientInfo, Error>;

	/// Get block status.
	fn block_status(&self, hash: &block::HeaderHash) -> Result<BlockStatus, Error>;

	/// Get block hash by number.
	fn block_hash(&self, block_number: block::Number) -> Result<Option<block::HeaderHash>, Error>;
}

impl<B, E> Client for PolkadotClient<B, E> where
	B: client::backend::Backend + Send + Sync + 'static,
	E: state_machine::CodeExecutor + Send + Sync + 'static,
{
	fn import(&self, header: block::Header, body: Option<block::Body>) -> Result<ImportResult, Error> {
		(self as &Client).import(header, body)
	}

	fn info(&self) -> Result<ClientInfo, Error> {
		(self as &Client).info()
	}

	fn block_status(&self, hash: &block::HeaderHash) -> Result<BlockStatus, Error> {
		(self as &Client).block_status(hash)
	}

	fn block_hash(&self, block_number: block::Number) -> Result<Option<block::HeaderHash>, Error> {
		(self as &Client).block_hash(block_number)
	}
}


