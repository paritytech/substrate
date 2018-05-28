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

use client::{self, Client as PolkadotClient, ImportResult, ClientInfo, BlockStatus, BlockOrigin, CallExecutor};
use client::error::Error;
use state_machine;
use primitives::block::{self, Id as BlockId};
use primitives::bft::Justification;

pub trait Client: Send + Sync {
	/// Import a new block. Parent is supposed to be existing in the blockchain.
	fn import(&self, is_best: bool, header: block::Header, justification: Justification, body: Option<block::Body>) -> Result<ImportResult, Error>;

	/// Get blockchain info.
	fn info(&self) -> Result<ClientInfo, Error>;

	/// Get block status.
	fn block_status(&self, id: &BlockId) -> Result<BlockStatus, Error>;

	/// Get block hash by number.
	fn block_hash(&self, block_number: block::Number) -> Result<Option<block::HeaderHash>, Error>;

	/// Get block header.
	fn header(&self, id: &BlockId) -> Result<Option<block::Header>, Error>;

	/// Get block body.
	fn body(&self, id: &BlockId) -> Result<Option<block::Body>, Error>;

	/// Get block justification.
	fn justification(&self, id: &BlockId) -> Result<Option<Justification>, Error>;

	/// Get method execution proof.
	fn execution_proof(&self, block: &block::HeaderHash, method: &str, data: &[u8]) -> Result<(Vec<u8>, Vec<Vec<u8>>), Error>;
}

impl<B, E> Client for PolkadotClient<B, E> where
	B: client::backend::Backend + Send + Sync + 'static,
	E: CallExecutor + Send + Sync + 'static,
	Error: From<<<B as client::backend::Backend>::State as state_machine::backend::Backend>::Error>, {

	fn import(&self, is_best: bool, header: block::Header, justification: Justification, body: Option<block::Body>) -> Result<ImportResult, Error> {
		// TODO: defer justification check.
		let justified_header = self.check_justification(header, justification.into())?;
		let origin = if is_best { BlockOrigin::NetworkBroadcast } else { BlockOrigin::NetworkInitialSync };
		(self as &PolkadotClient<B, E>).import_block(origin, justified_header, body)
	}

	fn info(&self) -> Result<ClientInfo, Error> {
		(self as &PolkadotClient<B, E>).info()
	}

	fn block_status(&self, id: &BlockId) -> Result<BlockStatus, Error> {
		(self as &PolkadotClient<B, E>).block_status(id)
	}

	fn block_hash(&self, block_number: block::Number) -> Result<Option<block::HeaderHash>, Error> {
		(self as &PolkadotClient<B, E>).block_hash(block_number)
	}

	fn header(&self, id: &BlockId) -> Result<Option<block::Header>, Error> {
		(self as &PolkadotClient<B, E>).header(id)
	}

	fn body(&self, id: &BlockId) -> Result<Option<block::Body>, Error> {
		(self as &PolkadotClient<B, E>).body(id)
	}

	fn justification(&self, id: &BlockId) -> Result<Option<Justification>, Error> {
		(self as &PolkadotClient<B, E>).justification(id)
	}

	fn execution_proof(&self, block: &block::HeaderHash, method: &str, data: &[u8]) -> Result<(Vec<u8>, Vec<Vec<u8>>), Error> {
		(self as &PolkadotClient<B, E>).execution_proof(&BlockId::Hash(block.clone()), method, data)
	}
}
