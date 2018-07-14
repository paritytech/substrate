// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

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

//! Blockchain access trait

use client::{self, Client as SubstrateClient, ImportResult, ClientInfo, BlockStatus, BlockOrigin, CallExecutor};
use client::error::Error;
use runtime_primitives::traits::{Block as BlockT, Header as HeaderT};
use runtime_primitives::generic::BlockId;
use runtime_primitives::bft::Justification;

/// Local client abstraction for the network.
pub trait Client<Block: BlockT>: Send + Sync {
	/// Import a new block. Parent is supposed to be existing in the blockchain.
	fn import(&self, is_best: bool, header: Block::Header, justification: Justification<Block::Hash>, body: Option<Vec<Block::Extrinsic>>) -> Result<ImportResult, Error>;

	/// Get blockchain info.
	fn info(&self) -> Result<ClientInfo<Block>, Error>;

	/// Get block status.
	fn block_status(&self, id: &BlockId<Block>) -> Result<BlockStatus, Error>;

	/// Get block hash by number.
	fn block_hash(&self, block_number: <Block::Header as HeaderT>::Number) -> Result<Option<Block::Hash>, Error>;

	/// Get block header.
	fn header(&self, id: &BlockId<Block>) -> Result<Option<Block::Header>, Error>;

	/// Get block body.
	fn body(&self, id: &BlockId<Block>) -> Result<Option<Vec<Block::Extrinsic>>, Error>;

	/// Get block justification.
	fn justification(&self, id: &BlockId<Block>) -> Result<Option<Justification<Block::Hash>>, Error>;

	/// Get method execution proof.
	fn execution_proof(&self, block: &Block::Hash, method: &str, data: &[u8]) -> Result<(Vec<u8>, Vec<Vec<u8>>), Error>;
}

impl<B, E, Block> Client<Block> for SubstrateClient<B, E, Block> where
	B: client::backend::Backend<Block> + Send + Sync + 'static,
	E: CallExecutor<Block> + Send + Sync + 'static,
	Block: BlockT,
{
	fn import(&self, is_best: bool, header: Block::Header, justification: Justification<Block::Hash>, body: Option<Vec<Block::Extrinsic>>) -> Result<ImportResult, Error> {
		// TODO: defer justification check.
		let justified_header = self.check_justification(header, justification.into())?;
		let origin = if is_best { BlockOrigin::NetworkBroadcast } else { BlockOrigin::NetworkInitialSync };
		(self as &SubstrateClient<B, E, Block>).import_block(origin, justified_header, body)
	}

	fn info(&self) -> Result<ClientInfo<Block>, Error> {
		(self as &SubstrateClient<B, E, Block>).info()
	}

	fn block_status(&self, id: &BlockId<Block>) -> Result<BlockStatus, Error> {
		(self as &SubstrateClient<B, E, Block>).block_status(id)
	}

	fn block_hash(&self, block_number: <Block::Header as HeaderT>::Number) -> Result<Option<Block::Hash>, Error> {
		(self as &SubstrateClient<B, E, Block>).block_hash(block_number)
	}

	fn header(&self, id: &BlockId<Block>) -> Result<Option<Block::Header>, Error> {
		(self as &SubstrateClient<B, E, Block>).header(id)
	}

	fn body(&self, id: &BlockId<Block>) -> Result<Option<Vec<Block::Extrinsic>>, Error> {
		(self as &SubstrateClient<B, E, Block>).body(id)
	}

	fn justification(&self, id: &BlockId<Block>) -> Result<Option<Justification<Block::Hash>>, Error> {
		(self as &SubstrateClient<B, E, Block>).justification(id)
	}

	fn execution_proof(&self, block: &Block::Hash, method: &str, data: &[u8]) -> Result<(Vec<u8>, Vec<Vec<u8>>), Error> {
		(self as &SubstrateClient<B, E, Block>).execution_proof(&BlockId::Hash(block.clone()), method, data)
	}
}
