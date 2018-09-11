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

//! Blockchain access trait

use client::{self, Client as SubstrateClient, ImportResult, ClientInfo, BlockStatus,
		BlockOrigin, CallExecutor};
use client::error::Error;
use runtime_primitives::traits::{Block as BlockT, Chain as ChainT,
		Consensus as ConsensusT, Header as HeaderT};
use runtime_primitives::generic::BlockId;
use runtime_primitives::bft::Justification;
use primitives::{Blake2Hasher, RlpCodec};

/// Local client abstraction for the network.
pub trait Client<C: Chain>: Send + Sync {
	/// Import a new block. Parent is supposed to be existing in the blockchain.
	fn import(&self,
		origin: BlockOrigin,
		header: <C::Block as BlockT>::Header,
		justification: C,
		body: Option<Vec<<C::Block as BlockT>::Extrinsic>>)
	-> Result<ImportResult, Error>;

	/// Get blockchain info.
	fn info(&self) -> Result<ClientInfo<C::Block>, Error>;

	/// Get block status.
	fn block_status(&self, id: &BlockId<C::Block>) -> Result<BlockStatus, Error>;

	/// Get block hash by number.
	fn block_hash(&self, block_number: <<C::Block as BlockT>::Header as HeaderT>::Number)
		-> Result<Option<<C::Block as BlockT>::Hash>, Error>;

	/// Get block header.
	fn header(&self, id: &BlockId<C::Block>)
		-> Result<Option<<C::Block as BlockT>::Header>, Error>;

	/// Get block body.
	fn body(&self, id: &BlockId<C::Block>)
		-> Result<Option<Vec<<C::Block as BlockT>::Extrinsic>>, Error>;

	/// Get block justification.
	fn justification(&self, id: &BlockId<C::Block>) -> Result<Option<<C::Consensus as ConsensusT>::Signature>, Error>;

	/// Get block header proof.
	fn header_proof(&self, block_number: <<C::Block as BlockT>::Header as HeaderT>::Number)
		-> Result<(<C::Block as BlockT>::Header, Vec<Vec<u8>>), Error>;

	/// Get storage read execution proof.
	fn read_proof(&self, block: &<C::Block as BlockT>::Hash, key: &[u8])
		-> Result<Vec<Vec<u8>>, Error>;

	/// Get method execution proof.
	fn execution_proof(&self, block: &<C::Block as BlockT>::Hash, method: &str, data: &[u8])
		-> Result<(Vec<u8>, Vec<Vec<u8>>), Error>;
}

impl<B, E, C> Client<C> for SubstrateClient<B, E, C> where
	C: Chain,
	B: client::backend::Backend<C, Blake2Hasher, RlpCodec> + Send + Sync + 'static,
	E: CallExecutor<C::Block, Blake2Hasher, RlpCodec> + Send + Sync + 'static,
{
	fn import(&self,
		origin: BlockOrigin,
		header: <C::Block as BlockT>::Header,
		justification: C,
		body: Option<Vec<<C::Block as BlockT>::Extrinsic>>
	) -> Result<ImportResult, Error> {
		// TODO: defer justification check.
		let justified_header = self.check_justification(header, justification.into())?;
		(self as &SubstrateClient<B, E, C>).import_block(origin, justified_header, body)
	}

	fn info(&self) -> Result<ClientInfo<C::Block>, Error> {
		(self as &SubstrateClient<B, E, C>).info()
	}

	fn block_status(&self, id: &BlockId<C::Block>) -> Result<BlockStatus, Error> {
		(self as &SubstrateClient<B, E, C>).block_status(id)
	}

	fn block_hash(&self, block_number: <<C::Block as BlockT>::Header as HeaderT>::Number)
		-> Result<Option<<C::Block as BlockT>::Hash>, Error>
	{
		(self as &SubstrateClient<B, E, C>).block_hash(block_number)
	}

	fn header(&self, id: &BlockId<C::Block>)
		-> Result<Option<<C::Block as BlockT>::Header>, Error>
	{
		(self as &SubstrateClient<B, E, C>).header(id)
	}

	fn body(&self, id: &BlockId<C::Block>)
		-> Result<Option<Vec<<C::Block as BlockT>::Extrinsic>>, Error>
	{
		(self as &SubstrateClient<B, E, C>).body(id)
	}

	fn justification(&self, id: &BlockId<C::Block>) -> Result<Option<<C::Consensus as ConsensusT>::Signature>, Error> {
		(self as &SubstrateClient<B, E, C>).justification(id)
	}

	fn header_proof(&self, block_number: <<C::Block as BlockT>::Header as HeaderT>::Number)
		-> Result<(<C::Block as BlockT>::Header, Vec<Vec<u8>>), Error>
	{
		(self as &SubstrateClient<B, E, C>).header_proof(&BlockId::Number(block_number))
	}

	fn read_proof(&self, block: &<C::Block as BlockT>::Hash, key: &[u8])
		-> Result<Vec<Vec<u8>>, Error>
	{
		(self as &SubstrateClient<B, E, C>).read_proof(&BlockId::Hash(block.clone()), key)
	}

	fn execution_proof(&self, block: &<C::Block as BlockT>::Hash, method: &str, data: &[u8])
	-> Result<(Vec<u8>, Vec<Vec<u8>>), Error>
	{
		(self as &SubstrateClient<B, E, C>)
			.execution_proof(&BlockId::Hash(block.clone()), method, data)
	}
}
