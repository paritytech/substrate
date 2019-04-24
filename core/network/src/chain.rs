// Copyright 2017-2019 Parity Technologies (UK) Ltd
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//! Blockchain access trait

use client::{self, Client as SubstrateClient, ClientInfo, BlockStatus, CallExecutor};
use client::error::Error;
use client::light::fetcher::ChangesProof;
use consensus::{BlockImport, Error as ConsensusError};
use runtime_primitives::traits::{Block as BlockT, Header as HeaderT};
use runtime_primitives::generic::{BlockId};
use runtime_primitives::Justification;
use primitives::{H256, Blake2Hasher, storage::StorageKey};

/// Local client abstraction for the network.
pub trait Client<Block: BlockT>: Send + Sync {
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
	fn justification(&self, id: &BlockId<Block>) -> Result<Option<Justification>, Error>;

	/// Get block header proof.
	fn header_proof(&self, block_number: <Block::Header as HeaderT>::Number) -> Result<(Block::Header, Vec<Vec<u8>>), Error>;

	/// Get storage read execution proof.
	fn read_proof(&self, block: &Block::Hash, key: &[u8]) -> Result<Vec<Vec<u8>>, Error>;

	/// Get method execution proof.
	fn execution_proof(&self, block: &Block::Hash, method: &str, data: &[u8]) -> Result<(Vec<u8>, Vec<Vec<u8>>), Error>;

	/// Get key changes proof.
	fn key_changes_proof(
		&self,
		first: Block::Hash,
		last: Block::Hash,
		min: Block::Hash,
		max: Block::Hash,
		key: &StorageKey
	) -> Result<ChangesProof<Block::Header>, Error>;

	/// Returns `true` if the given `block` is a descendent of `base`.
	fn is_descendent_of(&self, base: &Block::Hash, block: &Block::Hash) -> Result<bool, Error>;
}

impl<B, E, Block, RA> Client<Block> for SubstrateClient<B, E, Block, RA> where
	B: client::backend::Backend<Block, Blake2Hasher> + Send + Sync + 'static,
	E: CallExecutor<Block, Blake2Hasher> + Send + Sync + 'static,
	Self: BlockImport<Block, Error=ConsensusError>,
	Block: BlockT<Hash=H256>,
	RA: Send + Sync
{
	fn info(&self) -> Result<ClientInfo<Block>, Error> {
		(self as &SubstrateClient<B, E, Block, RA>).info()
	}

	fn block_status(&self, id: &BlockId<Block>) -> Result<BlockStatus, Error> {
		(self as &SubstrateClient<B, E, Block, RA>).block_status(id)
	}

	fn block_hash(&self, block_number: <Block::Header as HeaderT>::Number) -> Result<Option<Block::Hash>, Error> {
		(self as &SubstrateClient<B, E, Block, RA>).block_hash(block_number)
	}

	fn header(&self, id: &BlockId<Block>) -> Result<Option<Block::Header>, Error> {
		(self as &SubstrateClient<B, E, Block, RA>).header(id)
	}

	fn body(&self, id: &BlockId<Block>) -> Result<Option<Vec<Block::Extrinsic>>, Error> {
		(self as &SubstrateClient<B, E, Block, RA>).body(id)
	}

	fn justification(&self, id: &BlockId<Block>) -> Result<Option<Justification>, Error> {
		(self as &SubstrateClient<B, E, Block, RA>).justification(id)
	}

	fn header_proof(&self, block_number: <Block::Header as HeaderT>::Number) -> Result<(Block::Header, Vec<Vec<u8>>), Error> {
		(self as &SubstrateClient<B, E, Block, RA>).header_proof(&BlockId::Number(block_number))
	}

	fn read_proof(&self, block: &Block::Hash, key: &[u8]) -> Result<Vec<Vec<u8>>, Error> {
		(self as &SubstrateClient<B, E, Block, RA>).read_proof(&BlockId::Hash(block.clone()), key)
	}

	fn execution_proof(&self, block: &Block::Hash, method: &str, data: &[u8]) -> Result<(Vec<u8>, Vec<Vec<u8>>), Error> {
		(self as &SubstrateClient<B, E, Block, RA>).execution_proof(&BlockId::Hash(block.clone()), method, data)
	}

	fn key_changes_proof(
		&self,
		first: Block::Hash,
		last: Block::Hash,
		min: Block::Hash,
		max: Block::Hash,
		key: &StorageKey
	) -> Result<ChangesProof<Block::Header>, Error> {
		(self as &SubstrateClient<B, E, Block, RA>).key_changes_proof(first, last, min, max, key)
	}

	fn is_descendent_of(&self, base: &Block::Hash, block: &Block::Hash) -> Result<bool, Error> {
		if base == block {
			return Ok(false);
		}

		let tree_route = ::client::blockchain::tree_route(
			self.backend().blockchain(),
			BlockId::Hash(*block),
			BlockId::Hash(*base),
		)?;

		Ok(tree_route.common_block().hash == *base)
	}
}
