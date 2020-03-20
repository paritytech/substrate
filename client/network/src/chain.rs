// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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

use sc_client::Client as SubstrateClient;
use sp_blockchain::{Error, Info as BlockchainInfo};
use sc_client_api::{ChangesProof, StorageProof, CallExecutor};
use sp_consensus::{BlockImport, BlockStatus, Error as ConsensusError};
use sp_runtime::traits::{Block as BlockT, Header as HeaderT, NumberFor};
use sp_runtime::generic::{BlockId};
use sp_runtime::Justification;
use sp_core::storage::{StorageKey, ChildInfo};

/// Local client abstraction for the network.
pub trait Client<Block: BlockT>: Send + Sync {
	/// Get blockchain info.
	fn info(&self) -> BlockchainInfo<Block>;

	/// Get block status.
	fn block_status(&self, id: &BlockId<Block>) -> Result<BlockStatus, Error>;

	/// Get block hash by number.
	fn block_hash(&self, block_number: NumberFor<Block>) -> Result<Option<Block::Hash>, Error>;

	/// Get block header.
	fn header(&self, id: &BlockId<Block>) -> Result<Option<Block::Header>, Error>;

	/// Get block body.
	fn body(&self, id: &BlockId<Block>) -> Result<Option<Vec<Block::Extrinsic>>, Error>;

	/// Get block justification.
	fn justification(&self, id: &BlockId<Block>) -> Result<Option<Justification>, Error>;

	/// Get block header proof.
	fn header_proof(&self, block_number: NumberFor<Block>)
		-> Result<(Block::Header, StorageProof), Error>;

	/// Get storage read execution proof.
	fn read_proof(&self, block: &Block::Hash, keys: &[Vec<u8>]) -> Result<StorageProof, Error>;

	/// Get child storage read execution proof.
	fn read_child_proof(
		&self,
		block: &Block::Hash,
		storage_key: &[u8],
		child_info: ChildInfo,
		keys: &[Vec<u8>],
	) -> Result<StorageProof, Error>;

	/// Get method execution proof.
	fn execution_proof(
		&self,
		block: &Block::Hash,
		method: &str,
		data: &[u8],
	) -> Result<(Vec<u8>, StorageProof), Error>;

	/// Get key changes proof.
	fn key_changes_proof(
		&self,
		first: Block::Hash,
		last: Block::Hash,
		min: Block::Hash,
		max: Block::Hash,
		storage_key: Option<&StorageKey>,
		key: &StorageKey
	) -> Result<ChangesProof<Block::Header>, Error>;

	/// Returns `true` if the given `block` is a descendent of `base`.
	fn is_descendent_of(&self, base: &Block::Hash, block: &Block::Hash) -> Result<bool, Error>;
}

/// Finality proof provider.
pub trait FinalityProofProvider<Block: BlockT>: Send + Sync {
	/// Prove finality of the block.
	fn prove_finality(&self, for_block: Block::Hash, request: &[u8]) -> Result<Option<Vec<u8>>, Error>;
}

impl<Block: BlockT> FinalityProofProvider<Block> for () {
	fn prove_finality(&self, _for_block: Block::Hash, _request: &[u8]) -> Result<Option<Vec<u8>>, Error> {
		Ok(None)
	}
}

impl<B, E, Block, RA> Client<Block> for SubstrateClient<B, E, Block, RA> where
	B: sc_client_api::backend::Backend<Block> + Send + Sync + 'static,
	E: CallExecutor<Block> + Send + Sync + 'static,
	Self: BlockImport<Block, Error=ConsensusError>,
	Block: BlockT,
	RA: Send + Sync
{
	fn info(&self) -> BlockchainInfo<Block> {
		(self as &SubstrateClient<B, E, Block, RA>).chain_info()
	}

	fn block_status(&self, id: &BlockId<Block>) -> Result<BlockStatus, Error> {
		(self as &SubstrateClient<B, E, Block, RA>).block_status(id)
	}

	fn block_hash(
		&self,
		block_number: <Block::Header as HeaderT>::Number,
	) -> Result<Option<Block::Hash>, Error> {
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

	fn header_proof(&self, block_number: <Block::Header as HeaderT>::Number)
		-> Result<(Block::Header, StorageProof), Error>
	{
		(self as &SubstrateClient<B, E, Block, RA>).header_proof(&BlockId::Number(block_number))
	}

	fn read_proof(&self, block: &Block::Hash, keys: &[Vec<u8>]) -> Result<StorageProof, Error> {
		(self as &SubstrateClient<B, E, Block, RA>).read_proof(&BlockId::Hash(block.clone()), keys)
	}

	fn read_child_proof(
		&self,
		block: &Block::Hash,
		storage_key: &[u8],
		child_info: ChildInfo,
		keys: &[Vec<u8>],
	) -> Result<StorageProof, Error> {
		(self as &SubstrateClient<B, E, Block, RA>)
			.read_child_proof(&BlockId::Hash(block.clone()), storage_key, child_info, keys)
	}

	fn execution_proof(
		&self,
		block: &Block::Hash,
		method: &str,
		data: &[u8],
	) -> Result<(Vec<u8>, StorageProof), Error> {
		SubstrateClient::execution_proof(self, &BlockId::Hash(block.clone()), method, data)
	}

	fn key_changes_proof(
		&self,
		first: Block::Hash,
		last: Block::Hash,
		min: Block::Hash,
		max: Block::Hash,
		storage_key: Option<&StorageKey>,
		key: &StorageKey,
	) -> Result<ChangesProof<Block::Header>, Error> {
		(self as &SubstrateClient<B, E, Block, RA>).key_changes_proof(
			first,
			last,
			min,
			max,
			storage_key,
			key,
		)
	}

	fn is_descendent_of(&self, base: &Block::Hash, block: &Block::Hash) -> Result<bool, Error> {
		if base == block {
			return Ok(false);
		}

		let ancestor = sp_blockchain::lowest_common_ancestor(self, *block, *base)?;

		Ok(ancestor.hash == *base)
	}
}
