// Copyright 2018-2019 Parity Technologies (UK) Ltd.
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

//! Client extension for tests.

use client::{self, Client};
use client_api::backend::Finalizer;
use consensus::{
	BlockImportParams, BlockImport, BlockOrigin, Error as ConsensusError,
	ForkChoiceStrategy,
};
use hash_db::Hasher;
use sr_primitives::Justification;
use sr_primitives::traits::{Block as BlockT};
use sr_primitives::generic::BlockId;
use primitives::Blake2Hasher;
use codec::alloc::collections::hash_map::HashMap;

/// Extension trait for a test client.
pub trait ClientExt<Block: BlockT>: Sized {
	/// Import block to the chain. No finality.
	fn import(&self, origin: BlockOrigin, block: Block)
		-> Result<(), ConsensusError>;

	/// Import a block and make it our best block if possible.
	fn import_as_best(&self, origin: BlockOrigin, block: Block)
		-> Result<(), ConsensusError>;

	/// Import a block and finalize it.
	fn import_as_final(&self, origin: BlockOrigin, block: Block)
		-> Result<(), ConsensusError>;

	/// Import block with justification, finalizes block.
	fn import_justified(
		&self,
		origin: BlockOrigin,
		block: Block,
		justification: Justification
	) -> Result<(), ConsensusError>;

	/// Finalize a block.
	fn finalize_block(
		&self,
		id: BlockId<Block>,
		justification: Option<Justification>,
	) -> sp_blockchain::Result<()>;

	/// Returns hash of the genesis block.
	fn genesis_hash(&self) -> <Block as BlockT>::Hash;
}

impl<B, E, RA, Block> ClientExt<Block> for Client<B, E, Block, RA>
	where
		B: client_api::backend::Backend<Block, Blake2Hasher>,
		E: client::CallExecutor<Block, Blake2Hasher>,
		for<'r> &'r Self: BlockImport<Block, Error=ConsensusError>,
		Block: BlockT<Hash=<Blake2Hasher as Hasher>::Out>,
{
	fn import(&self, origin: BlockOrigin, block: Block)
		-> Result<(), ConsensusError>
	{
		let (header, extrinsics) = block.deconstruct();
		let import = BlockImportParams {
			origin,
			header,
			justification: None,
			post_digests: vec![],
			body: Some(extrinsics),
			finalized: false,
			auxiliary: Vec::new(),
			fork_choice: ForkChoiceStrategy::LongestChain,
			allow_missing_state: false,
		};

		BlockImport::import_block(&mut (&*self), import, HashMap::new()).map(|_| ())
	}

	fn import_as_best(&self, origin: BlockOrigin, block: Block)
		-> Result<(), ConsensusError>
	{
		let (header, extrinsics) = block.deconstruct();
		let import = BlockImportParams {
			origin,
			header,
			justification: None,
			post_digests: vec![],
			body: Some(extrinsics),
			finalized: false,
			auxiliary: Vec::new(),
			fork_choice: ForkChoiceStrategy::Custom(true),
			allow_missing_state: false,
		};

		BlockImport::import_block(&mut (&*self), import, HashMap::new()).map(|_| ())
	}

	fn import_as_final(&self, origin: BlockOrigin, block: Block)
		-> Result<(), ConsensusError>
	{
		let (header, extrinsics) = block.deconstruct();
		let import = BlockImportParams {
			origin,
			header,
			justification: None,
			post_digests: vec![],
			body: Some(extrinsics),
			finalized: true,
			auxiliary: Vec::new(),
			fork_choice: ForkChoiceStrategy::Custom(true),
			allow_missing_state: false,
		};

		BlockImport::import_block(&mut (&*self), import, HashMap::new()).map(|_| ())
	}

	fn import_justified(
		&self,
		origin: BlockOrigin,
		block: Block,
		justification: Justification,
	) -> Result<(), ConsensusError> {
		let (header, extrinsics) = block.deconstruct();
		let import = BlockImportParams {
			origin,
			header,
			justification: Some(justification),
			post_digests: vec![],
			body: Some(extrinsics),
			finalized: true,
			auxiliary: Vec::new(),
			fork_choice: ForkChoiceStrategy::LongestChain,
			allow_missing_state: false,
		};

		BlockImport::import_block(&mut (&*self), import, HashMap::new()).map(|_| ())
	}

	fn finalize_block(
		&self,
		id: BlockId<Block>,
		justification: Option<Justification>,
	) -> sp_blockchain::Result<()> {
		Finalizer::finalize_block(self, id, justification, true)
	}

	fn genesis_hash(&self) -> <Block as BlockT>::Hash {
		self.block_hash(0.into()).unwrap().unwrap()
	}
}
