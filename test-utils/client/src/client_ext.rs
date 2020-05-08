// Copyright 2018-2020 Parity Technologies (UK) Ltd.
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

use sc_service::client::Client;
use sc_client_api::backend::Finalizer;
use sp_consensus::{
	BlockImportParams, BlockImport, BlockOrigin, Error as ConsensusError,
	ForkChoiceStrategy,
};
use sp_runtime::Justification;
use sp_runtime::traits::{Block as BlockT};
use sp_runtime::generic::BlockId;
use codec::alloc::collections::hash_map::HashMap;

/// Extension trait for a test client.
pub trait ClientExt<Block: BlockT>: Sized {
	/// Finalize a block.
	fn finalize_block(
		&self,
		id: BlockId<Block>,
		justification: Option<Justification>,
	) -> sp_blockchain::Result<()>;

	/// Returns hash of the genesis block.
	fn genesis_hash(&self) -> <Block as BlockT>::Hash;
}

/// Extension trait for a test client around block importing.
pub trait ClientBlockImportExt<Block: BlockT>: Sized {
	/// Import block to the chain. No finality.
	fn import(&mut self, origin: BlockOrigin, block: Block) -> Result<(), ConsensusError>;

	/// Import a block and make it our best block if possible.
	fn import_as_best(&mut self, origin: BlockOrigin, block: Block) -> Result<(), ConsensusError>;

	/// Import a block and finalize it.
	fn import_as_final(&mut self, origin: BlockOrigin, block: Block)
		-> Result<(), ConsensusError>;

	/// Import block with justification, finalizes block.
	fn import_justified(
		&mut self,
		origin: BlockOrigin,
		block: Block,
		justification: Justification
	) -> Result<(), ConsensusError>;
}

impl<B, E, RA, Block> ClientExt<Block> for Client<B, E, Block, RA>
	where
		B: sc_client_api::backend::Backend<Block>,
		E: sc_client_api::CallExecutor<Block> + 'static,
		Self: BlockImport<Block, Error = ConsensusError>,
		Block: BlockT,
{
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

/// This implementation is required, because of the weird api requirements around `BlockImport`.
impl<Block: BlockT, T, Transaction> ClientBlockImportExt<Block> for std::sync::Arc<T>
	where for<'r> &'r T: BlockImport<Block, Error = ConsensusError, Transaction = Transaction>
{
	fn import(&mut self, origin: BlockOrigin, block: Block) -> Result<(), ConsensusError> {
		let (header, extrinsics) = block.deconstruct();
		let mut import = BlockImportParams::new(origin, header);
		import.body = Some(extrinsics);
		import.fork_choice = Some(ForkChoiceStrategy::LongestChain);

		BlockImport::import_block(self, import, HashMap::new()).map(|_| ())
	}

	fn import_as_best(&mut self, origin: BlockOrigin, block: Block) -> Result<(), ConsensusError> {
		let (header, extrinsics) = block.deconstruct();
		let mut import = BlockImportParams::new(origin, header);
		import.body = Some(extrinsics);
		import.fork_choice = Some(ForkChoiceStrategy::Custom(true));

		BlockImport::import_block(self, import, HashMap::new()).map(|_| ())
	}

	fn import_as_final(&mut self, origin: BlockOrigin, block: Block) -> Result<(), ConsensusError> {
		let (header, extrinsics) = block.deconstruct();
		let mut import = BlockImportParams::new(origin, header);
		import.body = Some(extrinsics);
		import.finalized = true;
		import.fork_choice = Some(ForkChoiceStrategy::Custom(true));

		BlockImport::import_block(self, import, HashMap::new()).map(|_| ())
	}

	fn import_justified(
		&mut self,
		origin: BlockOrigin,
		block: Block,
		justification: Justification,
	) -> Result<(), ConsensusError> {
		let (header, extrinsics) = block.deconstruct();
		let mut import = BlockImportParams::new(origin, header);
		import.justification = Some(justification);
		import.body = Some(extrinsics);
		import.finalized = true;
		import.fork_choice = Some(ForkChoiceStrategy::LongestChain);

		BlockImport::import_block(self, import, HashMap::new()).map(|_| ())
	}
}

impl<B, E, RA, Block: BlockT> ClientBlockImportExt<Block> for Client<B, E, Block, RA>
	where
		Self: BlockImport<Block, Error = ConsensusError>,
{
	fn import(&mut self, origin: BlockOrigin, block: Block) -> Result<(), ConsensusError> {
		let (header, extrinsics) = block.deconstruct();
		let mut import = BlockImportParams::new(origin, header);
		import.body = Some(extrinsics);
		import.fork_choice = Some(ForkChoiceStrategy::LongestChain);

		BlockImport::import_block(self, import, HashMap::new()).map(|_| ())
	}

	fn import_as_best(&mut self, origin: BlockOrigin, block: Block) -> Result<(), ConsensusError> {
		let (header, extrinsics) = block.deconstruct();
		let mut import = BlockImportParams::new(origin, header);
		import.body = Some(extrinsics);
		import.fork_choice = Some(ForkChoiceStrategy::Custom(true));

		BlockImport::import_block(self, import, HashMap::new()).map(|_| ())
	}

	fn import_as_final(&mut self, origin: BlockOrigin, block: Block) -> Result<(), ConsensusError> {
		let (header, extrinsics) = block.deconstruct();
		let mut import = BlockImportParams::new(origin, header);
		import.body = Some(extrinsics);
		import.finalized = true;
		import.fork_choice = Some(ForkChoiceStrategy::Custom(true));

		BlockImport::import_block(self, import, HashMap::new()).map(|_| ())
	}

	fn import_justified(
		&mut self,
		origin: BlockOrigin,
		block: Block,
		justification: Justification,
	) -> Result<(), ConsensusError> {
		let (header, extrinsics) = block.deconstruct();
		let mut import = BlockImportParams::new(origin, header);
		import.justification = Some(justification);
		import.body = Some(extrinsics);
		import.finalized = true;
		import.fork_choice = Some(ForkChoiceStrategy::LongestChain);

		BlockImport::import_block(self, import, HashMap::new()).map(|_| ())
	}
}
