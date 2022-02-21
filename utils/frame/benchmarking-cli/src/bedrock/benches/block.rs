use sc_block_builder::{BlockBuilderProvider, BuiltBlock, RecordProof};
use sc_cli::{CliConfiguration, DatabaseParams, PruningParams, Result, SharedParams};
use sc_client_api::{
	blockchain::Backend as BlockchainBackend, Backend, StorageProvider, UsageProvider,
};
use sc_consensus::{BlockImport, BlockImportParams};
use sp_api::{
	ApiExt, ApiRef, Core, ProvideRuntimeApi, StorageChanges, StorageProof, TransactionOutcome,
};
use sp_runtime::traits::Block as BlockT;

use clap::Parser;
use log::info;
use std::sync::Arc;

#[derive(Debug, PartialEq, Parser)]
pub struct BlockImportCmd {
	#[allow(missing_docs)]
	#[clap(flatten)]
	pub shared_params: SharedParams,
}

impl BlockImportCmd {
	pub fn run<Block, C, B, RA>(&self, client: Arc<C>) -> Result<()>
	where
		C: BlockBuilderProvider<B, Block, RA> + BlockImport<Block>,
		B: sc_client_api::Backend<Block>,
		Block: BlockT,
		RA: ProvideRuntimeApi<Block>,
	{
		Ok(())
	}
}

impl CliConfiguration for BlockImportCmd {
	fn shared_params(&self) -> &SharedParams {
		&self.shared_params
	}
}
