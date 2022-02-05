//! Command boilerplate code and setup.
//!
//! Calls into the respective functions in mod `bedrock`.

// TODO license everywhere

use crate::bedrock::{benches, BedrockCmd, BedrockType};
use clap::{ArgEnum, Parser};
use codec::{Decode, Encode};
use frame_benchmarking::{
	Analysis, BenchmarkBatch, BenchmarkBatchSplitResults, BenchmarkList, BenchmarkParameter,
	BenchmarkResult, BenchmarkSelector,
};
use frame_support::traits::StorageInfo;
use linked_hash_map::LinkedHashMap;
use sc_cli::{CliConfiguration, DatabaseParams, ExecutionStrategy, Result, SharedParams};
use sc_client_api::{blockchain::Backend as BlockchainBackend, Backend, UsageProvider};
use sc_client_db::{utils::{read_meta, open_database, DatabaseType}, Database, DbHash, BenchmarkingState, DatabaseSource, columns};
use sc_executor::NativeElseWasmExecutor;
use sc_service::{chain_ops::revert_chain, Configuration, NativeExecutionDispatch};
use sp_core::offchain::{
	testing::{TestOffchainExt, TestTransactionPoolExt},
	OffchainDbExt, OffchainWorkerExt, TransactionPoolExt,
};
use sp_database::Transaction;
use sp_externalities::Extensions;
use sp_keystore::{testing::KeyStore, KeystoreExt, SyncCryptoStorePtr};
use sp_runtime::traits::{Block as BlockT, Header as HeaderT};
use sp_state_machine::StateMachine;
use std::{fmt::Debug, fs, str::FromStr, sync::Arc, time};
use log::{info, debug};

type DB = dyn Database<DbHash>;

impl BedrockCmd {
	pub fn run<BB, ExecDispatch>(&self, config: Configuration) -> Result<()>
	where
		BB: BlockT + Debug,
		<<<BB as BlockT>::Header as HeaderT>::Number as std::str::FromStr>::Err: std::fmt::Debug,
		<BB as BlockT>::Hash: std::str::FromStr,
		ExecDispatch: NativeExecutionDispatch + 'static,
	{
		match self.bedrock_type {
			BedrockType::BlockImport => self.block_import(),
			BedrockType::DbRead => self.db_read(&config),
			BedrockType::DbWrite => self.db_write::<BB>(&config),
			BedrockType::TxExecution => self.tx_execution(),
		}
	}

	fn block_import(&self) -> Result<()> {
		// import_single_block
		unimplemented!();
	}

	fn db_read(&self, config: &Configuration) -> Result<()> {
		unimplemented!();
	}

	fn db_write<BB>(&self, config: &Configuration) -> Result<()>
	where
		BB: BlockT,
	{
		let db = setup_db::<BB>(&config)?;
		benches::db_write(&self.bedrock_params, db.as_ref());
		Ok(())
	}

	fn tx_execution(&self) -> Result<()> {
		unimplemented!();
	}
}

impl CliConfiguration for BedrockCmd {
	fn shared_params(&self) -> &SharedParams {
		&self.shared_params
	}

	fn database_params(&self) -> Option<&DatabaseParams> {
		Some(&self.database_params)
	}
}

fn setup_db<BB>(config: &Configuration) -> Result<Arc<DB>>
	where
		BB: BlockT,
	{
	let mut db_config = sc_client_db::DatabaseSettings {
		state_cache_size: config.state_cache_size,
		state_cache_child_ratio: config.state_cache_child_ratio.map(|v| (v, 100)),
		state_pruning: config.state_pruning.clone(),
		source: config.database.clone(),
		keep_blocks: config.keep_blocks.clone(),
		transaction_storage: config.transaction_storage.clone(),
	};
	info!("Loading {}...", db_config.source);

	let db = open_database::<BB>(&db_config, DatabaseType::Full).map_err(|e|  sc_cli::Error::Input("TODO".to_string()))?;
	let meta = read_meta::<BB>(&*db, columns::HEADER)?;
	info!("Best block: {}", meta.best_number);
	Ok(db)
}
