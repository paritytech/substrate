//! Command boilerplate code and setup.
//!
//! Calls into the respective functions in mod `bedrock`.

// TODO license everywhere

#![allow(unused_imports)] // TODO

use clap::{ArgEnum, Parser};
use codec::{Decode, Encode};
use frame_benchmarking::{
	Analysis, BenchmarkBatch, BenchmarkBatchSplitResults, BenchmarkList, BenchmarkParameter,
	BenchmarkResult, BenchmarkSelector,
};
use frame_support::traits::StorageInfo;
use linked_hash_map::LinkedHashMap;
use log::{debug, info};
use sc_block_builder::BlockBuilderProvider;
use sc_cli::{
	CliConfiguration, DatabaseParams, ExecutionStrategy, PruningParams, Result, SharedParams,
};
use sc_client_api::{
	blockchain::Backend as BlockchainBackend, Backend, StorageProvider, UsageProvider,
};
use sc_client_db::{
	columns,
	utils::{open_database, read_meta, DatabaseType},
	BenchmarkingState, Database, DatabaseSource, DbHash,
};
use sc_consensus::BlockImport;
use sc_executor::NativeElseWasmExecutor;
use sc_service::{
	chain_ops::revert_chain, Configuration, NativeExecutionDispatch, PartialComponents,
};
use sp_core::offchain::{
	testing::{TestOffchainExt, TestTransactionPoolExt},
	OffchainDbExt, OffchainWorkerExt, TransactionPoolExt,
};

use sp_api::StateBackend;
use sp_blockchain::HeaderBackend;
use sp_database::Transaction;
use sp_externalities::Extensions;
use sp_keystore::{testing::KeyStore, KeystoreExt, SyncCryptoStorePtr};
use sp_runtime::{
	generic::BlockId,
	traits::{Block as BlockT, HashFor, Header as HeaderT},
};
use sp_state_machine::StateMachine;

use crate::bedrock::{benches, Bedrock, Benchmark};
use std::{fmt::Debug, fs, str::FromStr, sync::Arc, time};

impl Benchmark {
	/// Dispatches a concrete sub command related to benchmarking with client overhead.
	pub async fn run<Block, BA, S, C>(
		&self,
		cfg: Configuration,
		client: Arc<C>,
		backend: Arc<BA>,
		db: Arc<dyn sp_database::Database<DbHash>>,
		storage: Arc<dyn sp_state_machine::Storage<HashFor<Block>>>,
	) -> Result<()>
	where
		BA: Backend<Block, State = S>,
		Block: BlockT<Hash = sp_core::H256>,
		C: UsageProvider<Block> + StorageProvider<Block, BA> + HeaderBackend<Block>,
		S: sp_state_machine::Backend<
			HashFor<Block>,
			Transaction = sp_trie::PrefixedMemoryDB<HashFor<Block>>,
		>,
	{
		info!("DB at: {}", cfg.database.path().unwrap().display());
		match self {
			Self::StorageWrite(cmd) => cmd.run(&cfg, client, backend, db, storage),
			Self::StorageRead(cmd) => cmd.run(&cfg, client),
			//Self::ExtBase(cmd) => cmd.run(),
			_ => unimplemented!(),
		}
	}
}

impl Bedrock {
	/// Dispatches a concrete sub command related to benchmarking without client overhead.
	pub fn run<B>(&self, cfg: Configuration) -> Result<()>
	where
		B: BlockT,
	{
		match self {
			Self::DbRead(cmd) => cmd.run::<B>(cfg),
			// TODO add Self::DbWrite(cmd) => cmd.run::<B>(cfg),
			Self::DbFill(cmd) => cmd.run::<B>(cfg),
			_ => unimplemented!(),
		}
	}
}

// Boilerplate
impl CliConfiguration for Benchmark {
	fn shared_params(&self) -> &SharedParams {
		match self {
			Self::StorageRead(cmd) => cmd.shared_params(),
			Self::StorageWrite(cmd) => cmd.shared_params(),
			_ => unimplemented!(),
		}
	}

	fn database_params(&self) -> Option<&DatabaseParams> {
		match self {
			Self::StorageRead(cmd) => cmd.database_params(),
			Self::StorageWrite(cmd) => cmd.database_params(),
			_ => unimplemented!(),
		}
	}

	fn pruning_params(&self) -> Option<&PruningParams> {
		match self {
			Self::StorageRead(cmd) => cmd.pruning_params(),
			Self::StorageWrite(cmd) => cmd.pruning_params(),
			_ => unimplemented!(),
		}
	}
}

// Boilerplate
impl CliConfiguration for Bedrock {
	fn shared_params(&self) -> &SharedParams {
		match self {
			Self::DbRead(cmd) => cmd.shared_params(),
			Self::DbWrite(cmd) => cmd.shared_params(),
			Self::DbFill(cmd) => cmd.shared_params(),
			_ => unimplemented!(),
		}
	}

	fn database_params(&self) -> Option<&DatabaseParams> {
		match self {
			Self::DbRead(cmd) => cmd.database_params(),
			Self::DbWrite(cmd) => cmd.database_params(),
			Self::DbFill(cmd) => cmd.database_params(),
			_ => unimplemented!(),
		}
	}

	fn pruning_params(&self) -> Option<&PruningParams> {
		match self {
			Self::DbRead(cmd) => cmd.pruning_params(),
			Self::DbWrite(cmd) => cmd.pruning_params(),
			Self::DbFill(cmd) => cmd.pruning_params(),
			_ => unimplemented!(),
		}
	}
}
