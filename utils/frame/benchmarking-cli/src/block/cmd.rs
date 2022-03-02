// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use sc_cli::{CliConfiguration, DatabaseParams, PruningParams, Result, SharedParams};
use sc_client_api::{Backend as ClientBackend, StorageProvider, UsageProvider};
use sc_client_db::DbHash;
use sc_service::Configuration;
use sp_blockchain::HeaderBackend;
use sp_database::{ColumnId, Database};
use sp_runtime::{
	OpaqueExtrinsic,
	traits::{Block as BlockT, HashFor},
	transaction_validity::{InvalidTransaction, TransactionValidityError},
};
use sp_state_machine::Storage;
use sp_storage::StateVersion;
use sp_inherents::InherentData;
use sc_block_builder::{BlockBuilderProvider, BlockBuilder};
use sc_block_builder::BlockBuilderApi;
use sp_api::{ApiExt, ProvideRuntimeApi};
use sc_consensus::{
	block_import::{BlockImportParams, ForkChoiceStrategy},
	BlockImport, StateAction,
};
use sp_blockchain::{ApplyExtrinsicFailed::Validity, Error::ApplyExtrinsicFailed};
use sp_consensus::BlockOrigin;
use sp_api::BlockId;

use clap::{Args, Parser};
use log::info;
use rand::prelude::*;
use serde::Serialize;
use std::{boxed::Box, fmt::Debug, sync::Arc, time::Instant};

use crate::storage::{record::{Stats, StatSelect}, template::TemplateData};

#[derive(Debug, Parser)]
pub struct BlockCmd {
	#[allow(missing_docs)]
	#[clap(flatten)]
	pub shared_params: SharedParams,

	#[allow(missing_docs)]
	#[clap(flatten)]
	pub database_params: DatabaseParams,

	#[allow(missing_docs)]
	#[clap(flatten)]
	pub pruning_params: PruningParams,

	#[allow(missing_docs)]
	#[clap(flatten)]
	pub params: BlockParams,
}

#[derive(Debug, Default, Serialize, Clone, PartialEq, Args)]
pub struct BlockParams {
	/// Path to write the *weight* file to. Can be a file or directory.
	/// For substrate this should be `frame/support/src/weights`.
	#[clap(long, default_value = ".")]
	pub weight_path: String,

	/// Select a specific metric to calculate the final weight output.
	#[clap(long = "metric", default_value = "average")]
	pub weight_metric: StatSelect,

	/// Multiply the resulting weight with the given factor. Must be positive.
	/// Is calculated before `weight_add`.
	#[clap(long = "mul", default_value = "1")]
	pub weight_mul: f64,

	/// Add the given offset to the resulting weight.
	/// Is calculated after `weight_mul`.
	#[clap(long = "add", default_value = "0")]
	pub weight_add: u64,

	/// Skip the `read` benchmark.
	#[clap(long)]
	pub skip_read: bool,

	/// Skip the `write` benchmark.
	#[clap(long)]
	pub skip_write: bool,

	/// Rounds of warmups before measuring.
	/// Only supported for `read` benchmarks.
	#[clap(long, default_value = "1")]
	pub warmups: u32,

	/// State cache size.
	#[clap(long, default_value = "0")]
	pub state_cache_size: usize,

	/// Limit them number of extrinsics to put in a block.
	#[clap(long)]
	pub max_ext_per_block: Option<u32>,

	/// Repeats for measuring the time of a an empty block execution.
	#[clap(long, default_value = "1000")]
	pub repeat_empty_block: u32,

	/// Repeats for measuring the time of a a full block execution.
	#[clap(long, default_value = "100")]
	pub repeat_full_block: u32,
}

/// The results of multiple runs in ns.
type BenchRecord = Vec<u64>;

pub trait ExtrinsicGenerator {
	fn noop(&self, nonce: u32) -> Option<OpaqueExtrinsic>;
}

impl BlockCmd {
	pub async fn run<Block, BA, C, IQ, RA, API>(
		&self,
		cfg: Configuration,
		client: Arc<C>,
		mut iq: IQ,
		db: (Arc<dyn Database<DbHash>>, ColumnId),
		storage: Arc<dyn Storage<HashFor<Block>>>,
		ra: Arc<RA>,
		idps: Arc<dyn sp_inherents::InherentDataProvider>,
		ext_gen: Arc<dyn ExtrinsicGenerator>,
	) -> Result<()>
	where
		// TODO remove the Extrinsic = OpaqueExtrinsic
		Block: BlockT<Hash = DbHash, Extrinsic = OpaqueExtrinsic>,
		BA: ClientBackend<Block>,
		C: BlockBuilderProvider<BA, Block, RA>
			+ UsageProvider<Block>
			+ StorageProvider<Block, BA>
			+ HeaderBackend<Block>,
		RA: ProvideRuntimeApi<Block, Api = API>,
		IQ: sc_consensus::BlockImport<Block>,
		API: ApiExt<Block, StateBackend = BA::State> + BlockBuilderApi<Block>,
	{
		let genesis = BlockId::Number(client.info().best_number);
		//let mut template = TemplateData::new(&cfg, &self.params);
		info!("Creating empty block");
		// Block builders are not cloneable, so we need two.
		let mut build_empty = client.new_block(Default::default()).unwrap();
		let mut build_full = client.new_block(Default::default()).unwrap();
		let mut data = sp_inherents::InherentData::new();
		idps.provide_inherent_data(&mut data).unwrap();
		info!("Creating inherents from {} inherent datas", data.len());
		let inherents = build_empty.create_inherents(data).unwrap();
		info!("Inserting {} inherent extrinsic", inherents.len());
		for ext in inherents.clone() {
			build_empty.push(ext.clone())?;
			build_full.push(ext.clone())?;
		}
		// Build a block with only inherents aka empty.
		let empty_block = build_empty.build()?.block;
		// Interesting part here:
		// Benchmark 1; Execution time of a an empty block.
		let mut rec_empty = BenchRecord::new();
		info!("Executing an empty block {} times", self.params.repeat_empty_block);
		for i in 0..self.params.repeat_empty_block {
			let block = empty_block.clone();
			let start = Instant::now();
			ra.runtime_api().execute_block(&genesis, block).unwrap();
			rec_empty.push(start.elapsed().as_nanos() as u64);
		}

		info!("Estimating max NO-OPs per block, capped at {}", self.max_ext_per_block());
		let mut noops = Vec::new();
		for nonce in 0..self.max_ext_per_block() {
			let ext = ext_gen.noop(nonce).expect("Need noop");
			match build_full.push(ext.clone()) {
				Ok(_) => {},
				Err(ApplyExtrinsicFailed(Validity(TransactionValidityError::Invalid(
					InvalidTransaction::ExhaustsResources,
				)))) => break,
				Err(error) => panic!("{}", error),
			}
			noops.push(ext);
		}
		info!("Max NO-OPs per block {}, continuing with benchmark.", noops.len());
		let full_block = build_full.build()?.block;

		// Interesting part here:
		// Benchmark 2; Execution time of a block filled with NO-OPs.
		let mut rec_full = BenchRecord::new();
		info!("Executing a full block {} times", self.params.repeat_full_block);
		for i in 0..self.params.repeat_full_block {
			let block = full_block.clone();
			let start = Instant::now();
			ra.runtime_api().execute_block(&genesis, block).unwrap();
			let took = start.elapsed().as_nanos();
			// Divide by the number of extrinsics in a block.
			rec_full.push(took as u64 / noops.len() as u64);
		}

		let start = Instant::now();
		Self::must_import(full_block, &mut iq);
		let speed = noops.len() as f32 / start.elapsed().as_secs_f32();
		info!("Imported block {:.2} NO-OP/s", speed);

		let stats = Stats::new(&rec_empty).unwrap();
		info!("Executing an empty block [ns]:\n{:?}", stats);

		let stats = Stats::new(&rec_full).unwrap();
		info!("Executing NO-OP extrinsic [ns]:\n{:?}", stats);

		Ok(())
	}

	/*fn new_block<'a, Block, BA, RA, C>(client: Arc<C>, idps: Arc<dyn BlockInherentDataProvider>,) -> Result<BlockBuilder<'a, Block, RA, BA>>
	where Block: BlockT,
	C: BlockBuilderProvider<BA, Block, RA> + 'a,
	RA: sp_api::ProvideRuntimeApi<Block>,
	BA: sc_client_api::Backend<Block> {
		let builder = client.new_block(Default::default()).unwrap();
		Ok(builder)
	}*/

	fn must_import<B, IQ>(block: B, iq: &mut IQ)
	where
		B: BlockT,
		IQ: sc_consensus::BlockImport<B>,
	{
		let mut params = BlockImportParams::new(BlockOrigin::File, block.header().clone());
		params.body = Some(block.extrinsics().to_vec());
		params.fork_choice = Some(ForkChoiceStrategy::LongestChain);
		let block_hash = block.hash();
		let import =
			futures::executor::block_on(iq.import_block(params, Default::default())).unwrap();
		if !matches!(import, sc_consensus::ImportResult::Imported(_)) {
			panic!("Could not import block: {:?}", import)
		}
	}

	/// Creates an rng from a random seed.
	pub(crate) fn setup_rng() -> impl rand::Rng {
		let seed = rand::thread_rng().gen::<u64>();
		info!("Using seed {}", seed);
		StdRng::seed_from_u64(seed)
	}

	fn max_ext_per_block(&self) -> u32 {
		self.params.max_ext_per_block.unwrap_or(u32::MAX)
	}
}

// Boilerplate
impl CliConfiguration for BlockCmd {
	fn shared_params(&self) -> &SharedParams {
		&self.shared_params
	}

	fn database_params(&self) -> Option<&DatabaseParams> {
		Some(&self.database_params)
	}

	fn pruning_params(&self) -> Option<&PruningParams> {
		Some(&self.pruning_params)
	}

	fn state_cache_size(&self) -> Result<usize> {
		Ok(self.params.state_cache_size)
	}
}


		
		/*info!("Importing empty block as warmup");
		let block = block_builder.build()?.block;
		info!("Executing block");
		ra.runtime_api().execute_block(&BlockId::Number(genesis), block.clone()).expect("Must execute");
		info!("Importing block");
		Self::must_import(block, &mut iq);

		info!("Creating empty block");
		let mut block_builder = client.new_block(Default::default()).unwrap();

		let idps = block_inherents.providers(1).unwrap();
		info!("Creating inherent data from {} providers", idps.len());

		let mut data = sp_inherents::InherentData::new();
		for idp in idps.clone() {
			idp.provide_inherent_data(&mut data).unwrap();
		}
		info!("Creating inherents from {} inherent datas", data.len());
		let inherents = block_builder.create_inherents(data).unwrap();
		info!("Inserting {} extrinsic", inherents.len());
		for ext in inherents.clone() {
			block_builder.push(ext.clone())?;
		}*/
