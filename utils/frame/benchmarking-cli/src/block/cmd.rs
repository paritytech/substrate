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

use sc_block_builder::BlockBuilderApi;
use sc_cli::{CliConfiguration, DatabaseParams, PruningParams, Result, SharedParams};
use sc_client_api::{BlockBackend, UsageProvider};
use sc_service::Configuration;
use sp_api::{ApiExt, ProvideRuntimeApi};
use sp_blockchain::HeaderBackend;
use sp_runtime::traits::Block as BlockT;

use clap::{Args, Parser};
use log::info;
use serde::Serialize;
use std::{fmt::Debug, sync::Arc};

use crate::{
	block::{
		bench::{Benchmark, BenchmarkParams, BenchmarkType},
		template::TemplateData,
	},
	post_processing::WeightParams,
};

/// Command for running block and extrinsic benchmarks.
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

/// Parameters for a block benchmark and its result post processing.
#[derive(Debug, Default, Serialize, Clone, PartialEq, Args)]
pub struct BlockParams {
	#[allow(missing_docs)]
	#[clap(flatten)]
	pub weight: WeightParams,

	#[allow(missing_docs)]
	#[clap(flatten)]
	pub bench: BenchmarkParams,

	/// Ignore safety checks. Only useful for debugging.
	#[clap(long)]
	pub no_check: bool,
}

impl BlockCmd {
	/// Run the block and extrinsic benchmark.
	pub async fn run<Block, C, API>(&self, cfg: Configuration, client: Arc<C>) -> Result<()>
	where
		Block: BlockT,
		C: UsageProvider<Block>
			+ HeaderBackend<Block>
			+ BlockBackend<Block>
			+ ProvideRuntimeApi<Block, Api = API>,
		API: ApiExt<Block> + BlockBuilderApi<Block>,
	{
		let bench = Benchmark::new(client, self.params.bench.clone(), self.params.no_check);

		if !self.params.bench.skip_block {
			let stats = bench.bench(BenchmarkType::Block)?;
			info!("Executing an empty block [ns]:\n{:?}", stats);
			let template = TemplateData::new(BenchmarkType::Block, &cfg, &self.params, &stats)?;
			template.write(&self.params.weight.weight_path)?;
		}

		if !self.params.bench.skip_extrinsic {
			let stats = bench.bench(BenchmarkType::Extrinsic)?;
			info!("Executing a NO-OP extrinsic [ns]:\n{:?}", stats);
			let template = TemplateData::new(BenchmarkType::Extrinsic, &cfg, &self.params, &stats)?;
			template.write(&self.params.weight.weight_path)?;
		}

		Ok(())
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
}
