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

//! Contains the [`OverheadCmd`] as entry point for the CLI to execute
//! the *overhead* benchmarks.

use sc_block_builder::{BlockBuilderApi, BlockBuilderProvider};
use sc_cli::{CliConfiguration, ImportParams, Result, SharedParams};
use sc_client_api::Backend as ClientBackend;
use sc_service::Configuration;
use sp_api::{ApiExt, ProvideRuntimeApi};
use sp_runtime::{traits::Block as BlockT, OpaqueExtrinsic};

use clap::{Args, Parser};
use log::info;
use serde::Serialize;
use std::{fmt::Debug, sync::Arc};

use crate::{
	overhead::{
		bench::{Benchmark, BenchmarkParams, BenchmarkType},
		template::TemplateData,
	},
	shared::WeightParams,
};

/// Benchmark the execution overhead per-block and per-extrinsic.
#[derive(Debug, Parser)]
pub struct OverheadCmd {
	#[allow(missing_docs)]
	#[clap(flatten)]
	pub shared_params: SharedParams,

	#[allow(missing_docs)]
	#[clap(flatten)]
	pub import_params: ImportParams,

	#[allow(missing_docs)]
	#[clap(flatten)]
	pub params: OverheadParams,
}

/// Configures the benchmark, the post-processing and weight generation.
#[derive(Debug, Default, Serialize, Clone, PartialEq, Args)]
pub struct OverheadParams {
	#[allow(missing_docs)]
	#[clap(flatten)]
	pub weight: WeightParams,

	#[allow(missing_docs)]
	#[clap(flatten)]
	pub bench: BenchmarkParams,
}

/// Used by the benchmark to build signed extrinsics.
///
/// The built extrinsics only need to be valid in the first block
/// who's parent block is the genesis block.
pub trait ExtrinsicBuilder {
	/// Build a `System::remark` extrinsic.
	fn remark(&self, nonce: u32) -> std::result::Result<OpaqueExtrinsic, &'static str>;
}

impl OverheadCmd {
	/// Measure the per-block and per-extrinsic execution overhead.
	///
	/// Writes the results to console and into two instances of the
	/// `weights.hbs` template, one for each benchmark.
	pub fn run<Block, BA, C>(
		&self,
		cfg: Configuration,
		client: Arc<C>,
		inherent_data: sp_inherents::InherentData,
		ext_builder: Arc<dyn ExtrinsicBuilder>,
	) -> Result<()>
	where
		Block: BlockT<Extrinsic = OpaqueExtrinsic>,
		BA: ClientBackend<Block>,
		C: BlockBuilderProvider<BA, Block, C> + ProvideRuntimeApi<Block>,
		C::Api: ApiExt<Block, StateBackend = BA::State> + BlockBuilderApi<Block>,
	{
		let bench = Benchmark::new(client, self.params.bench.clone(), inherent_data, ext_builder);

		// per-block execution overhead
		{
			let stats = bench.bench(BenchmarkType::Block)?;
			info!("Per-block execution overhead [ns]:\n{:?}", stats);
			let template = TemplateData::new(BenchmarkType::Block, &cfg, &self.params, &stats)?;
			template.write(&self.params.weight.weight_path)?;
		}
		// per-extrinsic execution overhead
		{
			let stats = bench.bench(BenchmarkType::Extrinsic)?;
			info!("Per-extrinsic execution overhead [ns]:\n{:?}", stats);
			let template = TemplateData::new(BenchmarkType::Extrinsic, &cfg, &self.params, &stats)?;
			template.write(&self.params.weight.weight_path)?;
		}

		Ok(())
	}
}

// Boilerplate
impl CliConfiguration for OverheadCmd {
	fn shared_params(&self) -> &SharedParams {
		&self.shared_params
	}

	fn import_params(&self) -> Option<&ImportParams> {
		Some(&self.import_params)
	}
}
