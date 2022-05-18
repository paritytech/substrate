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

use sc_cli::CliConfiguration;
use sc_cli::{ImportParams, SharedParams};
use sc_block_builder::{BlockBuilderApi, BlockBuilderProvider};
use sc_cli::{Result};
use sc_client_api::Backend as ClientBackend;
use sp_api::{ApiExt, ProvideRuntimeApi};
use sp_runtime::{traits::Block as BlockT, OpaqueExtrinsic};

use clap::{Args, Parser};
use log::info;
use serde::Serialize;
use std::{fmt::Debug, sync::Arc};

use super::bench::Benchmark;
use super::bench::BenchmarkParams;
use super::extrinsic_factory::ExtrinsicFactory;

#[derive(Debug, Parser)]
pub struct ExtrinsicCmd {
	#[allow(missing_docs)]
	#[clap(flatten)]
	pub shared_params: SharedParams,

	#[allow(missing_docs)]
	#[clap(flatten)]
	pub import_params: ImportParams,

	#[allow(missing_docs)]
	#[clap(flatten)]
	pub params: ExtrinsicParams,
}

#[derive(Debug, Default, Serialize, Clone, PartialEq, Args)]
pub struct ExtrinsicParams {
	#[clap(flatten)]
	pub bench: BenchmarkParams,

	/// Pallet name of the extrinsic.
	#[clap(short, long, value_name = "PALLET", index = 1)]
	pub pallet: String,

	/// Extrinsic name.
	#[clap(short, long, value_name = "EXTRINSIC", index = 2)]
	pub extrinsic: String,
}

impl ExtrinsicCmd {
	pub fn run<Block, BA, C>(
		&self,
		client: Arc<C>,
		inherent_data: sp_inherents::InherentData,
		ext_factory: &ExtrinsicFactory,
	) -> Result<()>
	where
		Block: BlockT<Extrinsic = OpaqueExtrinsic>,
		BA: ClientBackend<Block>,
		C: BlockBuilderProvider<BA, Block, C> + ProvideRuntimeApi<Block>,
		C::Api: ApiExt<Block, StateBackend = BA::State> + BlockBuilderApi<Block>,
	{
		let ext_builder = ext_factory.try_get(&self.params.pallet, &self.params.extrinsic).expect("TODO");
		let bench = Benchmark::new(client, self.params.bench.clone(), inherent_data);

		let stats = bench.bench(Some(ext_builder))?;
		info!("Executing a {} extrinsic takes[ns]:\n{:?}", &ext_builder, stats);

		Ok(())
	}
}

// Boilerplate
impl CliConfiguration for ExtrinsicCmd {
	fn shared_params(&self) -> &SharedParams {
		&self.shared_params
	}

	fn import_params(&self) -> Option<&ImportParams> {
		Some(&self.import_params)
	}
}
