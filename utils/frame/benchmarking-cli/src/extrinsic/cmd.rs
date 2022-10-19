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

use sc_block_builder::{BlockBuilderApi, BlockBuilderProvider};
use sc_cli::{CliConfiguration, ImportParams, Result, SharedParams};
use sc_client_api::Backend as ClientBackend;
use sp_api::{ApiExt, ProvideRuntimeApi};
use sp_runtime::{traits::Block as BlockT, DigestItem, OpaqueExtrinsic};

use clap::{Args, Parser};
use log::info;
use serde::Serialize;
use std::{fmt::Debug, sync::Arc};

use super::{
	bench::{Benchmark, BenchmarkParams},
	extrinsic_factory::ExtrinsicFactory,
};

/// Benchmark the execution time of different extrinsics.
///
/// This is calculated by filling a block with a specific extrinsic and executing the block.
/// The result time is then divided by the number of extrinsics in that block.
///
/// NOTE: The BlockExecutionWeight is ignored  in this case since it
// is very small compared to the total block execution time.
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

/// The params for the [`ExtrinsicCmd`].
#[derive(Debug, Default, Serialize, Clone, PartialEq, Args)]
pub struct ExtrinsicParams {
	#[clap(flatten)]
	pub bench: BenchmarkParams,

	/// List all available pallets and extrinsics.
	///
	/// The format is CSV with header `pallet, extrinsic`.
	#[arg(long)]
	pub list: bool,

	/// Pallet name of the extrinsic to benchmark.
	#[arg(long, value_name = "PALLET", required_unless_present = "list")]
	pub pallet: Option<String>,

	/// Extrinsic to benchmark.
	#[arg(long, value_name = "EXTRINSIC", required_unless_present = "list")]
	pub extrinsic: Option<String>,

	/// Enable the Trie cache.
	///
	/// This should only be used for performance analysis and not for final results.
	#[arg(long)]
	pub enable_trie_cache: bool,
}

impl ExtrinsicCmd {
	/// Benchmark the execution time of a specific type of extrinsic.
	///
	/// The output will be printed to console.
	pub fn run<Block, BA, C>(
		&self,
		client: Arc<C>,
		inherent_data: sp_inherents::InherentData,
		digest_items: Vec<DigestItem>,
		ext_factory: &ExtrinsicFactory,
	) -> Result<()>
	where
		Block: BlockT<Extrinsic = OpaqueExtrinsic>,
		BA: ClientBackend<Block>,
		C: BlockBuilderProvider<BA, Block, C> + ProvideRuntimeApi<Block>,
		C::Api: ApiExt<Block, StateBackend = BA::State> + BlockBuilderApi<Block>,
	{
		// Short circuit if --list was specified.
		if self.params.list {
			let list: Vec<String> = ext_factory.0.iter().map(|b| b.name()).collect();
			info!(
				"Listing available extrinsics ({}):\npallet, extrinsic\n{}",
				list.len(),
				list.join("\n")
			);
			return Ok(())
		}

		let pallet = self.params.pallet.clone().unwrap_or_default();
		let extrinsic = self.params.extrinsic.clone().unwrap_or_default();
		let ext_builder = match ext_factory.try_get(&pallet, &extrinsic) {
			Some(ext_builder) => ext_builder,
			None =>
				return Err("Unknown pallet or extrinsic. Use --list for a complete list.".into()),
		};

		let bench = Benchmark::new(client, self.params.bench.clone(), inherent_data, digest_items);
		let stats = bench.bench_extrinsic(ext_builder)?;
		info!(
			"Executing a {}::{} extrinsic takes[ns]:\n{:?}",
			ext_builder.pallet(),
			ext_builder.extrinsic(),
			stats
		);

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

	fn trie_cache_maximum_size(&self) -> Result<Option<usize>> {
		if self.params.enable_trie_cache {
			Ok(self.import_params().map(|x| x.trie_cache_maximum_size()).unwrap_or_default())
		} else {
			Ok(None)
		}
	}
}
