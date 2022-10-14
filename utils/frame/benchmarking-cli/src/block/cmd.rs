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

//! Contains the [`BlockCmd`] as entry point for the CLI to execute
//! the *block* benchmark.

use sc_block_builder::{BlockBuilderApi, BlockBuilderProvider};
use sc_cli::{CliConfiguration, ImportParams, Result, SharedParams};
use sc_client_api::{Backend as ClientBackend, BlockBackend, StorageProvider, UsageProvider};
use sp_api::{ApiExt, ProvideRuntimeApi};
use sp_runtime::{traits::Block as BlockT, OpaqueExtrinsic};

use clap::Parser;
use std::{fmt::Debug, sync::Arc};

use super::bench::{Benchmark, BenchmarkParams};

/// Benchmark the execution time of historic blocks.
///
/// This can be used to verify that blocks do not use more weight than they consumed
/// in their `WeightInfo`. Example:
///
/// Let's say you are on a Substrate chain and want to verify that the first 3 blocks
/// did not use more weight than declared which would otherwise be an issue.
/// To test this with a dev node, first create one with a temp directory:
///
/// $ substrate --dev -d /tmp/my-dev --execution wasm --wasm-execution compiled
///
/// And wait some time to let it produce 3 blocks. Then benchmark them with:
///
/// $ substrate benchmark-block --from 1 --to 3 --dev -d /tmp/my-dev
///   --execution wasm --wasm-execution compiled --pruning archive
///
/// The output will be similar to this:
///
/// Block 1 with 1 tx used 77.34% of its weight ( 5,308,964 of 6,864,645 ns)
/// Block 2 with 1 tx used 77.99% of its weight ( 5,353,992 of 6,864,645 ns)
/// Block 3 with 1 tx used 75.91% of its weight ( 5,305,938 of 6,989,645 ns)
///
/// The percent number is important and indicates how much weight
/// was used as compared to the consumed weight.
/// This number should be below 100% for reference hardware.
#[derive(Debug, Parser)]
pub struct BlockCmd {
	#[allow(missing_docs)]
	#[clap(flatten)]
	pub shared_params: SharedParams,

	#[allow(missing_docs)]
	#[clap(flatten)]
	pub import_params: ImportParams,

	#[allow(missing_docs)]
	#[clap(flatten)]
	pub params: BenchmarkParams,

	/// Enable the Trie cache.
	///
	/// This should only be used for performance analysis and not for final results.
	#[clap(long)]
	pub enable_trie_cache: bool,
}

impl BlockCmd {
	/// Benchmark the execution time of historic blocks and compare it to their consumed weight.
	///
	/// Output will be printed to console.
	pub fn run<Block, BA, C>(&self, client: Arc<C>) -> Result<()>
	where
		Block: BlockT<Extrinsic = OpaqueExtrinsic>,
		BA: ClientBackend<Block>,
		C: BlockBuilderProvider<BA, Block, C>
			+ BlockBackend<Block>
			+ ProvideRuntimeApi<Block>
			+ StorageProvider<Block, BA>
			+ UsageProvider<Block>,
		C::Api: ApiExt<Block, StateBackend = BA::State> + BlockBuilderApi<Block>,
	{
		// Put everything in the benchmark type to have the generic types handy.
		Benchmark::new(client, self.params.clone()).run()
	}
}

// Boilerplate
impl CliConfiguration for BlockCmd {
	fn shared_params(&self) -> &SharedParams {
		&self.shared_params
	}

	fn import_params(&self) -> Option<&ImportParams> {
		Some(&self.import_params)
	}

	fn trie_cache_maximum_size(&self) -> Result<Option<usize>> {
		if self.enable_trie_cache {
			Ok(self.import_params().map(|x| x.trie_cache_maximum_size()).unwrap_or_default())
		} else {
			Ok(None)
		}
	}
}
