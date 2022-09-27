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

//! Contains the core benchmarking logic.

use codec::DecodeAll;
use frame_support::weights::constants::WEIGHT_PER_NANOS;
use frame_system::ConsumedWeight;
use sc_block_builder::{BlockBuilderApi, BlockBuilderProvider};
use sc_cli::{Error, Result};
use sc_client_api::{Backend as ClientBackend, BlockBackend, StorageProvider, UsageProvider};
use sp_api::{ApiExt, Core, HeaderT, ProvideRuntimeApi};
use sp_blockchain::Error::RuntimeApiError;
use sp_runtime::{generic::BlockId, traits::Block as BlockT, DigestItem, OpaqueExtrinsic};
use sp_storage::StorageKey;

use clap::Args;
use log::{info, warn};
use serde::Serialize;
use std::{fmt::Debug, marker::PhantomData, sync::Arc, time::Instant};
use thousands::Separable;

use crate::shared::{StatSelect, Stats};

/// Log target for printing block weight info.
const LOG_TARGET: &'static str = "benchmark::block::weight";

/// Parameters for modifying the benchmark behaviour.
#[derive(Debug, Default, Serialize, Clone, PartialEq, Args)]
pub struct BenchmarkParams {
	/// Number of the first block to consider.
	#[clap(long)]
	pub from: u32,

	/// Last block number to consider.
	#[clap(long)]
	pub to: u32,

	/// Number of times that the benchmark should be repeated for each block.
	#[clap(long, default_value = "10")]
	pub repeat: u32,
}

/// Convenience closure for the [`Benchmark::run()`] function.
pub struct Benchmark<Block, BA, C> {
	client: Arc<C>,
	params: BenchmarkParams,
	_p: PhantomData<(Block, BA, C)>,
}

/// Helper for nano seconds.
type NanoSeconds = u64;

impl<Block, BA, C> Benchmark<Block, BA, C>
where
	Block: BlockT<Extrinsic = OpaqueExtrinsic>,
	BA: ClientBackend<Block>,
	C: BlockBuilderProvider<BA, Block, C>
		+ ProvideRuntimeApi<Block>
		+ StorageProvider<Block, BA>
		+ UsageProvider<Block>
		+ BlockBackend<Block>,
	C::Api: ApiExt<Block, StateBackend = BA::State> + BlockBuilderApi<Block>,
{
	/// Returns a new [`Self`] from the arguments.
	pub fn new(client: Arc<C>, params: BenchmarkParams) -> Self {
		Self { client, params, _p: PhantomData }
	}

	/// Benchmark the execution speed of historic blocks and log the results.
	pub fn run(&self) -> Result<()> {
		if self.params.from == 0 {
			return Err("Cannot benchmark the genesis block".into())
		}

		for i in self.params.from..=self.params.to {
			let block_num = BlockId::Number(i.into());
			let parent_num = BlockId::Number(((i - 1) as u32).into());
			let consumed = self.consumed_weight(&block_num)?;

			let block =
				self.client.block(&block_num)?.ok_or(format!("Block {} not found", block_num))?;
			let block = self.unsealed(block.block);
			let took = self.measure_block(&block, &parent_num)?;

			self.log_weight(i, block.extrinsics().len(), consumed, took);
		}

		Ok(())
	}

	/// Return the average *execution* aka. *import* time of the block.
	fn measure_block(&self, block: &Block, parent_num: &BlockId<Block>) -> Result<NanoSeconds> {
		let mut record = Vec::<NanoSeconds>::default();
		// Interesting part here:
		// Execute the block multiple times and collect stats about its execution time.
		for _ in 0..self.params.repeat {
			let block = block.clone();
			let runtime_api = self.client.runtime_api();
			let start = Instant::now();

			runtime_api
				.execute_block(&parent_num, block)
				.map_err(|e| Error::Client(RuntimeApiError(e)))?;

			record.push(start.elapsed().as_nanos() as NanoSeconds);
		}

		let took = Stats::new(&record)?.select(StatSelect::Average);
		Ok(took)
	}

	/// Returns the total nanoseconds of a [`frame_system::ConsumedWeight`] for a block number.
	///
	/// This is the post-dispatch corrected weight and is only available
	/// after executing the block.
	fn consumed_weight(&self, block: &BlockId<Block>) -> Result<NanoSeconds> {
		// Hard-coded key for System::BlockWeight. It could also be passed in as argument
		// for the benchmark, but I think this should work as well.
		let hash = array_bytes::hex2bytes(
			"26aa394eea5630e07c48ae0c9558cef734abf5cb34d6244378cddbf18e849d96",
		)?;
		let key = StorageKey(hash);

		let mut raw_weight = &self
			.client
			.storage(&block, &key)?
			.ok_or(format!("Could not find System::BlockWeight for block: {}", block))?
			.0[..];

		let weight = ConsumedWeight::decode_all(&mut raw_weight)?;
		// Should be divisible, but still use floats in case we ever change that.
		Ok((weight.total().ref_time() as f64 / WEIGHT_PER_NANOS.ref_time() as f64).floor()
			as NanoSeconds)
	}

	/// Prints the weight info of a block to the console.
	fn log_weight(&self, num: u32, num_ext: usize, consumed: NanoSeconds, took: NanoSeconds) {
		// The ratio of weight that the block used vs what it consumed.
		// This should in general not exceed 100% (minus outliers).
		let percent = (took as f64 / consumed as f64) * 100.0;

		let msg = format!(
			"Block {} with {: >5} tx used {: >6.2}% of its weight ({: >14} of {: >14} ns)",
			num,
			num_ext,
			percent,
			took.separate_with_commas(),
			consumed.separate_with_commas()
		);

		if took <= consumed {
			info!(target: LOG_TARGET, "{}", msg);
		} else {
			warn!(target: LOG_TARGET, "{} - OVER WEIGHT!", msg);
		}
	}

	/// Removes the consensus seal from the block.
	fn unsealed(&self, block: Block) -> Block {
		let (mut header, exts) = block.deconstruct();
		header.digest_mut().logs.retain(|item| !matches!(item, DigestItem::Seal(_, _)));
		Block::new(header, exts)
	}
}
