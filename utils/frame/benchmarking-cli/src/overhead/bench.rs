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

use sc_block_builder::{BlockBuilderApi, BlockBuilderProvider};
use sc_cli::{Error, Result};
use sc_client_api::Backend as ClientBackend;
use sp_api::{ApiExt, BlockId, Core, ProvideRuntimeApi};
use sp_blockchain::{
	ApplyExtrinsicFailed::Validity,
	Error::{ApplyExtrinsicFailed, RuntimeApiError},
};
use sp_runtime::{
	traits::{Block as BlockT, Zero},
	transaction_validity::{InvalidTransaction, TransactionValidityError},
	OpaqueExtrinsic,
};

use clap::Args;
use log::info;
use serde::Serialize;
use std::{marker::PhantomData, sync::Arc, time::Instant};

use crate::{overhead::cmd::ExtrinsicBuilder, storage::record::Stats};

/// Parameters to configure an *overhead* benchmark.
#[derive(Debug, Default, Serialize, Clone, PartialEq, Args)]
pub struct BenchmarkParams {
	/// Rounds of warmups before measuring.
	#[clap(long, default_value = "100")]
	pub warmup: u32,

	/// How many times the benchmark should be repeated.
	#[clap(long, default_value = "1000")]
	pub repeat: u32,

	/// Maximal number of extrinsics that should be put into a block.
	///
	/// Only useful for debugging.
	#[clap(long)]
	pub max_ext_per_block: Option<u32>,
}

/// The results of multiple runs in nano seconds.
pub(crate) type BenchRecord = Vec<u64>;

/// Type of a benchmark.
#[derive(Serialize, Clone, PartialEq, Copy)]
pub(crate) enum BenchmarkType {
	/// Measure the per-extrinsic execution overhead.
	Extrinsic,
	/// Measure the per-block execution overhead.
	Block,
}

/// Holds all objects needed to run the *overhead* benchmarks.
pub(crate) struct Benchmark<Block, BA, C> {
	client: Arc<C>,
	params: BenchmarkParams,
	inherent_data: sp_inherents::InherentData,
	ext_builder: Arc<dyn ExtrinsicBuilder>,
	_p: PhantomData<(Block, BA)>,
}

impl<Block, BA, C> Benchmark<Block, BA, C>
where
	Block: BlockT<Extrinsic = OpaqueExtrinsic>,
	BA: ClientBackend<Block>,
	C: BlockBuilderProvider<BA, Block, C> + ProvideRuntimeApi<Block>,
	C::Api: ApiExt<Block, StateBackend = BA::State> + BlockBuilderApi<Block>,
{
	/// Create a new [`Self`] from the arguments.
	pub fn new(
		client: Arc<C>,
		params: BenchmarkParams,
		inherent_data: sp_inherents::InherentData,
		ext_builder: Arc<dyn ExtrinsicBuilder>,
	) -> Self {
		Self { client, params, inherent_data, ext_builder, _p: PhantomData }
	}

	/// Run the specified benchmark.
	pub fn bench(&self, bench_type: BenchmarkType) -> Result<Stats> {
		let (block, num_ext) = self.build_block(bench_type)?;
		let record = self.measure_block(&block, num_ext, bench_type)?;
		Stats::new(&record)
	}

	/// Builds a block for the given benchmark type.
	///
	/// Returns the block and the number of extrinsics in the block
	/// that are not inherents.
	fn build_block(&self, bench_type: BenchmarkType) -> Result<(Block, u64)> {
		let mut builder = self.client.new_block(Default::default())?;
		// Create and insert the inherents.
		let inherents = builder.create_inherents(self.inherent_data.clone())?;
		for inherent in inherents {
			builder.push(inherent)?;
		}

		// Return early if we just want a block with inherents and no additional extrinsics.
		if bench_type == BenchmarkType::Block {
			return Ok((builder.build()?.block, 0))
		}

		// Put as many extrinsics into the block as possible and count them.
		info!("Building block, this takes some time...");
		let mut num_ext = 0;
		for nonce in 0..self.max_ext_per_block() {
			let ext = self.ext_builder.remark(nonce)?;
			match builder.push(ext.clone()) {
				Ok(()) => {},
				Err(ApplyExtrinsicFailed(Validity(TransactionValidityError::Invalid(
					InvalidTransaction::ExhaustsResources,
				)))) => break, // Block is full
				Err(e) => return Err(Error::Client(e)),
			}
			num_ext += 1;
		}
		if num_ext == 0 {
			return Err("A Block must hold at least one extrinsic".into())
		}
		info!("Extrinsics per block: {}", num_ext);
		let block = builder.build()?.block;

		Ok((block, num_ext))
	}

	/// Measures the time that it take to execute a block or an extrinsic.
	fn measure_block(
		&self,
		block: &Block,
		num_ext: u64,
		bench_type: BenchmarkType,
	) -> Result<BenchRecord> {
		let mut record = BenchRecord::new();
		if bench_type == BenchmarkType::Extrinsic && num_ext == 0 {
			return Err("Cannot measure the extrinsic time of an empty block".into())
		}
		let genesis = BlockId::Number(Zero::zero());

		info!("Running {} warmups...", self.params.warmup);
		for _ in 0..self.params.warmup {
			self.client
				.runtime_api()
				.execute_block(&genesis, block.clone())
				.map_err(|e| Error::Client(RuntimeApiError(e)))?;
		}

		info!("Executing block {} times", self.params.repeat);
		// Interesting part here:
		// Execute a block multiple times and record each execution time.
		for _ in 0..self.params.repeat {
			let block = block.clone();
			let runtime_api = self.client.runtime_api();
			let start = Instant::now();

			runtime_api
				.execute_block(&genesis, block)
				.map_err(|e| Error::Client(RuntimeApiError(e)))?;

			let elapsed = start.elapsed().as_nanos();
			if bench_type == BenchmarkType::Extrinsic {
				// Checked for non-zero div above.
				record.push((elapsed as f64 / num_ext as f64).ceil() as u64);
			} else {
				record.push(elapsed as u64);
			}
		}

		Ok(record)
	}

	fn max_ext_per_block(&self) -> u32 {
		self.params.max_ext_per_block.unwrap_or(u32::MAX)
	}
}

impl BenchmarkType {
	/// Short name of the benchmark type.
	pub(crate) fn short_name(&self) -> &'static str {
		match self {
			Self::Extrinsic => "extrinsic",
			Self::Block => "block",
		}
	}

	/// Long name of the benchmark type.
	pub(crate) fn long_name(&self) -> &'static str {
		match self {
			Self::Extrinsic => "ExtrinsicBase",
			Self::Block => "BlockExecution",
		}
	}
}
