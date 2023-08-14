// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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
use sp_api::{ApiExt, Core, ProvideRuntimeApi};
use sp_blockchain::{
	ApplyExtrinsicFailed::Validity,
	Error::{ApplyExtrinsicFailed, RuntimeApiError},
};
use sp_runtime::{
	traits::Block as BlockT,
	transaction_validity::{InvalidTransaction, TransactionValidityError},
	Digest, DigestItem, OpaqueExtrinsic,
};

use clap::Args;
use log::info;
use serde::Serialize;
use std::{marker::PhantomData, sync::Arc, time::Instant};

use super::ExtrinsicBuilder;
use crate::shared::{StatSelect, Stats};

/// Parameters to configure an *overhead* benchmark.
#[derive(Debug, Default, Serialize, Clone, PartialEq, Args)]
pub struct BenchmarkParams {
	/// Rounds of warmups before measuring.
	#[arg(long, default_value_t = 10)]
	pub warmup: u32,

	/// How many times the benchmark should be repeated.
	#[arg(long, default_value_t = 100)]
	pub repeat: u32,

	/// Maximal number of extrinsics that should be put into a block.
	///
	/// Only useful for debugging.
	#[arg(long)]
	pub max_ext_per_block: Option<u32>,
}

/// The results of multiple runs in nano seconds.
pub(crate) type BenchRecord = Vec<u64>;

/// Holds all objects needed to run the *overhead* benchmarks.
pub(crate) struct Benchmark<Block, BA, C> {
	client: Arc<C>,
	params: BenchmarkParams,
	inherent_data: sp_inherents::InherentData,
	digest_items: Vec<DigestItem>,
	_p: PhantomData<(Block, BA)>,
}

impl<Block, BA, C> Benchmark<Block, BA, C>
where
	Block: BlockT<Extrinsic = OpaqueExtrinsic>,
	BA: ClientBackend<Block>,
	C: BlockBuilderProvider<BA, Block, C>
		+ ProvideRuntimeApi<Block>
		+ sp_blockchain::HeaderBackend<Block>,
	C::Api: ApiExt<Block, StateBackend = BA::State> + BlockBuilderApi<Block>,
{
	/// Create a new [`Self`] from the arguments.
	pub fn new(
		client: Arc<C>,
		params: BenchmarkParams,
		inherent_data: sp_inherents::InherentData,
		digest_items: Vec<DigestItem>,
	) -> Self {
		Self { client, params, inherent_data, digest_items, _p: PhantomData }
	}

	/// Benchmark a block with only inherents.
	pub fn bench_block(&self) -> Result<Stats> {
		let (block, _) = self.build_block(None)?;
		let record = self.measure_block(&block)?;
		Stats::new(&record)
	}

	/// Benchmark the time of an extrinsic in a full block.
	///
	/// First benchmarks an empty block, analogous to `bench_block` and use it as baseline.
	/// Then benchmarks a full block built with the given `ext_builder` and subtracts the baseline
	/// from the result.
	/// This is necessary to account for the time the inherents use.
	pub fn bench_extrinsic(&self, ext_builder: &dyn ExtrinsicBuilder) -> Result<Stats> {
		let (block, _) = self.build_block(None)?;
		let base = self.measure_block(&block)?;
		let base_time = Stats::new(&base)?.select(StatSelect::Average);

		let (block, num_ext) = self.build_block(Some(ext_builder))?;
		let num_ext = num_ext.ok_or_else(|| Error::Input("Block was empty".into()))?;
		let mut records = self.measure_block(&block)?;

		for r in &mut records {
			// Subtract the base time.
			*r = r.saturating_sub(base_time);
			// Divide by the number of extrinsics in the block.
			*r = ((*r as f64) / (num_ext as f64)).ceil() as u64;
		}

		Stats::new(&records)
	}

	/// Builds a block with some optional extrinsics.
	///
	/// Returns the block and the number of extrinsics in the block
	/// that are not inherents.
	/// Returns a block with only inherents if `ext_builder` is `None`.
	fn build_block(
		&self,
		ext_builder: Option<&dyn ExtrinsicBuilder>,
	) -> Result<(Block, Option<u64>)> {
		let mut builder = self.client.new_block(Digest { logs: self.digest_items.clone() })?;
		// Create and insert the inherents.
		let inherents = builder.create_inherents(self.inherent_data.clone())?;
		for inherent in inherents {
			builder.push(inherent)?;
		}

		// Return early if `ext_builder` is `None`.
		let ext_builder = if let Some(ext_builder) = ext_builder {
			ext_builder
		} else {
			return Ok((builder.build()?.block, None))
		};

		// Put as many extrinsics into the block as possible and count them.
		info!("Building block, this takes some time...");
		let mut num_ext = 0;
		for nonce in 0..self.max_ext_per_block() {
			let ext = ext_builder.build(nonce)?;
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

		Ok((block, Some(num_ext)))
	}

	/// Measures the time that it take to execute a block or an extrinsic.
	fn measure_block(&self, block: &Block) -> Result<BenchRecord> {
		let mut record = BenchRecord::new();
		let genesis = self.client.info().genesis_hash;

		info!("Running {} warmups...", self.params.warmup);
		for _ in 0..self.params.warmup {
			self.client
				.runtime_api()
				.execute_block(genesis, block.clone())
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
				.execute_block(genesis, block)
				.map_err(|e| Error::Client(RuntimeApiError(e)))?;

			let elapsed = start.elapsed().as_nanos();
			record.push(elapsed as u64);
		}

		Ok(record)
	}

	fn max_ext_per_block(&self) -> u32 {
		self.params.max_ext_per_block.unwrap_or(u32::MAX)
	}
}
