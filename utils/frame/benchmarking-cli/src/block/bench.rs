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
use sc_cli::Result;
use sc_client_api::{BlockBackend, UsageProvider};
use sp_api::{ApiExt, BlockId, HeaderT, ProvideRuntimeApi};
use sp_blockchain::HeaderBackend;
use sp_runtime::{traits::Block as BlockT, DigestItem};

use clap::Args;
use log::{info, warn};
use serde::Serialize;
use std::{marker::PhantomData, sync::Arc, time::Instant};

use crate::storage::record::Stats;

/// Parameters to configure a block benchmark.
#[derive(Debug, Default, Serialize, Clone, PartialEq, Args)]
pub struct BenchmarkParams {
	/// Skip benchmarking NO-OP extrinsics.
	#[clap(long)]
	pub skip_extrinsic: bool,

	/// Skip benchmark an empty block.
	#[clap(long)]
	pub skip_block: bool,

	/// Specify the id of a full block. 0 is treated as last block.
	/// The block should be filled with `System::remark` extrinsics.
	#[clap(long, default_value = "0")]
	pub full_block: u32,

	/// Specify the id of an empty block. 0 is treated as last block.
	/// The block should not contains any user extrinsics but only inherents.
	#[clap(long, default_value = "0")]
	pub empty_block: u32,

	/// How many executions should be measured.
	#[clap(long, default_value = "100")]
	pub repeat: u32,

	/// How many executions should be run as warmup.
	#[clap(long, default_value = "100")]
	pub warmup: u32,

	/// Maximum number of inherents that can be present in a block
	/// such that the block will still be considered empty.
	///
	/// Default is 1 since that is the case for Substrate.
	/// This check exists to make sure that a non-empty block is not
	/// accidentally counted as empty.
	#[clap(long, default_value = "1")]
	pub max_inherents: u32,

	/// Minimum number of extrinsics that must be present in a block
	/// such that the block will be considered full.
	///
	/// Default is 12_000 since in Substrate a block can hold that many NO-OPs.
	#[clap(long, default_value = "12000")]
	pub min_extrinsics: u32,
}

/// The results of multiple runs in ns.
pub(crate) type BenchRecord = Vec<u64>;

/// Type of a benchmark.
#[derive(Serialize, Clone)]
pub(crate) enum BenchmarkType {
	/// Extrinsic execution speed was measured.
	Extrinsic,
	/// Empty block execution speed was measured.
	Block,
}

/// Benchmarks the time it takes to execute an empty block or a NO-OP extrinsic.
pub(crate) struct Benchmark<B, C, API> {
	client: Arc<C>,
	params: BenchmarkParams,
	no_check: bool,
	_p: PhantomData<(B, API)>,
}

impl<B, C, API> Benchmark<B, C, API>
where
	B: BlockT,
	C: UsageProvider<B> + HeaderBackend<B> + BlockBackend<B> + ProvideRuntimeApi<B, Api = API>,
	API: ApiExt<B> + BlockBuilderApi<B>,
{
	/// Create a new benchmark object. `no_check` will ignore some safety checks.
	pub fn new(client: Arc<C>, params: BenchmarkParams, no_check: bool) -> Self {
		Self { client, params, no_check, _p: PhantomData }
	}

	/// Benchmarks the execution time of a block.
	pub fn bench(&self, which: BenchmarkType) -> Result<Stats> {
		let (id, empty) = match which {
			BenchmarkType::Block => (self.params.empty_block, true),
			BenchmarkType::Extrinsic => (self.params.full_block, false),
		};
		let (block, parent) = self.load_block(id)?;
		self.check_block(&block, empty)?;
		let block = self.unsealed(block)?;

		let rec = self.measure_block(&block, &parent, !empty)?;
		Stats::new(&rec)
	}

	/// Loads a block and its parent hash. 0 loads the latest block.
	fn load_block(&self, num: u32) -> Result<(B, BlockId<B>)> {
		let mut num = BlockId::Number(num.into());
		if num == BlockId::Number(0u32.into()) {
			num = BlockId::Number(self.client.info().best_number);

			if num == BlockId::Number(0u32.into()) {
				return Err("Chain must have some blocks but was empty".into())
			}
		}
		info!("Loading block {}", num);

		let block = self
			.client
			.block(&num)?
			.map(|b| b.block)
			.ok_or::<sc_cli::Error>("Could not load block".into())?;
		let parent = BlockId::Hash(*block.header().parent_hash());
		Ok((block, parent))
	}

	/// Checks if the passed block is empty.
	/// The resulting error can be demoted to a warning via `--no-check`.
	fn check_block(&self, block: &B, want_empty: bool) -> Result<()> {
		let num_ext = block.extrinsics().len() as u32;
		let is_empty = num_ext <= self.params.max_inherents;
		let is_full = num_ext >= self.params.min_extrinsics;
		info!("Block contains {} extrinsics", num_ext);

		if want_empty {
			match (is_empty, self.no_check) {
				(true, _) => {},
				(false, false) => return Err("Block should be empty but was not".into()),
				(false, true) => warn!("Treating non-empty block as empty because of --no-check"),
			}
		} else {
			match (is_full, self.no_check) {
				(true, _) => {},
				(false, false) => return Err("Block should be full but was not".into()),
				(false, true) => warn!("Treating non-full block as full because of --no-check"),
			}
		}

		Ok(())
	}

	/// Removes the consensus seal from a block if there is any.
	fn unsealed(&self, block: B) -> Result<B> {
		let (mut header, extrinsics) = block.deconstruct();
		match header.digest_mut().pop() {
			Some(DigestItem::Seal(_, _)) => {},
			Some(other) => header.digest_mut().push(other),
			_ => {},
		}
		Ok(B::new(header, extrinsics))
	}

	/// Measures the time that it take to execute a block.
	/// `per_ext` specifies if the result should be divided
	/// by the number of extrinsics in the block.
	/// This is useful for the case that you want to know
	/// how long it takes to execute one extrinsic.
	fn measure_block(&self, block: &B, before: &BlockId<B>, per_ext: bool) -> Result<BenchRecord> {
		let mut record = BenchRecord::new();
		let num_ext = block.extrinsics().len() as u64;
		if per_ext && num_ext == 0 {
			return Err("Cannot measure the extrinsic time of an empty block".into())
		}

		info!("Running {} warmups...", self.params.warmup);
		for _ in 0..self.params.warmup {
			self.client
				.runtime_api()
				.execute_block(before, block.clone())
				.expect("Past blocks must execute");
		}

		info!("Executing block {} times", self.params.repeat);
		// Interesting part here:
		// Execute a block multiple times and record each execution time.
		for _ in 0..self.params.repeat {
			let block = block.clone();
			let start = Instant::now();
			self.client
				.runtime_api()
				.execute_block(before, block)
				.expect("Past blocks must execute");

			let elapsed = start.elapsed().as_nanos();
			if per_ext {
				// checked for non zero div above.
				record.push(elapsed as u64 / num_ext);
			} else {
				record.push(elapsed as u64);
			}
		}

		Ok(record)
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
