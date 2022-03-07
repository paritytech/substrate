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
use sc_client_db::DbHash;
use sp_api::{ApiExt, BlockId, HeaderT, ProvideRuntimeApi};
use sp_blockchain::HeaderBackend;
use sp_runtime::{traits::Block as BlockT, DigestItem};

use clap::Args;
use log::{info, warn};
use serde::Serialize;
use std::{fmt, marker::PhantomData, sync::Arc, time::Instant};

/// Parameters to configure a block benchmark.
#[derive(Debug, Default, Serialize, Clone, PartialEq, Args)]
pub struct BenchmarkParams {
	/// Skip benchmarking NO-OP extrinsics.
	#[clap(long)]
	pub skip_extrinsic: bool,

	/// Skip benchmark an empty block.
	#[clap(long)]
	pub skip_block: bool,

	/// Specify the number of a full block. 0 is treated as last block.
	/// The block should be filled with `System::remark` extrinsics.
	#[clap(long, default_value = "0")]
	pub full_block: u32,

	/// Specify the number of an empty block. 0 is treated as last block.
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
	/// such that the block will still be considered full.
	///
	/// Default is 12_000 since in Substrate a block can hold that many NO-OPs.
	/// To benchmark the speed of a NO-OP extrinsic, there should be
	/// as many in the block as possible, for Substrate this is 12_000.
	#[clap(long, default_value = "12000")]
	pub min_extrinsics: u32,
}

/// The results of multiple runs in ns.
pub(crate) type BenchRecord = Vec<u64>;

/// Type of
#[derive(Serialize, Clone)]
pub(crate) enum BenchmarkType {
	Extrinsic,
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
	B: BlockT<Hash = DbHash>,
	C: UsageProvider<B> + HeaderBackend<B> + BlockBackend<B> + ProvideRuntimeApi<B, Api = API>,
	API: ApiExt<B> + BlockBuilderApi<B>,
{
	pub fn new(client: Arc<C>, params: BenchmarkParams, no_check: bool) -> Self {
		Self { client, params, no_check, _p: PhantomData }
	}

	/// Benchmarks the execution time of a block.
	/// `empty_block` defines if the block should be empty.
	pub fn bench(&self, which: BenchmarkType) -> Result<BenchRecord> {
		let block_empty: bool;
		let block = match which {
			BenchmarkType::Block => {
				block_empty = true;
				self.load_block(self.params.empty_block)?
			},
			BenchmarkType::Extrinsic => {
				block_empty = false;
				self.load_block(self.params.full_block)?
			},
		};
		let parent = BlockId::Hash(*block.header().parent_hash());

		self.check_block(&block, block_empty)?;
		let block = self.unseal(block)?;
		self.measure_block(&block, &parent, !block_empty)
	}

	/// Loads a block. 0 loads the latest block.
	fn load_block(&self, num: u32) -> Result<B> {
		let mut num = BlockId::Number(num.into());
		if num == BlockId::Number(0u32.into()) {
			num = BlockId::Number(self.client.info().best_number);
		}
		info!("Loading block {}", num);

		self.client.block(&num)?.map(|b| b.block).ok_or("Could not find block".into())
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
				(false, true) => warn!("Treating non-full block as full because of --no-check"),
				(false, false) => return Err("Block should be full but was not".into()),
			}
		}

		Ok(())
	}

	/// Removes the consensus seal from the block if there is any.
	fn unseal(&self, block: B) -> Result<B> {
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
	/// This is useful for the case that you only want to know
	/// how long it takes to execute one extrinsic.
	fn measure_block(&self, block: &B, before: &BlockId<B>, per_ext: bool) -> Result<BenchRecord> {
		let num_ext = block.extrinsics().len() as u64;
		info!("Executing block with {} extrinsics {} times", num_ext, self.params.repeat);
		let mut record = BenchRecord::new();

		info!("Running warmup...");
		for _ in 0..self.params.warmup {
			self.client
				.runtime_api()
				.execute_block(before, block.clone())
				.expect("Old blocks must execute");
		}

		info!("Measuring execution time");
		// Interesting part here:
		// Execute a block multiple times and record each execution time.
		for _ in 0..self.params.repeat {
			let block = block.clone();
			let start = Instant::now();
			self.client
				.runtime_api()
				.execute_block(before, block)
				.expect("Old blocks must execute");

			let elapsed = start.elapsed().as_nanos();
			if per_ext {
				// Zero div here can only happen with --no-check.
				record.push(elapsed as u64 / num_ext);
			} else {
				record.push(elapsed as u64);
			}
		}

		Ok(record)
	}
}

impl fmt::Debug for BenchmarkType {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self {
			Self::Extrinsic => write!(f, "extrinsic"),
			Self::Block => write!(f, "block"),
		}
	}
}

impl BenchmarkType {
	pub(crate) fn name(&self) -> &'static str {
		match self {
			Self::Extrinsic => "ExtrinsicBase",
			Self::Block => "BlockExecution",
		}
	}
}
