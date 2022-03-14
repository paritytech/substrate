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

use sc_block_builder::{BlockBuilder, BlockBuilderApi, BlockBuilderProvider};
use sc_cli::{CliConfiguration, DatabaseParams, PruningParams, Result, SharedParams};
use sc_client_api::{Backend as ClientBackend, StorageProvider, UsageProvider};
use sc_client_db::DbHash;
use sc_consensus::{
	block_import::{BlockImportParams, ForkChoiceStrategy},
	BlockImport, StateAction,
};
use sc_service::Configuration;
use sp_api::{ApiExt, BlockId, Core, ProvideRuntimeApi};
use sp_blockchain::{ApplyExtrinsicFailed::Validity, Error::ApplyExtrinsicFailed, HeaderBackend};
use sp_consensus::BlockOrigin;
use sp_database::{ColumnId, Database};
use sp_inherents::InherentData;
use sp_runtime::{
	traits::{Block as BlockT, HashFor, Zero},
	transaction_validity::{InvalidTransaction, TransactionValidityError},
	OpaqueExtrinsic,
};
use sp_state_machine::Storage;
use sp_storage::StateVersion;


use clap::Args;
use log::{info, warn};
use serde::Serialize;
use std::{marker::PhantomData, sync::Arc, time::Instant};

use super::cmd::{CommandParams, ExtrinsicGenerator};
use crate::storage::record::Stats;

/// Parameters to configure a block benchmark.
#[derive(Debug, Default, Serialize, Clone, PartialEq, Args)]
pub struct BenchmarkParams {
	/// Rounds of warmups before measuring.
	#[clap(long, default_value = "100")]
	pub warmup: u32,

	/// How many times the benchmark should be repeated.
	#[clap(long, default_value = "1000")]
	pub repeat: u32,

	/// Limit them number of extrinsics per block.
	///
	/// Only useful for debugging since for a real benchmark you
	/// want full blocks.
	#[clap(long)]
	pub max_ext_per_block: Option<u32>,
}

/// The results of multiple runs in ns.
pub(crate) type BenchRecord = Vec<u64>;

/// Type of a benchmark.
#[derive(Serialize, Clone)]
pub(crate) enum BenchmarkType {
	/// Per-extrinsic execution overhead was measured.
	Extrinsic,
	/// Per-block execution overhead was measured.
	Block,
}

/// Benchmarks the time it takes to execute an empty block or a NO-OP extrinsic.
pub(crate) struct Benchmark<Block, BA, C> {
	client: Arc<C>,
	params: BenchmarkParams,
	inherent_data: sp_inherents::InherentData,
	ext_gen: Arc<dyn ExtrinsicGenerator>,
	_p: PhantomData<(Block, BA)>,
}

impl<Block, BA, C> Benchmark<Block, BA, C>
where
	Block: BlockT<Extrinsic = OpaqueExtrinsic>,
	BA: ClientBackend<Block>,
	C: BlockBuilderProvider<BA, Block, C> + ProvideRuntimeApi<Block>,
	C::Api: ApiExt<Block, StateBackend = BA::State> + BlockBuilderApi<Block>,
{
	/// Create a new benchmark object.
	pub fn new(client: Arc<C>,inherent_data: sp_inherents::InherentData,
		ext_gen: Arc<dyn ExtrinsicGenerator>, params: BenchmarkParams) -> Self {
		Self { client, params, inherent_data, ext_gen, _p: PhantomData }
	}

	/// Benchmarks the execution time of a block.
	pub fn bench(&self, which: BenchmarkType) -> Result<Stats> {
		let has_extrinsics = which.has_extrinsics();
		let (block, extrinsics) = self.build_block(!has_extrinsics)?;
		// TODO only divide by extrinsics.len not block.ext.len
		let rec = self.measure_block(&block, has_extrinsics)?;
		Stats::new(&rec)
	}

	fn build_block(&self, empty: bool) -> Result<(Block, Vec<Block::Extrinsic>)> {
		let mut build = self.client.new_block(Default::default()).unwrap();
		let inherents = build.create_inherents(self.inherent_data.clone()).unwrap();
		for inherent in inherents {
			build.push(inherent)?;
		}

		// Return early if we just want an empty block.
		if empty {
			return Ok((build.build()?.block, vec![]));
		}
		
		info!("Counting max NO-OPs per block, capped at {}", self.max_ext_per_block());
		let mut remarks = Vec::new();
		for nonce in 0..self.max_ext_per_block() {
			let ext = self.ext_gen.remark(nonce).expect("Need remark");
			match build.push(ext.clone()) {
				Ok(_) => {},
				Err(ApplyExtrinsicFailed(Validity(TransactionValidityError::Invalid(
					InvalidTransaction::ExhaustsResources,
				)))) => break,
				Err(error) => panic!("{}", error),
			}
			remarks.push(ext);
		}
		assert!(!remarks.is_empty(), "A Block must hold at least one extrinsic");
		info!("Max NO-OPs per block: {}", remarks.len());
		let block = build.build()?.block;

		Ok((block, remarks))
	}

	/// Measures the time that it take to execute a block.
	/// `per_ext` specifies if the result should be divided
	/// by the number of extrinsics in the block.
	/// This is useful for the case that you want to know
	/// how long it takes to execute one extrinsic.
	fn measure_block(&self, block: &Block, per_ext: bool) -> Result<BenchRecord> {
		let mut record = BenchRecord::new();
		let num_ext = block.extrinsics().len() as u64;
		if per_ext && num_ext == 0 {
			return Err("Cannot measure the extrinsic time of an empty block".into())
		}
		let genesis = BlockId::Number(Zero::zero());

		info!("Running {} warmups...", self.params.warmup);
		for _ in 0..self.params.warmup {
			self.client
				.runtime_api()
				.execute_block(&genesis, block.clone())
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
				.execute_block(&genesis, block)
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

	fn max_ext_per_block(&self) -> u32 {
		self.params.max_ext_per_block.unwrap_or(u32::MAX)
	}
}

impl BenchmarkType {
	pub(crate) fn has_extrinsics(&self) -> bool {
		match self {
			Self::Extrinsic => true,
			Self::Block => false,
		}
	}

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
