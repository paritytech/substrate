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
use sc_client_api::{Backend as ClientBackend, HeaderBackend};
use sp_api::{ApiExt, BlockId, Core, ProvideRuntimeApi};
use sp_blockchain::{
	ApplyExtrinsicFailed::Validity,
	Error::{ApplyExtrinsicFailed, RuntimeApiError},
};
use sp_runtime::{
	traits::{Block as BlockT, Header},
	transaction_validity::{InvalidTransaction, TransactionValidityError},
	Digest, DigestItem, OpaqueExtrinsic,
};

use clap::Args;
use codec::Encode;
use log::info;
use serde::Serialize;
use std::{marker::PhantomData, sync::Arc, time::Instant};

use super::ExtrinsicBuilder;
use crate::shared::{StatSelect, Stats as TimeStats};

/// Parameters to configure an *overhead* benchmark.
#[derive(Debug, Default, Serialize, Clone, PartialEq, Args)]
pub struct BenchmarkParams {
	/// Rounds of warmups before measuring.
	#[clap(long, default_value = "10")]
	pub warmup: u32,

	/// How many times the benchmark should be repeated.
	#[clap(long, default_value = "100")]
	pub repeat: u32,

	/// Maximal number of extrinsics that should be put into a block.
	///
	/// Only useful for debugging.
	#[clap(long)]
	pub max_ext_per_block: Option<u32>,
}

/// The results of multiple runs in nano seconds.
pub(crate) type TimeRecord = Vec<u64>;

/// Proof size in bytes of a storage proof.
#[derive(Debug, Default, Serialize, Clone)]
pub(crate) struct ProofSize {
	/// The storage proof size.
	pub storage: u64,
	/// The compacted storage proof size.
	pub storage_compact: u64,
	/// The compacted and `zstd` compressed storage proof size.
	///
	/// NOTE: This is not a stable feature and just for eyeballing of how much we can save.
	pub storage_compressed_zstd: u64,
}

/// Proof size for proving the execution blocks.
#[derive(Debug, Default, Serialize, Clone)]
pub(crate) struct BlockProofSize {
	/// The proof size of an empty (= inherents only) block.
	pub empty: ProofSize,
	/// The proof size of a non-empty (= one extrinsic) block.
	pub non_empty: ProofSize,
}

/// Weight of execution a block.
#[derive(Debug, Default, Serialize, Clone)]
pub(crate) struct BlockWeight {
	/// The ref time that it took to execute the block.
	pub ref_time: TimeStats,
	/// The proof size that is required to prove the execution of the block.
	pub proof: BlockProofSize,
}

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
	C: BlockBuilderProvider<BA, Block, C> + ProvideRuntimeApi<Block> + HeaderBackend<Block>,
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

	/// Benchmark a block with only inherents and one block with one NO-OP extrinsic.
	///
	/// Returns the execution ref time of the empty block and the proof sizes of both.
	pub fn bench_block(&self, noop_builder: &dyn ExtrinsicBuilder) -> Result<BlockWeight> {
		let (empty_block, _) = self.build_block(None, None)?;
		let empty_weight = self.measure_block(&empty_block)?;

		let (non_empty_block, _) = self.build_block(Some(noop_builder), Some(1))?;
		let non_empty_proof = self.measure_block_proof_size(&non_empty_block)?;

		Ok(BlockWeight {
			ref_time: TimeStats::new(&empty_weight.0)?,
			proof: BlockProofSize { empty: empty_weight.1, non_empty: non_empty_proof },
		})
	}

	/// Benchmark the time of an extrinsic in a full block.
	///
	/// First benchmarks an empty block, analogous to `bench_block` and use it as baseline.
	/// Then benchmarks a full block built with the given `ext_builder` and subtracts the baseline
	/// from the result.
	/// This is necessary to account for the time the inherents use.
	pub fn bench_extrinsic(&self, ext_builder: &dyn ExtrinsicBuilder) -> Result<TimeStats> {
		let (block, _) = self.build_block(None, None)?;
		let (base, _proof) = self.measure_block(&block)?;
		let ref_time = TimeStats::new(&base)?.select(StatSelect::Average);

		let (block, num_ext) = self.build_block(Some(ext_builder), None)?;
		let num_ext = num_ext.ok_or_else(|| Error::Input("Block was empty".into()))?;
		let (mut full, _proof) = self.measure_block(&block)?;

		for r in &mut full {
			// Subtract the base time.
			*r = r.saturating_sub(ref_time);
			// Divide by the number of extrinsics in the block.
			*r = ((*r as f64) / (num_ext as f64)).ceil() as u64;
		}

		TimeStats::new(&full)
	}

	/// Builds a block with some optional extrinsics.
	///
	/// Returns the block and the number of extrinsics in the block
	/// that are not inherents.
	/// Returns a block with only inherents if `ext_builder` is `None`.
	fn build_block(
		&self,
		ext_builder: Option<&dyn ExtrinsicBuilder>,
		override_max_ext_per_block: Option<u32>,
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
		for nonce in 0..override_max_ext_per_block.unwrap_or(self.max_ext_per_block()) {
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

	/// Measure the time that it takes to execute a block and the storage proof size
	/// that it takes to proof its execution.
	fn measure_block(&self, block: &Block) -> Result<(TimeRecord, ProofSize)> {
		let parent_hash = block.header().parent_hash();
		let parent_id = BlockId::Hash(*parent_hash);

		info!("Running {} warmups...", self.params.warmup);
		for _ in 0..self.params.warmup {
			self.client
				.runtime_api()
				.execute_block(&parent_id, block.clone())
				.map_err(|e| Error::Client(RuntimeApiError(e)))?;
		}

		info!("Executing block {} times...", self.params.repeat);
		// Interesting part here:
		// Execute a block multiple times and record each execution time.
		let mut time = TimeRecord::new();
		for _ in 0..self.params.repeat {
			let block = block.clone();
			let runtime_api = self.client.runtime_api();
			let start = Instant::now();

			runtime_api
				.execute_block(&parent_id, block)
				.map_err(|e| Error::Client(RuntimeApiError(e)))?;

			let elapsed = start.elapsed().as_nanos();
			time.push(elapsed as u64);
		}
		let proof = self.measure_block_proof_size(block)?;

		Ok((time, proof))
	}

	/// Measure the storage proof size of a block.
	fn measure_block_proof_size(&self, block: &Block) -> Result<ProofSize> {
		let parent_hash = block.header().parent_hash();
		let parent_id = BlockId::Hash(*parent_hash);
		let parent_header = self
			.client
			.header(parent_id.clone())?
			.ok_or_else(|| Error::Input(format!("Parent header {} not found", parent_hash)))?;
		let parent_state_root = *parent_header.state_root();

		info!("Recording storage proof size...");
		let mut runtime_api = self.client.runtime_api();
		runtime_api.record_proof();
		runtime_api
			.execute_block(&parent_id, block.clone())
			.map_err(|e| Error::Client(RuntimeApiError(e)))?;
		let proof = runtime_api
			.extract_proof()
			.expect("Proof recording is enabled - a proof must be available; qed");
		let proof_len = proof.encoded_size() as u64;
		let compact_proof = proof
			.clone()
			.into_compact_proof::<<<Block as BlockT>::Header as Header>::Hashing>(parent_state_root)
			.unwrap();
		let compressed_proof =
			zstd::stream::encode_all(&compact_proof.encode()[..], 0).unwrap().len() as u64;

		info!(
			"Proof size in bytes: Raw {}, Compact {}, Compressed {}",
			proof_len,
			compact_proof.encoded_size(),
			compressed_proof
		);

		Ok(ProofSize {
			storage: proof_len,
			storage_compact: compact_proof.encoded_size() as u64,
			storage_compressed_zstd: compressed_proof,
		})
	}

	fn max_ext_per_block(&self) -> u32 {
		self.params.max_ext_per_block.unwrap_or(u32::MAX)
	}
}
