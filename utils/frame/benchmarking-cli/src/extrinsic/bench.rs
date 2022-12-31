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

use log::{debug, error, info};
use sc_block_builder::{BlockBuilderApi, BlockBuilderProvider};
use sc_block_builder_ver::{
	validate_transaction, BlockBuilderApi as BlockBuilderApiVer,
	BlockBuilderProvider as BlockBuilderProviderVer,
};
use sc_cli::{Error, Result};
use sc_client_api::{Backend as ClientBackend, StateBackend};
use sc_consensus::{
	block_import::{BlockImportParams, ForkChoiceStrategy},
	BlockImport, StateAction,
};
use sp_api::{ApiExt, BlockId, Core, ProvideRuntimeApi};
use sp_blockchain::{
	ApplyExtrinsicFailed::Validity,
	Error::{ApplyExtrinsicFailed, RuntimeApiError},
	HeaderBackend,
};
use sp_consensus_aura::{digests::CompatibleDigestItem, sr25519::AuthoritySignature};
use sp_runtime::{
	traits::{Block as BlockT, Header as HeaderT, One, Zero},
	transaction_validity::{InvalidTransaction, TransactionValidityError},
	Digest, DigestItem, OpaqueExtrinsic,
};
use ver_api::VerApi;

use clap::Args;
use serde::Serialize;
use sp_consensus::BlockOrigin;
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

pub(crate) struct BenchmarkVer<Block, BA, C> {
	client: Arc<C>,
	params: BenchmarkParams,
	inherent_data: (sp_inherents::InherentData, sp_inherents::InherentData),
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
			record.push(elapsed as u64);
		}

		Ok(record)
	}

	fn max_ext_per_block(&self) -> u32 {
		self.params.max_ext_per_block.unwrap_or(u32::MAX)
	}
}

impl<Block, BA, C> BenchmarkVer<Block, BA, C>
where
	Block: BlockT<Extrinsic = OpaqueExtrinsic>,
	BA: ClientBackend<Block>,
	C: BlockBuilderProviderVer<BA, Block, C>,
	C: ProvideRuntimeApi<Block>,
	C: BlockImport<
		Block,
		Transaction = <BA::State as StateBackend<
			<<Block as BlockT>::Header as HeaderT>::Hashing,
		>>::Transaction,
	>,
	C: HeaderBackend<Block>,
	C::Api: ApiExt<Block, StateBackend = BA::State>,
	C::Api: BlockBuilderApiVer<Block>,
	C::Api: VerApi<Block>,
{
	/// Create a new [`Self`] from the arguments.
	pub fn new(
		client: Arc<C>,
		params: BenchmarkParams,
		inherent_data: (sp_inherents::InherentData, sp_inherents::InherentData),
	) -> Self {
		Self { client, params, inherent_data, _p: PhantomData }
	}

	pub fn prepare_benchmark(&mut self, ext_builder: &dyn ExtrinsicBuilder) -> Result<usize> {
		let block = self.build_first_block(ext_builder)?;
		let num_ext = block.block.extrinsics().len();
		self.import_block(block);
		Ok(num_ext)
	}

	/// Benchmark a block that does not include any new extrinsics but needs to shuffle previous one
	pub fn bench_block(&mut self, ext_builder: &dyn ExtrinsicBuilder) -> Result<Stats> {
		let block = self.build_second_block(ext_builder, 0, false)?;
		let record = self.measure_block(&block.block, BlockId::Number(One::one()))?;
		Stats::new(&record)
	}

	/// Benchmark the time of an extrinsic in a full block.
	///
	/// First benchmarks an empty block, analogous to `bench_block` and use it as baseline.
	/// Then benchmarks a full block built with the given `ext_builder` and subtracts the baseline
	/// from the result.
	/// This is necessary to account for the time the inherents use.
	pub fn bench_extrinsic(
		&mut self,
		ext_builder: &dyn ExtrinsicBuilder,
		count: usize,
	) -> Result<Stats> {
		let block = self.build_second_block(ext_builder, count, true)?;
		let num_ext = block.block.extrinsics().len();
		let mut records = self.measure_block(&block.block.clone(), BlockId::Number(One::one()))?;

		for r in &mut records {
			// Divide by the number of extrinsics in the block.
			*r = ((*r as f64) / (num_ext as f64)).ceil() as u64;
		}

		Stats::new(&records)
	}

	fn create_digest(&self, aura_slot: u64) -> Digest {
		let mut digest = Digest::default();
		let digest_item = <DigestItem as CompatibleDigestItem<AuthoritySignature>>::aura_pre_digest(
			aura_slot.into(),
		);
		digest.push(digest_item);
		digest
	}

	fn import_block(&mut self, block: sc_block_builder_ver::BuiltBlock<Block, BA::State>) {
		info!("importing new block");
		let mut params = BlockImportParams::new(BlockOrigin::File, block.block.header().clone());
		params.state_action =
			StateAction::ApplyChanges(sc_consensus::StorageChanges::Changes(block.storage_changes));
		params.fork_choice = Some(ForkChoiceStrategy::LongestChain);

		let mut c = self.client.clone();
		unsafe {
			let mut_c = Arc::<C>::get_mut_unchecked(&mut c);
			futures::executor::block_on(mut_c.import_block(params, Default::default()))
				.expect("importing a block doesn't fail");
		}
		info!("best number: {} ", c.info().best_number);
	}

	/// Builds a block that enqueues maximum possible amount of extrinsics
	fn build_first_block(
		&mut self,
		ext_builder: &dyn ExtrinsicBuilder,
	) -> Result<sc_block_builder_ver::BuiltBlock<Block, BA::State>> {
		let digest = self.create_digest(1_u64);
		let mut builder = self.client.new_block(digest)?;
		// Create and insert the inherents.

		info!("creating inherents");
		let (seed, inherents) = builder.create_inherents(self.inherent_data.0.clone()).unwrap();
		info!("pushing inherents");
		for inherent in inherents {
			builder.push(inherent)?;
		}

		info!("applying previous block txs");
		builder.apply_previous_block_extrinsics(seed.clone(), &mut 0, usize::MAX, || false);

		let mut txs_count = 0u64;
		let txs_count_ref = &mut txs_count;

		// Put as many extrinsics into the block as possible and count them.
		info!("Building block, this takes some time...");
		let block = builder.build_with_seed(seed, |at, api| {
			let mut valid_txs: Vec<(Option<sp_runtime::AccountId32>, Block::Extrinsic)> =
				Default::default();
			for nonce in 0..self.max_ext_per_block() {
				let remark = ext_builder.build(nonce).expect("remark txs creation should not fail");
				match validate_transaction::<Block, C>(at, &api, remark.clone()) {
					Ok(()) => {
						valid_txs.push((None, remark));
					},
					Err(ApplyExtrinsicFailed(Validity(e))) if e.exhausted_resources() => break,
					Err(e) => {
						error!("{:?}", e);
						panic!("collecting txs failed");
					},
				}
			}

			if valid_txs.is_empty() {
				panic!("block should not be empty");
			}
			*txs_count_ref = valid_txs.len() as u64;
			valid_txs
		})?;
		info!("Extrinsics per block: {}", txs_count);
		Ok(block)
	}

	fn build_second_block(
		&mut self,
		ext_builder: &dyn ExtrinsicBuilder,
		txs_count: usize,
		apply_previous_block_extrinsics: bool,
	) -> Result<sc_block_builder_ver::BuiltBlock<Block, BA::State>> {
		// Return early if we just want a block with inherents and no additional extrinsics.

		let digest = self.create_digest(3_u64);
		let mut builder = self.client.new_block(digest)?;
		let (seed, inherents) = builder.create_inherents(self.inherent_data.1.clone()).unwrap();
		info!("pushing inherents");
		for inherent in inherents {
			builder.push(inherent)?;
		}

		builder.apply_previous_block_extrinsics(seed.clone(), &mut 0, usize::MAX, || {
			!apply_previous_block_extrinsics
		});

		let block = builder.build_with_seed(seed, |_, _| {
			(txs_count..(txs_count * 2))
				.map(|nonce| {
					let remark = ext_builder
						.build(nonce as u32)
						.expect("remark txs creation should not fail");
					(None, remark)
				})
				.collect::<Vec<_>>()
		})?;

		debug!("created block {:?}", block.block.clone());
		Ok(block)
	}

	/// Measures the time that it take to execute a block or an extrinsic.
	fn measure_block(&self, block: &Block, block_id: BlockId<Block>) -> Result<BenchRecord> {
		let mut record = BenchRecord::new();

		info!("Running {} warmups...", self.params.warmup);
		for _ in 0..self.params.warmup {
			self.client
				.runtime_api()
				.execute_block(&block_id, block.clone())
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
				.execute_block(&block_id, block)
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
