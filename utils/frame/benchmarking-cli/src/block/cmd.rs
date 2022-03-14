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

use clap::{Args, Parser};
use log::info;
use rand::prelude::*;
use serde::Serialize;
use std::{boxed::Box, fmt::Debug, sync::Arc, time::Instant};

use crate::{
	post_processing::WeightParams,
	storage::{
	record::{StatSelect, Stats},
}};
use super::{template::TemplateData, bench::{Benchmark, BenchmarkType, BenchmarkParams}};

#[derive(Debug, Parser)]
pub struct BlockCmd {
	#[allow(missing_docs)]
	#[clap(flatten)]
	pub shared_params: SharedParams,

	#[allow(missing_docs)]
	#[clap(flatten)]
	pub params: CommandParams,
}

#[derive(Debug, Default, Serialize, Clone, PartialEq, Args)]
pub struct CommandParams {
	#[allow(missing_docs)]
	#[clap(flatten)]
	pub weight: WeightParams,

	#[allow(missing_docs)]
	#[clap(flatten)]
	pub bench: BenchmarkParams,
}

/// Used by the benchmark to generate signed extrinsics.
pub trait ExtrinsicGenerator {
	/// Generates a `System::remark` extrinsic.
	fn remark(&self, nonce: u32) -> Option<OpaqueExtrinsic>;
}

impl BlockCmd {
	pub async fn run<Block, BA, C>(
		&self,
		cfg: Configuration,
		client: Arc<C>,
		inherent_data: sp_inherents::InherentData,
		ext_gen: Arc<dyn ExtrinsicGenerator>,
	) -> Result<()>
	where
		Block: BlockT<Extrinsic = OpaqueExtrinsic>,
		BA: ClientBackend<Block>,
		C: BlockBuilderProvider<BA, Block, C> + ProvideRuntimeApi<Block>,
		C::Api: ApiExt<Block, StateBackend = BA::State> + BlockBuilderApi<Block>,
	{
		let bench = Benchmark::new(client, inherent_data, ext_gen, self.params.bench.clone());

		{
			let stats = bench.bench(BenchmarkType::Block)?;
			info!("Executing an empty block [ns]:\n{:?}", stats);
			let template = TemplateData::new(BenchmarkType::Block, &cfg, &self.params, &stats)?;
			template.write(&self.params.weight.weight_path)?;
		}
		{
			let stats = bench.bench(BenchmarkType::Extrinsic)?;
			info!("Executing a NO-OP extrinsic [ns]:\n{:?}", stats);
			let template = TemplateData::new(BenchmarkType::Extrinsic, &cfg, &self.params, &stats)?;
			template.write(&self.params.weight.weight_path)?;
		}

		Ok(())
	}
}

// Boilerplate
impl CliConfiguration for BlockCmd {
	fn shared_params(&self) -> &SharedParams {
		&self.shared_params
	}
}
