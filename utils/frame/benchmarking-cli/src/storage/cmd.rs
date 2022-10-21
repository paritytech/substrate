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

use sc_cli::{CliConfiguration, DatabaseParams, PruningParams, Result, SharedParams};
use sc_client_api::{Backend as ClientBackend, StorageProvider, UsageProvider};
use sc_client_db::DbHash;
use sc_service::Configuration;
use sp_blockchain::HeaderBackend;
use sp_database::{ColumnId, Database};
use sp_runtime::traits::{Block as BlockT, HashFor};
use sp_state_machine::Storage;
use sp_storage::StateVersion;

use clap::{Args, Parser};
use log::info;
use rand::prelude::*;
use serde::Serialize;
use std::{fmt::Debug, sync::Arc};

use super::{record::StatSelect, template::TemplateData};

/// Benchmark the storage of a Substrate node with a live chain snapshot.
#[derive(Debug, Parser)]
pub struct StorageCmd {
	#[allow(missing_docs)]
	#[clap(flatten)]
	pub shared_params: SharedParams,

	#[allow(missing_docs)]
	#[clap(flatten)]
	pub database_params: DatabaseParams,

	#[allow(missing_docs)]
	#[clap(flatten)]
	pub pruning_params: PruningParams,

	#[allow(missing_docs)]
	#[clap(flatten)]
	pub params: StorageParams,
}

/// Parameters for modifying the benchmark behaviour and the post processing of the results.
#[derive(Debug, Default, Serialize, Clone, PartialEq, Args)]
pub struct StorageParams {
	/// Path to write the *weight* file to. Can be a file or directory.
	/// For substrate this should be `frame/support/src/weights`.
	#[clap(long, default_value = ".")]
	pub weight_path: String,

	/// Select a specific metric to calculate the final weight output.
	#[clap(long = "metric", default_value = "average")]
	pub weight_metric: StatSelect,

	/// Multiply the resulting weight with the given factor. Must be positive.
	/// Is calculated before `weight_add`.
	#[clap(long = "mul", default_value = "1")]
	pub weight_mul: f64,

	/// Add the given offset to the resulting weight.
	/// Is calculated after `weight_mul`.
	#[clap(long = "add", default_value = "0")]
	pub weight_add: u64,

	/// Skip the `read` benchmark.
	#[clap(long)]
	pub skip_read: bool,

	/// Skip the `write` benchmark.
	#[clap(long)]
	pub skip_write: bool,

	/// Rounds of warmups before measuring.
	/// Only supported for `read` benchmarks.
	#[clap(long, default_value = "1")]
	pub warmups: u32,

	/// The `StateVersion` to use. Substrate `--dev` should use `V1` and Polkadot `V0`.
	/// Selecting the wrong version can corrupt the DB.
	#[clap(long, possible_values = ["0", "1"])]
	pub state_version: u8,

	/// State cache size.
	#[clap(long, default_value = "0")]
	pub state_cache_size: usize,
}

impl StorageCmd {
	/// Calls into the Read and Write benchmarking functions.
	/// Processes the output and writes it into files and stdout.
	pub async fn run<Block, BA, C>(
		&self,
		cfg: Configuration,
		client: Arc<C>,
		db: (Arc<dyn Database<DbHash>>, ColumnId),
		storage: Arc<dyn Storage<HashFor<Block>>>,
	) -> Result<()>
	where
		BA: ClientBackend<Block>,
		Block: BlockT<Hash = DbHash>,
		C: UsageProvider<Block> + StorageProvider<Block, BA> + HeaderBackend<Block>,
	{
		let mut template = TemplateData::new(&cfg, &self.params);

		if !self.params.skip_read {
			let record = self.bench_read(client.clone())?;
			record.save_json(&cfg, "read")?;
			let stats = record.calculate_stats()?;
			info!("Time summary [ns]:\n{:?}\nValue size summary:\n{:?}", stats.0, stats.1);
			template.set_stats(Some(stats), None)?;
		}

		if !self.params.skip_write {
			let record = self.bench_write(client, db, storage)?;
			record.save_json(&cfg, "write")?;
			let stats = record.calculate_stats()?;
			info!("Time summary [ns]:\n{:?}\nValue size summary:\n{:?}", stats.0, stats.1);
			template.set_stats(None, Some(stats))?;
		}

		template.write(&self.params.weight_path)
	}

	/// Returns the specified state version.
	pub(crate) fn state_version(&self) -> StateVersion {
		match self.params.state_version {
			0 => StateVersion::V0,
			1 => StateVersion::V1,
			_ => unreachable!("Clap set to only allow 0 and 1"),
		}
	}

	/// Creates an rng from a random seed.
	pub(crate) fn setup_rng() -> impl rand::Rng {
		let seed = rand::thread_rng().gen::<u64>();
		info!("Using seed {}", seed);
		StdRng::seed_from_u64(seed)
	}
}

// Boilerplate
impl CliConfiguration for StorageCmd {
	fn shared_params(&self) -> &SharedParams {
		&self.shared_params
	}

	fn database_params(&self) -> Option<&DatabaseParams> {
		Some(&self.database_params)
	}

	fn pruning_params(&self) -> Option<&PruningParams> {
		Some(&self.pruning_params)
	}

	fn state_cache_size(&self) -> Result<usize> {
		Ok(self.params.state_cache_size)
	}
}
