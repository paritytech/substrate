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
use sp_database::Database;
use sp_runtime::traits::{Block as BlockT, HashFor};
use sp_state_machine::{Storage};
use sp_storage::StateVersion;

use serde::Serialize;
use clap::{Args, Parser};
use log::info;
use rand::prelude::*;
use std::{fmt::Debug, sync::Arc};

use super::template::TemplateData;

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

	/// Use a specific seed instead of picking a random one.
	#[clap(long)]
	pub seed: Option<u64>,

	/// The `StateVersion` to use.
	#[clap(long, possible_values = ["0", "1"], default_value = "0")]
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
		db: Arc<dyn Database<DbHash>>,
		storage: Arc<dyn Storage<HashFor<Block>>>,
	) -> Result<()>
	where
		BA: ClientBackend<Block>,
		Block: BlockT<Hash = sp_core::H256>,
		C: UsageProvider<Block> + StorageProvider<Block, BA> + HeaderBackend<Block>,
	{
		let mut template = TemplateData::new(&cfg, &self.params);

		if !self.params.skip_read {
			let record = self.bench_read(client.clone())?;
			record.save_json("read.json")?;
			let (time_stats, size_stats) = record.stats()?;
			info!("Time summary:\n{:?}\nValue size summary:\n{:?}", time_stats, size_stats);
			template.read = Some((time_stats, size_stats));
		}

		if !self.params.skip_write {
			let record = self.bench_write(&cfg, client, db, storage)?;
			record.save_json("write.json")?;
			let (time_stats, size_stats) = record.stats()?;
			info!("Time summary:\n{:?}\nValue size summary:\n{:?}", time_stats, size_stats);
			template.write = Some((time_stats, size_stats));
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

	/// Creates an rng from the specified seed or from a random seed otherwise.
	pub(crate) fn setup_rng(&self) -> impl rand::Rng {
		let seed = self.params.seed.unwrap_or(rand::thread_rng().gen::<u64>());
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
