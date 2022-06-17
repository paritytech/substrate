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
use sp_core::storage::StorageKey;
use sp_database::{ColumnId, Database};
use sp_runtime::traits::{Block as BlockT, HashFor};
use sp_state_machine::Storage;
use sp_storage::StateVersion;

use clap::{Args, Parser};
use log::info;
use rand::prelude::*;
use serde::Serialize;
use sp_runtime::generic::BlockId;
use std::{fmt::Debug, path::PathBuf, sync::Arc};

use super::template::TemplateData;
use crate::shared::{new_rng, HostInfoParams, WeightParams};

/// Benchmark the storage speed of a chain snapshot.
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
	#[allow(missing_docs)]
	#[clap(flatten)]
	pub weight_params: WeightParams,

	#[allow(missing_docs)]
	#[clap(flatten)]
	pub hostinfo: HostInfoParams,

	/// Skip the `read` benchmark.
	#[clap(long)]
	pub skip_read: bool,

	/// Skip the `write` benchmark.
	#[clap(long)]
	pub skip_write: bool,

	/// Specify the Handlebars template to use for outputting benchmark results.
	#[clap(long)]
	pub template_path: Option<PathBuf>,

	/// Path to write the raw 'read' results in JSON format to. Can be a file or directory.
	#[clap(long)]
	pub json_read_path: Option<PathBuf>,

	/// Path to write the raw 'write' results in JSON format to. Can be a file or directory.
	#[clap(long)]
	pub json_write_path: Option<PathBuf>,

	/// Rounds of warmups before measuring.
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
	pub fn run<Block, BA, C>(
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

		let block_id = BlockId::<Block>::Number(client.usage_info().chain.best_number);
		template.set_block_number(block_id.to_string());

		if !self.params.skip_read {
			self.bench_warmup(&client)?;
			let record = self.bench_read(client.clone())?;
			if let Some(path) = &self.params.json_read_path {
				record.save_json(&cfg, path, "read")?;
			}
			let stats = record.calculate_stats()?;
			info!("Time summary [ns]:\n{:?}\nValue size summary:\n{:?}", stats.0, stats.1);
			template.set_stats(Some(stats), None)?;
		}

		if !self.params.skip_write {
			self.bench_warmup(&client)?;
			let record = self.bench_write(client, db, storage)?;
			if let Some(path) = &self.params.json_write_path {
				record.save_json(&cfg, path, "write")?;
			}
			let stats = record.calculate_stats()?;
			info!("Time summary [ns]:\n{:?}\nValue size summary:\n{:?}", stats.0, stats.1);
			template.set_stats(None, Some(stats))?;
		}

		template.write(&self.params.weight_params.weight_path, &self.params.template_path)
	}

	/// Returns the specified state version.
	pub(crate) fn state_version(&self) -> StateVersion {
		match self.params.state_version {
			0 => StateVersion::V0,
			1 => StateVersion::V1,
			_ => unreachable!("Clap set to only allow 0 and 1"),
		}
	}

	/// Run some rounds of the (read) benchmark as warmup.
	/// See `frame_benchmarking_cli::storage::read::bench_read` for detailed comments.
	fn bench_warmup<B, BA, C>(&self, client: &Arc<C>) -> Result<()>
	where
		C: UsageProvider<B> + StorageProvider<B, BA>,
		B: BlockT + Debug,
		BA: ClientBackend<B>,
	{
		let block = BlockId::Number(client.usage_info().chain.best_number);
		let empty_prefix = StorageKey(Vec::new());
		let mut keys = client.storage_keys(&block, &empty_prefix)?;
		let (mut rng, _) = new_rng(None);
		keys.shuffle(&mut rng);

		for i in 0..self.params.warmups {
			info!("Warmup round {}/{}", i + 1, self.params.warmups);
			for key in keys.clone() {
				let _ = client
					.storage(&block, &key)
					.expect("Checked above to exist")
					.ok_or("Value unexpectedly empty");
			}
		}

		Ok(())
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
