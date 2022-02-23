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
use sp_state_machine::{Backend as StateBackend, Storage};
use sp_storage::StateVersion;
use sp_trie::PrefixedMemoryDB;

use clap::Parser;
use log::info;
use rand::prelude::*;
use std::{fmt::Debug, sync::Arc};

use super::post_process::{PostProcParams, TemplateData};

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
	pub postproc_params: PostProcParams,

	/// Skip the `read` benchmark.
	#[clap(long)]
	pub skip_read: bool,

	/// Skip the `write` benchmark.
	#[clap(long)]
	pub skip_write: bool,

	/// State cache size.
	#[clap(long, default_value = "0")]
	pub state_cache_size: usize,

	/// Use a specific seed instead of picking one at random.
	#[clap(long)]
	pub seed: Option<u64>,

	/// The `StateVersion` to use.
	#[clap(long, possible_values = ["0", "1"], default_value = "0")]
	pub state_version: u8,

	/// Rounds of warmups before measuring.
	/// Only supported for `read` benchmarks.
	#[clap(long, default_value = "1")]
	pub warmups: u32,
}

impl StorageCmd {
	/// Dispatches a concrete sub command related to benchmarking with client overhead.
	pub async fn run<Block, BA, S, C>(
		&self,
		cfg: Configuration,
		client: Arc<C>,
		db: Arc<dyn Database<DbHash>>,
		storage: Arc<dyn Storage<HashFor<Block>>>,
	) -> Result<()>
	where
		BA: ClientBackend<Block, State = S>,
		Block: BlockT<Hash = sp_core::H256>,
		C: UsageProvider<Block> + StorageProvider<Block, BA> + HeaderBackend<Block>,
		S: StateBackend<HashFor<Block>, Transaction = PrefixedMemoryDB<HashFor<Block>>>,
	{
		let mut template = TemplateData::new(&cfg);

		if !self.skip_read {
			let times = self.read(client.clone())?;
			times.summary();
			times.save_json("read.json")?;
			template.read = Some(times.stats(&self.postproc_params)?);
		}

		if !self.skip_write {
			let times = self.write(&cfg, client.clone(), db, storage)?;
			times.summary();
			times.save_json("write.json")?;
			template.write = Some(times.stats(&self.postproc_params)?);
		}

		template.write(&self.postproc_params.weight_path)
	}

	pub fn state_version(&self) -> StateVersion {
		match self.state_version {
			0 => StateVersion::V0,
			1 => StateVersion::V1,
			_ => unreachable!("Clap set to only allow 0 and 1"),
		}
	}

	pub fn setup_rng(&self) -> impl rand::Rng {
		let seed = self.seed.unwrap_or(rand::thread_rng().gen::<u64>());
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
		Ok(self.state_cache_size)
	}
}
