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

//! Benchmarks the time it takes to access runtime storage.

use clap::Parser;
use frame_benchmarking::BenchmarkResult;
use itertools::Itertools;
use log::info;
use rand::Rng;
use sc_cli::{CliConfiguration, DatabaseParams, PruningParams, Result, SharedParams};
use sc_client_api::{
	blockchain::Backend as BlockchainBackend, Backend, StorageProvider, UsageProvider,
};
use sc_client_db::{Database, DatabaseSource, DbHash};
use sc_service::Configuration;
use sp_core::storage::{well_known_keys, ChildInfo, Storage, StorageChild, StorageKey, StorageMap};
use sp_database::Transaction;
use sp_runtime::{
	generic::BlockId,
	traits::{Block as BlockT, Header as HeaderT},
};
use std::{
	collections::BTreeMap,
	fmt::Debug,
	sync::Arc,
	time::{Duration, Instant},
};

use crate::bedrock::PostProcParams;

#[derive(Debug, PartialEq, Parser)]
pub struct ReadCmd {
	#[allow(missing_docs)]
	#[clap(flatten)]
	pub shared_params: SharedParams,

	#[allow(missing_docs)]
	#[clap(flatten)]
	pub database_params: DatabaseParams,

	#[allow(missing_docs)]
	#[clap(flatten)]
	pub pruning_params: PruningParams,

	/// Specify the state cache size.
	#[clap(long, value_name = "Bytes", default_value = "0")]
	pub state_cache_size: usize,

	#[allow(missing_docs)]
	#[clap(flatten)]
	pub post_proc: PostProcParams,
}

#[derive(Debug, PartialEq, Parser)]
pub struct WriteCmd {
	#[allow(missing_docs)]
	#[clap(flatten)]
	pub shared_params: SharedParams,

	#[allow(missing_docs)]
	#[clap(flatten)]
	pub database_params: DatabaseParams,

	#[allow(missing_docs)]
	#[clap(flatten)]
	pub pruning_params: PruningParams,

	/// Specify the state cache size.
	#[clap(long, value_name = "Bytes", default_value = "0")]
	pub state_cache_size: usize,

	#[allow(missing_docs)]
	#[clap(flatten)]
	pub post_proc: PostProcParams,

	/// RNG seed used to generate key-value pairs.
	#[clap(long, default_value = "0")]
	pub seed: u64,
}

/// Fills a DB with random data and random sizes.
/// Errors when the DB already contains data to avoid loss thereof.
#[derive(Debug, PartialEq, Parser)]
pub struct FillCmd {
	#[allow(missing_docs)]
	#[clap(flatten)]
	pub shared_params: SharedParams,

	#[allow(missing_docs)]
	#[clap(flatten)]
	pub database_params: DatabaseParams,
}

// Biolerplate below

impl CliConfiguration for ReadCmd {
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

impl CliConfiguration for WriteCmd {
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

impl CliConfiguration for FillCmd {
	fn shared_params(&self) -> &SharedParams {
		&self.shared_params
	}

	fn database_params(&self) -> Option<&DatabaseParams> {
		Some(&self.database_params)
	}
}
