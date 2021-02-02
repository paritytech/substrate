// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use std::fmt::Debug;
use sc_service::Configuration;
use sp_api::{ProvideRuntimeApi, BlockId};
use sp_blockchain::{HeaderBackend, HeaderMetadata, Error as BlockChainError};
use sp_runtime::traits::{Block as BlockT, Header as _};
use std::sync::Arc;
use runtime_upgrade_dryrun_api::DryRunRuntimeUpgrade;
use sc_cli::CliConfiguration;
use sc_client_api::Backend;

#[derive(Debug, structopt::StructOpt)]
pub struct DryRunCmd {
	#[structopt(short, long)]
	pub pallet: String,
}

enum Target {
	All,
	Pallet(String),
}

enum State {
	Snapshot(String),
	// -----^^ File path
	Live(String),
	// -^^ https URL.
}

pub struct DryRunConfig {
	target: Target,
	state: State,
}

impl DryRunCmd {
	pub async fn run<B, BB, C>(&self, client: Arc<C>, backend: BB, config: Configuration) where
		B: BlockT,
		C: ProvideRuntimeApi<B> + HeaderBackend<B> + HeaderMetadata<B, Error=BlockChainError> + 'static,
		C::Api: DryRunRuntimeUpgrade<B>,
	{
		// Option1: Use remote ext, it uses RPC, or a cache file, get state, call runtime api
		// somehow in that context (unclear how to do, but should be possible).
		let mut ext = remote_externalities::Builder::default()
			// .cache("polkadot.bin")
			// .at("polkadot.wss")
			.build()
			.await;
		ext.execute_with(|| {
			client.runtime_api().dry_run_runtime_upgrade(todo!());
		});

		// Option2: use test runner, seems like an overkill as it scrapes the whole DB, but we use
		// only the "state" part of it, anyhow.
	}
}

impl CliConfiguration for DryRunCmd {
	fn shared_params(&self) -> &sc_cli::SharedParams {
		&self.shared_params()
	}

	fn chain_id(&self, _is_dev: bool) -> sc_cli::Result<String> {
		Ok(match self.shared_params().chain {
			Some(ref chain) => chain.clone(),
			None => "dev".into(),
		})
	}
}
