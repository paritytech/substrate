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
use runtime_upgrade_dryrun_api::runtime_decl_for_DryRunRuntimeUpgrade::DryRunRuntimeUpgrade;

#[derive(Debug, structopt::StructOpt)]
pub struct DruRunCmd {
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

struct DryRunConfig {
	target: Target,
	state: State,
}

impl DruRunCmd {
	pub async fn run<B, BB, C>(&self, client: Arc<C>, backend: BB, config: DryRunConfig) where
		B: BlockT,
		C: ProvideRuntimeApi<B> + HeaderBackend<B> + HeaderMetadata<B, Error=BlockChainError> + 'static,
		C::Api: DryRunRuntimeUpgrade<B>
	{
		// substrate-test-runner
		// client.runtime_api().dry_run_runtime_upgrade(config);

		let ext = remote_externalities::Builder::default()
			.cache("polkadot.bin")
			// .at("polkadot.wss")
			.build()
			.await;
		ext::execute_with(|| {
			client.runtime_api().dry_run_runtime_upgrade(config);
		});
	}
}
