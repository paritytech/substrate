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
use std::sync::Arc;
use runtime_upgrade_dryrun_api::DryRunRuntimeUpgrade;
use sc_cli::{SharedParams, CliConfiguration, ExecutionStrategy};
use sc_executor::WasmExecutionMethod;
use sc_client_api::Backend;
use sc_executor::NativeExecutor;
use sp_state_machine::StateMachine;
use sp_externalities::Extensions;
use sc_service::{NativeExecutionDispatch};
use sp_runtime::traits::{Block as BlockT, Header as HeaderT, NumberFor};

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
	pub async fn run<B, ExecDispatch>(
		&self,
		config: Configuration,
	) -> Result<(), ()>
	where
		B: BlockT,
		// BA: Backend<B>,
		// C: ProvideRuntimeApi<B>
		// 	+ HeaderBackend<B>
		// 	+ HeaderMetadata<B, Error = BlockChainError>
		// 	+ 'static,
		// C::Api: DryRunRuntimeUpgrade<B>,
		ExecDispatch: NativeExecutionDispatch + 'static,
	{
		let spec = config.chain_spec;
		let wasm_method = WasmExecutionMethod::Compiled;
		let strategy = ExecutionStrategy::Native;
		let mut changes = Default::default();
		let cache_size = Some(1024usize);
		let heap_pages = Some(1024);
		let ext = remote_externalities::Builder::new().build().await;
		let executor = NativeExecutor::<ExecDispatch>::new(wasm_method, heap_pages, 2);

		let mut extensions = Extensions::default();

		let result = StateMachine::<_, _, NumberFor<B>, _>::new(
			&ext.backend,
			None,
			&mut changes,
			&executor,
			"DryRunRuntimeUpgrade_dry_run_runtime_upgrade",
			&[],
			ext.extensions,
			&sp_state_machine::backend::BackendRuntimeCode::new(&ext.backend).runtime_code().unwrap(),
			sp_core::testing::TaskExecutor::new(),
		)
		.execute(strategy.into())
		.unwrap();

		return Ok(());
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
