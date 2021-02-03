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

use std::{fmt::Debug, str::FromStr};
use sc_service::Configuration;
use sp_api::BlockId;
use std::sync::Arc;
use runtime_upgrade_dryrun_api::DryRunRuntimeUpgrade;
use sc_cli::{CliConfiguration, ExecutionStrategy};
use sc_executor::{WasmExecutionMethod, NativeExecutor};
use sp_state_machine::StateMachine;
use sc_service::NativeExecutionDispatch;
use sp_runtime::traits::{Block as BlockT, Header as HeaderT, NumberFor};

#[derive(Debug)]
pub enum Error {}

impl ToString for Error {
	fn to_string(&self) -> String {
		"..".to_string()
	}
}

#[derive(Debug, structopt::StructOpt)]
pub struct DryRunCmd {
	#[structopt(short, long)]
	pub target: Target,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub shared_params: sc_cli::SharedParams,

	// #[structopt(short, long)]
	// pub state: State,
}

#[derive(Debug)]
pub enum Target {
	All,
	Pallet(String),
}

impl FromStr for Target {
	type Err = Error;
	fn from_str(s: &str) -> Result<Self, Self::Err> {
		Ok(if s.to_lowercase() == "All" { Target::All } else { Target::Pallet(s.to_string()) })
	}
}

pub enum State {
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
	pub async fn run<B, BA, ExecDispatch>(
		&self,
		config: Configuration,
		backend: Arc<BA>,
	) -> sc_cli::Result<()>
	where
		B: BlockT,
		BA: sc_client_api::Backend<B>,
		ExecDispatch: NativeExecutionDispatch + 'static,
		/* C: ProvideRuntimeApi<B>
		 * 	+ HeaderBackend<B>
		 * 	+ HeaderMetadata<B, Error = BlockChainError>
		 * 	+ 'static,
		 * C::Api: DryRunRuntimeUpgrade<B>,
		 *    ^^ In case you want to use test-runner or generally the client abstraction, you'd
		 * want    something like this. */
	{
		let spec = config.chain_spec;
		let genesis_storage = spec.build_storage()?;
		let code = sp_core::storage::StorageData(genesis_storage.top.get(sp_core::storage::well_known_keys::CODE).unwrap().to_vec());
		let code_key = sp_core::storage::StorageKey(sp_core::storage::well_known_keys::CODE.to_vec());
		let wasm_method = WasmExecutionMethod::Interpreted;
		let strategy = ExecutionStrategy::Native;
		let mut changes = Default::default();
		let cache_size = Some(1024usize);
		let heap_pages = Some(1024);
		let executor = NativeExecutor::<ExecDispatch>::new(wasm_method, heap_pages, 2);

		let ext = remote_externalities::Builder::new()
			.cache_mode(remote_externalities::CacheMode::UseElseCreate)
			.cache_name(remote_externalities::CacheName::Forced(
				"Kusama,0xdd772d86d5cfd2be9a11dd504866c7878ee071aefe02ff7db3d749f98bf890b8,.bin"
					.into(),
			))
			.inject(&[(code_key, code)])
			.build()
			.await;

		// replace :CODE:
		let real_state = backend.state_at(BlockId::Number(1u32.into()));
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
		&self.shared_params
	}

	fn chain_id(&self, _is_dev: bool) -> sc_cli::Result<String> {
		Ok(match self.shared_params.chain {
			Some(ref chain) => chain.clone(),
			None => "dev".into(),
		})
	}
}
