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
use sc_cli::{CliConfiguration, ExecutionStrategy};
use sc_executor::{WasmExecutionMethod, NativeExecutor};
use sp_state_machine::StateMachine;
use sc_service::NativeExecutionDispatch;
use sp_runtime::traits::{Block as BlockT, NumberFor};
use sp_core::storage::{StorageData, StorageKey, well_known_keys};

#[derive(Debug, structopt::StructOpt)]
pub struct DryRunCmd {
	/// The shared parameters
	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub shared_params: sc_cli::SharedParams,

	/// The target pallet to run the migration against.
	#[structopt(short, long, default_value = "All")]
	pub target: Target,

	/// The state to use to run the migration. It should be a ":" separated string, where the
	/// prefix is either `live` or `snap`, and the postfix is either the HTTP uri or the file path,
	/// respectively.
	#[structopt(short, long, default_value = "live:http://localhost:9933")]
	pub state: State,
}

/// Possible targets for dryrun runtime upgrade.
#[derive(Debug)]
pub enum Target {
	/// All pallets.
	All,
	/// A single pallet.
	Pallet(String),
}

impl FromStr for Target {
	type Err = &'static str;
	fn from_str(s: &str) -> Result<Self, Self::Err> {
		Ok(if s.to_lowercase() == "All" { Target::All } else { Target::Pallet(s.to_string()) })
	}
}

/// The state to use for a migration dryrun.
#[derive(Debug)]
pub enum State {
	/// A snapshot. Inner value is file path.
	Snap(String),

	/// A live chain. Inner value is the HTTP uri.
	Live(String),
}

impl FromStr for State {
	type Err = &'static str;
	fn from_str(s: &str) -> Result<Self, Self::Err> {
		let splitted = s.splitn(2, ":").collect::<Vec<_>>();
		if splitted.len() != 2 {
			return Err("invalid format. Must be [state_type]:[state_value].");
		}
		let state_type = splitted[0];
		let value = splitted[1];
		match state_type {
			"live" => Ok(State::Live(value.to_string())),
			"snap" => Ok(State::Snap(value.to_string())),
			_ => Err("Invalid state type."),
		}
	}
}

impl DryRunCmd {
	pub async fn run<B, ExecDispatch>(&self, config: Configuration) -> sc_cli::Result<()>
	where
		B: BlockT,
		ExecDispatch: NativeExecutionDispatch + 'static,
	{
		let spec = config.chain_spec;
		let genesis_storage = spec.build_storage()?;

		let code = StorageData(genesis_storage.top.get(well_known_keys::CODE).unwrap().to_vec());
		let code_key = StorageKey(well_known_keys::CODE.to_vec());

		let wasm_method = WasmExecutionMethod::Interpreted;
		let strategy = ExecutionStrategy::Native;
		let mut changes = Default::default();

		let heap_pages = Some(1024);
		let executor = NativeExecutor::<ExecDispatch>::new(wasm_method, heap_pages, 2);

		let ext = remote_externalities::Builder::new().inject(&[(code_key, code)]).build().await;

		let raw_result = StateMachine::<_, _, NumberFor<B>, _>::new(
			&ext.backend,
			None,
			&mut changes,
			&executor,
			"DryRunRuntimeUpgrade_dry_run_runtime_upgrade",
			&[],
			ext.extensions,
			&sp_state_machine::backend::BackendRuntimeCode::new(&ext.backend)
				.runtime_code()
				.unwrap(),
			sp_core::testing::TaskExecutor::new(),
		)
		.execute(strategy.into())
		.unwrap();

		Ok(())
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
