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

//! `Structopt`-ready struct for `try-runtime`.

use parity_scale_codec::{Decode, Encode};
use std::{fmt::Debug, str::FromStr};
use sc_service::Configuration;
use sc_cli::{CliConfiguration, ExecutionStrategy};
use sc_executor::{WasmExecutionMethod, NativeExecutor};
use sp_state_machine::StateMachine;
use sc_service::NativeExecutionDispatch;
use sp_runtime::traits::{Block as BlockT, NumberFor};
use sp_core::storage::{StorageData, StorageKey, well_known_keys};
use frame_try_runtime::Target;

/// Various commands to try out the new runtime, over configurable states.
///
/// For now this only assumes running the `on_runtime_upgrade` hooks.
#[derive(Debug, structopt::StructOpt)]
pub struct TryRuntimeCmd {
	/// The shared parameters
	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub shared_params: sc_cli::SharedParams,

	/// The target pallet to run the migration against.
	#[structopt(short, long, default_value = "All")]
	pub target: Target,

	/// The state to use to run the migration. Should be a valid FILE or HTTP URI.
	#[structopt(short, long, default_value = "http://localhost:9933")]
	pub state: State,
}

/// The state to use for a migration dry-run.
#[derive(Debug)]
pub enum State {
	/// A snapshot. Inner value is a file path.
	Snap(String),

	/// A live chain. Inner value is the HTTP uri.
	Live(String),
}

impl FromStr for State {
	type Err = &'static str;
	fn from_str(s: &str) -> Result<Self, Self::Err> {
		match s.get(..7) {
			// could use Url crate as well, but lets keep it simple for now.
			Some("http://") => Ok(State::Live(s.to_string())),
			Some("file://") => s
				.split("//")
				.collect::<Vec<_>>()
				.get(1)
				.map(|s| State::Snap(s.to_string()))
				.ok_or("invalid file URI"),
			_ => Err("invalid format. Must be a valid HTTP or File URI"),
		}
	}
}

impl TryRuntimeCmd {
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

		let ext = {
			use remote_externalities::{Builder, Mode, CacheConfig, OfflineConfig, OnlineConfig};
			let builder = match &self.state {
				State::Snap(file_path) => Builder::new().mode(Mode::Offline(OfflineConfig {
					cache: CacheConfig { name: file_path.into(), ..Default::default() },
				})),
				State::Live(http_uri) => Builder::new().mode(Mode::Online(OnlineConfig {
					uri: http_uri.into(),
					..Default::default()
				})),
			};

			builder.inject(&[(code_key, code)]).build().await
		};

		let consumed_weight = StateMachine::<_, _, NumberFor<B>, _>::new(
			&ext.backend,
			None,
			&mut changes,
			&executor,
			"TryRuntime_on_runtime_upgrade",
			&self.target.encode(),
			ext.extensions,
			&sp_state_machine::backend::BackendRuntimeCode::new(&ext.backend)
				.runtime_code()
				.unwrap(),
			sp_core::testing::TaskExecutor::new(),
		)
		.execute(strategy.into())
		.unwrap();

		let weight = <u64 as Decode>::decode(&mut &*consumed_weight).unwrap();
		log::info!(
			"try-runtime executed without errors. Consumed weight = {}",
			weight,
		);

		Ok(())
	}
}

impl CliConfiguration for TryRuntimeCmd {
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
