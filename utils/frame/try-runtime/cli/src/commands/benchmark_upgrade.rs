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

use std::{fmt::Debug, str::FromStr, time};

use parity_scale_codec::Decode;
use sc_executor::NativeExecutionDispatch;
use sc_service::Configuration;
use sp_runtime::traits::{Block as BlockT, NumberFor};

use crate::{
	build_executor, ensure_matching_spec, extract_code, local_spec, state_machine_call,
	SharedParams, State, LOG_TARGET,
};

/// Configurations of the [`Command::BenchmarkUpgradeCmd`].
#[derive(Debug, Clone, structopt::StructOpt)]
pub struct BenchmarkUpgradeCmd {
	/// The state type to use.
	#[structopt(subcommand)]
	pub state: State,

	/// Number of iterations of _`on_runtime_upgrade()`
	#[structopt(long)]
	steps: u64,
}

pub(crate) async fn on_runtime_upgrade_bench<Block, ExecDispatch>(
	shared: SharedParams,
	command: BenchmarkUpgradeCmd,
	config: Configuration,
) -> sc_cli::Result<()>
where
	Block: BlockT + serde::de::DeserializeOwned,
	Block::Hash: FromStr,
	<Block::Hash as FromStr>::Err: Debug,
	NumberFor<Block>: FromStr,
	<NumberFor<Block> as FromStr>::Err: Debug,
	ExecDispatch: NativeExecutionDispatch + 'static,
{
	let executor = build_executor(&shared, &config);
	let execution = shared.execution;

	let ext = {
		let builder = command.state.builder::<Block>()?;
		let (code_key, code) = extract_code(&config.chain_spec)?;
		builder.inject_hashed_key_value(&[(code_key, code)]).build().await?
	};

	if let Some(uri) = command.state.live_uri() {
		let (expected_spec_name, expected_spec_version) =
			local_spec::<Block, ExecDispatch>(&ext, &executor);
		ensure_matching_spec::<Block>(
			uri,
			expected_spec_name,
			expected_spec_version,
			shared.no_spec_name_check,
		)
		.await;
	}

	let mut sum = 0;
	let iter_num = command.steps;
	for _ in 0..iter_num {
		let timer = time::SystemTime::now();
		state_machine_call::<Block, ExecDispatch>(
			&ext,
			&executor,
			execution,
			"TryRuntime_on_runtime_upgrade_bench",
			&[],
			Default::default(), // we don't really need any extensions here.
		)?;
		if let Some(elapsed) = timer.elapsed().ok() {
			sum += elapsed.as_nanos() as u64;
		}
	}

	// Used to retrieve the result, which will be the max block weight
	let encoded_result = state_machine_call::<Block, ExecDispatch>(
		&ext,
		&executor,
		execution,
		"TryRuntime_on_runtime_upgrade_bench",
		&[],
		Default::default(), // we don't really need any extensions here.
	)?
	.1;

	let average_time_nanos = sum / iter_num;
	// weight is represented as 1_000 nanoseconds
	let absolute_weight = average_time_nanos * 1000;

	let total_weight = <u64 as Decode>::decode(&mut &*encoded_result)
		.map_err(|e| format!("failed to decode output: {:?}", e))?;

	log::info!(
        target: LOG_TARGET,
        "TryRuntime_on_runtime_upgrade executed without errors. Consumed weight = {}, total weight = {} ({})",
        absolute_weight,
        total_weight,
        absolute_weight as f64 / total_weight.max(1) as f64
    );
	Ok(())
}
