// This file is part of Substrate.

// Copyright (C) 2021-2022 Parity Technologies (UK) Ltd.
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

use parity_scale_codec::Decode;
use sc_executor::NativeExecutionDispatch;
use sc_service::Configuration;
use sp_runtime::traits::{Block as BlockT, NumberFor};

use crate::{
	build_executor, ensure_matching_spec, extract_code, local_spec, state_machine_call_with_proof,
	SharedParams, State, LOG_TARGET,
};

/// Configurations of the [`Command::OnRuntimeUpgrade`].
#[derive(Debug, Clone, clap::Parser)]
pub struct OnRuntimeUpgradeCmd {
	/// The state type to use.
	#[clap(subcommand)]
	pub state: State,
}

pub(crate) async fn on_runtime_upgrade<Block, ExecDispatch>(
	shared: SharedParams,
	command: OnRuntimeUpgradeCmd,
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
		let (expected_spec_name, expected_spec_version, _) =
			local_spec::<Block, ExecDispatch>(&ext, &executor);
		ensure_matching_spec::<Block>(
			uri,
			expected_spec_name,
			expected_spec_version,
			shared.no_spec_name_check,
		)
		.await;
	}

	let (_, encoded_result) = state_machine_call_with_proof::<Block, ExecDispatch>(
		&ext,
		&executor,
		execution,
		"TryRuntime_on_runtime_upgrade",
		&[],
		Default::default(), // we don't really need any extensions here.
	)?;

	let (weight, total_weight) = <(u64, u64) as Decode>::decode(&mut &*encoded_result)
		.map_err(|e| format!("failed to decode output: {:?}", e))?;
	log::info!(
		target: LOG_TARGET,
		"TryRuntime_on_runtime_upgrade executed without errors. Consumed weight = {}, total weight = {} ({})",
		weight,
		total_weight,
		weight as f64 / total_weight.max(1) as f64
	);

	Ok(())
}
