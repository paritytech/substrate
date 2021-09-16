use std::{fmt::Debug, str::FromStr};

use parity_scale_codec::Decode;
use sc_executor::NativeExecutionDispatch;
use sc_service::Configuration;
use sp_runtime::traits::{Block as BlockT, NumberFor};

use crate::{
	build_executor, ensure_matching_spec_name, extract_code, local_spec_name, state_machine_call,
	SharedParams, State, LOG_TARGET,
};

#[derive(Debug, Clone, structopt::StructOpt)]
pub struct OnRuntimeUpgradeCmd {
	/// The state type to use.
	#[structopt(subcommand)]
	pub state: State,
}

pub async fn on_runtime_upgrade<Block, ExecDispatch>(
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
		builder.inject_key_value(&[(code_key, code)]).build().await?
	};

	if let Some(uri) = command.state.live_uri() {
		let expected_spec_name = local_spec_name::<Block, ExecDispatch>(&ext, &executor);
		ensure_matching_spec_name::<Block>(uri, expected_spec_name).await;
	}

	let (_, encoded_result) = state_machine_call::<Block, ExecDispatch>(
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
		weight as f64 / total_weight as f64
	);

	Ok(())
}
