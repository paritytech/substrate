use std::{fmt::Debug, str::FromStr};

use parity_scale_codec::Decode;
use sc_executor::{NativeElseWasmExecutor, NativeExecutionDispatch};
use sc_service::Configuration;
use sp_core::twox_128;
use sp_runtime::traits::{Block as BlockT, NumberFor};
use sp_state_machine::StateMachine;

use crate::{check_spec_name, extract_code, SharedParams, State, LOG_TARGET};

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
	let wasm_method = shared.wasm_method;
	let execution = shared.execution;
	let heap_pages = shared.heap_pages.or(config.default_heap_pages);

	let mut changes = Default::default();
	let max_runtime_instances = config.max_runtime_instances;
	let executor = NativeElseWasmExecutor::<ExecDispatch>::new(
		wasm_method.into(),
		heap_pages,
		max_runtime_instances,
	);

	if let Some(uri) = command.state.live_uri() {
		check_spec_name::<Block>(uri, config.chain_spec.name().to_string()).await;
	}

	let ext = {
		let builder = command.state.builder::<Block>()?;
		let (code_key, code) = extract_code(config.chain_spec)?;
		builder
			.inject_key_value(&[(code_key, code)])
			.inject_hashed_key(&[twox_128(b"System"), twox_128(b"LastRuntimeUpgrade")].concat())
			.build()
			.await?
	};

	let encoded_result = StateMachine::<_, _, NumberFor<Block>, _>::new(
		&ext.backend,
		None,
		&mut changes,
		&executor,
		"TryRuntime_on_runtime_upgrade",
		&[],
		ext.extensions,
		&sp_state_machine::backend::BackendRuntimeCode::new(&ext.backend).runtime_code()?,
		sp_core::testing::TaskExecutor::new(),
	)
	.execute(execution.into())
	.map_err(|e| format!("failed to execute 'TryRuntime_on_runtime_upgrade': {:?}", e))?;

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
