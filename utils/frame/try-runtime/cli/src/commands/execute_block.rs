use crate::{
	build_executor, ensure_matching_spec_name, extract_code, full_extensions, hash_of,
	local_spec_name, state_machine_call, SharedParams, State, LOG_TARGET,
};
use remote_externalities::rpc_api;
use sc_service::{Configuration, NativeExecutionDispatch};
use sp_core::storage::well_known_keys;
use sp_runtime::traits::{Block as BlockT, Header as HeaderT, NumberFor};
use std::{fmt::Debug, str::FromStr};

#[derive(Debug, Clone, structopt::StructOpt)]
pub struct ExecuteBlockCmd {
	/// Overwrite the wasm code in state or not.
	#[structopt(long)]
	overwrite_wasm_code: bool,

	/// If set, then the state root check is disabled by the virtue of calling into
	/// `TryRuntime_execute_block_no_state_root_check` instead of `Core_execute_block`.
	#[structopt(long)]
	no_state_root_check: bool,

	/// The block hash at which to fetch the block.
	///
	/// If the `live` state type is being used, then this can be omitted, and is equal to whatever
	/// the `state::at` is. Only use this (with care) when combined with a snapshot.
	#[structopt(
		long,
		multiple = false,
		parse(try_from_str = crate::parse::hash)
	)]
	block_at: Option<String>,

	/// The block uri from which to fetch the block.
	///
	/// If the `live` state type is being used, then this can be omitted, and is equal to whatever
	/// the `state::uri` is. Only use this (with care) when combined with a snapshot.
	#[structopt(
		long,
		multiple = false,
		parse(try_from_str = crate::parse::url)
	)]
	block_uri: Option<String>,

	/// The state type to use.
	///
	/// For this command only, if the `live` is used, then state of the parent block is fetched.
	#[structopt(subcommand)]
	state: State,
}

impl ExecuteBlockCmd {
	fn block_at<Block: BlockT>(&self) -> sc_cli::Result<Block::Hash>
	where
		Block::Hash: FromStr,
		<Block::Hash as FromStr>::Err: Debug,
	{
		match (&self.block_at, &self.state) {
			(Some(block_at), State::Snap { .. }) => hash_of::<Block>(&block_at),
			(Some(block_at), State::Live { .. }) => {
				log::warn!(target: LOG_TARGET, "--block-at is provided while state type is live, this will most likely lead to a nonsensical result.");
				hash_of::<Block>(&block_at)
			},
			(None, State::Live { at: Some(at), .. }) => hash_of::<Block>(&at),
			_ => {
				panic!("either `--block-at` must be provided, or state must be `live with a proper `--at``");
			},
		}
	}

	fn block_uri<Block: BlockT>(&self) -> String
	where
		Block::Hash: FromStr,
		<Block::Hash as FromStr>::Err: Debug,
	{
		match (&self.block_uri, &self.state) {
			(Some(block_uri), State::Snap { .. }) => block_uri.to_owned(),
			(Some(block_uri), State::Live { .. }) => {
				log::warn!(target: LOG_TARGET, "--block-uri is provided while state type is live, this will most likely lead to a nonsensical result.");
				block_uri.to_owned()
			},
			(None, State::Live { uri, .. }) => uri.clone(),
			(None, State::Snap { .. }) => {
				panic!("either `--block-uri` must be provided, or state must be `live`");
			},
		}
	}
}

pub async fn execute_block<Block, ExecDispatch>(
	shared: SharedParams,
	command: ExecuteBlockCmd,
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
	let executor = build_executor::<ExecDispatch>(&shared, &config);
	let execution = shared.execution;

	let block_at = command.block_at::<Block>()?;
	let block_uri = command.block_uri::<Block>();
	let block: Block = rpc_api::get_block::<Block, _>(block_uri.clone(), block_at).await?;
	let parent_hash = block.header().parent_hash();
	log::info!(
		target: LOG_TARGET,
		"fetched block from {:?}, parent_hash to fetch the state {:?}",
		block_uri,
		parent_hash
	);

	let ext = {
		let builder = command
			.state
			.builder::<Block>()?
			// make sure the state is being build with the parent hash, if it is online.
			.overwrite_online_at(parent_hash.to_owned());

		let builder = if command.overwrite_wasm_code {
			let (code_key, code) = extract_code(&config.chain_spec)?;
			builder.inject_key_value(&[(code_key, code)])
		} else {
			builder.inject_hashed_key(well_known_keys::CODE)
		};

		builder.build().await?
	};

	// A digest item gets added when the runtime is processing the block, so we need to pop
	// the last one to be consistent with what a gossiped block would contain.
	let (mut header, extrinsics) = block.deconstruct();
	header.digest_mut().pop();
	let block = Block::new(header, extrinsics);

	let expected_spec_name = local_spec_name::<Block, ExecDispatch>(&ext, &executor);
	ensure_matching_spec_name::<Block>(block_uri.clone(), expected_spec_name).await;

	let _ = state_machine_call::<Block, ExecDispatch>(
		&ext,
		&executor,
		execution,
		if command.no_state_root_check {
			"Core_execute_block"
		} else {
			"TryRuntime_execute_block_no_state_root_check"
		},
		block.encode().as_ref(),
		full_extensions(),
	)?;

	log::info!(target: LOG_TARGET, "Core_execute_block executed without errors.");

	Ok(())
}
