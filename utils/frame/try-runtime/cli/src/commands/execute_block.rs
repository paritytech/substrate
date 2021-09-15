use crate::{check_spec_name, extract_code, hash_of, parse, SharedParams, State, LOG_TARGET};
use remote_externalities::rpc_api;
use sc_executor::NativeElseWasmExecutor;
use sc_service::{Configuration, NativeExecutionDispatch};
use sp_core::{
	hashing::twox_128,
	offchain::{
		testing::{TestOffchainExt, TestTransactionPoolExt},
		OffchainDbExt, OffchainWorkerExt, TransactionPoolExt,
	},
	storage::well_known_keys,
};
use sp_keystore::{testing::KeyStore, KeystoreExt};
use sp_runtime::traits::{Block as BlockT, Header as HeaderT, NumberFor};
use sp_state_machine::StateMachine;
use std::{fmt::Debug, str::FromStr, sync::Arc};

#[derive(Debug, Clone, structopt::StructOpt)]
pub struct ExecuteBlockCmd {
	#[structopt(long)]
	overwrite_wasm_code: bool,

	/// The block hash at which to fetch the block.
	///
	/// If the `live` state type is being used, then this can be omitted, and is equal to whatever
	/// the `state::at` is. Only use this (with care) when combined with a snapshot.
	#[structopt(
		long,
		multiple = false,
		parse(try_from_str = parse::hash)
	)]
	block_at: Option<String>,

	/// The block uri from which to fetch the block.
	///
	/// If the `live` state type is being used, then this can be omitted, and is equal to whatever
	/// the `state::uri` is. Only use this (with care) when combined with a snapshot.
	#[structopt(
		long,
		multiple = false,
		parse(try_from_str = parse::hash)
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
			(None, State::Live { at, .. }) => hash_of::<Block>(&at),
			(None, State::Snap { .. }) => {
				panic!("either `--block-at` must be provided, or state must be `live`");
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

	check_spec_name::<Block>(block_uri.clone(), config.chain_spec.name().to_string()).await;

	let ext = {
		let builder = command
			.state
			.builder::<Block>()?
			// make sure the state is being build with the parent hash, if it is online.
			.overwrite_online_at(parent_hash.to_owned())
			.inject_hashed_key(&[twox_128(b"System"), twox_128(b"LastRuntimeUpgrade")].concat());

		let builder = if command.overwrite_wasm_code {
			let (code_key, code) = extract_code(config.chain_spec)?;
			builder.inject_key_value(&[(code_key, code)])
		} else {
			builder.inject_hashed_key(well_known_keys::CODE)
		};

		let mut ext = builder.build().await?;

		// register externality extensions in order to provide host interface for OCW to the
		// runtime.
		let (offchain, _offchain_state) = TestOffchainExt::new();
		let (pool, _pool_state) = TestTransactionPoolExt::new();
		ext.register_extension(OffchainDbExt::new(offchain.clone()));
		ext.register_extension(OffchainWorkerExt::new(offchain));
		ext.register_extension(KeystoreExt(Arc::new(KeyStore::new())));
		ext.register_extension(TransactionPoolExt::new(pool));

		ext
	};

	// A digest item gets added when the runtime is processing the block, so we need to pop
	// the last one to be consistent with what a gossiped block would contain.
	let (mut header, extrinsics) = block.deconstruct();
	header.digest_mut().pop();
	let block = Block::new(header, extrinsics);

	let _encoded_result = StateMachine::<_, _, NumberFor<Block>, _>::new(
		&ext.backend,
		None,
		&mut changes,
		&executor,
		"Core_execute_block",
		block.encode().as_ref(),
		ext.extensions,
		&sp_state_machine::backend::BackendRuntimeCode::new(&ext.backend).runtime_code()?,
		sp_core::testing::TaskExecutor::new(),
	)
	.execute(execution.into())
	.map_err(|e| format!("failed to execute 'Core_execute_block': {:?}", e))?;

	log::info!(target: LOG_TARGET, "Core_execute_block executed without errors.");

	Ok(())
}
