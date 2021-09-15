use crate::{check_spec_name, extract_code, hash_of, parse, SharedParams, State, LOG_TARGET};
use parity_scale_codec::Encode;
use remote_externalities::rpc_api;
use sc_executor::{NativeElseWasmExecutor, NativeExecutionDispatch};
use sc_service::Configuration;
use sp_core::{
	offchain::{
		testing::{TestOffchainExt, TestTransactionPoolExt},
		OffchainDbExt, OffchainWorkerExt, TransactionPoolExt,
	},
	storage::well_known_keys,
	testing::TaskExecutor,
	twox_128,
};
use sp_keystore::{testing::KeyStore, KeystoreExt};
use sp_runtime::traits::{Block as BlockT, Header, NumberFor};
use sp_state_machine::{backend::BackendRuntimeCode, StateMachine};
use std::{fmt::Debug, str::FromStr, sync::Arc};

#[derive(Debug, Clone, structopt::StructOpt)]
pub struct OffchainWorkerCmd {
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
	header_at: Option<String>,

	/// The block uri from which to fetch the block.
	///
	/// If the `live` state type is being used, then this can be omitted, and is equal to whatever
	/// the `state::uri` is. Only use this (with care) when combined with a snapshot.
	#[structopt(
		long,
		multiple = false,
		parse(try_from_str = parse::hash)
	)]
	header_uri: Option<String>,

	/// The state type to use.
	#[structopt(subcommand)]
	pub state: State,
}

impl OffchainWorkerCmd {
	fn header_at<Block: BlockT>(&self) -> sc_cli::Result<Block::Hash>
	where
		Block::Hash: FromStr,
		<Block::Hash as FromStr>::Err: Debug,
	{
		match (&self.header_at, &self.state) {
			(Some(header_at), State::Snap { .. }) => hash_of::<Block>(&header_at),
			(Some(header_at), State::Live { .. }) => {
				log::warn!(target: LOG_TARGET, "--header-at is provided while state type is live, this will most likely lead to a nonsensical result.");
				hash_of::<Block>(&header_at)
			},
			(None, State::Live { at, .. }) => hash_of::<Block>(&at),
			(None, State::Snap { .. }) => {
				panic!("either `--header-at` must be provided, or state must be `live`");
			},
		}
	}

	fn header_uri<Block: BlockT>(&self) -> String
	where
		Block::Hash: FromStr,
		<Block::Hash as FromStr>::Err: Debug,
	{
		match (&self.header_uri, &self.state) {
			(Some(header_uri), State::Snap { .. }) => header_uri.to_owned(),
			(Some(header_uri), State::Live { .. }) => {
				log::warn!(target: LOG_TARGET, "--header-uri is provided while state type is live, this will most likely lead to a nonsensical result.");
				header_uri.to_owned()
			},
			(None, State::Live { uri, .. }) => uri.clone(),
			(None, State::Snap { .. }) => {
				panic!("either `--header-uri` must be provided, or state must be `live`");
			},
		}
	}
}

pub async fn offchain_worker<Block, ExecDispatch>(
	shared: SharedParams,
	command: OffchainWorkerCmd,
	config: Configuration,
) -> sc_cli::Result<()>
where
	Block: BlockT + serde::de::DeserializeOwned,
	Block::Hash: FromStr,
	Block::Header: serde::de::DeserializeOwned,
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

	let header_at = command.header_at::<Block>()?;
	let header_uri = command.header_uri::<Block>();

	let header = rpc_api::get_header::<Block, _>(header_uri.clone(), header_at).await?;
	log::info!(
		target: LOG_TARGET,
		"fetched header from {:?}, block number: {:?}",
		header_uri,
		header.number()
	);

	check_spec_name::<Block>(header_uri, config.chain_spec.name().to_string()).await;

	let ext = {
		let builder = command
			.state
			.builder::<Block>()?
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

	let _ = StateMachine::<_, _, NumberFor<Block>, _>::new(
		&ext.backend,
		None,
		&mut changes,
		&executor,
		"OffchainWorkerApi_offchain_worker",
		header.encode().as_ref(),
		ext.extensions,
		&BackendRuntimeCode::new(&ext.backend).runtime_code()?,
		TaskExecutor::new(),
	)
	.execute(execution.into())
	.map_err(|e| format!("failed to execute 'OffchainWorkerApi_offchain_worker':  {:?}", e))?;

	log::info!(target: LOG_TARGET, "OffchainWorkerApi_offchain_worker executed without errors.");

	Ok(())
}
