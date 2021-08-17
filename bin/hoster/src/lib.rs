use num_traits::AsPrimitive;
use sc_cli::SubstrateCli;
use sc_executor::NativeExecutionDispatch;
use sp_api::ConstructRuntimeApi;
use sp_consensus_aura::sr25519::AuthorityId as AuraId;
use sp_runtime::traits::{Block as BlockT, Header as HeaderT};
use sp_transaction_pool::runtime_api::TaggedTransactionQueue;
use std::{marker::Unpin, str::FromStr};

type StateBackend<Block> =
	sc_client_db::SyncingCachingState<sc_client_db::RefTrackingState<Block>, Block>;

mod service_functions;

use service_functions::{new_full_aura, new_full_babe};

#[derive(structopt::StructOpt)]
struct Cli<GenesisConfig, Extension = sc_chain_spec::NoExtension> {
	#[structopt(skip)]
	_phantom: std::marker::PhantomData<(GenesisConfig, Extension)>,
	#[structopt(flatten)]
	run: sc_cli::RunCmd,
}

impl<GenesisConfig, Extension> SubstrateCli for Cli<GenesisConfig, Extension>
where
	GenesisConfig: sc_chain_spec::RuntimeGenesis + 'static,
	Extension:
		sp_runtime::DeserializeOwned + Send + Sync + sc_service::ChainSpecExtension + 'static,
{
	fn impl_name() -> String {
		"Runtime Hoster".into()
	}

	fn impl_version() -> String {
		Default::default()
	}

	fn description() -> String {
		env!("CARGO_PKG_DESCRIPTION").into()
	}

	fn author() -> String {
		env!("CARGO_PKG_AUTHORS").into()
	}

	fn support_url() -> String {
		"https://github.com/paritytech/substrate/issues/new".into()
	}

	fn copyright_start_year() -> i32 {
		2017
	}

	fn load_spec(&self, id: &str) -> std::result::Result<Box<dyn sc_service::ChainSpec>, String> {
		Ok(Box::new(sc_chain_spec::GenericChainSpec::<GenesisConfig, Extension>::from_json_file(
			std::path::PathBuf::from(id),
		)?))
	}

	fn native_runtime_version(
		_: &Box<dyn sc_chain_spec::ChainSpec>,
	) -> &'static sp_api::RuntimeVersion {
		&sp_api::RuntimeVersion {
			spec_name: sp_runtime::RuntimeString::Borrowed(""),
			impl_name: sp_runtime::RuntimeString::Borrowed(""),
			authoring_version: 0,
			spec_version: 0,
			impl_version: 0,
			apis: std::borrow::Cow::Borrowed(&[]),
			transaction_version: 0,
		}
	}
}

pub struct Builder<Block, RuntimeApi, Executor, GenesisConfig, Extension> {
	_phantom: std::marker::PhantomData<(Block, RuntimeApi, Executor, GenesisConfig, Extension)>,
}

impl<Block, RuntimeApi, Executor, GenesisConfig, Extension>
	Builder<Block, RuntimeApi, Executor, GenesisConfig, Extension>
{
	pub fn new() -> Self {
		Self { _phantom: Default::default() }
	}

	pub fn with_babe_consensus(
		self,
	) -> BabeBuilder<Block, RuntimeApi, Executor, GenesisConfig, Extension> {
		BabeBuilder { _phantom: self._phantom }
	}

	pub fn with_aura_consensus(
		self,
	) -> AuraBuilder<Block, RuntimeApi, Executor, GenesisConfig, Extension> {
		AuraBuilder { _phantom: self._phantom }
	}
}

pub struct BabeBuilder<Block, RuntimeApi, Executor, GenesisConfig, Extension> {
	_phantom: std::marker::PhantomData<(Block, RuntimeApi, Executor, GenesisConfig, Extension)>,
}

impl<Block, RuntimeApi, Executor, GenesisConfig, Extension>
	BabeBuilder<Block, RuntimeApi, Executor, GenesisConfig, Extension>
{
	pub fn run(self) -> Result<(), sc_cli::Error>
	where
		Block: BlockT + Unpin,
		<Block as BlockT>::Hash: FromStr + Unpin,
		<Block as BlockT>::Header: Unpin,
		<<Block as BlockT>::Header as HeaderT>::Number: AsPrimitive<usize>,
		Executor: NativeExecutionDispatch + 'static,
		RuntimeApi: ConstructRuntimeApi<Block, sc_service::TFullClient<Block, RuntimeApi, Executor>>
			+ Send
			+ Sync
			+ 'static,
		<RuntimeApi as ConstructRuntimeApi<
			Block,
			sc_service::TFullClient<Block, RuntimeApi, Executor>,
		>>::RuntimeApi: TaggedTransactionQueue<Block>
			+ sp_consensus_babe::BabeApi<Block>
			+ sp_block_builder::BlockBuilder<Block>
			+ sp_api::ApiExt<Block, StateBackend = StateBackend<Block>>
			+ sc_finality_grandpa::GrandpaApi<Block>
			+ sp_offchain::OffchainWorkerApi<Block>
			+ sp_api::Metadata<Block>
			+ sp_session::SessionKeys<Block>
			+ sp_authority_discovery::AuthorityDiscoveryApi<Block>,
		GenesisConfig: sc_chain_spec::RuntimeGenesis + 'static,
		Extension:
			sp_runtime::DeserializeOwned + Send + Sync + sc_service::ChainSpecExtension + 'static,
	{
		let cli = Cli::<GenesisConfig, Extension>::from_args();

		let runner = cli.create_runner(&cli.run)?;
		runner.run_node_until_exit(|config| async move {
			new_full_babe::<Block, RuntimeApi, Executor>(config)
		})?;

		Ok(())
	}
}

pub struct AuraBuilder<Block, RuntimeApi, Executor, GenesisConfig, Extension> {
	_phantom: std::marker::PhantomData<(Block, RuntimeApi, Executor, GenesisConfig, Extension)>,
}

impl<Block, RuntimeApi, Executor, GenesisConfig, Extension>
	AuraBuilder<Block, RuntimeApi, Executor, GenesisConfig, Extension>
{
	pub fn run(self) -> Result<(), sc_cli::Error>
	where
		Block: BlockT + Unpin,
		<Block as BlockT>::Hash: FromStr + Unpin,
		<Block as BlockT>::Header: Unpin,
		<<Block as BlockT>::Header as HeaderT>::Number: AsPrimitive<usize>,
		Executor: NativeExecutionDispatch + 'static,
		RuntimeApi: ConstructRuntimeApi<Block, sc_service::TFullClient<Block, RuntimeApi, Executor>>
			+ Send
			+ Sync
			+ 'static,
		<RuntimeApi as ConstructRuntimeApi<
			Block,
			sc_service::TFullClient<Block, RuntimeApi, Executor>,
		>>::RuntimeApi: TaggedTransactionQueue<Block>
			+ sp_consensus_aura::AuraApi<Block, AuraId>
			+ sp_block_builder::BlockBuilder<Block>
			+ sp_api::ApiExt<Block, StateBackend = StateBackend<Block>>
			+ sc_finality_grandpa::GrandpaApi<Block>
			+ sp_offchain::OffchainWorkerApi<Block>
			+ sp_api::Metadata<Block>
			+ sp_session::SessionKeys<Block>
			+ sp_authority_discovery::AuthorityDiscoveryApi<Block>,
		GenesisConfig: sc_chain_spec::RuntimeGenesis + 'static,
		Extension:
			sp_runtime::DeserializeOwned + Send + Sync + sc_service::ChainSpecExtension + 'static,
	{
		let cli = Cli::<GenesisConfig, Extension>::from_args();

		let runner = cli.create_runner(&cli.run)?;
		runner.run_node_until_exit(|config| async move {
			new_full_aura::<Block, RuntimeApi, Executor>(config)
		})?;

		Ok(())
	}
}
