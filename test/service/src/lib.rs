// Copyright 2019-2021 Parity Technologies (UK) Ltd.
// This file is part of Cumulus.

// Cumulus is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Cumulus is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Cumulus.  If not, see <http://www.gnu.org/licenses/>.

//! Crate used for testing with Cumulus.

#![warn(missing_docs)]

mod chain_spec;
mod genesis;

use core::future::Future;
//use cumulus_client_consensus_common::{ParachainCandidate, ParachainConsensus};
//use cumulus_client_network::BlockAnnounceValidator;

use cumulus_test_runtime::{Hash, NodeBlock as Block, RuntimeApi};
use frame_system_rpc_runtime_api::AccountNonceApi;
use sc_client_api::execution_extensions::ExecutionStrategies;
use sc_network::{config::TransportConfig, multiaddr, NetworkService};
use sc_service::{
	config::{
		DatabaseSource, KeepBlocks, KeystoreConfig, MultiaddrWithPeerId, NetworkConfiguration,
		OffchainWorkerConfig, PruningMode, TransactionStorageMode, WasmExecutionMethod,
	},
	BasePath, ChainSpec, Configuration, Error as ServiceError, PartialComponents, Role,
	RpcHandlers, TFullBackend, TFullClient, TaskManager,
};
use sp_arithmetic::traits::SaturatedConversion;
use sp_blockchain::HeaderBackend;
use sp_core::{Pair, H256};
use sp_keyring::Sr25519Keyring;
use sp_runtime::{codec::Encode, generic, traits::BlakeTwo256};
use sp_state_machine::BasicExternalities;
use sp_trie::PrefixedMemoryDB;
use std::sync::Arc;
use substrate_test_client::{
	
	BlockchainEventsExt, RpcHandlersExt, RpcTransactionError, RpcTransactionOutput,
};
use sp_api::ProvideRuntimeApi;
use sp_api::BlockT;
pub use chain_spec::*;
pub use cumulus_test_runtime as runtime;
pub use genesis::*;
pub use sp_keyring::Sr25519Keyring as Keyring;
use std::marker::PhantomData;
use sc_consensus::BlockImport;
use sc_client_api::BlockBackend;
use sc_client_api::UsageProvider;
use sc_client_api::Finalizer;
use sc_client_api::BlockchainEvents;
use sc_client_api::{
	backend::{Backend as BackendT},
};
use sc_client_api::ExecutorProvider;
//use sc_executor::NativeElseWasmExecutor;
/// A consensus that will never produce any block.
#[derive(Clone)]
struct NullConsensus;

// #[async_trait::async_trait]
// impl ParachainConsensus<Block> for NullConsensus {
// 	async fn produce_candidate(
// 		&mut self,
// 		_: &Header,
// 		_: PHash,
// 		_: &PersistedValidationData,
// 	) -> Option<ParachainCandidate<Block>> {
// 		None
// 	}
// }

/// The signature of the announce block fn.
pub type AnnounceBlockFn = Arc<dyn Fn(Hash, Option<Vec<u8>>) + Send + Sync>;

/// Native executor instance.
pub struct RuntimeExecutor;

impl sc_executor::NativeExecutionDispatch for RuntimeExecutor {
	type ExtendHostFunctions = ();

	fn dispatch(method: &str, data: &[u8]) -> Option<Vec<u8>> {
		cumulus_test_runtime::api::dispatch(method, data)
	}

	fn native_version() -> sc_executor::NativeVersion {
		cumulus_test_runtime::native_version()
	}
}

/// The client type being used by the test service.
pub type Client = TFullClient<
	runtime::NodeBlock,
	runtime::RuntimeApi,
	sc_executor::NativeElseWasmExecutor<RuntimeExecutor>,
>;

/// Transaction pool type used by the test service
pub type TransactionPool = Arc<sc_transaction_pool::FullPool<Block, Client>>;

/// Starts a `ServiceBuilder` for a full service.
///
/// Use this macro if you don't actually need the full service, but just the builder in order to
/// be able to perform chain operations.
pub fn new_partial(
	config: &mut Configuration,
) -> Result<
	PartialComponents<
		Client,
		TFullBackend<Block>,
		(),
		sc_consensus::import_queue::BasicQueue<Block, PrefixedMemoryDB<BlakeTwo256>>,
		sc_transaction_pool::FullPool<Block, Client>,
		(),
	>,
	sc_service::Error,
> {
	let executor = sc_executor::NativeElseWasmExecutor::<RuntimeExecutor>::new(
		config.wasm_method,
		config.default_heap_pages,
		config.max_runtime_instances,
	);

	let (client, backend, keystore_container, task_manager) =
		sc_service::new_full_parts::<Block, RuntimeApi, _>(&config, None, executor)?;
	let client = Arc::new(client);

	let registry = config.prometheus_registry();

	let transaction_pool = sc_transaction_pool::BasicPool::new_full(
		config.transaction_pool.clone(),
		config.role.is_authority().into(),
		config.prometheus_registry(),
		task_manager.spawn_essential_handle(),
		client.clone(),
	);

	let select_chain = sc_consensus::LongestChain::new(backend.clone());
	let (grandpa_block_import, grandpa_link) = grandpa::block_import(
		client.clone(),
		&(client.clone() as Arc<_>),
		select_chain.clone(),
		None//telemetry.as_ref().map(|x| x.handle()),
	)?;

	let (block_import, babe_link) = sc_consensus_babe::block_import(
		sc_consensus_babe::Config::get_or_compute(&*client)?,
		grandpa_block_import,
		client.clone(),
	)?;

	let import_queue = sc_consensus_babe::import_queue(
		babe_link,
		block_import,
		None,
		client.clone(),
		select_chain,
		|_, _| async { Ok(sp_timestamp::InherentDataProvider::from_system_time()) },
		&task_manager.spawn_essential_handle(),
		registry.clone(),
		sp_consensus::CanAuthorWithNativeVersion::new(
			client.executor().clone(),
		),
		None
	)?;

	let params = PartialComponents {
		backend,
		client,
		import_queue,
		keystore_container,
		task_manager,
		transaction_pool,
		select_chain: (),
		other: (),
	};

	Ok(params)
}

/// Prepare the parachain's node condifugration
///
/// This function will disable the default announcement of Substrate for the parachain in favor
/// of the one of Cumulus.
pub fn prepare_node_config(mut parachain_config: Configuration) -> Configuration {
	parachain_config.announce_block = false;

	parachain_config
}


/// Parameters given to [`start_full_node`].
pub struct StartFullNodeParams<'a, Block: BlockT, Client> {
	pub client: Arc<Client>,
	//pub relay_chain_full_node: RFullNode<PClient>,
	pub task_manager: &'a mut TaskManager,
	pub announce_block: Arc<dyn Fn(Block::Hash, Option<Vec<u8>>) + Send + Sync>,
}

struct StartConsensus<'a, Block: BlockT, Client, Backend> {
	announce_block: Arc<dyn Fn(Block::Hash, Option<Vec<u8>>) + Send + Sync>,
	client: Arc<Client>,
	task_manager: &'a mut TaskManager,
	_phantom: PhantomData<Backend>,
}


// /// Execute something with the client instance.
// ///
// /// As there exist multiple chains inside Polkadot, like Polkadot itself, Kusama, Westend etc,
// /// there can exist different kinds of client types. As these client types differ in the generics
// /// that are being used, we can not easily return them from a function. For returning them from a
// /// function there exists [`Client`]. However, the problem on how to use this client instance still
// /// exists. This trait "solves" it in a dirty way. It requires a type to implement this trait and
// /// than the [`execute_with_client`](ExecuteWithClient::execute_with_client) function can be called
// /// with any possible client instance.
// ///
// /// In a perfect world, we could make a closure work in this way.
// pub trait ExecuteWithClient {
// 	/// The return type when calling this instance.
// 	type Output;

// 	/// Execute whatever should be executed with the given client instance.
// 	fn execute_with_client<Client, Api, Backend>(self, client: Arc<Client>) -> Self::Output
// 	where
// 		<Api as sp_api::ApiExt<Block>>::StateBackend: sp_api::StateBackend<BlakeTwo256>,
// 		Backend: sc_client_api::Backend<Block> + 'static,
// 		Backend::State: sp_api::StateBackend<BlakeTwo256>,
// 		//Api: crate::RuntimeApiCollection<StateBackend = Backend::State>,
// 		//Client: AbstractClient<Block, Backend, Api = Api> + 'static;
// 		Api: sp_api::ApiExt<sp_runtime::generic::Block<sp_runtime::generic::Header<u32, sp_runtime::traits::BlakeTwo256>, sp_runtime::OpaqueExtrinsic>>;
// }


// /// A handle to a Polkadot client instance.
// ///
// /// The Polkadot service supports multiple different runtimes (Westend, Polkadot itself, etc). As each runtime has a
// /// specialized client, we need to hide them behind a trait. This is this trait.
// ///
// /// When wanting to work with the inner client, you need to use `execute_with`.
// ///
// /// See [`ExecuteWithClient`](trait.ExecuteWithClient.html) for more information.
// pub trait ClientHandle {
// 	/// Execute the given something with the client.
// 	fn execute_with<T: ExecuteWithClient>(&self, t: T) -> T::Output;
// }

// /// A wrapper for the test client that implements `ClientHandle`.
// pub struct TestClient(pub Arc<Client>);

// impl ClientHandle for TestClient {
// 	fn execute_with<T: ExecuteWithClient>(&self, t: T) -> T::Output {
// 		T::execute_with_client::<_, _, sc_service::TFullBackend<Block>>(t, self.0.clone())
// 	}
// }

/// Start a full node for a parachain.
///
/// A full node will only sync the given parachain and will follow the
/// tip of the chain.
pub fn start_full_node<Block, Client, Backend>(
	StartFullNodeParams {
		client,
		announce_block,
		task_manager,
		//relay_chain_full_node,
	}: StartFullNodeParams<Block, Client>,
) -> sc_service::error::Result<()>
where
	Block: BlockT,
	Client: Finalizer<Block, Backend>
		+ UsageProvider<Block>
		+ Send
		+ Sync
		+ BlockBackend<Block>
		+ BlockchainEvents<Block>
		+ 'static,
	for<'a> &'a Client: BlockImport<Block>,
	Backend: BackendT<Block> + 'static,
	//PClient: ClientHandle,
{
	//TODO????
	// (*client).execute_with(StartConsensus {
	// 	announce_block,
	// 	client,
	// 	task_manager,
	// 	_phantom: PhantomData,
	// });

	//task_manager.add_child(relay_chain_full_node.relay_chain_full_node.task_manager);

	Ok(())
}


/// Start a node with the given parachain `Configuration` and relay chain `Configuration`.
///
/// This is the actual implementation that is abstract over the executor and the runtime api.
async fn start_node_impl<RB>(
	parachain_config: Configuration,
	
	
	wrap_announce_block: Option<Box<dyn FnOnce(AnnounceBlockFn) -> AnnounceBlockFn>>,
	rpc_ext_builder: RB,
	consensus: Consensus,
) -> sc_service::error::Result<(
	TaskManager,
	Arc<Client>,
	Arc<NetworkService<Block, H256>>,
	RpcHandlers,
	TransactionPool,
)>
where
	RB: Fn(Arc<Client>) -> Result<jsonrpc_core::IoHandler<sc_rpc::Metadata>, sc_service::Error>
		+ Send
		+ 'static,
{
	if matches!(parachain_config.role, Role::Light) {
		return Err("Light client not supported!".into())
	}


	//let builder = TestClientBuilder::default();
	//let (client, fork_choice_rule) = builder.build_with_executor(NativeElseWasmExecutor::new(WasmExecutionMethod::Interpreted, None, 8));


	let mut parachain_config = prepare_node_config(parachain_config);

	let params = new_partial(&mut parachain_config)?;

	let transaction_pool = params.transaction_pool;
	let mut task_manager = params.task_manager;

	// let relay_chain_full_node = polkadot_test_service::new_full(
	// 	relay_chain_config,
	// 	if let Some(ref key) = collator_key {
	// 		polkadot_service::IsCollator::Yes(key.clone())
	// 	} else {
	// 		polkadot_service::IsCollator::No
	// 	},
	// 	None,
	// )
	// .map_err(|e| match e {
	// 	polkadot_service::Error::Sub(x) => x,
	// 	s => format!("{}", s).into(),
	// })?;

	let client = params.client.clone();
	
	//let backend = builder.backend(); //params.backend.clone();
	// let block_announce_validator = BlockAnnounceValidator::new(
	// 	relay_chain_full_node.client.clone(),
	// 	para_id,
	// 	Box::new(relay_chain_full_node.network.clone()),
	// 	relay_chain_full_node.backend.clone(),
	// 	relay_chain_full_node.client.clone(),
	// );
	//let block_announce_validator_builder = move |_| Box::new(block_announce_validator) as Box<_>;

	let prometheus_registry = parachain_config.prometheus_registry().cloned();
	let import_queue = params.import_queue;
	let (network, system_rpc_tx, start_network) =
		sc_service::build_network(sc_service::BuildNetworkParams {
			config: &parachain_config,
			client: client.clone(),
			transaction_pool: transaction_pool.clone(),
			spawn_handle: task_manager.spawn_handle(),
			import_queue: import_queue,
			//on_demand: None,
			block_announce_validator_builder: None, //Some(Box::new(block_announce_validator_builder)),
			warp_sync: None,
		})?;

	let rpc_extensions_builder = {
		let client = client.clone();

		Box::new(move |_, _| rpc_ext_builder(client.clone()))
	};

	let rpc_handlers = sc_service::spawn_tasks(sc_service::SpawnTasksParams {
		//on_demand: None,
		//remote_blockchain: None,
		rpc_extensions_builder,
		client: client.clone(),
		transaction_pool: transaction_pool.clone(),
		task_manager: &mut task_manager,
		config: parachain_config,
		keystore: params.keystore_container.sync_keystore(),
		backend: params.backend.clone(),
		network: network.clone(),
		system_rpc_tx,
		telemetry: None,
	})?;

	let announce_block = {
		let network = network.clone();
		Arc::new(move |hash, data| network.announce_block(hash, data))
	};

	let announce_block = wrap_announce_block
		.map(|w| (w)(announce_block.clone()))
		.unwrap_or_else(|| announce_block);


	// let relay_chain_full_node =
	// 	relay_chain_full_node.with_client(substrate_test_service::TestClient);

	let params = StartFullNodeParams {
		client: client.clone(),
		announce_block,
		task_manager: &mut task_manager,
		
	};

	start_full_node(params)?;
	

	start_network.start_network();

	Ok((task_manager, client, network, rpc_handlers, transaction_pool))
}

/// A Cumulus test node instance used for testing.
pub struct TestNode {
	/// TaskManager's instance.
	pub task_manager: TaskManager,
	/// Client's instance.
	pub client: Arc<Client>,
	/// Node's network.
	pub network: Arc<NetworkService<Block, H256>>,
	/// The `MultiaddrWithPeerId` to this node. This is useful if you want to pass it as "boot node"
	/// to other nodes.
	pub addr: MultiaddrWithPeerId,
	/// RPCHandlers to make RPC queries.
	pub rpc_handlers: RpcHandlers,
	/// Node's transaction pool
	pub transaction_pool: TransactionPool,
}

enum Consensus {
	/// Use the relay-chain provided consensus.
	RelayChain,
	/// Use the null consensus that will never produce any block.
	Null,
}

/// A builder to create a [`TestNode`].
pub struct TestNodeBuilder {
	tokio_handle: tokio::runtime::Handle,
	key: Sr25519Keyring,
	parachain_nodes: Vec<MultiaddrWithPeerId>,
	wrap_announce_block: Option<Box<dyn FnOnce(AnnounceBlockFn) -> AnnounceBlockFn>>,
	storage_update_func_parachain: Option<Box<dyn Fn()>>,
	storage_update_func_relay_chain: Option<Box<dyn Fn()>>,
	consensus: Consensus,
}

impl TestNodeBuilder {
	/// Create a new instance of `Self`.
	///
	/// `para_id` - The parachain id this node is running for.
	/// `tokio_handle` - The tokio handler to use.
	/// `key` - The key that will be used to generate the name and that will be passed as `dev_seed`.
	pub fn new(tokio_handle: tokio::runtime::Handle, key: Sr25519Keyring) -> Self {
		TestNodeBuilder {
			key,
			tokio_handle,
			parachain_nodes: Vec::new(),
			wrap_announce_block: None,
			storage_update_func_parachain: None,
			storage_update_func_relay_chain: None,
			consensus: Consensus::RelayChain,
		}
	}

	/// Make the node connect to the given parachain node.
	///
	/// By default the node will not be connected to any node or will be able to discover any other
	/// node.
	pub fn connect_to_parachain_node(mut self, node: &TestNode) -> Self {
		self.parachain_nodes.push(node.addr.clone());
		self
	}

	/// Make the node connect to the given parachain nodes.
	///
	/// By default the node will not be connected to any node or will be able to discover any other
	/// node.
	pub fn connect_to_parachain_nodes<'a>(
		mut self,
		nodes: impl Iterator<Item = &'a TestNode>,
	) -> Self {
		self.parachain_nodes.extend(nodes.map(|n| n.addr.clone()));
		self
	}

	/// Wrap the announce block function of this node.
	pub fn wrap_announce_block(
		mut self,
		wrap: impl FnOnce(AnnounceBlockFn) -> AnnounceBlockFn + 'static,
	) -> Self {
		self.wrap_announce_block = Some(Box::new(wrap));
		self
	}

	/// Allows accessing the parachain storage before the test node is built.
	pub fn update_storage_parachain(mut self, updater: impl Fn() + 'static) -> Self {
		self.storage_update_func_parachain = Some(Box::new(updater));
		self
	}

	/// Allows accessing the relay chain storage before the test node is built.
	pub fn update_storage_relay_chain(mut self, updater: impl Fn() + 'static) -> Self {
		self.storage_update_func_relay_chain = Some(Box::new(updater));
		self
	}

	/// Use the null consensus that will never author any block.
	pub fn use_null_consensus(mut self) -> Self {
		self.consensus = Consensus::Null;
		self
	}

	/// Build the [`TestNode`].
	pub async fn build(self) -> TestNode {
		let parachain_config = node_config(
			self.storage_update_func_parachain.unwrap_or_else(|| Box::new(|| ())),
			self.tokio_handle.clone(),
			self.key.clone(),
			self.parachain_nodes,
			true
		)
		.expect("could not generate Configuration");
		

		let multiaddr = parachain_config.network.listen_addresses[0].clone();
		let (task_manager, client, network, rpc_handlers, transaction_pool) = start_node_impl(
			parachain_config,
			
		
			self.wrap_announce_block,
			|_| Ok(Default::default()),
			self.consensus,
		)
		.await
		.expect("could not create Cumulus test service");

		let peer_id = network.local_peer_id().clone();
		let addr = MultiaddrWithPeerId { multiaddr, peer_id };

		TestNode { task_manager, client, network, addr, rpc_handlers, transaction_pool }
	}
}

/// Create a Cumulus `Configuration`.
///
/// By default an in-memory socket will be used, therefore you need to provide nodes if you want the
/// node to be connected to other nodes. If `nodes_exclusive` is `true`, the node will only connect
/// to the given `nodes` and not to any other node. The `storage_update_func` can be used to make
/// adjustments to the runtime genesis.
pub fn node_config(
	storage_update_func: impl Fn(),
	tokio_handle: tokio::runtime::Handle,
	key: Sr25519Keyring,
	nodes: Vec<MultiaddrWithPeerId>,
	nodes_exlusive: bool,
) -> Result<Configuration, ServiceError> {
	let base_path = BasePath::new_temp_dir()?;
	let root = base_path.path().to_path_buf();
	let role = Role::Full;
	let key_seed = key.to_seed();
	let mut spec = Box::new(chain_spec::get_chain_spec());

	let mut storage = spec.as_storage_builder().build_storage().expect("could not build storage");

	BasicExternalities::execute_with_storage(&mut storage, storage_update_func);
	spec.set_storage(storage);

	let mut network_config = NetworkConfiguration::new(
		format!("{} (parachain)", key_seed.to_string()),
		"network/test/0.1",
		Default::default(),
		None,
	);

	if nodes_exlusive {
		network_config.default_peers_set.reserved_nodes = nodes;
		network_config.default_peers_set.non_reserved_mode =
			sc_network::config::NonReservedPeerMode::Deny;
	} else {
		network_config.boot_nodes = nodes;
	}

	network_config.allow_non_globals_in_dht = true;

	network_config
		.listen_addresses
		.push(multiaddr::Protocol::Memory(rand::random()).into());

	network_config.transport = TransportConfig::MemoryOnly;

	Ok(Configuration {
		impl_name: "cumulus-test-node".to_string(),
		impl_version: "0.1".to_string(),
		role,
		tokio_handle,
		transaction_pool: Default::default(),
		network: network_config,
		keystore: KeystoreConfig::InMemory,
		keystore_remote: Default::default(),
		database: DatabaseSource::RocksDb { path: root.join("db"), cache_size: 128 },
		state_cache_size: 67108864,
		state_cache_child_ratio: None,
		state_pruning: PruningMode::ArchiveAll,
		keep_blocks: KeepBlocks::All,
		transaction_storage: TransactionStorageMode::BlockBody,
		chain_spec: spec,
		wasm_method: WasmExecutionMethod::Interpreted,
		// NOTE: we enforce the use of the native runtime to make the errors more debuggable
		execution_strategies: ExecutionStrategies {
			syncing: sc_client_api::ExecutionStrategy::NativeWhenPossible,
			importing: sc_client_api::ExecutionStrategy::NativeWhenPossible,
			block_construction: sc_client_api::ExecutionStrategy::NativeWhenPossible,
			offchain_worker: sc_client_api::ExecutionStrategy::NativeWhenPossible,
			other: sc_client_api::ExecutionStrategy::NativeWhenPossible,
		},
		rpc_http: None,
		rpc_ws: None,
		rpc_ipc: None,
		rpc_ws_max_connections: None,
		rpc_cors: None,
		rpc_methods: Default::default(),
		rpc_max_payload: None,
		ws_max_out_buffer_capacity: None,
		prometheus_config: None,
		telemetry_endpoints: None,
		default_heap_pages: None,
		offchain_worker: OffchainWorkerConfig { enabled: true, indexing_enabled: false },
		force_authoring: false,
		disable_grandpa: false,
		dev_key_seed: Some(key_seed),
		tracing_targets: None,
		tracing_receiver: Default::default(),
		max_runtime_instances: 8,
		announce_block: true,
		base_path: Some(base_path),
		informant_output_format: Default::default(),
		wasm_runtime_overrides: None,
	})
}

impl TestNode {
	/// Wait for `count` blocks to be imported in the node and then exit. This function will not
	/// return if no blocks are ever created, thus you should restrict the maximum amount of time of
	/// the test execution.
	pub fn wait_for_blocks(&self, count: usize) -> impl Future<Output = ()> {
		self.client.wait_for_blocks(count)
	}

	/// Send an extrinsic to this node.
	pub async fn send_extrinsic(
		&self,
		function: impl Into<runtime::Call>,
		caller: Sr25519Keyring,
	) -> Result<RpcTransactionOutput, RpcTransactionError> {
		let extrinsic = construct_extrinsic(&*self.client, function, caller.pair(), Some(0));

		self.rpc_handlers.send_transaction(extrinsic.into()).await
	}

	/// Register a parachain at this relay chain.
	pub async fn schedule_upgrade(&self, validation: Vec<u8>) -> Result<(), RpcTransactionError> {
		let call = frame_system::Call::set_code { code: validation };

		self.send_extrinsic(
			runtime::SudoCall::sudo_unchecked_weight { call: Box::new(call.into()), weight: 1_000 },
			Sr25519Keyring::Alice,
		)
		.await
		.map(drop)
	}
}

/// Fetch account nonce for key pair
pub fn fetch_nonce(client: &Client, account: sp_core::sr25519::Public) -> u32 {
	let best_hash = client.chain_info().best_hash;
	client
		.runtime_api()
		.account_nonce(&generic::BlockId::Hash(best_hash), account.into())
		.expect("Fetching account nonce works; qed")
}

/// Construct an extrinsic that can be applied to the test runtime.
pub fn construct_extrinsic(
	client: &Client,
	function: impl Into<runtime::Call>,
	caller: sp_core::sr25519::Pair,
	nonce: Option<u32>,
) -> runtime::UncheckedExtrinsic {
	let function = function.into();
	let current_block_hash = client.info().best_hash;
	let current_block = client.info().best_number.saturated_into();
	let genesis_block = client.hash(0).unwrap().unwrap();
	let nonce = nonce.unwrap_or_else(|| fetch_nonce(client, caller.public()));
	let period = runtime::BlockHashCount::get()
		.checked_next_power_of_two()
		.map(|c| c / 2)
		.unwrap_or(2) as u64;
	let tip = 0;
	let extra: runtime::SignedExtra = (
		frame_system::CheckSpecVersion::<runtime::Runtime>::new(),
		frame_system::CheckGenesis::<runtime::Runtime>::new(),
		frame_system::CheckEra::<runtime::Runtime>::from(generic::Era::mortal(
			period,
			current_block,
		)),
		frame_system::CheckNonce::<runtime::Runtime>::from(nonce),
		frame_system::CheckWeight::<runtime::Runtime>::new(),
		// pallet_transaction_payment::ChargeTransactionPayment::<runtime::Runtime>::from(tip),
	);
	let raw_payload = runtime::SignedPayload::from_raw(
		function.clone(),
		extra.clone(),
		(runtime::VERSION.spec_version, genesis_block, current_block_hash, (), ()),
	);
	let signature = raw_payload.using_encoded(|e| caller.sign(e));
	runtime::UncheckedExtrinsic::new_signed(
		function.clone(),
		caller.public().into(),
		runtime::Signature::Sr25519(signature.clone()),
		extra.clone(),
	)
}