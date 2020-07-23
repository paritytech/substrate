// This file is part of Substrate.

// Copyright (C) 2017-2020 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

use crate::{
	NetworkStatus, NetworkState, error::Error, DEFAULT_PROTOCOL_ID, MallocSizeOfWasm,
	start_rpc_servers, build_network_future, TransactionPoolAdapter, TaskManager, SpawnTaskHandle,
	status_sinks, metrics::MetricsService,
	client::{light, Client, ClientConfig},
	config::{Configuration, KeystoreConfig, PrometheusConfig, OffchainWorkerConfig},
};
use sc_client_api::{
	light::RemoteBlockchain, ForkBlocks, BadBlocks, CloneableSpawn, UsageProvider,
	ExecutorProvider,
};
use sp_utils::mpsc::{tracing_unbounded, TracingUnboundedSender, TracingUnboundedReceiver};
use sc_chain_spec::get_extension;
use sp_consensus::{
	block_validation::{BlockAnnounceValidator, DefaultBlockAnnounceValidator, Chain},
	import_queue::ImportQueue,
};
use futures::{
	Future, FutureExt, StreamExt,
	future::ready,
};
use jsonrpc_pubsub::manager::SubscriptionManager;
use sc_keystore::Store as Keystore;
use log::{info, warn, error};
use sc_network::config::{Role, FinalityProofProvider, OnDemand, BoxFinalityProofRequestBuilder};
use sc_network::NetworkService;
use parking_lot::{Mutex, RwLock};
use sp_runtime::generic::BlockId;
use sp_runtime::traits::{
	Block as BlockT, SaturatedConversion, HashFor, Zero, BlockIdTo,
};
use sp_api::{ProvideRuntimeApi, CallApiAt};
use sc_executor::{NativeExecutor, NativeExecutionDispatch, RuntimeInfo};
use std::{collections::HashMap, sync::Arc, pin::Pin};
use wasm_timer::SystemTime;
use sc_telemetry::{telemetry, SUBSTRATE_INFO};
use sp_transaction_pool::MaintainedTransactionPool;
use prometheus_endpoint::Registry;
use sc_client_db::{Backend, DatabaseSettings};
use sp_core::traits::CodeExecutor;
use sp_runtime::BuildStorage;
use sc_client_api::{
	BlockBackend, BlockchainEvents,
	backend::StorageProvider,
	proof_provider::ProofProvider,
	execution_extensions::ExecutionExtensions
};
use sp_blockchain::{HeaderMetadata, HeaderBackend};
use crate::{ServiceComponents, TelemetryOnConnectSinks, RpcHandlers, NetworkStatusSinks};

/// A utility trait for building an RPC extension given a `DenyUnsafe` instance.
/// This is useful since at service definition time we don't know whether the
/// specific interface where the RPC extension will be exposed is safe or not.
/// This trait allows us to lazily build the RPC extension whenever we bind the
/// service to an interface.
pub trait RpcExtensionBuilder {
	/// The type of the RPC extension that will be built.
	type Output: sc_rpc::RpcExtension<sc_rpc::Metadata>;

	/// Returns an instance of the RPC extension for a particular `DenyUnsafe`
	/// value, e.g. the RPC extension might not expose some unsafe methods.
	fn build(&self, deny: sc_rpc::DenyUnsafe) -> Self::Output;
}

impl<F, R> RpcExtensionBuilder for F where
	F: Fn(sc_rpc::DenyUnsafe) -> R,
	R: sc_rpc::RpcExtension<sc_rpc::Metadata>,
{
	type Output = R;

	fn build(&self, deny: sc_rpc::DenyUnsafe) -> Self::Output {
		(*self)(deny)
	}
}

/// A utility struct for implementing an `RpcExtensionBuilder` given a cloneable
/// `RpcExtension`, the resulting builder will simply ignore the provided
/// `DenyUnsafe` instance and return a static `RpcExtension` instance.
pub struct NoopRpcExtensionBuilder<R>(pub R);

impl<R> RpcExtensionBuilder for NoopRpcExtensionBuilder<R> where
	R: Clone + sc_rpc::RpcExtension<sc_rpc::Metadata>,
{
	type Output = R;

	fn build(&self, _deny: sc_rpc::DenyUnsafe) -> Self::Output {
		self.0.clone()
	}
}

impl<R> From<R> for NoopRpcExtensionBuilder<R> where
	R: sc_rpc::RpcExtension<sc_rpc::Metadata>,
{
	fn from(e: R) -> NoopRpcExtensionBuilder<R> {
		NoopRpcExtensionBuilder(e)
	}
}


/// Full client type.
pub type TFullClient<TBl, TRtApi, TExecDisp> = Client<
	TFullBackend<TBl>,
	TFullCallExecutor<TBl, TExecDisp>,
	TBl,
	TRtApi,
>;

/// Full client backend type.
pub type TFullBackend<TBl> = sc_client_db::Backend<TBl>;

/// Full client call executor type.
pub type TFullCallExecutor<TBl, TExecDisp> = crate::client::LocalCallExecutor<
	sc_client_db::Backend<TBl>,
	NativeExecutor<TExecDisp>,
>;

/// Light client type.
pub type TLightClient<TBl, TRtApi, TExecDisp> = TLightClientWithBackend<
	TBl, TRtApi, TExecDisp, TLightBackend<TBl>
>;

/// Light client backend type.
pub type TLightBackend<TBl> = sc_light::Backend<
	sc_client_db::light::LightStorage<TBl>,
	HashFor<TBl>,
>;

/// Light call executor type.
pub type TLightCallExecutor<TBl, TExecDisp> = sc_light::GenesisCallExecutor<
	sc_light::Backend<
		sc_client_db::light::LightStorage<TBl>,
		HashFor<TBl>
	>,
	crate::client::LocalCallExecutor<
		sc_light::Backend<
			sc_client_db::light::LightStorage<TBl>,
			HashFor<TBl>
		>,
		NativeExecutor<TExecDisp>
	>,
>;

type TFullParts<TBl, TRtApi, TExecDisp> = (
	TFullClient<TBl, TRtApi, TExecDisp>,
	Arc<TFullBackend<TBl>>,
	Arc<RwLock<sc_keystore::Store>>,
	TaskManager,
);

type TLightParts<TBl, TRtApi, TExecDisp> = (
	Arc<TLightClient<TBl, TRtApi, TExecDisp>>,
	Arc<TLightBackend<TBl>>,
	Arc<RwLock<sc_keystore::Store>>,
	TaskManager,
	Arc<OnDemand<TBl>>,
);

/// Light client backend type with a specific hash type.
pub type TLightBackendWithHash<TBl, THash> = sc_light::Backend<
	sc_client_db::light::LightStorage<TBl>,
	THash,
>;

/// Light client type with a specific backend.
pub type TLightClientWithBackend<TBl, TRtApi, TExecDisp, TBackend> = Client<
	TBackend,
	sc_light::GenesisCallExecutor<
		TBackend,
		crate::client::LocalCallExecutor<TBackend, NativeExecutor<TExecDisp>>,
	>,
	TBl,
	TRtApi,
>;

/// Creates a new full client for the given config.
pub fn new_full_client<TBl, TRtApi, TExecDisp>(
	config: &Configuration,
) -> Result<TFullClient<TBl, TRtApi, TExecDisp>, Error> where
	TBl: BlockT,
	TExecDisp: NativeExecutionDispatch + 'static,
{
	new_full_parts(config).map(|parts| parts.0)
}

/// Create the initial parts of a full node.
pub fn new_full_parts<TBl, TRtApi, TExecDisp>(
	config: &Configuration,
) -> Result<TFullParts<TBl, TRtApi, TExecDisp>,	Error> where
	TBl: BlockT,
	TExecDisp: NativeExecutionDispatch + 'static,
{
	let keystore = match &config.keystore {
		KeystoreConfig::Path { path, password } => Keystore::open(
			path.clone(),
			password.clone()
		)?,
		KeystoreConfig::InMemory => Keystore::new_in_memory(),
	};

	let task_manager = {
		let registry = config.prometheus_config.as_ref().map(|cfg| &cfg.registry);
		TaskManager::new(config.task_executor.clone(), registry)?
	};

	let executor = NativeExecutor::<TExecDisp>::new(
		config.wasm_method,
		config.default_heap_pages,
		config.max_runtime_instances,
	);

	let chain_spec = &config.chain_spec;
	let fork_blocks = get_extension::<ForkBlocks<TBl>>(chain_spec.extensions())
		.cloned()
		.unwrap_or_default();

	let bad_blocks = get_extension::<BadBlocks<TBl>>(chain_spec.extensions())
		.cloned()
		.unwrap_or_default();

	let (client, backend) = {
		let db_config = sc_client_db::DatabaseSettings {
			state_cache_size: config.state_cache_size,
			state_cache_child_ratio:
			config.state_cache_child_ratio.map(|v| (v, 100)),
			pruning: config.pruning.clone(),
			source: config.database.clone(),
		};

		let extensions = sc_client_api::execution_extensions::ExecutionExtensions::new(
			config.execution_strategies.clone(),
			Some(keystore.clone()),
		);

		new_client(
			db_config,
			executor,
			chain_spec.as_storage_builder(),
			fork_blocks,
			bad_blocks,
			extensions,
			Box::new(task_manager.spawn_handle()),
			config.prometheus_config.as_ref().map(|config| config.registry.clone()),
			ClientConfig {
				offchain_worker_enabled : config.offchain_worker.enabled ,
				offchain_indexing_api: config.offchain_worker.indexing_enabled,
			},
		)?
	};

	Ok((client, backend, keystore, task_manager))
}

/// Create the initial parts of a light node.
pub fn new_light_parts<TBl, TRtApi, TExecDisp>(
	config: &Configuration
) -> Result<TLightParts<TBl, TRtApi, TExecDisp>, Error> where
	TBl: BlockT,
	TExecDisp: NativeExecutionDispatch + 'static,
{

	let task_manager = {
		let registry = config.prometheus_config.as_ref().map(|cfg| &cfg.registry);
		TaskManager::new(config.task_executor.clone(), registry)?
	};

	let keystore = match &config.keystore {
		KeystoreConfig::Path { path, password } => Keystore::open(
			path.clone(),
			password.clone()
		)?,
		KeystoreConfig::InMemory => Keystore::new_in_memory(),
	};

	let executor = NativeExecutor::<TExecDisp>::new(
		config.wasm_method,
		config.default_heap_pages,
		config.max_runtime_instances,
	);

	let db_storage = {
		let db_settings = sc_client_db::DatabaseSettings {
			state_cache_size: config.state_cache_size,
			state_cache_child_ratio:
				config.state_cache_child_ratio.map(|v| (v, 100)),
			pruning: config.pruning.clone(),
			source: config.database.clone(),
		};
		sc_client_db::light::LightStorage::new(db_settings)?
	};
	let light_blockchain = sc_light::new_light_blockchain(db_storage);
	let fetch_checker = Arc::new(
		sc_light::new_fetch_checker::<_, TBl, _>(
			light_blockchain.clone(),
			executor.clone(),
			Box::new(task_manager.spawn_handle()),
		),
	);
	let on_demand = Arc::new(sc_network::config::OnDemand::new(fetch_checker));
	let backend = sc_light::new_light_backend(light_blockchain);
	let client = Arc::new(light::new_light(
		backend.clone(),
		config.chain_spec.as_storage_builder(),
		executor,
		Box::new(task_manager.spawn_handle()),
		config.prometheus_config.as_ref().map(|config| config.registry.clone()),
	)?);

	Ok((client, backend, keystore, task_manager, on_demand))
}

/// Create an instance of db-backed client.
pub fn new_client<E, Block, RA>(
	settings: DatabaseSettings,
	executor: E,
	genesis_storage: &dyn BuildStorage,
	fork_blocks: ForkBlocks<Block>,
	bad_blocks: BadBlocks<Block>,
	execution_extensions: ExecutionExtensions<Block>,
	spawn_handle: Box<dyn CloneableSpawn>,
	prometheus_registry: Option<Registry>,
	config: ClientConfig,
) -> Result<(
	crate::client::Client<
		Backend<Block>,
		crate::client::LocalCallExecutor<Backend<Block>, E>,
		Block,
		RA,
	>,
	Arc<Backend<Block>>,
),
	sp_blockchain::Error,
>
	where
		Block: BlockT,
		E: CodeExecutor + RuntimeInfo,
{
	const CANONICALIZATION_DELAY: u64 = 4096;

	let backend = Arc::new(Backend::new(settings, CANONICALIZATION_DELAY)?);
	let executor = crate::client::LocalCallExecutor::new(backend.clone(), executor, spawn_handle, config.clone());
	Ok((
		crate::client::Client::new(
			backend.clone(),
			executor,
			genesis_storage,
			fork_blocks,
			bad_blocks,
			execution_extensions,
			prometheus_registry,
			config,
		)?,
		backend,
	))
}

/// Parameters to pass into `build`.
pub struct ServiceParams<TBl: BlockT, TCl, TImpQu, TExPool, TRpc, Backend> {
	/// The service configuration.
	pub config: Configuration,
	/// A shared client returned by `new_full_parts`/`new_light_parts`.
	pub client: Arc<TCl>,
	/// A shared backend returned by `new_full_parts`/`new_light_parts`.
	pub backend: Arc<Backend>,
	/// A task manager returned by `new_full_parts`/`new_light_parts`.
	pub task_manager: TaskManager,
	/// A shared keystore returned by `new_full_parts`/`new_light_parts`.
	pub keystore: Arc<RwLock<Keystore>>,
	/// An optional, shared data fetcher for light clients.
	pub on_demand: Option<Arc<OnDemand<TBl>>>,
	/// An import queue.
	pub import_queue: TImpQu,
	/// An optional finality proof request builder.
	pub finality_proof_request_builder: Option<BoxFinalityProofRequestBuilder<TBl>>,
	/// An optional, shared finality proof request provider.
	pub finality_proof_provider: Option<Arc<dyn FinalityProofProvider<TBl>>>,
	/// A shared transaction pool.
	pub transaction_pool: Arc<TExPool>,
	/// A RPC extension builder. Use `NoopRpcExtensionBuilder` if you just want to pass in the
	/// extensions directly.
	pub rpc_extensions_builder: Box<dyn RpcExtensionBuilder<Output = TRpc> + Send>,
	/// An optional, shared remote blockchain instance. Used for light clients.
	pub remote_blockchain: Option<Arc<dyn RemoteBlockchain<TBl>>>,
	/// A block annouce validator builder.
	pub block_announce_validator_builder:
		Option<Box<dyn FnOnce(Arc<TCl>) -> Box<dyn BlockAnnounceValidator<TBl> + Send> + Send>>,
}

/// Put together the components of a service from the parameters.
pub fn build<TBl, TBackend, TImpQu, TExPool, TRpc, TCl>(
	builder: ServiceParams<TBl, TCl, TImpQu, TExPool, TRpc, TBackend>,
) -> Result<ServiceComponents<TBl, TBackend, TCl>, Error>
	where
		TCl: ProvideRuntimeApi<TBl> + HeaderMetadata<TBl, Error=sp_blockchain::Error> + Chain<TBl> +
		BlockBackend<TBl> + BlockIdTo<TBl, Error=sp_blockchain::Error> + ProofProvider<TBl> +
		HeaderBackend<TBl> + BlockchainEvents<TBl> + ExecutorProvider<TBl> + UsageProvider<TBl> +
		StorageProvider<TBl, TBackend> + CallApiAt<TBl, Error=sp_blockchain::Error> +
		Send + 'static,
		<TCl as ProvideRuntimeApi<TBl>>::Api:
			sp_api::Metadata<TBl> +
			sc_offchain::OffchainWorkerApi<TBl> +
			sp_transaction_pool::runtime_api::TaggedTransactionQueue<TBl> +
			sp_session::SessionKeys<TBl> +
			sp_api::ApiErrorExt<Error = sp_blockchain::Error> +
			sp_api::ApiExt<TBl, StateBackend = TBackend::State>,
		TBl: BlockT,
		TBackend: 'static + sc_client_api::backend::Backend<TBl> + Send,
		TImpQu: 'static + ImportQueue<TBl>,
		TExPool: MaintainedTransactionPool<Block=TBl, Hash = <TBl as BlockT>::Hash> +
			MallocSizeOfWasm + 'static,
		TRpc: sc_rpc::RpcExtension<sc_rpc::Metadata>
{
	let ServiceParams {
		mut config,
		mut task_manager,
		client,
		on_demand,
		backend,
		keystore,
		import_queue,
		finality_proof_request_builder,
		finality_proof_provider,
		transaction_pool,
		rpc_extensions_builder,
		remote_blockchain,
		block_announce_validator_builder,
	} = builder;

	let chain_info = client.usage_info().chain;

	sp_session::generate_initial_session_keys(
		client.clone(),
		&BlockId::Hash(chain_info.best_hash),
		config.dev_key_seed.clone().map(|s| vec![s]).unwrap_or_default(),
	)?;

	info!("📦 Highest known block at #{}", chain_info.best_number);
	telemetry!(
		SUBSTRATE_INFO;
		"node.start";
		"height" => chain_info.best_number.saturated_into::<u64>(),
		"best" => ?chain_info.best_hash
	);

	let (system_rpc_tx, system_rpc_rx) = tracing_unbounded("mpsc_system_rpc");

	let (network, network_status_sinks, network_future) = build_network(
		&config, client.clone(), transaction_pool.clone(), task_manager.spawn_handle(),
		on_demand.clone(), block_announce_validator_builder, finality_proof_request_builder,
		finality_proof_provider, system_rpc_rx, import_queue
	)?;

	let spawn_handle = task_manager.spawn_handle();

	// The network worker is responsible for gathering all network messages and processing
	// them. This is quite a heavy task, and at the time of the writing of this comment it
	// frequently happens that this future takes several seconds or in some situations
	// even more than a minute until it has processed its entire queue. This is clearly an
	// issue, and ideally we would like to fix the network future to take as little time as
	// possible, but we also take the extra harm-prevention measure to execute the networking
	// future using `spawn_blocking`.
	spawn_handle.spawn_blocking("network-worker", network_future);

	let offchain_storage = backend.offchain_storage();
	let offchain_workers = match (config.offchain_worker.clone(), offchain_storage.clone()) {
		(OffchainWorkerConfig {enabled: true, .. }, Some(db)) => {
			Some(Arc::new(sc_offchain::OffchainWorkers::new(client.clone(), db)))
		},
		(OffchainWorkerConfig {enabled: true, .. }, None) => {
			warn!("Offchain workers disabled, due to lack of offchain storage support in backend.");
			None
		},
		_ => None,
	};

	// Inform the tx pool about imported and finalized blocks.
	spawn_handle.spawn(
		"txpool-notifications",
		sc_transaction_pool::notification_future(client.clone(), transaction_pool.clone()),
	);

	// Inform the offchain worker about new imported blocks
	if let Some(offchain) = offchain_workers.clone() {
		spawn_handle.spawn(
			"offchain-notifications",
			sc_offchain::notification_future(
				config.role.is_authority(),
				client.clone(),
				offchain,
				task_manager.spawn_handle(),
				network.clone()
			)
		);
	}

	spawn_handle.spawn(
		"on-transaction-imported",
		transaction_notifications(transaction_pool.clone(), network.clone()),
	);

	// Prometheus metrics.
	let metrics_service = if let Some(PrometheusConfig { port, registry }) =
		config.prometheus_config.clone()
	{
		// Set static metrics.
		let metrics = MetricsService::with_prometheus(&registry, &config)?;
		spawn_handle.spawn(
			"prometheus-endpoint",
			prometheus_endpoint::init_prometheus(port, registry).map(drop)
		);

		metrics
	} else {
		MetricsService::new()
	};

	// Periodically notify the telemetry.
	spawn_handle.spawn("telemetry-periodic-send", telemetry_periodic_send(
		client.clone(), transaction_pool.clone(), metrics_service, network_status_sinks.clone()
	));

	// Periodically send the network state to the telemetry.
	spawn_handle.spawn(
		"telemetry-periodic-network-state",
		telemetry_periodic_network_state(network_status_sinks.clone()),
	);

	// RPC
	let gen_handler = |deny_unsafe: sc_rpc::DenyUnsafe| gen_handler(
		deny_unsafe, &config, task_manager.spawn_handle(), client.clone(), transaction_pool.clone(),
		keystore.clone(), on_demand.clone(), remote_blockchain.clone(), &*rpc_extensions_builder,
		offchain_storage.clone(), system_rpc_tx.clone()
	);
	let rpc = start_rpc_servers(&config, gen_handler)?;
	// This is used internally, so don't restrict access to unsafe RPC
	let rpc_handlers = Arc::new(RpcHandlers(gen_handler(sc_rpc::DenyUnsafe::No)));

	let telemetry_connection_sinks: Arc<Mutex<Vec<TracingUnboundedSender<()>>>> = Default::default();

	// Telemetry
	let telemetry = config.telemetry_endpoints.clone().and_then(|endpoints| {
		if endpoints.is_empty() {
			// we don't want the telemetry to be initialized if telemetry_endpoints == Some([])
			return None;
		}

		let genesis_hash = match client.block_hash(Zero::zero()) {
			Ok(Some(hash)) => hash,
			_ => Default::default(),
		};

		Some(build_telemetry(
			&mut config, endpoints, telemetry_connection_sinks.clone(), network.clone(),
			task_manager.spawn_handle(), genesis_hash,
		))
	});

	// Instrumentation
	if let Some(tracing_targets) = config.tracing_targets.as_ref() {
		let subscriber = sc_tracing::ProfilingSubscriber::new(
			config.tracing_receiver, tracing_targets
		);
		match tracing::subscriber::set_global_default(subscriber) {
			Ok(_) => (),
			Err(e) => error!(target: "tracing", "Unable to set global default subscriber {}", e),
		}
	}

	// Spawn informant task
	spawn_handle.spawn("informant", sc_informant::build(
		client.clone(),
		network_status_sinks.clone(),
		transaction_pool.clone(),
		config.informant_output_format,
	));

	task_manager.keep_alive((telemetry, config.base_path, rpc, rpc_handlers.clone()));

	Ok(ServiceComponents {
		task_manager, network, rpc_handlers, offchain_workers,
		telemetry_on_connect_sinks: TelemetryOnConnectSinks(telemetry_connection_sinks),
		network_status_sinks: NetworkStatusSinks::new(network_status_sinks),
	})
}

async fn transaction_notifications<TBl, TExPool>(
	transaction_pool: Arc<TExPool>,
	network: Arc<NetworkService<TBl, <TBl as BlockT>::Hash>>
)
	where
		TBl: BlockT,
		TExPool: MaintainedTransactionPool<Block=TBl, Hash = <TBl as BlockT>::Hash>,
{
	// transaction notifications
	transaction_pool.import_notification_stream()
		.for_each(move |hash| {
			network.propagate_transaction(hash);
			let status = transaction_pool.status();
			telemetry!(SUBSTRATE_INFO; "txpool.import";
				"ready" => status.ready,
				"future" => status.future
			);
			ready(())
		})
		.await;
}

// Periodically notify the telemetry.
async fn telemetry_periodic_send<TBl, TExPool, TCl>(
	client: Arc<TCl>,
	transaction_pool: Arc<TExPool>,
	mut metrics_service: MetricsService,
	network_status_sinks: Arc<status_sinks::StatusSinks<(NetworkStatus<TBl>, NetworkState)>>
)
	where
		TBl: BlockT,
		TCl: ProvideRuntimeApi<TBl> + UsageProvider<TBl>,
		TExPool: MaintainedTransactionPool<Block=TBl, Hash = <TBl as BlockT>::Hash>,
{
	let (state_tx, state_rx) = tracing_unbounded::<(NetworkStatus<_>, NetworkState)>("mpsc_netstat1");
	network_status_sinks.push(std::time::Duration::from_millis(5000), state_tx);
	state_rx.for_each(move |(net_status, _)| {
		let info = client.usage_info();
		metrics_service.tick(
			&info,
			&transaction_pool.status(),
			&net_status,
		);
		ready(())
	}).await;
}

async fn telemetry_periodic_network_state<TBl: BlockT>(
	network_status_sinks: Arc<status_sinks::StatusSinks<(NetworkStatus<TBl>, NetworkState)>>
) {
	// Periodically send the network state to the telemetry.
	let (netstat_tx, netstat_rx) = tracing_unbounded::<(NetworkStatus<_>, NetworkState)>("mpsc_netstat2");
	network_status_sinks.push(std::time::Duration::from_secs(30), netstat_tx);
	netstat_rx.for_each(move |(_, network_state)| {
		telemetry!(
			SUBSTRATE_INFO;
			"system.network_state";
			"state" => network_state,
		);
		ready(())
	}).await;
}

fn build_telemetry<TBl: BlockT>(
	config: &mut Configuration,
	endpoints: sc_telemetry::TelemetryEndpoints,
	telemetry_connection_sinks: Arc<Mutex<Vec<TracingUnboundedSender<()>>>>,
	network: Arc<NetworkService<TBl, <TBl as BlockT>::Hash>>,
	spawn_handle: SpawnTaskHandle,
	genesis_hash: <TBl as BlockT>::Hash,
) -> sc_telemetry::Telemetry {
	let is_authority = config.role.is_authority();
	let network_id = network.local_peer_id().to_base58();
	let name = config.network.node_name.clone();
	let impl_name = config.impl_name.clone();
	let impl_version = config.impl_version.clone();
	let chain_name = config.chain_spec.name().to_owned();
	let telemetry = sc_telemetry::init_telemetry(sc_telemetry::TelemetryConfig {
		endpoints,
		wasm_external_transport: config.telemetry_external_transport.take(),
	});
	let startup_time = SystemTime::UNIX_EPOCH.elapsed()
		.map(|dur| dur.as_millis())
		.unwrap_or(0);
	
	spawn_handle.spawn(
		"telemetry-worker",
		telemetry.clone()
			.for_each(move |event| {
				// Safe-guard in case we add more events in the future.
				let sc_telemetry::TelemetryEvent::Connected = event;

				telemetry!(SUBSTRATE_INFO; "system.connected";
					"name" => name.clone(),
					"implementation" => impl_name.clone(),
					"version" => impl_version.clone(),
					"config" => "",
					"chain" => chain_name.clone(),
					"genesis_hash" => ?genesis_hash,
					"authority" => is_authority,
					"startup_time" => startup_time,
					"network_id" => network_id.clone()
				);

				telemetry_connection_sinks.lock().retain(|sink| {
					sink.unbounded_send(()).is_ok()
				});
				ready(())
			})
	);

	telemetry
}

fn gen_handler<TBl, TBackend, TExPool, TRpc, TCl>(
	deny_unsafe: sc_rpc::DenyUnsafe,
	config: &Configuration,
	spawn_handle: SpawnTaskHandle,
	client: Arc<TCl>,
	transaction_pool: Arc<TExPool>,
	keystore: Arc<RwLock<Keystore>>,
	on_demand: Option<Arc<OnDemand<TBl>>>,
	remote_blockchain: Option<Arc<dyn RemoteBlockchain<TBl>>>,
	rpc_extensions_builder: &(dyn RpcExtensionBuilder<Output = TRpc> + Send),
	offchain_storage: Option<<TBackend as sc_client_api::backend::Backend<TBl>>::OffchainStorage>,
	system_rpc_tx: TracingUnboundedSender<sc_rpc::system::Request<TBl>>
) -> jsonrpc_pubsub::PubSubHandler<sc_rpc::Metadata>
	where
		TBl: BlockT,
		TCl: ProvideRuntimeApi<TBl> + BlockchainEvents<TBl> + HeaderBackend<TBl> +
		HeaderMetadata<TBl, Error=sp_blockchain::Error> + ExecutorProvider<TBl> +
		CallApiAt<TBl, Error=sp_blockchain::Error> + ProofProvider<TBl> +
		StorageProvider<TBl, TBackend> + BlockBackend<TBl> + Send + Sync + 'static,
		TExPool: MaintainedTransactionPool<Block=TBl, Hash = <TBl as BlockT>::Hash> + 'static,
		TBackend: sc_client_api::backend::Backend<TBl> + 'static,
		TRpc: sc_rpc::RpcExtension<sc_rpc::Metadata>,
		<TCl as ProvideRuntimeApi<TBl>>::Api:
			sp_session::SessionKeys<TBl> +
			sp_api::Metadata<TBl, Error = sp_blockchain::Error>,
{
	use sc_rpc::{chain, state, author, system, offchain};

	let system_info = sc_rpc::system::SystemInfo {
		chain_name: config.chain_spec.name().into(),
		impl_name: config.impl_name.clone(),
		impl_version: config.impl_version.clone(),
		properties: config.chain_spec.properties(),
		chain_type: config.chain_spec.chain_type(),
	};

	let subscriptions = SubscriptionManager::new(Arc::new(spawn_handle));

	let (chain, state, child_state) = if let (Some(remote_blockchain), Some(on_demand)) =
		(remote_blockchain, on_demand) {
		// Light clients
		let chain = sc_rpc::chain::new_light(
			client.clone(),
			subscriptions.clone(),
			remote_blockchain.clone(),
			on_demand.clone(),
		);
		let (state, child_state) = sc_rpc::state::new_light(
			client.clone(),
			subscriptions.clone(),
			remote_blockchain.clone(),
			on_demand,
		);
		(chain, state, child_state)

	} else {
		// Full nodes
		let chain = sc_rpc::chain::new_full(client.clone(), subscriptions.clone());
		let (state, child_state) = sc_rpc::state::new_full(client.clone(), subscriptions.clone());
		(chain, state, child_state)
	};

	let author = sc_rpc::author::Author::new(
		client,
		transaction_pool,
		subscriptions,
		keystore,
		deny_unsafe,
	);
	let system = system::System::new(system_info, system_rpc_tx, deny_unsafe);

	let maybe_offchain_rpc = offchain_storage
	.map(|storage| {
		let offchain = sc_rpc::offchain::Offchain::new(storage, deny_unsafe);
		// FIXME: Use plain Option (don't collect into HashMap) when we upgrade to jsonrpc 14.1
		// https://github.com/paritytech/jsonrpc/commit/20485387ed06a48f1a70bf4d609a7cde6cf0accf
		let delegate = offchain::OffchainApi::to_delegate(offchain);
			delegate.into_iter().collect::<HashMap<_, _>>()
	}).unwrap_or_default();

	sc_rpc_server::rpc_handler((
		state::StateApi::to_delegate(state),
		state::ChildStateApi::to_delegate(child_state),
		chain::ChainApi::to_delegate(chain),
		maybe_offchain_rpc,
		author::AuthorApi::to_delegate(author),
		system::SystemApi::to_delegate(system),
		rpc_extensions_builder.build(deny_unsafe),
	))
}

fn build_network<TBl, TExPool, TImpQu, TCl>(
	config: &Configuration,
	client: Arc<TCl>,
	transaction_pool: Arc<TExPool>,
	spawn_handle: SpawnTaskHandle,
	on_demand: Option<Arc<OnDemand<TBl>>>,
	block_announce_validator_builder: Option<Box<
		dyn FnOnce(Arc<TCl>) -> Box<dyn BlockAnnounceValidator<TBl> + Send> + Send
	>>,
	finality_proof_request_builder: Option<BoxFinalityProofRequestBuilder<TBl>>,
	finality_proof_provider: Option<Arc<dyn FinalityProofProvider<TBl>>>,
	system_rpc_rx: TracingUnboundedReceiver<sc_rpc::system::Request<TBl>>,
	import_queue: TImpQu
) -> Result<
	(
		Arc<NetworkService<TBl, <TBl as BlockT>::Hash>>,
		Arc<status_sinks::StatusSinks<(NetworkStatus<TBl>, NetworkState)>>,
		Pin<Box<dyn Future<Output = ()> + Send>>
	),
	Error
>
	where
		TBl: BlockT,
		TCl: ProvideRuntimeApi<TBl> + HeaderMetadata<TBl, Error=sp_blockchain::Error> + Chain<TBl> +
		BlockBackend<TBl> + BlockIdTo<TBl, Error=sp_blockchain::Error> + ProofProvider<TBl> +
		HeaderBackend<TBl> + BlockchainEvents<TBl> + 'static,
		TExPool: MaintainedTransactionPool<Block=TBl, Hash = <TBl as BlockT>::Hash> + 'static,
		TImpQu: ImportQueue<TBl> + 'static,
{
	let transaction_pool_adapter = Arc::new(TransactionPoolAdapter {
		imports_external_transactions: !matches!(config.role, Role::Light),
		pool: transaction_pool,
		client: client.clone(),
	});

	let protocol_id = {
		let protocol_id_full = match config.chain_spec.protocol_id() {
			Some(pid) => pid,
			None => {
				warn!("Using default protocol ID {:?} because none is configured in the \
					chain specs", DEFAULT_PROTOCOL_ID
				);
				DEFAULT_PROTOCOL_ID
			}
		}.as_bytes();
		sc_network::config::ProtocolId::from(protocol_id_full)
	};

	let block_announce_validator = if let Some(f) = block_announce_validator_builder {
		f(client.clone())
	} else {
		Box::new(DefaultBlockAnnounceValidator)
	};

	let network_params = sc_network::config::Params {
		role: config.role.clone(),
		executor: {
			Some(Box::new(move |fut| {
				spawn_handle.spawn("libp2p-node", fut);
			}))
		},
		network_config: config.network.clone(),
		chain: client.clone(),
		finality_proof_provider,
		finality_proof_request_builder,
		on_demand: on_demand,
		transaction_pool: transaction_pool_adapter as _,
		import_queue: Box::new(import_queue),
		protocol_id,
		block_announce_validator,
		metrics_registry: config.prometheus_config.as_ref().map(|config| config.registry.clone())
	};

	let has_bootnodes = !network_params.network_config.boot_nodes.is_empty();
	let network_mut = sc_network::NetworkWorker::new(network_params)?;
	let network = network_mut.service().clone();
	let network_status_sinks = Arc::new(status_sinks::StatusSinks::new());

	let future = build_network_future(
		config.role.clone(),
		network_mut,
		client,
		network_status_sinks.clone(),
		system_rpc_rx,
		has_bootnodes,
		config.announce_block,
	).boxed();

	Ok((network, network_status_sinks, future))
}
