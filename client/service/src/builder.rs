// Copyright 2017-2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

#![allow(unused_imports)]

use crate::{Service, NetworkStatus, NetworkState, error::Error, DEFAULT_PROTOCOL_ID, MallocSizeOfWasm};
use crate::{TaskManagerBuilder, start_rpc_servers, build_network_future, TransactionPoolAdapter};
use crate::status_sinks;
use crate::config::{Configuration, DatabaseConfig, KeystoreConfig, PrometheusConfig};
use crate::metrics::MetricsService;
use sc_client_api::{
	self,
	BlockchainEvents,
	backend::RemoteBackend, light::RemoteBlockchain,
	execution_extensions::ExtensionsFactory,
	ExecutorProvider, CallExecutor
};
use sp_utils::mpsc::{tracing_unbounded, TracingUnboundedSender};
use sc_client::Client;
use sc_chain_spec::get_extension;
use sp_consensus::import_queue::ImportQueue;
use futures::{
	Future, FutureExt, StreamExt,
	future::ready,
};
use sc_keystore::{Store as Keystore};
use log::{info, warn, error};
use sc_network::config::{Role, FinalityProofProvider, OnDemand, BoxFinalityProofRequestBuilder};
use sc_network::{NetworkService, NetworkStateInfo};
use parking_lot::{Mutex, RwLock};
use sp_runtime::generic::BlockId;
use sp_runtime::traits::{
	Block as BlockT, NumberFor, SaturatedConversion, HashFor,
};
use sp_api::ProvideRuntimeApi;
use sc_executor::{NativeExecutor, NativeExecutionDispatch};
use std::{
	io::{Read, Write, Seek},
	marker::PhantomData, sync::Arc, pin::Pin
};
use wasm_timer::SystemTime;
use sc_telemetry::{telemetry, SUBSTRATE_INFO};
use sp_transaction_pool::{MaintainedTransactionPool, ChainEvent};
use sp_blockchain;

pub type BackgroundTask = Pin<Box<dyn Future<Output=()> + Send>>;

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
pub type TFullCallExecutor<TBl, TExecDisp> = sc_client::LocalCallExecutor<
	sc_client_db::Backend<TBl>,
	NativeExecutor<TExecDisp>,
>;

type TFullParts<TBl, TRtApi, TExecDisp> = (
	TFullClient<TBl, TRtApi, TExecDisp>,
	Arc<TFullBackend<TBl>>,
	Arc<RwLock<sc_keystore::Store>>,
	TaskManagerBuilder,
);

/// Light client type.
pub type TLightClient<TBl, TRtApi, TExecDisp> = Client<
	TLightBackend<TBl>,
	TLightCallExecutor<TBl, TExecDisp>,
	TBl,
	TRtApi,
>;

/// Light client backend type.
pub type TLightBackend<TBl> = sc_client::light::backend::Backend<
	sc_client_db::light::LightStorage<TBl>,
	HashFor<TBl>,
>;

/// Light call executor type.
pub type TLightCallExecutor<TBl, TExecDisp> = sc_client::light::call_executor::GenesisCallExecutor<
	sc_client::light::backend::Backend<
		sc_client_db::light::LightStorage<TBl>,
		HashFor<TBl>
	>,
	sc_client::LocalCallExecutor<
		sc_client::light::backend::Backend<
			sc_client_db::light::LightStorage<TBl>,
			HashFor<TBl>
		>,
		NativeExecutor<TExecDisp>
	>,
>;

type TLightParts<TBl, TRtApi, TExecDisp> = (
	TLightClient<TBl, TRtApi, TExecDisp>,
	Arc<TLightBackend<TBl>>,
	Arc<RwLock<sc_keystore::Store>>,
	TaskManagerBuilder,
);

/// Creates a new full client for the given config.
pub fn new_full_client<TBl, TRtApi, TExecDisp>(
	config: &Configuration,
) -> Result<TFullClient<TBl, TRtApi, TExecDisp>, Error> where
	TBl: BlockT,
	TExecDisp: NativeExecutionDispatch + 'static,
{
	new_full_parts(config).map(|parts| parts.0)
}

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

	let tasks_builder = TaskManagerBuilder::new();

	let executor = NativeExecutor::<TExecDisp>::new(
		config.wasm_method,
		config.default_heap_pages,
		config.max_runtime_instances,
	);

	let chain_spec = &config.chain_spec;
	let fork_blocks = get_extension::<sc_client::ForkBlocks<TBl>>(chain_spec.extensions())
		.cloned()
		.unwrap_or_default();

	let bad_blocks = get_extension::<sc_client::BadBlocks<TBl>>(chain_spec.extensions())
		.cloned()
		.unwrap_or_default();

	let (client, backend) = {
		let db_config = sc_client_db::DatabaseSettings {
			state_cache_size: config.state_cache_size,
			state_cache_child_ratio:
			config.state_cache_child_ratio.map(|v| (v, 100)),
			pruning: config.pruning.clone(),
			source: match &config.database {
				DatabaseConfig::Path { path, cache_size } =>
					sc_client_db::DatabaseSettingsSrc::Path {
						path: path.clone(),
						cache_size: *cache_size,
					},
				DatabaseConfig::Custom(db) =>
					sc_client_db::DatabaseSettingsSrc::Custom(db.clone()),
			},
		};

		let extensions = sc_client_api::execution_extensions::ExecutionExtensions::new(
			config.execution_strategies.clone(),
			Some(keystore.clone()),
		);

		sc_client_db::new_client(
			db_config,
			executor,
			chain_spec.as_storage_builder(),
			fork_blocks,
			bad_blocks,
			extensions,
			Box::new(tasks_builder.spawn_handle()),
			config.prometheus_config.as_ref().map(|config| config.registry.clone()),
		)?
	};

	Ok((client, backend, keystore, tasks_builder))
}

/// Start the service builder with a configuration.
pub fn new_light_parts<TBl: BlockT, TRtApi, TExecDisp: NativeExecutionDispatch + 'static>(
	config: &Configuration,
) -> Result<(TLightParts<TBl, TRtApi, TExecDisp>, Arc<OnDemand<TBl>>), Error> {
	let tasks_builder = TaskManagerBuilder::new();

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
			source: match &config.database {
				DatabaseConfig::Path { path, cache_size } =>
					sc_client_db::DatabaseSettingsSrc::Path {
						path: path.clone(),
						cache_size: *cache_size,
					},
				DatabaseConfig::Custom(db) =>
					sc_client_db::DatabaseSettingsSrc::Custom(db.clone()),
			},
		};
		sc_client_db::light::LightStorage::new(db_settings)?
	};
	let light_blockchain = sc_client::light::new_light_blockchain(db_storage);
	let fetch_checker = Arc::new(
		sc_client::light::new_fetch_checker::<_, TBl, _>(
			light_blockchain.clone(),
			executor.clone(),
			Box::new(tasks_builder.spawn_handle()),
		),
	);
	let fetcher = Arc::new(sc_network::config::OnDemand::new(fetch_checker));
	let backend = sc_client::light::new_light_backend(light_blockchain);
	let remote_blockchain = backend.remote_blockchain();
	let client = sc_client::light::new_light(
		backend.clone(),
		config.chain_spec.as_storage_builder(),
		executor,
		Box::new(tasks_builder.spawn_handle()),
		config.prometheus_config.as_ref().map(|config| config.registry.clone()),
	)?;

	Ok(((client, backend, keystore, tasks_builder), fetcher))
}

/// Builds the service.
pub fn build<
	TBl,
	TRtApi,
	TSc,
	TImpQu,
	TExPool,
	TRpc,
	TBackend,
	TExec,
>(
	mut config: Configuration,
	client: Arc<Client<TBackend, TExec, TBl, TRtApi>,>,
	backend: Arc<TBackend>,
	tasks_builder: TaskManagerBuilder,
	keystore: Arc<RwLock<Keystore>>,
	on_demand: Option<Arc<OnDemand<TBl>>>,
	select_chain: Option<TSc>,
	import_queue: TImpQu,
	finality_proof_request_builder: Option<BoxFinalityProofRequestBuilder<TBl>>,
	finality_proof_provider: Option<Arc<dyn FinalityProofProvider<TBl>>>,
	transaction_pool: Arc<TExPool>,
	rpc_extensions: TRpc,
	remote_backend: Option<Arc<dyn RemoteBlockchain<TBl>>>,
	background_tasks: Vec<(&'static str, BackgroundTask)>,
) -> Result<Service<
	TBl,
	Client<TBackend, TExec, TBl, TRtApi>,
	TSc,
	NetworkStatus<TBl>,
	NetworkService<TBl, <TBl as BlockT>::Hash>,
	TExPool,
	sc_offchain::OffchainWorkers<
		Client<TBackend, TExec, TBl, TRtApi>,
		TBackend::OffchainStorage,
		TBl
	>,
>, Error>
where
	Client<TBackend, TExec, TBl, TRtApi>: ProvideRuntimeApi<TBl>,
	<Client<TBackend, TExec, TBl, TRtApi> as ProvideRuntimeApi<TBl>>::Api:
		sp_api::Metadata<TBl> +
		sc_offchain::OffchainWorkerApi<TBl> +
		sp_transaction_pool::runtime_api::TaggedTransactionQueue<TBl> +
		sp_session::SessionKeys<TBl> +
		sp_api::ApiErrorExt<Error = sp_blockchain::Error> +
		sp_api::ApiExt<TBl, StateBackend = TBackend::State>,
	TBl: BlockT,
	TRtApi: 'static + Send + Sync,
	TBackend: 'static + sc_client_api::backend::Backend<TBl> + Send,
	TExec: 'static + sc_client::CallExecutor<TBl> + Send + Sync + Clone,
	TSc: Clone,
	TImpQu: 'static + ImportQueue<TBl>,
	TExPool: MaintainedTransactionPool<Block=TBl, Hash = <TBl as BlockT>::Hash> + MallocSizeOfWasm + 'static,
	TRpc: sc_rpc::RpcExtension<sc_rpc::Metadata> + Clone,
	TExec: CallExecutor<TBl, Backend = TBackend>,
{
	sp_session::generate_initial_session_keys(
		client.clone(),
		&BlockId::Hash(client.chain_info().best_hash),
		config.dev_key_seed.clone().map(|s| vec![s]).unwrap_or_default(),
	)?;

	// A side-channel for essential tasks to communicate shutdown.
	let (essential_failed_tx, essential_failed_rx) = mpsc::unbounded();

	let import_queue = Box::new(import_queue);
	let chain_info = client.chain_info();
	let chain_spec = &config.chain_spec;

	let version = config.impl_version;
	info!("📦 Highest known block at #{}", chain_info.best_number);
	telemetry!(
		SUBSTRATE_INFO;
		"node.start";
		"height" => chain_info.best_number.saturated_into::<u64>(),
		"best" => ?chain_info.best_hash
	);

	// make transaction pool available for off-chain runtime calls.
	client.execution_extensions()
		.register_transaction_pool(Arc::downgrade(&transaction_pool) as _);

	let transaction_pool_adapter = Arc::new(TransactionPoolAdapter {
		imports_external_transactions: !config.roles.is_light(),
		pool: transaction_pool.clone(),
		client: client.clone(),
		executor: tasks_builder.spawn_handle(),
	});

	let protocol_id = {
		let protocol_id_full = match chain_spec.protocol_id() {
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

	let block_announce_validator =
		Box::new(sp_consensus::block_validation::DefaultBlockAnnounceValidator::new(client.clone()));

	let network_params = sc_network::config::Params {
		roles: config.roles,
		executor: {
			let spawn_handle = tasks_builder.spawn_handle();
			Some(Box::new(move |fut| {
				spawn_handle.spawn("libp2p-node", fut);
			}))
		},
		network_config: config.network.clone(),
		chain: client.clone(),
		finality_proof_provider,
		finality_proof_request_builder,
		on_demand: on_demand.clone(),
		transaction_pool: transaction_pool_adapter.clone() as _,
		import_queue,
		protocol_id,
		block_announce_validator,
		metrics_registry: config.prometheus_config.as_ref().map(|config| config.registry.clone())
	};

	let has_bootnodes = !network_params.network_config.boot_nodes.is_empty();
	let network_mut = sc_network::NetworkWorker::new(network_params)?;
	let network = network_mut.service().clone();
	let network_status_sinks = Arc::new(Mutex::new(status_sinks::StatusSinks::new()));

	let offchain_storage = backend.offchain_storage();
	let offchain_workers = match (config.offchain_worker, offchain_storage.clone()) {
		(true, Some(db)) => {
			Some(Arc::new(sc_offchain::OffchainWorkers::new(client.clone(), db)))
		},
		(true, None) => {
			warn!("Offchain workers disabled, due to lack of offchain storage support in backend.");
			None
		},
		_ => None,
	};

	let spawn_handle = tasks_builder.spawn_handle();

	// Spawn background tasks which were stacked during the
	// service building.
	for (title, background_task) in background_tasks {
		spawn_handle.spawn(title, background_task);
	}

	{
		// block notifications
		let txpool = Arc::downgrade(&transaction_pool);
		let offchain = offchain_workers.as_ref().map(Arc::downgrade);
		let notifications_spawn_handle = tasks_builder.spawn_handle();
		let network_state_info: Arc<dyn NetworkStateInfo + Send + Sync> = network.clone();
		let is_validator = config.roles.is_authority();

		let (import_stream, finality_stream) = (
			client.import_notification_stream().map(|n| ChainEvent::NewBlock {
				id: BlockId::Hash(n.hash),
				header: n.header,
				retracted: n.retracted,
				is_new_best: n.is_new_best,
			}),
			client.finality_notification_stream().map(|n| ChainEvent::Finalized {
				hash: n.hash
			})
		);
		let events = futures::stream::select(import_stream, finality_stream)
			.for_each(move |event| {
				// offchain worker is only interested in block import events
				if let ChainEvent::NewBlock { ref header, is_new_best, .. } = event {
					let offchain = offchain.as_ref().and_then(|o| o.upgrade());
					match offchain {
						Some(offchain) if is_new_best => {
							notifications_spawn_handle.spawn(
								"offchain-on-block",
								offchain.on_block_imported(
									&header,
									network_state_info.clone(),
									is_validator,
								),
							);
						},
						Some(_) => log::debug!(
								target: "sc_offchain",
								"Skipping offchain workers for non-canon block: {:?}",
								header,
							),
						_ => {},
					}
				};

				let txpool = txpool.upgrade();
				if let Some(txpool) = txpool.as_ref() {
					notifications_spawn_handle.spawn(
						"txpool-maintain",
						txpool.maintain(event),
					);
				}

				ready(())
			});

		spawn_handle.spawn(
			"txpool-and-offchain-notif",
			events,
		);
	}

	{
		// extrinsic notifications
		let network = Arc::downgrade(&network);
		let transaction_pool_ = transaction_pool.clone();
		let events = transaction_pool.import_notification_stream()
			.for_each(move |hash| {
				if let Some(network) = network.upgrade() {
					network.propagate_extrinsic(hash);
				}
				let status = transaction_pool_.status();
				telemetry!(SUBSTRATE_INFO; "txpool.import";
					"ready" => status.ready,
					"future" => status.future
				);
				ready(())
			});

		spawn_handle.spawn(
			"telemetry-on-block",
			events,
		);
	}

	// Prometheus metrics.
	let metrics = if let Some(PrometheusConfig { port, registry }) = config.prometheus_config.clone() {
		// Set static metrics.
		register(Gauge::<U64>::with_opts(
			Opts::new(
				"build_info",
				"A metric with a constant '1' value labeled by name, version, and commit."
			)
				.const_label("name", config.impl_name)
				.const_label("version", config.impl_version)
		)?, &registry)?.set(1);
		register(Gauge::<U64>::new(
			"node_roles", "The roles the node is running as",
		)?, &registry)?.set(u64::from(config.roles.bits()));

		let metrics = ServiceMetrics::register(&registry)?;

		spawn_handle.spawn(
			"prometheus-endpoint",
			prometheus_endpoint::init_prometheus(port, registry).map(drop)
		);

		Some(metrics)
	} else {
		None
	};

	// Periodically notify the telemetry.
	let transaction_pool_ = transaction_pool.clone();
	let client_ = client.clone();
	let mut sys = System::new();
	let self_pid = get_current_pid().ok();
	let (state_tx, state_rx) = mpsc::unbounded::<(NetworkStatus<_>, NetworkState)>();
	network_status_sinks.lock().push(std::time::Duration::from_millis(5000), state_tx);
	let tel_task = state_rx.for_each(move |(net_status, _)| {
		let info = client_.usage_info();
		let best_number = info.chain.best_number.saturated_into::<u64>();
		let best_hash = info.chain.best_hash;
		let num_peers = net_status.num_connected_peers;
		let txpool_status = transaction_pool_.status();
		let finalized_number: u64 = info.chain.finalized_number.saturated_into::<u64>();
		let bandwidth_download = net_status.average_download_per_sec;
		let bandwidth_upload = net_status.average_upload_per_sec;
		let best_seen_block = net_status.best_seen_block
			.map(|num: NumberFor<TBl>| num.unique_saturated_into() as u64);

		// get cpu usage and memory usage of this process
		let (cpu_usage, memory) = if let Some(self_pid) = self_pid {
			if sys.refresh_process(self_pid) {
				let proc = sys.get_process(self_pid)
					.expect("Above refresh_process succeeds, this should be Some(), qed");
				(proc.cpu_usage(), proc.memory())
			} else { (0.0, 0) }
		} else { (0.0, 0) };

		telemetry!(
			SUBSTRATE_INFO;
			"system.interval";
			"peers" => num_peers,
			"height" => best_number,
			"best" => ?best_hash,
			"txcount" => txpool_status.ready,
			"cpu" => cpu_usage,
			"memory" => memory,
			"finalized_height" => finalized_number,
			"finalized_hash" => ?info.chain.finalized_hash,
			"bandwidth_download" => bandwidth_download,
			"bandwidth_upload" => bandwidth_upload,
			"used_state_cache_size" => info.usage.as_ref()
				.map(|usage| usage.memory.state_cache.as_bytes())
				.unwrap_or(0),
			"used_db_cache_size" => info.usage.as_ref()
				.map(|usage| usage.memory.database_cache.as_bytes())
				.unwrap_or(0),
			"disk_read_per_sec" => info.usage.as_ref()
				.map(|usage| usage.io.bytes_read)
				.unwrap_or(0),
			"disk_write_per_sec" => info.usage.as_ref()
				.map(|usage| usage.io.bytes_written)
				.unwrap_or(0),
		);
		if let Some(metrics) = metrics.as_ref() {
			// `sysinfo::Process::memory` returns memory usage in KiB and not bytes.
			metrics.memory_usage_bytes.set(memory * 1024);
			metrics.cpu_usage_percentage.set(f64::from(cpu_usage));
			metrics.ready_transactions_number.set(txpool_status.ready as u64);

			metrics.network_per_sec_bytes.with_label_values(&["download"]).set(net_status.average_download_per_sec);
			metrics.network_per_sec_bytes.with_label_values(&["upload"]).set(net_status.average_upload_per_sec);

			metrics.block_height_number.with_label_values(&["finalized"]).set(finalized_number);
			metrics.block_height_number.with_label_values(&["best"]).set(best_number);

			if let Some(best_seen_block) = best_seen_block {
				metrics.block_height_number.with_label_values(&["sync_target"]).set(best_seen_block);
			}

			if let Some(info) = info.usage.as_ref() {
				metrics.database_cache.set(info.memory.database_cache.as_bytes() as u64);
				metrics.state_cache.set(info.memory.state_cache.as_bytes() as u64);

				metrics.state_db.with_label_values(&["non_canonical"]).set(info.memory.state_db.non_canonical.as_bytes() as u64);
				if let Some(pruning) = info.memory.state_db.pruning {
					metrics.state_db.with_label_values(&["pruning"]).set(pruning.as_bytes() as u64);
				}
				metrics.state_db.with_label_values(&["pinned"]).set(info.memory.state_db.pinned.as_bytes() as u64);
			}
		}

		ready(())
	});

	spawn_handle.spawn(
		"telemetry-periodic-send",
		tel_task,
	);

	// Periodically send the network state to the telemetry.
	let (netstat_tx, netstat_rx) = mpsc::unbounded::<(NetworkStatus<_>, NetworkState)>();
	network_status_sinks.lock().push(std::time::Duration::from_secs(30), netstat_tx);
	let tel_task_2 = netstat_rx.for_each(move |(_, network_state)| {
		telemetry!(
			SUBSTRATE_INFO;
			"system.network_state";
			"state" => network_state,
		);
		ready(())
	});
	spawn_handle.spawn(
		"telemetry-periodic-network-state",
		tel_task_2,
	);

	// RPC
	let (system_rpc_tx, system_rpc_rx) = mpsc::unbounded();
	let gen_handler = || {
		use sc_rpc::{chain, state, author, system, offchain};

		let system_info = sc_rpc::system::SystemInfo {
			chain_name: chain_spec.name().into(),
			impl_name: config.impl_name.into(),
			impl_version: config.impl_version.into(),
			properties: chain_spec.properties().clone(),
		};

		let subscriptions = sc_rpc::Subscriptions::new(Arc::new(tasks_builder.spawn_handle()));

		let (chain, state) = if let (Some(remote_backend), Some(on_demand)) =
			(remote_backend.as_ref(), on_demand.as_ref()) {
			// Light clients
			let chain = sc_rpc::chain::new_light(
				client.clone(),
				subscriptions.clone(),
				remote_backend.clone(),
				on_demand.clone()
			);
			let state = sc_rpc::state::new_light(
				client.clone(),
				subscriptions.clone(),
				remote_backend.clone(),
				on_demand.clone()
			);
			(chain, state)

		} else {
			// Full nodes
			let chain = sc_rpc::chain::new_full(client.clone(), subscriptions.clone());
			let state = sc_rpc::state::new_full(client.clone(), subscriptions.clone());
			(chain, state)
		};

		let author = sc_rpc::author::Author::new(
			client.clone(),
			transaction_pool.clone(),
			subscriptions,
			keystore.clone(),
		);
		let system = system::System::new(system_info, system_rpc_tx.clone());

		match offchain_storage.clone() {
			Some(storage) => {
				let offchain = sc_rpc::offchain::Offchain::new(storage);
				sc_rpc_server::rpc_handler((
					state::StateApi::to_delegate(state),
					chain::ChainApi::to_delegate(chain),
					offchain::OffchainApi::to_delegate(offchain),
					author::AuthorApi::to_delegate(author),
					system::SystemApi::to_delegate(system),
					rpc_extensions.clone(),
				))
			},
			None => sc_rpc_server::rpc_handler((
				state::StateApi::to_delegate(state),
				chain::ChainApi::to_delegate(chain),
				author::AuthorApi::to_delegate(author),
				system::SystemApi::to_delegate(system),
				rpc_extensions.clone(),
			))
		}
	};
	let rpc_handlers = gen_handler();
	let rpc = start_rpc_servers(&config, gen_handler)?;

	spawn_handle.spawn(
		"network-worker",
		build_network_future(
			config.roles,
			network_mut,
			client.clone(),
			network_status_sinks.clone(),
			system_rpc_rx,
			has_bootnodes,
			config.announce_block,
		),
	);

	let telemetry_connection_sinks: Arc<Mutex<Vec<futures::channel::mpsc::UnboundedSender<()>>>> = Default::default();

	// Telemetry
	let telemetry = config.telemetry_endpoints.clone().map(|endpoints| {
		let is_authority = config.roles.is_authority();
		let network_id = network.local_peer_id().to_base58();
		let name = config.network.node_name.clone();
		let impl_name = config.impl_name.to_owned();
		let version = version.clone();
		let chain_name = config.chain_spec.name().to_owned();
		let telemetry_connection_sinks_ = telemetry_connection_sinks.clone();
		let telemetry = sc_telemetry::init_telemetry(sc_telemetry::TelemetryConfig {
			endpoints,
			wasm_external_transport: config.telemetry_external_transport.take(),
		});
		let startup_time = SystemTime::UNIX_EPOCH.elapsed()
			.map(|dur| dur.as_millis())
			.unwrap_or(0);
		let future = telemetry.clone()
			.for_each(move |event| {
				// Safe-guard in case we add more events in the future.
				let sc_telemetry::TelemetryEvent::Connected = event;

				telemetry!(SUBSTRATE_INFO; "system.connected";
					"name" => name.clone(),
					"implementation" => impl_name.clone(),
					"version" => version.clone(),
					"config" => "",
					"chain" => chain_name.clone(),
					"authority" => is_authority,
					"startup_time" => startup_time,
					"network_id" => network_id.clone()
				);

				telemetry_connection_sinks_.lock().retain(|sink| {
					sink.unbounded_send(()).is_ok()
				});
				ready(())
			});

		spawn_handle.spawn(
			"telemetry-worker",
			future,
		);

		telemetry
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

	Ok(Service {
		client,
		task_manager: tasks_builder.into_task_manager(config.task_executor),
		network,
		network_status_sinks,
		select_chain,
		transaction_pool,
		essential_failed_tx,
		essential_failed_rx,
		rpc_handlers,
		_rpc: rpc,
		_telemetry: telemetry,
		_offchain_workers: offchain_workers,
		_telemetry_on_connect_sinks: telemetry_connection_sinks.clone(),
		keystore,
		marker: PhantomData::<TBl>,
		prometheus_registry: config.prometheus_config.map(|config| config.registry)
	})
}
