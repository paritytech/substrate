// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

//! Substrate service. Starts a thread that spins up the network, client, and extrinsic pool.
//! Manages communication between them.

#![warn(missing_docs)]

pub mod config;
#[macro_use]
pub mod chain_ops;
pub mod error;

use std::io;
use std::marker::PhantomData;
use std::net::SocketAddr;
use std::collections::HashMap;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::{Duration, Instant};
use futures::sync::mpsc;
use parking_lot::Mutex;

use client::{runtime_api::BlockT, Client};
use exit_future::Signal;
use futures::prelude::*;
use futures03::{
	future::{ready, FutureExt as _, TryFutureExt as _},
	stream::{StreamExt as _, TryStreamExt as _},
};
use network::{
	NetworkService, NetworkState, specialization::NetworkSpecialization,
	Event, DhtEvent, PeerId, ReportHandle,
};
use log::{log, warn, debug, error, Level};
use codec::{Encode, Decode};
use primitives::{Blake2Hasher, H256};
use sr_primitives::generic::BlockId;
use sr_primitives::traits::NumberFor;

pub use self::error::Error;
pub use self::builder::{ServiceBuilder, ServiceBuilderExport, ServiceBuilderImport, ServiceBuilderRevert};
pub use config::{Configuration, Roles, PruningMode};
pub use chain_spec::{ChainSpec, Properties, RuntimeGenesis, Extension as ChainSpecExtension};
pub use transaction_pool::txpool::{
	self, Pool as TransactionPool, Options as TransactionPoolOptions, ChainApi, IntoPoolError
};
pub use client::FinalityNotifications;
pub use rpc::Metadata as RpcMetadata;
#[doc(hidden)]
pub use std::{ops::Deref, result::Result, sync::Arc};
#[doc(hidden)]
pub use network::{FinalityProofProvider, OnDemand, config::BoxFinalityProofRequestBuilder};
#[doc(hidden)]
pub use futures::future::Executor;

const DEFAULT_PROTOCOL_ID: &str = "sup";

/// Substrate service.
pub struct NewService<TBl, TCl, TSc, TNetStatus, TNet, TTxPool, TOc> {
	client: Arc<TCl>,
	select_chain: Option<TSc>,
	network: Arc<TNet>,
	/// Sinks to propagate network status updates.
	network_status_sinks: Arc<Mutex<Vec<mpsc::UnboundedSender<(
		TNetStatus, NetworkState
	)>>>>,
	transaction_pool: Arc<TTxPool>,
	/// A future that resolves when the service has exited, this is useful to
	/// make sure any internally spawned futures stop when the service does.
	exit: exit_future::Exit,
	/// A signal that makes the exit future above resolve, fired on service drop.
	signal: Option<Signal>,
	/// Set to `true` when a spawned essential task has failed. The next time
	/// the service future is polled it should complete with an error.
	essential_failed: Arc<AtomicBool>,
	/// Sender for futures that must be spawned as background tasks.
	to_spawn_tx: mpsc::UnboundedSender<Box<dyn Future<Item = (), Error = ()> + Send>>,
	/// Receiver for futures that must be spawned as background tasks.
	to_spawn_rx: mpsc::UnboundedReceiver<Box<dyn Future<Item = (), Error = ()> + Send>>,
	/// List of futures to poll from `poll`.
	/// If spawning a background task is not possible, we instead push the task into this `Vec`.
	/// The elements must then be polled manually.
	to_poll: Vec<Box<dyn Future<Item = (), Error = ()> + Send>>,
	rpc_handlers: rpc_servers::RpcHandler<rpc::Metadata>,
	_rpc: Box<dyn std::any::Any + Send + Sync>,
	_telemetry: Option<tel::Telemetry>,
	_telemetry_on_connect_sinks: Arc<Mutex<Vec<mpsc::UnboundedSender<()>>>>,
	_offchain_workers: Option<Arc<TOc>>,
	keystore: keystore::KeyStorePtr,
	marker: PhantomData<TBl>,
}

/// Alias for a an implementation of `futures::future::Executor`.
pub type TaskExecutor = Arc<dyn Executor<Box<dyn Future<Item = (), Error = ()> + Send>> + Send + Sync>;

/// An handle for spawning tasks in the service.
#[derive(Clone)]
pub struct SpawnTaskHandle {
	sender: mpsc::UnboundedSender<Box<dyn Future<Item = (), Error = ()> + Send>>,
	on_exit: exit_future::Exit,
}

impl Executor<Box<dyn Future<Item = (), Error = ()> + Send>> for SpawnTaskHandle {
	fn execute(
		&self,
		future: Box<dyn Future<Item = (), Error = ()> + Send>,
	) -> Result<(), futures::future::ExecuteError<Box<dyn Future<Item = (), Error = ()> + Send>>> {
		let future = Box::new(future.select(self.on_exit.clone()).then(|_| Ok(())));
		if let Err(err) = self.sender.unbounded_send(future) {
			let kind = futures::future::ExecuteErrorKind::Shutdown;
			Err(futures::future::ExecuteError::new(kind, err.into_inner()))
		} else {
			Ok(())
		}
	}
}

macro_rules! new_impl {
	(
		$block:ty,
		$config:ident,
		$build_components:expr,
		$maintain_transaction_pool:expr,
		$offchain_workers:expr,
		$start_rpc:expr,
	) => {{
		let (signal, exit) = exit_future::signal();

		// List of asynchronous tasks to spawn. We collect them, then spawn them all at once.
		let (to_spawn_tx, to_spawn_rx) =
			mpsc::unbounded::<Box<dyn Future<Item = (), Error = ()> + Send>>();

		// Create all the components.
		let (
			client,
			on_demand,
			backend,
			keystore,
			select_chain,
			import_queue,
			finality_proof_request_builder,
			finality_proof_provider,
			network_protocol,
			transaction_pool,
			rpc_extensions,
			dht_event_tx,
		) = $build_components(&$config)?;
		let import_queue = Box::new(import_queue);
		let chain_info = client.info().chain;

		let version = $config.full_version();
		info!("Highest known block at #{}", chain_info.best_number);
		telemetry!(
			SUBSTRATE_INFO;
			"node.start";
			"height" => chain_info.best_number.saturated_into::<u64>(),
			"best" => ?chain_info.best_hash
		);

		let transaction_pool_adapter = Arc::new(TransactionPoolAdapter {
			imports_external_transactions: !$config.roles.is_light(),
			pool: transaction_pool.clone(),
			client: client.clone(),
			executor: Arc::new(SpawnTaskHandle { sender: to_spawn_tx.clone(), on_exit: exit.clone() }),
		});

		let protocol_id = {
			let protocol_id_full = match $config.chain_spec.protocol_id() {
				Some(pid) => pid,
				None => {
					warn!("Using default protocol ID {:?} because none is configured in the \
						chain specs", DEFAULT_PROTOCOL_ID
					);
					DEFAULT_PROTOCOL_ID
				}
			}.as_bytes();
			network::config::ProtocolId::from(protocol_id_full)
		};

		let block_announce_validator =
			Box::new(consensus_common::block_validation::DefaultBlockAnnounceValidator::new(client.clone()));

		let network_params = network::config::Params {
			roles: $config.roles,
			network_config: $config.network.clone(),
			chain: client.clone(),
			finality_proof_provider,
			finality_proof_request_builder,
			on_demand,
			transaction_pool: transaction_pool_adapter.clone() as _,
			import_queue,
			protocol_id,
			specialization: network_protocol,
			block_announce_validator,
		};

		let has_bootnodes = !network_params.network_config.boot_nodes.is_empty();
		let network_mut = network::NetworkWorker::new(network_params)?;
		let network = network_mut.service().clone();
		let network_status_sinks = Arc::new(Mutex::new(Vec::new()));

		let offchain_storage = backend.offchain_storage();
		let offchain_workers = match ($config.offchain_worker, offchain_storage) {
			(true, Some(db)) => {
				Some(Arc::new(offchain::OffchainWorkers::new(client.clone(), db)))
			},
			(true, None) => {
				log::warn!("Offchain workers disabled, due to lack of offchain storage support in backend.");
				None
			},
			_ => None,
		};

		{
			// block notifications
			let txpool = Arc::downgrade(&transaction_pool);
			let wclient = Arc::downgrade(&client);
			let offchain = offchain_workers.as_ref().map(Arc::downgrade);
			let to_spawn_tx_ = to_spawn_tx.clone();
			let network_state_info: Arc<dyn NetworkStateInfo + Send + Sync> = network.clone();
			let is_validator = $config.roles.is_authority();

			let events = client.import_notification_stream()
				.map(|v| Ok::<_, ()>(v)).compat()
				.for_each(move |notification| {
					let number = *notification.header.number();
					let txpool = txpool.upgrade();

					if let (Some(txpool), Some(client)) = (txpool.as_ref(), wclient.upgrade()) {
						let future = $maintain_transaction_pool(
							&BlockId::hash(notification.hash),
							&client,
							&*txpool,
							&notification.retracted,
						).map_err(|e| warn!("Pool error processing new block: {:?}", e))?;
						let _ = to_spawn_tx_.unbounded_send(future);
					}

					let offchain = offchain.as_ref().and_then(|o| o.upgrade());
					if let (Some(txpool), Some(offchain)) = (txpool, offchain) {
						let future = $offchain_workers(
							&number,
							&offchain,
							&txpool,
							&network_state_info,
							is_validator,
						).map_err(|e| warn!("Offchain workers error processing new block: {:?}", e))?;
						let _ = to_spawn_tx_.unbounded_send(future);
					}

					Ok(())
				})
				.select(exit.clone())
				.then(|_| Ok(()));
			let _ = to_spawn_tx.unbounded_send(Box::new(events));
		}

		{
			// extrinsic notifications
			let network = Arc::downgrade(&network);
			let transaction_pool_ = transaction_pool.clone();
			let events = transaction_pool.import_notification_stream()
				.map(|v| Ok::<_, ()>(v)).compat()
				.for_each(move |_| {
					if let Some(network) = network.upgrade() {
						network.trigger_repropagate();
					}
					let status = transaction_pool_.status();
					telemetry!(SUBSTRATE_INFO; "txpool.import";
						"ready" => status.ready,
						"future" => status.future
					);
					Ok(())
				})
				.select(exit.clone())
				.then(|_| Ok(()));

			let _ = to_spawn_tx.unbounded_send(Box::new(events));
		}

		// Periodically notify the telemetry.
		let transaction_pool_ = transaction_pool.clone();
		let client_ = client.clone();
		let mut sys = System::new();
		let self_pid = get_current_pid().ok();
		let (netstat_tx, netstat_rx) = mpsc::unbounded::<(NetworkStatus<_>, NetworkState)>();
		network_status_sinks.lock().push(netstat_tx);
		let tel_task = netstat_rx.for_each(move |(net_status, network_state)| {
			let info = client_.info();
			let best_number = info.chain.best_number.saturated_into::<u64>();
			let best_hash = info.chain.best_hash;
			let num_peers = net_status.num_connected_peers;
			let txpool_status = transaction_pool_.status();
			let finalized_number: u64 = info.chain.finalized_number.saturated_into::<u64>();
			let bandwidth_download = net_status.average_download_per_sec;
			let bandwidth_upload = net_status.average_upload_per_sec;

			let used_state_cache_size = match info.used_state_cache_size {
				Some(size) => size,
				None => 0,
			};

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
				"network_state" => network_state,
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
				"used_state_cache_size" => used_state_cache_size,
			);

			Ok(())
		}).select(exit.clone()).then(|_| Ok(()));
		let _ = to_spawn_tx.unbounded_send(Box::new(tel_task));

		// RPC
		let (system_rpc_tx, system_rpc_rx) = futures03::channel::mpsc::unbounded();
		let gen_handler = || {
			let system_info = rpc::system::SystemInfo {
				chain_name: $config.chain_spec.name().into(),
				impl_name: $config.impl_name.into(),
				impl_version: $config.impl_version.into(),
				properties: $config.chain_spec.properties().clone(),
			};
			$start_rpc(
				client.clone(),
				//light_components.clone(),
				system_rpc_tx.clone(),
				system_info.clone(),
				Arc::new(SpawnTaskHandle { sender: to_spawn_tx.clone(), on_exit: exit.clone() }),
				transaction_pool.clone(),
				rpc_extensions.clone(),
				keystore.clone(),
			)
		};
		let rpc_handlers = gen_handler();
		let rpc = start_rpc_servers(&$config, gen_handler)?;


		let _ = to_spawn_tx.unbounded_send(Box::new(build_network_future(
			network_mut,
			client.clone(),
			network_status_sinks.clone(),
			system_rpc_rx,
			has_bootnodes,
			dht_event_tx,
		)
			.map_err(|_| ())
			.select(exit.clone())
			.then(|_| Ok(()))));

		let telemetry_connection_sinks: Arc<Mutex<Vec<mpsc::UnboundedSender<()>>>> = Default::default();

		// Telemetry
		let telemetry = $config.telemetry_endpoints.clone().map(|endpoints| {
			let is_authority = $config.roles.is_authority();
			let network_id = network.local_peer_id().to_base58();
			let name = $config.name.clone();
			let impl_name = $config.impl_name.to_owned();
			let version = version.clone();
			let chain_name = $config.chain_spec.name().to_owned();
			let telemetry_connection_sinks_ = telemetry_connection_sinks.clone();
			let telemetry = tel::init_telemetry(tel::TelemetryConfig {
				endpoints,
				wasm_external_transport: $config.telemetry_external_transport.take(),
			});
			let future = telemetry.clone()
				.map(|ev| Ok::<_, ()>(ev))
				.compat()
				.for_each(move |event| {
					// Safe-guard in case we add more events in the future.
					let tel::TelemetryEvent::Connected = event;

					telemetry!(SUBSTRATE_INFO; "system.connected";
						"name" => name.clone(),
						"implementation" => impl_name.clone(),
						"version" => version.clone(),
						"config" => "",
						"chain" => chain_name.clone(),
						"authority" => is_authority,
						"network_id" => network_id.clone()
					);

					telemetry_connection_sinks_.lock().retain(|sink| {
						sink.unbounded_send(()).is_ok()
					});
					Ok(())
				});
			let _ = to_spawn_tx.unbounded_send(Box::new(future
				.select(exit.clone())
				.then(|_| Ok(()))));
			telemetry
		});

		Ok(NewService {
			client,
			network,
			network_status_sinks,
			select_chain,
			transaction_pool,
			exit,
			signal: Some(signal),
			essential_failed: Arc::new(AtomicBool::new(false)),
			to_spawn_tx,
			to_spawn_rx,
			to_poll: Vec::new(),
			rpc_handlers,
			_rpc: rpc,
			_telemetry: telemetry,
			_offchain_workers: offchain_workers,
			_telemetry_on_connect_sinks: telemetry_connection_sinks.clone(),
			keystore,
			marker: PhantomData::<$block>,
		})
	}}
}

mod builder;

/// Abstraction over a Substrate service.
pub trait AbstractService: 'static + Future<Item = (), Error = Error> +
	Executor<Box<dyn Future<Item = (), Error = ()> + Send>> + Send {
	/// Type of block of this chain.
	type Block: BlockT<Hash = H256>;
	/// Backend storage for the client.
	type Backend: 'static + client::backend::Backend<Self::Block, Blake2Hasher>;
	/// How to execute calls towards the runtime.
	type CallExecutor: 'static + client::CallExecutor<Self::Block, Blake2Hasher> + Send + Sync + Clone;
	/// API that the runtime provides.
	type RuntimeApi: Send + Sync;
	/// Chain selection algorithm.
	type SelectChain: consensus_common::SelectChain<Self::Block>;
	/// API of the transaction pool.
	type TransactionPoolApi: ChainApi<Block = Self::Block>;
	/// Network specialization.
	type NetworkSpecialization: NetworkSpecialization<Self::Block>;

	/// Get event stream for telemetry connection established events.
	fn telemetry_on_connect_stream(&self) -> mpsc::UnboundedReceiver<()>;

	/// return a shared instance of Telemetry (if enabled)
	fn telemetry(&self) -> Option<tel::Telemetry>;

	/// Spawns a task in the background that runs the future passed as parameter.
	fn spawn_task(&self, task: impl Future<Item = (), Error = ()> + Send + 'static);

	/// Spawns a task in the background that runs the future passed as
	/// parameter. The given task is considered essential, i.e. if it errors we
	/// trigger a service exit.
	fn spawn_essential_task(&self, task: impl Future<Item = (), Error = ()> + Send + 'static);

	/// Returns a handle for spawning tasks.
	fn spawn_task_handle(&self) -> SpawnTaskHandle;

	/// Returns the keystore that stores keys.
	fn keystore(&self) -> keystore::KeyStorePtr;

	/// Starts an RPC query.
	///
	/// The query is passed as a string and must be a JSON text similar to what an HTTP client
	/// would for example send.
	///
	/// Returns a `Future` that contains the optional response.
	///
	/// If the request subscribes you to events, the `Sender` in the `RpcSession` object is used to
	/// send back spontaneous events.
	fn rpc_query(&self, mem: &RpcSession, request: &str) -> Box<dyn Future<Item = Option<String>, Error = ()> + Send>;

	/// Get shared client instance.
	fn client(&self) -> Arc<client::Client<Self::Backend, Self::CallExecutor, Self::Block, Self::RuntimeApi>>;

	/// Get clone of select chain.
	fn select_chain(&self) -> Option<Self::SelectChain>;

	/// Get shared network instance.
	fn network(&self) -> Arc<NetworkService<Self::Block, Self::NetworkSpecialization, H256>>;

	/// Returns a receiver that periodically receives a status of the network.
	fn network_status(&self) -> mpsc::UnboundedReceiver<(NetworkStatus<Self::Block>, NetworkState)>;

	/// Get shared transaction pool instance.
	fn transaction_pool(&self) -> Arc<TransactionPool<Self::TransactionPoolApi>>;

	/// Get a handle to a future that will resolve on exit.
	fn on_exit(&self) -> ::exit_future::Exit;
}

impl<TBl, TBackend, TExec, TRtApi, TSc, TNetSpec, TExPoolApi, TOc> AbstractService for
	NewService<TBl, Client<TBackend, TExec, TBl, TRtApi>, TSc, NetworkStatus<TBl>,
		NetworkService<TBl, TNetSpec, H256>, TransactionPool<TExPoolApi>, TOc>
where
	TBl: BlockT<Hash = H256>,
	TBackend: 'static + client::backend::Backend<TBl, Blake2Hasher>,
	TExec: 'static + client::CallExecutor<TBl, Blake2Hasher> + Send + Sync + Clone,
	TRtApi: 'static + Send + Sync,
	TSc: consensus_common::SelectChain<TBl> + 'static + Clone + Send,
	TExPoolApi: 'static + ChainApi<Block = TBl>,
	TOc: 'static + Send + Sync,
	TNetSpec: NetworkSpecialization<TBl>,
{
	type Block = TBl;
	type Backend = TBackend;
	type CallExecutor = TExec;
	type RuntimeApi = TRtApi;
	type SelectChain = TSc;
	type TransactionPoolApi = TExPoolApi;
	type NetworkSpecialization = TNetSpec;

	fn telemetry_on_connect_stream(&self) -> mpsc::UnboundedReceiver<()> {
		let (sink, stream) = mpsc::unbounded();
		self._telemetry_on_connect_sinks.lock().push(sink);
		stream
	}

	fn telemetry(&self) -> Option<tel::Telemetry> {
		self._telemetry.as_ref().map(|t| t.clone())
	}

	fn keystore(&self) -> keystore::KeyStorePtr {
		self.keystore.clone()
	}

	fn spawn_task(&self, task: impl Future<Item = (), Error = ()> + Send + 'static) {
		let task = task.select(self.on_exit()).then(|_| Ok(()));
		let _ = self.to_spawn_tx.unbounded_send(Box::new(task));
	}

	fn spawn_essential_task(&self, task: impl Future<Item = (), Error = ()> + Send + 'static) {
		let essential_failed = self.essential_failed.clone();
		let essential_task = task.map_err(move |_| {
			error!("Essential task failed. Shutting down service.");
			essential_failed.store(true, Ordering::Relaxed);
		});
		let task = essential_task.select(self.on_exit()).then(|_| Ok(()));

		let _ = self.to_spawn_tx.unbounded_send(Box::new(task));
	}

	fn spawn_task_handle(&self) -> SpawnTaskHandle {
		SpawnTaskHandle {
			sender: self.to_spawn_tx.clone(),
			on_exit: self.on_exit(),
		}
	}

	fn rpc_query(&self, mem: &RpcSession, request: &str) -> Box<dyn Future<Item = Option<String>, Error = ()> + Send> {
		Box::new(self.rpc_handlers.handle_request(request, mem.metadata.clone()))
	}

	fn client(&self) -> Arc<client::Client<Self::Backend, Self::CallExecutor, Self::Block, Self::RuntimeApi>> {
		self.client.clone()
	}

	fn select_chain(&self) -> Option<Self::SelectChain> {
		self.select_chain.clone()
	}

	fn network(&self) -> Arc<NetworkService<Self::Block, Self::NetworkSpecialization, H256>> {
		self.network.clone()
	}

	fn network_status(&self) -> mpsc::UnboundedReceiver<(NetworkStatus<Self::Block>, NetworkState)> {
		let (sink, stream) = mpsc::unbounded();
		self.network_status_sinks.lock().push(sink);
		stream
	}

	fn transaction_pool(&self) -> Arc<TransactionPool<Self::TransactionPoolApi>> {
		self.transaction_pool.clone()
	}

	fn on_exit(&self) -> exit_future::Exit {
		self.exit.clone()
	}
}

impl<TBl, TCl, TSc, TNetStatus, TNet, TTxPool, TOc> Future for
	NewService<TBl, TCl, TSc, TNetStatus, TNet, TTxPool, TOc>
{
	type Item = ();
	type Error = Error;

	fn poll(&mut self) -> Poll<Self::Item, Self::Error> {
		if self.essential_failed.load(Ordering::Relaxed) {
			return Err(Error::Other("Essential task failed.".into()));
		}

		while let Ok(Async::Ready(Some(task_to_spawn))) = self.to_spawn_rx.poll() {
			let executor = tokio_executor::DefaultExecutor::current();
			if let Err(err) = executor.execute(task_to_spawn) {
				debug!(
					target: "service",
					"Failed to spawn background task: {:?}; falling back to manual polling",
					err
				);
				self.to_poll.push(err.into_future());
			}
		}

		// Polling all the `to_poll` futures.
		while let Some(pos) = self.to_poll.iter_mut().position(|t| t.poll().map(|t| t.is_ready()).unwrap_or(true)) {
			let _ = self.to_poll.remove(pos);
		}

		// The service future never ends.
		Ok(Async::NotReady)
	}
}

impl<TBl, TCl, TSc, TNetStatus, TNet, TTxPool, TOc> Executor<Box<dyn Future<Item = (), Error = ()> + Send>> for
	NewService<TBl, TCl, TSc, TNetStatus, TNet, TTxPool, TOc>
{
	fn execute(
		&self,
		future: Box<dyn Future<Item = (), Error = ()> + Send>
	) -> Result<(), futures::future::ExecuteError<Box<dyn Future<Item = (), Error = ()> + Send>>> {
		if let Err(err) = self.to_spawn_tx.unbounded_send(future) {
			let kind = futures::future::ExecuteErrorKind::Shutdown;
			Err(futures::future::ExecuteError::new(kind, err.into_inner()))
		} else {
			Ok(())
		}
	}
}

/// Builds a never-ending future that continuously polls the network.
///
/// The `status_sink` contain a list of senders to send a periodic network status to.
fn build_network_future<
	B: BlockT,
	C: client::BlockchainEvents<B>,
	S: network::specialization::NetworkSpecialization<B>,
	H: network::ExHashT
> (
	mut network: network::NetworkWorker<B, S, H>,
	client: Arc<C>,
	status_sinks: Arc<Mutex<Vec<mpsc::UnboundedSender<(NetworkStatus<B>, NetworkState)>>>>,
	rpc_rx: futures03::channel::mpsc::UnboundedReceiver<rpc::system::Request<B>>,
	should_have_peers: bool,
	dht_event_tx: Option<mpsc::Sender<DhtEvent>>,
) -> impl Future<Item = (), Error = ()> {
	// Compatibility shim while we're transitionning to stable Futures.
	// See https://github.com/paritytech/substrate/issues/3099
	let mut rpc_rx = futures03::compat::Compat::new(rpc_rx.map(|v| Ok::<_, ()>(v)));

	// Interval at which we send status updates on the status stream.
	const STATUS_INTERVAL: Duration = Duration::from_millis(5000);
	let mut status_interval = tokio_timer::Interval::new_interval(STATUS_INTERVAL);

	let mut imported_blocks_stream = client.import_notification_stream().fuse()
		.map(|v| Ok::<_, ()>(v)).compat();
	let mut finality_notification_stream = client.finality_notification_stream().fuse()
		.map(|v| Ok::<_, ()>(v)).compat();

	futures::future::poll_fn(move || {
		let before_polling = Instant::now();

		// We poll `imported_blocks_stream`.
		while let Ok(Async::Ready(Some(notification))) = imported_blocks_stream.poll() {
			network.on_block_imported(notification.hash, notification.header, Vec::new(), notification.is_new_best);
		}

		// We poll `finality_notification_stream`, but we only take the last event.
		let mut last = None;
		while let Ok(Async::Ready(Some(item))) = finality_notification_stream.poll() {
			last = Some(item);
		}
		if let Some(notification) = last {
			network.on_block_finalized(notification.hash, notification.header);
		}

		// Poll the RPC requests and answer them.
		while let Ok(Async::Ready(Some(request))) = rpc_rx.poll() {
			match request {
				rpc::system::Request::Health(sender) => {
					let _ = sender.send(rpc::system::Health {
						peers: network.peers_debug_info().len(),
						is_syncing: network.service().is_major_syncing(),
						should_have_peers,
					});
				},
				rpc::system::Request::Peers(sender) => {
					let _ = sender.send(network.peers_debug_info().into_iter().map(|(peer_id, p)|
						rpc::system::PeerInfo {
							peer_id: peer_id.to_base58(),
							roles: format!("{:?}", p.roles),
							protocol_version: p.protocol_version,
							best_hash: p.best_hash,
							best_number: p.best_number,
						}
					).collect());
				}
				rpc::system::Request::NetworkState(sender) => {
					if let Some(network_state) = serde_json::to_value(&network.network_state()).ok() {
						let _ = sender.send(network_state);
					}
				}
			};
		}

		// Interval report for the external API.
		while let Ok(Async::Ready(_)) = status_interval.poll() {
			let status = NetworkStatus {
				sync_state: network.sync_state(),
				best_seen_block: network.best_seen_block(),
				num_sync_peers: network.num_sync_peers(),
				num_connected_peers: network.num_connected_peers(),
				num_active_peers: network.num_active_peers(),
				average_download_per_sec: network.average_download_per_sec(),
				average_upload_per_sec: network.average_upload_per_sec(),
			};
			let state = network.network_state();

			status_sinks.lock().retain(|sink| sink.unbounded_send((status.clone(), state.clone())).is_ok());
		}

		// Main network polling.
		while let Ok(Async::Ready(Some(Event::Dht(event)))) = network.poll().map_err(|err| {
			warn!(target: "service", "Error in network: {:?}", err);
		}) {
			// Given that core/authority-discovery is the only upper stack consumer of Dht events at the moment, all Dht
			// events are being passed on to the authority-discovery module. In the future there might be multiple
			// consumers of these events. In that case this would need to be refactored to properly dispatch the events,
			// e.g. via a subscriber model.
			if let Some(Err(e)) = dht_event_tx.as_ref().map(|c| c.clone().try_send(event)) {
				if e.is_full() {
					warn!(target: "service", "Dht event channel to authority discovery is full, dropping event.");
				} else if e.is_disconnected() {
					warn!(target: "service", "Dht event channel to authority discovery is disconnected, dropping event.");
				}
			}
		};

		// Now some diagnostic for performances.
		let polling_dur = before_polling.elapsed();
		log!(
			target: "service",
			if polling_dur >= Duration::from_millis(50) { Level::Debug } else { Level::Trace },
			"Polling the network future took {:?}",
			polling_dur
		);

		Ok(Async::NotReady)
	})
}

/// Overview status of the network.
#[derive(Clone)]
pub struct NetworkStatus<B: BlockT> {
	/// Current global sync state.
	pub sync_state: network::SyncState,
	/// Target sync block number.
	pub best_seen_block: Option<NumberFor<B>>,
	/// Number of peers participating in syncing.
	pub num_sync_peers: u32,
	/// Total number of connected peers
	pub num_connected_peers: usize,
	/// Total number of active peers.
	pub num_active_peers: usize,
	/// Downloaded bytes per second averaged over the past few seconds.
	pub average_download_per_sec: u64,
	/// Uploaded bytes per second averaged over the past few seconds.
	pub average_upload_per_sec: u64,
}

impl<TBl, TCl, TSc, TNetStatus, TNet, TTxPool, TOc> Drop for
	NewService<TBl, TCl, TSc, TNetStatus, TNet, TTxPool, TOc>
{
	fn drop(&mut self) {
		debug!(target: "service", "Substrate service shutdown");
		if let Some(signal) = self.signal.take() {
			signal.fire();
		}
	}
}

/// Starts RPC servers that run in their own thread, and returns an opaque object that keeps them alive.
#[cfg(not(target_os = "unknown"))]
fn start_rpc_servers<C, G, E, H: FnMut() -> rpc_servers::RpcHandler<rpc::Metadata>>(
	config: &Configuration<C, G, E>,
	mut gen_handler: H
) -> Result<Box<dyn std::any::Any + Send + Sync>, error::Error> {
	fn maybe_start_server<T, F>(address: Option<SocketAddr>, mut start: F) -> Result<Option<T>, io::Error>
		where F: FnMut(&SocketAddr) -> Result<T, io::Error>,
	{
		Ok(match address {
			Some(mut address) => Some(start(&address)
				.or_else(|e| match e.kind() {
					io::ErrorKind::AddrInUse |
					io::ErrorKind::PermissionDenied => {
						warn!("Unable to bind server to {}. Trying random port.", address);
						address.set_port(0);
						start(&address)
					},
					_ => Err(e),
				})?),
			None => None,
		})
	}

	Ok(Box::new((
		maybe_start_server(
			config.rpc_http,
			|address| rpc_servers::start_http(address, config.rpc_cors.as_ref(), gen_handler()),
		)?,
		maybe_start_server(
			config.rpc_ws,
			|address| rpc_servers::start_ws(
				address,
				config.rpc_ws_max_connections,
				config.rpc_cors.as_ref(),
				gen_handler(),
			),
		)?.map(Mutex::new),
	)))
}

/// Starts RPC servers that run in their own thread, and returns an opaque object that keeps them alive.
#[cfg(target_os = "unknown")]
fn start_rpc_servers<C, G, E, H: FnMut() -> components::RpcHandler>(
	_: &Configuration<C, G, E>,
	_: H
) -> Result<Box<std::any::Any + Send + Sync>, error::Error> {
	Ok(Box::new(()))
}

/// An RPC session. Used to perform in-memory RPC queries (ie. RPC queries that don't go through
/// the HTTP or WebSockets server).
pub struct RpcSession {
	metadata: rpc::Metadata,
}

impl RpcSession {
	/// Creates an RPC session.
	///
	/// The `sender` is stored inside the `RpcSession` and is used to communicate spontaneous JSON
	/// messages.
	///
	/// The `RpcSession` must be kept alive in order to receive messages on the sender.
	pub fn new(sender: mpsc::Sender<String>) -> RpcSession {
		RpcSession {
			metadata: sender.into(),
		}
	}
}

/// Transaction pool adapter.
pub struct TransactionPoolAdapter<C, P> {
	imports_external_transactions: bool,
	pool: Arc<P>,
	client: Arc<C>,
	executor: TaskExecutor,
}

/// Get transactions for propagation.
///
/// Function extracted to simplify the test and prevent creating `ServiceFactory`.
fn transactions_to_propagate<PoolApi, B, H, E>(pool: &TransactionPool<PoolApi>)
	-> Vec<(H, B::Extrinsic)>
where
	PoolApi: ChainApi<Block=B, Hash=H, Error=E>,
	B: BlockT,
	H: std::hash::Hash + Eq + sr_primitives::traits::Member + sr_primitives::traits::MaybeSerialize,
	E: txpool::error::IntoPoolError + From<txpool::error::Error>,
{
	pool.ready()
		.filter(|t| t.is_propagateable())
		.map(|t| {
			let hash = t.hash.clone();
			let ex: B::Extrinsic = t.data.clone();
			(hash, ex)
		})
		.collect()
}

impl<B, H, C, PoolApi, E> network::TransactionPool<H, B> for
	TransactionPoolAdapter<C, TransactionPool<PoolApi>>
where
	C: network::ClientHandle<B> + Send + Sync,
	PoolApi: 'static + ChainApi<Block=B, Hash=H, Error=E>,
	B: BlockT,
	H: std::hash::Hash + Eq + sr_primitives::traits::Member + sr_primitives::traits::MaybeSerialize,
	E: txpool::error::IntoPoolError + From<txpool::error::Error>,
{
	fn transactions(&self) -> Vec<(H, <B as BlockT>::Extrinsic)> {
		transactions_to_propagate(&self.pool)
	}

	fn hash_of(&self, transaction: &B::Extrinsic) -> H {
		self.pool.hash_of(transaction)
	}

	fn import(&self, report_handle: ReportHandle, who: PeerId, reputation_change: i32, transaction: B::Extrinsic) {
		if !self.imports_external_transactions {
			debug!("Transaction rejected");
			return;
		}

		let encoded = transaction.encode();
		match Decode::decode(&mut &encoded[..]) {
			Ok(uxt) => {
				let best_block_id = BlockId::hash(self.client.info().chain.best_hash);
				let import_future = self.pool.submit_one(&best_block_id, uxt);
				let import_future = import_future
					.then(move |import_result| {
						match import_result {
							Ok(_) => report_handle.report_peer(who, reputation_change),
							Err(e) => match e.into_pool_error() {
								Ok(txpool::error::Error::AlreadyImported(_)) => (),
								Ok(e) => debug!("Error adding transaction to the pool: {:?}", e),
								Err(e) => debug!("Error converting pool error: {:?}", e),
							}
						}
						ready(Ok(()))
					})
					.compat();

				if let Err(e) = self.executor.execute(Box::new(import_future)) {
					warn!("Error scheduling extrinsic import: {:?}", e);
				}
			}
			Err(e) => debug!("Error decoding transaction {}", e),
		}
	}

	fn on_broadcasted(&self, propagations: HashMap<H, Vec<String>>) {
		self.pool.on_broadcasted(propagations)
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use futures03::executor::block_on;
	use consensus_common::SelectChain;
	use sr_primitives::traits::BlindCheckable;
	use substrate_test_runtime_client::{prelude::*, runtime::{Extrinsic, Transfer}};

	#[test]
	fn should_not_propagate_transactions_that_are_marked_as_such() {
		// given
		let (client, longest_chain) = TestClientBuilder::new().build_with_longest_chain();
		let client = Arc::new(client);
		let pool = Arc::new(TransactionPool::new(
			Default::default(),
			transaction_pool::FullChainApi::new(client.clone())
		));
		let best = longest_chain.best_chain().unwrap();
		let transaction = Transfer {
			amount: 5,
			nonce: 0,
			from: AccountKeyring::Alice.into(),
			to: Default::default(),
		}.into_signed_tx();
		block_on(pool.submit_one(&BlockId::hash(best.hash()), transaction.clone())).unwrap();
		block_on(pool.submit_one(&BlockId::hash(best.hash()), Extrinsic::IncludeData(vec![1]))).unwrap();
		assert_eq!(pool.status().ready, 2);

		// when
		let transactions = transactions_to_propagate(&pool);

		// then
		assert_eq!(transactions.len(), 1);
		assert!(transactions[0].1.clone().check().is_ok());
		// this should not panic
		let _ = transactions[0].1.transfer();
	}
}
