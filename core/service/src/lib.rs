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

mod components;
mod chain_spec;
pub mod config;
pub mod chain_ops;
pub mod error;

use std::io;
use std::net::SocketAddr;
use std::collections::HashMap;
use std::time::Duration;
use futures::sync::mpsc;
use parking_lot::Mutex;

use client::{BlockchainEvents, backend::Backend, runtime_api::BlockT};
use exit_future::Signal;
use futures::prelude::*;
use keystore::Store as Keystore;
use log::{info, warn, debug, error};
use parity_codec::{Encode, Decode};
use primitives::Pair;
use runtime_primitives::generic::BlockId;
use runtime_primitives::traits::{Header, NumberFor, SaturatedConversion};
use substrate_executor::NativeExecutor;
use sysinfo::{get_current_pid, ProcessExt, System, SystemExt};
use tel::{telemetry, SUBSTRATE_INFO};

pub use self::error::Error;
pub use config::{Configuration, Roles, PruningMode};
pub use chain_spec::{ChainSpec, Properties};
pub use transaction_pool::txpool::{
	self, Pool as TransactionPool, Options as TransactionPoolOptions, ChainApi, IntoPoolError
};
pub use client::FinalityNotifications;

pub use components::{ServiceFactory, FullBackend, FullExecutor, LightBackend,
	LightExecutor, Components, PoolApi, ComponentClient, ComponentOffchainStorage,
	ComponentBlock, FullClient, LightClient, FullComponents, LightComponents,
	CodeExecutor, NetworkService, FactoryChainSpec, FactoryBlock,
	FactoryFullConfiguration, RuntimeGenesis, FactoryGenesis,
	ComponentExHash, ComponentExtrinsic, FactoryExtrinsic
};
use components::{StartRPC, MaintainTransactionPool, OffchainWorker};
#[doc(hidden)]
pub use std::{ops::Deref, result::Result, sync::Arc};
#[doc(hidden)]
pub use network::{FinalityProofProvider, OnDemand};
#[doc(hidden)]
pub use futures::future::Executor;

const DEFAULT_PROTOCOL_ID: &str = "sup";

/// Substrate service.
pub struct Service<Components: components::Components> {
	client: Arc<ComponentClient<Components>>,
	select_chain: Option<<Components as components::Components>::SelectChain>,
	network: Arc<components::NetworkService<Components>>,
	/// Sinks to propagate network status updates.
	network_status_sinks: Arc<Mutex<Vec<mpsc::UnboundedSender<NetworkStatus<ComponentBlock<Components>>>>>>,
	transaction_pool: Arc<TransactionPool<Components::TransactionPoolApi>>,
	keystore: Option<Keystore>,
	exit: ::exit_future::Exit,
	signal: Option<Signal>,
	/// Sender for futures that must be spawned as background tasks.
	to_spawn_tx: mpsc::UnboundedSender<Box<dyn Future<Item = (), Error = ()> + Send>>,
	/// Receiver for futures that must be spawned as background tasks.
	to_spawn_rx: mpsc::UnboundedReceiver<Box<dyn Future<Item = (), Error = ()> + Send>>,
	/// List of futures to poll from `poll`.
	/// If spawning a background task is not possible, we instead push the task into this `Vec`.
	/// The elements must then be polled manually.
	to_poll: Vec<Box<dyn Future<Item = (), Error = ()> + Send>>,
	/// Configuration of this Service
	pub config: FactoryFullConfiguration<Components::Factory>,
	_rpc: Box<dyn std::any::Any + Send + Sync>,
	_telemetry: Option<tel::Telemetry>,
	_telemetry_on_connect_sinks: Arc<Mutex<Vec<mpsc::UnboundedSender<()>>>>,
	_offchain_workers: Option<Arc<offchain::OffchainWorkers<
		ComponentClient<Components>,
		ComponentOffchainStorage<Components>,
		ComponentBlock<Components>>
	>>,
}

/// Creates bare client without any networking.
pub fn new_client<Factory: components::ServiceFactory>(config: &FactoryFullConfiguration<Factory>)
	-> Result<Arc<ComponentClient<components::FullComponents<Factory>>>, error::Error>
{
	let executor = NativeExecutor::new(config.default_heap_pages);
	let (client, _) = components::FullComponents::<Factory>::build_client(
		config,
		executor,
	)?;
	Ok(client)
}

/// An handle for spawning tasks in the service.
#[derive(Clone)]
pub struct SpawnTaskHandle {
	sender: mpsc::UnboundedSender<Box<dyn Future<Item = (), Error = ()> + Send>>,
}

impl Executor<Box<dyn Future<Item = (), Error = ()> + Send>> for SpawnTaskHandle {
	fn execute(
		&self,
		future: Box<dyn Future<Item = (), Error = ()> + Send>
	) -> Result<(), futures::future::ExecuteError<Box<dyn Future<Item = (), Error = ()> + Send>>> {
		if let Err(err) = self.sender.unbounded_send(future) {
			let kind = futures::future::ExecuteErrorKind::Shutdown;
			Err(futures::future::ExecuteError::new(kind, err.into_inner()))
		} else {
			Ok(())
		}
	}
}

/// Stream of events for connection established to a telemetry server.
pub type TelemetryOnConnectNotifications = mpsc::UnboundedReceiver<()>;

/// Used to hook on telemetry connection established events.
pub struct TelemetryOnConnect {
	/// Event stream.
	pub telemetry_connection_sinks: TelemetryOnConnectNotifications,
}

impl<Components: components::Components> Service<Components> {
	/// Get event stream for telemetry connection established events.
	pub fn telemetry_on_connect_stream(&self) -> TelemetryOnConnectNotifications {
		let (sink, stream) = mpsc::unbounded();
		self._telemetry_on_connect_sinks.lock().push(sink);
		stream
	}

	/// Creates a new service.
	pub fn new(
		mut config: FactoryFullConfiguration<Components::Factory>,
	) -> Result<Self, error::Error> {
		let (signal, exit) = ::exit_future::signal();

		// List of asynchronous tasks to spawn. We collect them, then spawn them all at once.
		let (to_spawn_tx, to_spawn_rx) =
			mpsc::unbounded::<Box<dyn Future<Item = (), Error = ()> + Send>>();

		// Create client
		let executor = NativeExecutor::new(config.default_heap_pages);

		let mut keystore = if let Some(keystore_path) = config.keystore_path.as_ref() {
			match Keystore::open(keystore_path.clone()) {
				Ok(ks) => Some(ks),
				Err(err) => {
					error!("Failed to initialize keystore: {}", err);
					None
				}
			}
		} else {
			None
		};

		// Keep the public key for telemetry
		let public_key: String;

		// This is meant to be for testing only
		// FIXME #1063 remove this
		if let Some(keystore) = keystore.as_mut() {
			for seed in &config.keys {
				keystore.generate_from_seed(seed)?;
			}

			public_key = match keystore.contents()?.get(0) {
				Some(public_key) => public_key.to_string(),
				None => {
					let key = keystore.generate(&config.password)?;
					let public_key = key.public();
					info!("Generated a new keypair: {:?}", public_key);
					public_key.to_string()
				}
			}
		} else {
			public_key = format!("<disabled-keystore>");
		}

		let (client, on_demand) = Components::build_client(&config, executor)?;
		let select_chain = Components::build_select_chain(&mut config, client.clone())?;
		let import_queue = Box::new(Components::build_import_queue(
			&mut config,
			client.clone(),
			select_chain.clone(),
		)?);
		let finality_proof_provider = Components::build_finality_proof_provider(client.clone())?;
		let chain_info = client.info().chain;

		let version = config.full_version();
		info!("Highest known block at #{}", chain_info.best_number);
		telemetry!(SUBSTRATE_INFO; "node.start";
			"height" => chain_info.best_number.saturated_into::<u64>(),
			"best" => ?chain_info.best_hash
		);

		let network_protocol = <Components::Factory>::build_network_protocol(&config)?;
		let transaction_pool = Arc::new(
			Components::build_transaction_pool(config.transaction_pool.clone(), client.clone())?
		);
		let transaction_pool_adapter = Arc::new(TransactionPoolAdapter::<Components> {
			imports_external_transactions: !config.roles.is_light(),
			pool: transaction_pool.clone(),
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
			network::ProtocolId::from(protocol_id_full)
		};

		let network_params = network::config::Params {
			roles: config.roles,
			network_config: config.network.clone(),
			chain: client.clone(),
			finality_proof_provider,
			on_demand,
			transaction_pool: transaction_pool_adapter.clone() as _,
			import_queue,
			protocol_id,
			specialization: network_protocol,
		};

		let has_bootnodes = !network_params.network_config.boot_nodes.is_empty();
		let network_mut = network::NetworkWorker::new(network_params)?;
		let network = network_mut.service().clone();
		let network_status_sinks = Arc::new(Mutex::new(Vec::new()));

		let _ = to_spawn_tx.unbounded_send(Box::new(build_network_future(network_mut, network_status_sinks.clone())
			.map_err(|_| ())
			.select(exit.clone())
			.then(|_| Ok(()))));

		#[allow(deprecated)]
		let offchain_storage = client.backend().offchain_storage();
		let offchain_workers = match (config.offchain_worker, offchain_storage) {
			(true, Some(db)) => {
				Some(Arc::new(offchain::OffchainWorkers::new(
					client.clone(),
					db,
				)))
			},
			(true, None) => {
				log::warn!("Offchain workers disabled, due to lack of offchain storage support in backend.");
				None
			},
			_ => None,
		};

		{
			// block notifications
			let network = Arc::downgrade(&network);
			let txpool = Arc::downgrade(&transaction_pool);
			let wclient = Arc::downgrade(&client);
			let offchain = offchain_workers.as_ref().map(Arc::downgrade);
			let to_spawn_tx_ = to_spawn_tx.clone();

			let events = client.import_notification_stream()
				.for_each(move |notification| {
					let number = *notification.header.number();

					if let Some(network) = network.upgrade() {
						network.on_block_imported(notification.hash, notification.header);
					}

					if let (Some(txpool), Some(client)) = (txpool.upgrade(), wclient.upgrade()) {
						Components::RuntimeServices::maintain_transaction_pool(
							&BlockId::hash(notification.hash),
							&*client,
							&*txpool,
						).map_err(|e| warn!("Pool error processing new block: {:?}", e))?;
					}

					if let (Some(txpool), Some(offchain)) = (txpool.upgrade(), offchain.as_ref().and_then(|o| o.upgrade())) {
						let future = Components::RuntimeServices::offchain_workers(
							&number,
							&offchain,
							&txpool,
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
			// finality notifications
			let network = Arc::downgrade(&network);

			// A utility stream that drops all ready items and only returns the last one.
			// This is used to only keep the last finality notification and avoid
			// overloading the sync module with notifications.
			struct MostRecentNotification<B: BlockT>(futures::stream::Fuse<FinalityNotifications<B>>);

			impl<B: BlockT> Stream for MostRecentNotification<B> {
				type Item = <FinalityNotifications<B> as Stream>::Item;
				type Error = <FinalityNotifications<B> as Stream>::Error;

				fn poll(&mut self) -> Poll<Option<Self::Item>, Self::Error> {
					let mut last = None;
					let last = loop {
						match self.0.poll()? {
							Async::Ready(Some(item)) => { last = Some(item) }
							Async::Ready(None) => match last {
								None => return Ok(Async::Ready(None)),
								Some(last) => break last,
							},
							Async::NotReady => match last {
								None => return Ok(Async::NotReady),
								Some(last) => break last,
							},
						}
					};

					Ok(Async::Ready(Some(last)))
				}
			}

			let events = MostRecentNotification(client.finality_notification_stream().fuse())
				.for_each(move |notification| {
					if let Some(network) = network.upgrade() {
						network.on_block_finalized(notification.hash, notification.header);
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
		let network_ = network.clone();
		let mut sys = System::new();
		let self_pid = get_current_pid().ok();
		let (netstat_tx, netstat_rx) = mpsc::unbounded();
		network_status_sinks.lock().push(netstat_tx);
		let tel_task = netstat_rx.for_each(move |net_status| {
			let info = client_.info();
			let best_number = info.chain.best_number.saturated_into::<u64>();
			let best_hash = info.chain.best_hash;
			let num_peers = net_status.num_connected_peers;
			let txpool_status = transaction_pool_.status();
			let finalized_number: u64 = info.chain.finalized_number.saturated_into::<u64>();
			let bandwidth_download = net_status.average_download_per_sec;
			let bandwidth_upload = net_status.average_upload_per_sec;

			#[allow(deprecated)]
			let backend = (*client_).backend();
			let used_state_cache_size = match backend.used_state_cache_size(){
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

			let network_state = network_.network_state();

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
		let system_info = rpc::apis::system::SystemInfo {
			chain_name: config.chain_spec.name().into(),
			impl_name: config.impl_name.into(),
			impl_version: config.impl_version.into(),
			properties: config.chain_spec.properties(),
		};
		let (system_rpc_tx, system_rpc_rx) = mpsc::unbounded();
		struct ExecutorWithTx(mpsc::UnboundedSender<Box<dyn Future<Item = (), Error = ()> + Send>>);
		impl futures::future::Executor<Box<dyn Future<Item = (), Error = ()> + Send>> for ExecutorWithTx {
			fn execute(
				&self,
				future: Box<dyn Future<Item = (), Error = ()> + Send>
			) -> Result<(), futures::future::ExecuteError<Box<dyn Future<Item = (), Error = ()> + Send>>> {
				self.0.unbounded_send(future)
					.map_err(|err| {
						let kind = futures::future::ExecuteErrorKind::Shutdown;
						futures::future::ExecuteError::new(kind, err.into_inner())
					})
			}
		}
		let rpc = Components::RuntimeServices::start_rpc(
			client.clone(),
			system_rpc_tx,
			system_info,
			config.rpc_http,
			config.rpc_ws,
			config.rpc_ws_max_connections,
			config.rpc_cors.clone(),
			Arc::new(ExecutorWithTx(to_spawn_tx.clone())),
			transaction_pool.clone(),
		)?;
		let _ = to_spawn_tx.unbounded_send(Box::new(build_system_rpc_handler::<Components>(
			network.clone(),
			system_rpc_rx,
			has_bootnodes
		)));

		let telemetry_connection_sinks: Arc<Mutex<Vec<mpsc::UnboundedSender<()>>>> = Default::default();

		// Telemetry
		let telemetry = config.telemetry_endpoints.clone().map(|endpoints| {
			let is_authority = config.roles == Roles::AUTHORITY;
			let network_id = network.local_peer_id().to_base58();
			let name = config.name.clone();
			let impl_name = config.impl_name.to_owned();
			let version = version.clone();
			let chain_name = config.chain_spec.name().to_owned();
			let telemetry_connection_sinks_ = telemetry_connection_sinks.clone();
			let telemetry = tel::init_telemetry(tel::TelemetryConfig {
				endpoints,
				wasm_external_transport: config.telemetry_external_transport.take(),
			});
			let future = telemetry.clone()
				.for_each(move |event| {
					// Safe-guard in case we add more events in the future.
					let tel::TelemetryEvent::Connected = event;

					telemetry!(SUBSTRATE_INFO; "system.connected";
						"name" => name.clone(),
						"implementation" => impl_name.clone(),
						"version" => version.clone(),
						"config" => "",
						"chain" => chain_name.clone(),
						"pubkey" => &public_key,
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

		Ok(Service {
			client,
			network,
			network_status_sinks,
			select_chain,
			transaction_pool,
			signal: Some(signal),
			to_spawn_tx,
			to_spawn_rx,
			to_poll: Vec::new(),
			keystore,
			config,
			exit,
			_rpc: Box::new(rpc),
			_telemetry: telemetry,
			_offchain_workers: offchain_workers,
			_telemetry_on_connect_sinks: telemetry_connection_sinks.clone(),
		})
	}

	/// give the authority key, if we are an authority and have a key
	pub fn authority_key(&self) -> Option<primitives::ed25519::Pair> {
		if self.config.roles != Roles::AUTHORITY { return None }
		if let Some(keystore) = &self.keystore {
			if let Ok(Some(Ok(key))) =  keystore.contents().map(|keys| keys.get(0)
					.map(|k| keystore.load(k, &self.config.password)))
			{
				Some(key)
			} else {
				None
			}
		} else {
			None
		}
	}

	/// return a shared instance of Telemetry (if enabled)
	pub fn telemetry(&self) -> Option<tel::Telemetry> {
		self._telemetry.as_ref().map(|t| t.clone())
	}

	/// Spawns a task in the background that runs the future passed as parameter.
	pub fn spawn_task(&self, task: impl Future<Item = (), Error = ()> + Send + 'static) {
		let _ = self.to_spawn_tx.unbounded_send(Box::new(task));
	}

	/// Returns a handle for spawning tasks.
	pub fn spawn_task_handle(&self) -> SpawnTaskHandle {
		SpawnTaskHandle {
			sender: self.to_spawn_tx.clone(),
		}
	}

	/// Get shared client instance.
	pub fn client(&self) -> Arc<ComponentClient<Components>> {
		self.client.clone()
	}

	/// Get clone of select chain.
	pub fn select_chain(&self) -> Option<<Components as components::Components>::SelectChain> {
		self.select_chain.clone()
	}

	/// Get shared network instance.
	pub fn network(&self) -> Arc<components::NetworkService<Components>> {
		self.network.clone()
	}

	/// Returns a receiver that periodically receives a status of the network.
	pub fn network_status(&self) -> mpsc::UnboundedReceiver<NetworkStatus<ComponentBlock<Components>>> {
		let (sink, stream) = mpsc::unbounded();
		self.network_status_sinks.lock().push(sink);
		stream
	}

	/// Get shared transaction pool instance.
	pub fn transaction_pool(&self) -> Arc<TransactionPool<Components::TransactionPoolApi>> {
		self.transaction_pool.clone()
	}

	/// Get a handle to a future that will resolve on exit.
	pub fn on_exit(&self) -> ::exit_future::Exit {
		self.exit.clone()
	}
}

impl<Components> Future for Service<Components> where Components: components::Components {
	type Item = ();
	type Error = ();

	fn poll(&mut self) -> Poll<Self::Item, Self::Error> {
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
			self.to_poll.remove(pos);
		}

		// The service future never ends.
		Ok(Async::NotReady)
	}
}

impl<Components> Executor<Box<dyn Future<Item = (), Error = ()> + Send>>
	for Service<Components> where Components: components::Components
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
fn build_network_future<B: BlockT, S: network::specialization::NetworkSpecialization<B>, H: network::ExHashT>(
	mut network: network::NetworkWorker<B, S, H>,
	status_sinks: Arc<Mutex<Vec<mpsc::UnboundedSender<NetworkStatus<B>>>>>,
) -> impl Future<Item = (), Error = ()> {
	// Interval at which we send status updates on the status stream.
	const STATUS_INTERVAL: Duration = Duration::from_millis(5000);
	let mut status_interval = tokio_timer::Interval::new_interval(STATUS_INTERVAL);

	futures::future::poll_fn(move || {
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

			status_sinks.lock().retain(|sink| sink.unbounded_send(status.clone()).is_ok());
		}

		network.poll()
			.map_err(|err| {
				warn!(target: "service", "Error in network: {:?}", err);
			})
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

impl<Components> Drop for Service<Components> where Components: components::Components {
	fn drop(&mut self) {
		debug!(target: "service", "Substrate service shutdown");
		if let Some(signal) = self.signal.take() {
			signal.fire();
		}
	}
}

fn maybe_start_server<T, F>(address: Option<SocketAddr>, start: F) -> Result<Option<T>, io::Error>
	where F: Fn(&SocketAddr) -> Result<T, io::Error>,
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

/// Transaction pool adapter.
pub struct TransactionPoolAdapter<C: Components> {
	imports_external_transactions: bool,
	pool: Arc<TransactionPool<C::TransactionPoolApi>>,
	client: Arc<ComponentClient<C>>,
}

impl<C: Components> TransactionPoolAdapter<C> {
	fn best_block_id(&self) -> Option<BlockId<ComponentBlock<C>>> {
		Some(BlockId::hash(self.client.info().chain.best_hash))
	}
}

/// Get transactions for propagation.
///
/// Function extracted to simplify the test and prevent creating `ServiceFactory`.
fn transactions_to_propagate<PoolApi, B, H, E>(pool: &TransactionPool<PoolApi>)
	-> Vec<(H, B::Extrinsic)>
where
	PoolApi: ChainApi<Block=B, Hash=H, Error=E>,
	B: BlockT,
	H: std::hash::Hash + Eq + runtime_primitives::traits::Member + serde::Serialize,
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

impl<C: Components> network::TransactionPool<ComponentExHash<C>, ComponentBlock<C>> for
	TransactionPoolAdapter<C> where <C as components::Components>::RuntimeApi: Send + Sync
{
	fn transactions(&self) -> Vec<(ComponentExHash<C>, ComponentExtrinsic<C>)> {
		transactions_to_propagate(&self.pool)
	}

	fn import(&self, transaction: &ComponentExtrinsic<C>) -> Option<ComponentExHash<C>> {
		if !self.imports_external_transactions {
			debug!("Transaction rejected");
			return None;
		}

		let encoded = transaction.encode();
		if let Some(uxt) = Decode::decode(&mut &encoded[..]) {
			let best_block_id = self.best_block_id()?;
			match self.pool.submit_one(&best_block_id, uxt) {
				Ok(hash) => Some(hash),
				Err(e) => match e.into_pool_error() {
					Ok(txpool::error::Error::AlreadyImported(hash)) => {
						hash.downcast::<ComponentExHash<C>>().ok()
							.map(|x| x.as_ref().clone())
					},
					Ok(e) => {
						debug!("Error adding transaction to the pool: {:?}", e);
						None
					},
					Err(e) => {
						debug!("Error converting pool error: {:?}", e);
						None
					},
				}
			}
		} else {
			debug!("Error decoding transaction");
			None
		}
	}

	fn on_broadcasted(&self, propagations: HashMap<ComponentExHash<C>, Vec<String>>) {
		self.pool.on_broadcasted(propagations)
	}
}

/// Builds a never-ending `Future` that answers the RPC requests coming on the receiver.
fn build_system_rpc_handler<Components: components::Components>(
	network: Arc<NetworkService<Components>>,
	rx: mpsc::UnboundedReceiver<rpc::apis::system::Request<ComponentBlock<Components>>>,
	should_have_peers: bool,
) -> impl Future<Item = (), Error = ()> {
	rx.for_each(move |request| {
		match request {
			rpc::apis::system::Request::Health(sender) => {
				let _ = sender.send(rpc::apis::system::Health {
					peers: network.peers_debug_info().len(),
					is_syncing: network.is_major_syncing(),
					should_have_peers,
				});
			},
			rpc::apis::system::Request::Peers(sender) => {
				let _ = sender.send(network.peers_debug_info().into_iter().map(|(peer_id, p)| rpc::apis::system::PeerInfo {
					peer_id: peer_id.to_base58(),
					roles: format!("{:?}", p.roles),
					protocol_version: p.protocol_version,
					best_hash: p.best_hash,
					best_number: p.best_number,
				}).collect());
			}
			rpc::apis::system::Request::NetworkState(sender) => {
				let _ = sender.send(network.network_state());
			}
		};

		Ok(())
	})
}

/// Constructs a service factory with the given name that implements the `ServiceFactory` trait.
/// The required parameters are required to be given in the exact order. Some parameters are followed
/// by `{}` blocks. These blocks are required and used to initialize the given parameter.
/// In these block it is required to write a closure that takes the same number of arguments,
/// the corresponding function in the `ServiceFactory` trait provides.
///
/// # Example
///
/// ```
/// # use substrate_service::{
/// # 	construct_service_factory, Service, FullBackend, FullExecutor, LightBackend, LightExecutor,
/// # 	FullComponents, LightComponents, FactoryFullConfiguration, FullClient
/// # };
/// # use transaction_pool::{self, txpool::{Pool as TransactionPool}};
/// # use network::construct_simple_protocol;
/// # use client::{self, LongestChain};
/// # use primitives::{Pair as PairT, ed25519};
/// # use consensus_common::import_queue::{BasicQueue, Verifier};
/// # use consensus_common::{BlockOrigin, ImportBlock, well_known_cache_keys::Id as CacheKeyId};
/// # use node_runtime::{GenesisConfig, RuntimeApi};
/// # use std::sync::Arc;
/// # use node_primitives::Block;
/// # use runtime_primitives::Justification;
/// # use runtime_primitives::traits::Block as BlockT;
/// # use grandpa;
/// # construct_simple_protocol! {
/// # 	pub struct NodeProtocol where Block = Block { }
/// # }
/// # struct MyVerifier;
/// # impl<B: BlockT> Verifier<B> for MyVerifier {
/// # 	fn verify(
/// # 		&self,
/// # 		origin: BlockOrigin,
/// # 		header: B::Header,
/// # 		justification: Option<Justification>,
/// # 		body: Option<Vec<B::Extrinsic>>,
/// # 	) -> Result<(ImportBlock<B>, Option<Vec<(CacheKeyId, Vec<u8>)>>), String> {
/// # 		unimplemented!();
/// # 	}
/// # }
/// type FullChainApi<T> = transaction_pool::ChainApi<
/// 	client::Client<FullBackend<T>, FullExecutor<T>, Block, RuntimeApi>, Block>;
/// type LightChainApi<T> = transaction_pool::ChainApi<
/// 	client::Client<LightBackend<T>, LightExecutor<T>, Block, RuntimeApi>, Block>;
///
/// construct_service_factory! {
/// 	struct Factory {
/// 		// Declare the block type
/// 		Block = Block,
/// 		RuntimeApi = RuntimeApi,
/// 		// Declare the network protocol and give an initializer.
/// 		NetworkProtocol = NodeProtocol { |config| Ok(NodeProtocol::new()) },
/// 		RuntimeDispatch = node_executor::Executor,
/// 		FullTransactionPoolApi = FullChainApi<Self>
/// 			{ |config, client| Ok(TransactionPool::new(config, transaction_pool::ChainApi::new(client))) },
/// 		LightTransactionPoolApi = LightChainApi<Self>
/// 			{ |config, client| Ok(TransactionPool::new(config, transaction_pool::ChainApi::new(client))) },
/// 		Genesis = GenesisConfig,
/// 		Configuration = (),
/// 		FullService = FullComponents<Self>
/// 			{ |config| <FullComponents<Factory>>::new(config) },
/// 		// Setup as Consensus Authority (if the role and key are given)
/// 		AuthoritySetup = {
/// 			|service: Self::FullService, key: Option<Arc<ed25519::Pair>>| {
/// 				Ok(service)
/// 			}},
/// 		LightService = LightComponents<Self>
/// 			{ |config| <LightComponents<Factory>>::new(config) },
/// 		FullImportQueue = BasicQueue<Block>
/// 			{ |_, client, _| Ok(BasicQueue::new(Arc::new(MyVerifier), client, None, None, None)) },
/// 		LightImportQueue = BasicQueue<Block>
/// 			{ |_, client| Ok(BasicQueue::new(Arc::new(MyVerifier), client, None, None, None)) },
/// 		SelectChain = LongestChain<FullBackend<Self>, Self::Block>
/// 			{ |config: &FactoryFullConfiguration<Self>, client: Arc<FullClient<Self>>| {
/// 				#[allow(deprecated)]
/// 				Ok(LongestChain::new(client.backend().clone()))
/// 			}},
/// 		FinalityProofProvider = { |client: Arc<FullClient<Self>>| {
/// 				Ok(Some(Arc::new(grandpa::FinalityProofProvider::new(client.clone(), client)) as _))
/// 			}},
/// 	}
/// }
/// ```
#[macro_export]
macro_rules! construct_service_factory {
	(
		$(#[$attr:meta])*
		struct $name:ident {
			Block = $block:ty,
			RuntimeApi = $runtime_api:ty,
			NetworkProtocol = $protocol:ty { $( $protocol_init:tt )* },
			RuntimeDispatch = $dispatch:ty,
			FullTransactionPoolApi = $full_transaction:ty { $( $full_transaction_init:tt )* },
			LightTransactionPoolApi = $light_transaction:ty { $( $light_transaction_init:tt )* },
			Genesis = $genesis:ty,
			Configuration = $config:ty,
			FullService = $full_service:ty { $( $full_service_init:tt )* },
			AuthoritySetup = { $( $authority_setup:tt )* },
			LightService = $light_service:ty { $( $light_service_init:tt )* },
			FullImportQueue = $full_import_queue:ty
				{ $( $full_import_queue_init:tt )* },
			LightImportQueue = $light_import_queue:ty
				{ $( $light_import_queue_init:tt )* },
			SelectChain = $select_chain:ty
				{ $( $select_chain_init:tt )* },
			FinalityProofProvider = { $( $finality_proof_provider_init:tt )* },
		}
	) => {
		$( #[$attr] )*
		pub struct $name {}

		#[allow(unused_variables)]
		impl $crate::ServiceFactory for $name {
			type Block = $block;
			type RuntimeApi = $runtime_api;
			type NetworkProtocol = $protocol;
			type RuntimeDispatch = $dispatch;
			type FullTransactionPoolApi = $full_transaction;
			type LightTransactionPoolApi = $light_transaction;
			type Genesis = $genesis;
			type Configuration = $config;
			type FullService = $full_service;
			type LightService = $light_service;
			type FullImportQueue = $full_import_queue;
			type LightImportQueue = $light_import_queue;
			type SelectChain = $select_chain;

			fn build_full_transaction_pool(
				config: $crate::TransactionPoolOptions,
				client: $crate::Arc<$crate::FullClient<Self>>
			) -> $crate::Result<$crate::TransactionPool<Self::FullTransactionPoolApi>, $crate::Error>
			{
				( $( $full_transaction_init )* ) (config, client)
			}

			fn build_light_transaction_pool(
				config: $crate::TransactionPoolOptions,
				client: $crate::Arc<$crate::LightClient<Self>>
			) -> $crate::Result<$crate::TransactionPool<Self::LightTransactionPoolApi>, $crate::Error>
			{
				( $( $light_transaction_init )* ) (config, client)
			}

			fn build_network_protocol(config: &$crate::FactoryFullConfiguration<Self>)
				-> $crate::Result<Self::NetworkProtocol, $crate::Error>
			{
				( $( $protocol_init )* ) (config)
			}

			fn build_select_chain(
				config: &mut $crate::FactoryFullConfiguration<Self>,
				client: Arc<$crate::FullClient<Self>>
			) -> $crate::Result<Self::SelectChain, $crate::Error> {
				( $( $select_chain_init )* ) (config, client)
			}

			fn build_full_import_queue(
				config: &mut $crate::FactoryFullConfiguration<Self>,
				client: $crate::Arc<$crate::FullClient<Self>>,
				select_chain: Self::SelectChain
			) -> $crate::Result<Self::FullImportQueue, $crate::Error> {
				( $( $full_import_queue_init )* ) (config, client, select_chain)
			}

			fn build_light_import_queue(
				config: &mut FactoryFullConfiguration<Self>,
				client: Arc<$crate::LightClient<Self>>,
			) -> Result<Self::LightImportQueue, $crate::Error> {
				( $( $light_import_queue_init )* ) (config, client)
			}

			fn build_finality_proof_provider(
				client: Arc<$crate::FullClient<Self>>
			) -> Result<Option<Arc<$crate::FinalityProofProvider<Self::Block>>>, $crate::Error> {
				( $( $finality_proof_provider_init )* ) (client)
			}

			fn new_light(
				config: $crate::FactoryFullConfiguration<Self>
			) -> $crate::Result<Self::LightService, $crate::Error>
			{
				( $( $light_service_init )* ) (config)
			}

			fn new_full(
				config: $crate::FactoryFullConfiguration<Self>
			) -> Result<Self::FullService, $crate::Error>
			{
				( $( $full_service_init )* ) (config).and_then(|service| {
					let key = (&service).authority_key().map(Arc::new);
					($( $authority_setup )*)(service, key)
				})
			}
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use consensus_common::SelectChain;
	use runtime_primitives::traits::BlindCheckable;
	use substrate_test_runtime_client::{prelude::*, runtime::{Extrinsic, Transfer}};

	#[test]
	fn should_not_propagate_transactions_that_are_marked_as_such() {
		// given
		let (client, longest_chain) = TestClientBuilder::new().build_with_longest_chain();
		let client = Arc::new(client);
		let pool = Arc::new(TransactionPool::new(
			Default::default(),
			transaction_pool::ChainApi::new(client.clone())
		));
		let best = longest_chain.best_chain().unwrap();
		let transaction = Transfer {
			amount: 5,
			nonce: 0,
			from: AccountKeyring::Alice.into(),
			to: Default::default(),
		}.into_signed_tx();
		pool.submit_one(&BlockId::hash(best.hash()), transaction.clone()).unwrap();
		pool.submit_one(&BlockId::hash(best.hash()), Extrinsic::IncludeData(vec![1])).unwrap();
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
