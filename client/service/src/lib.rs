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

//! Substrate service. Starts a thread that spins up the network, client, and extrinsic pool.
//! Manages communication between them.

#![warn(missing_docs)]
#![recursion_limit="128"]

pub mod config;
#[macro_use]
pub mod chain_ops;
pub mod error;

mod metrics;
mod builder;
#[cfg(feature = "test-helpers")]
pub mod client;
#[cfg(not(feature = "test-helpers"))]
mod client;
mod status_sinks;
mod task_manager;

use std::{io, pin::Pin};
use std::marker::PhantomData;
use std::net::SocketAddr;
use std::collections::HashMap;
use std::time::Duration;
use wasm_timer::Instant;
use std::task::{Poll, Context};
use parking_lot::Mutex;

use client::Client;
use futures::{
	Future, FutureExt, Stream, StreamExt,
	compat::*,
	sink::SinkExt,
	task::{Spawn, FutureObj, SpawnError},
};
use sc_network::{NetworkService, network_state::NetworkState, PeerId};
use log::{log, warn, debug, error, Level};
use codec::{Encode, Decode};
use sp_runtime::generic::BlockId;
use sp_runtime::traits::{NumberFor, Block as BlockT};
use parity_util_mem::MallocSizeOf;
use sp_utils::mpsc::{tracing_unbounded, TracingUnboundedReceiver,  TracingUnboundedSender};

pub use self::error::Error;
pub use self::builder::{
	new_full_client, new_client,
	ServiceBuilder, ServiceBuilderCommand, TFullClient, TLightClient, TFullBackend, TLightBackend,
	TFullCallExecutor, TLightCallExecutor,
};
pub use config::{Configuration, DatabaseConfig, PruningMode, Role, RpcMethods, TaskType};
pub use sc_chain_spec::{
	ChainSpec, GenericChainSpec, Properties, RuntimeGenesis, Extension as ChainSpecExtension,
	NoExtension, ChainType,
};
pub use sp_transaction_pool::{TransactionPool, InPoolTransaction, error::IntoPoolError};
pub use sc_transaction_pool::txpool::Options as TransactionPoolOptions;
pub use sc_rpc::Metadata as RpcMetadata;
pub use sc_executor::NativeExecutionDispatch;
#[doc(hidden)]
pub use std::{ops::Deref, result::Result, sync::Arc};
#[doc(hidden)]
pub use sc_network::config::{
	FinalityProofProvider, OnDemand, BoxFinalityProofRequestBuilder, TransactionImport,
	TransactionImportFuture,
};
pub use sc_tracing::TracingReceiver;
pub use task_manager::SpawnTaskHandle;
use task_manager::TaskManager;
use sp_blockchain::{HeaderBackend, HeaderMetadata};
use sp_api::{ApiExt, ConstructRuntimeApi, ApiErrorExt};
use sc_client_api::{
	Backend as BackendT, BlockchainEvents, CallExecutor, UsageProvider,
};
use sp_block_builder::BlockBuilder;

const DEFAULT_PROTOCOL_ID: &str = "sup";

/// A type that implements `MallocSizeOf` on native but not wasm.
#[cfg(not(target_os = "unknown"))]
pub trait MallocSizeOfWasm: MallocSizeOf {}
#[cfg(target_os = "unknown")]
pub trait MallocSizeOfWasm {}
#[cfg(not(target_os = "unknown"))]
impl<T: MallocSizeOf> MallocSizeOfWasm for T {}
#[cfg(target_os = "unknown")]
impl<T> MallocSizeOfWasm for T {}

/// Substrate service.
pub struct Service<TBl, TCl, TSc, TNetStatus, TNet, TTxPool, TOc> {
	client: Arc<TCl>,
	task_manager: TaskManager,
	select_chain: Option<TSc>,
	network: Arc<TNet>,
	/// Sinks to propagate network status updates.
	/// For each element, every time the `Interval` fires we push an element on the sender.
	network_status_sinks: Arc<Mutex<status_sinks::StatusSinks<(TNetStatus, NetworkState)>>>,
	transaction_pool: Arc<TTxPool>,
	/// Send a signal when a spawned essential task has concluded. The next time
	/// the service future is polled it should complete with an error.
	essential_failed_tx: TracingUnboundedSender<()>,
	/// A receiver for spawned essential-tasks concluding.
	essential_failed_rx: TracingUnboundedReceiver<()>,
	rpc_handlers: sc_rpc_server::RpcHandler<sc_rpc::Metadata>,
	_rpc: Box<dyn std::any::Any + Send + Sync>,
	_telemetry: Option<sc_telemetry::Telemetry>,
	_telemetry_on_connect_sinks: Arc<Mutex<Vec<TracingUnboundedSender<()>>>>,
	_offchain_workers: Option<Arc<TOc>>,
	keystore: sc_keystore::KeyStorePtr,
	marker: PhantomData<TBl>,
	prometheus_registry: Option<prometheus_endpoint::Registry>,
}

impl<TBl, TCl, TSc, TNetStatus, TNet, TTxPool, TOc> Unpin for Service<TBl, TCl, TSc, TNetStatus, TNet, TTxPool, TOc> {}

/// Abstraction over a Substrate service.
pub trait AbstractService: Future<Output = Result<(), Error>> + Send + Unpin + Spawn + 'static {
	/// Type of block of this chain.
	type Block: BlockT;
	/// Backend storage for the client.
	type Backend: 'static + BackendT<Self::Block>;
	/// How to execute calls towards the runtime.
	type CallExecutor: 'static + CallExecutor<Self::Block> + Send + Sync + Clone;
	/// API that the runtime provides.
	type RuntimeApi: Send + Sync;
	/// Chain selection algorithm.
	type SelectChain: sp_consensus::SelectChain<Self::Block>;
	/// Transaction pool.
	type TransactionPool: TransactionPool<Block = Self::Block> + MallocSizeOfWasm;
	/// The generic Client type, the bounds here are the ones specifically required by
	/// internal crates like sc_informant.
	type Client:
		HeaderMetadata<Self::Block, Error = sp_blockchain::Error> + UsageProvider<Self::Block>
		+ BlockchainEvents<Self::Block> + HeaderBackend<Self::Block> + Send + Sync;

	/// Get event stream for telemetry connection established events.
	fn telemetry_on_connect_stream(&self) -> TracingUnboundedReceiver<()>;

	/// return a shared instance of Telemetry (if enabled)
	fn telemetry(&self) -> Option<sc_telemetry::Telemetry>;

	/// Spawns a task in the background that runs the future passed as parameter.
	///
	/// Information about this task will be reported to Prometheus.
	///
	/// The task name is a `&'static str` as opposed to a `String`. The reason for that is that
	/// in order to avoid memory consumption issues with the Prometheus metrics, the set of
	/// possible task names has to be bounded.
	fn spawn_task(&self, name: &'static str, task: impl Future<Output = ()> + Send + 'static);

	/// Spawns a task in the background that runs the future passed as
	/// parameter. The given task is considered essential, i.e. if it errors we
	/// trigger a service exit.
	fn spawn_essential_task(&self, name: &'static str, task: impl Future<Output = ()> + Send + 'static);

	/// Returns a handle for spawning tasks.
	fn spawn_task_handle(&self) -> SpawnTaskHandle;

	/// Returns the keystore that stores keys.
	fn keystore(&self) -> sc_keystore::KeyStorePtr;

	/// Starts an RPC query.
	///
	/// The query is passed as a string and must be a JSON text similar to what an HTTP client
	/// would for example send.
	///
	/// Returns a `Future` that contains the optional response.
	///
	/// If the request subscribes you to events, the `Sender` in the `RpcSession` object is used to
	/// send back spontaneous events.
	fn rpc_query(&self, mem: &RpcSession, request: &str) -> Pin<Box<dyn Future<Output = Option<String>> + Send>>;

	/// Get shared client instance.
	fn client(&self) -> Arc<Self::Client>;

	/// Get clone of select chain.
	fn select_chain(&self) -> Option<Self::SelectChain>;

	/// Get shared network instance.
	fn network(&self)
		-> Arc<NetworkService<Self::Block, <Self::Block as BlockT>::Hash>>;

	/// Returns a receiver that periodically receives a status of the network.
	fn network_status(&self, interval: Duration) -> TracingUnboundedReceiver<(NetworkStatus<Self::Block>, NetworkState)>;

	/// Get shared transaction pool instance.
	fn transaction_pool(&self) -> Arc<Self::TransactionPool>;

	/// Get a handle to a future that will resolve on exit.
	#[deprecated(note = "Use `spawn_task`/`spawn_essential_task` instead, those functions will attach on_exit signal.")]
	fn on_exit(&self) -> ::exit_future::Exit;

	/// Get the prometheus metrics registry, if available.
	fn prometheus_registry(&self) -> Option<prometheus_endpoint::Registry>;
}

impl<TBl, TBackend, TExec, TRtApi, TSc, TExPool, TOc> AbstractService for
	Service<TBl, Client<TBackend, TExec, TBl, TRtApi>, TSc, NetworkStatus<TBl>,
		NetworkService<TBl, TBl::Hash>, TExPool, TOc>
where
	TBl: BlockT,
	TBackend: 'static + BackendT<TBl>,
	TExec: 'static + CallExecutor<TBl, Backend = TBackend> + Send + Sync + Clone,
	TRtApi: 'static + Send + Sync + ConstructRuntimeApi<TBl, Client<TBackend, TExec, TBl, TRtApi>>,
	<TRtApi as ConstructRuntimeApi<TBl, Client<TBackend, TExec, TBl, TRtApi>>>::RuntimeApi:
		sp_api::Core<TBl>
		+ ApiExt<TBl, StateBackend = TBackend::State>
		+ ApiErrorExt<Error = sp_blockchain::Error>
		+ BlockBuilder<TBl>,
	TSc: sp_consensus::SelectChain<TBl> + 'static + Clone + Send + Unpin,
	TExPool: 'static + TransactionPool<Block = TBl> + MallocSizeOfWasm,
	TOc: 'static + Send + Sync,
{
	type Block = TBl;
	type Backend = TBackend;
	type CallExecutor = TExec;
	type RuntimeApi = TRtApi;
	type SelectChain = TSc;
	type TransactionPool = TExPool;
	type Client = Client<Self::Backend, Self::CallExecutor, Self::Block, Self::RuntimeApi>;

	fn telemetry_on_connect_stream(&self) -> TracingUnboundedReceiver<()> {
		let (sink, stream) = tracing_unbounded("mpsc_telemetry_on_connect");
		self._telemetry_on_connect_sinks.lock().push(sink);
		stream
	}

	fn telemetry(&self) -> Option<sc_telemetry::Telemetry> {
		self._telemetry.as_ref().map(|t| t.clone())
	}

	fn keystore(&self) -> sc_keystore::KeyStorePtr {
		self.keystore.clone()
	}

	fn spawn_task(&self, name: &'static str, task: impl Future<Output = ()> + Send + 'static) {
		self.task_manager.spawn(name, task)
	}

	fn spawn_essential_task(&self, name: &'static str, task: impl Future<Output = ()> + Send + 'static) {
		let mut essential_failed = self.essential_failed_tx.clone();
		let essential_task = std::panic::AssertUnwindSafe(task)
			.catch_unwind()
			.map(move |_| {
				error!("Essential task `{}` failed. Shutting down service.", name);
				let _ = essential_failed.send(());
			});

		let _ = self.spawn_task(name, essential_task);
	}

	fn spawn_task_handle(&self) -> SpawnTaskHandle {
		self.task_manager.spawn_handle()
	}

	fn rpc_query(&self, mem: &RpcSession, request: &str) -> Pin<Box<dyn Future<Output = Option<String>> + Send>> {
		Box::pin(
			self.rpc_handlers.handle_request(request, mem.metadata.clone())
				.compat()
				.map(|res| res.expect("this should never fail"))
		)
	}

	fn client(&self) -> Arc<Self::Client> {
		self.client.clone()
	}

	fn select_chain(&self) -> Option<Self::SelectChain> {
		self.select_chain.clone()
	}

	fn network(&self)
		-> Arc<NetworkService<Self::Block, <Self::Block as BlockT>::Hash>>
	{
		self.network.clone()
	}

	fn network_status(&self, interval: Duration) -> TracingUnboundedReceiver<(NetworkStatus<Self::Block>, NetworkState)> {
		let (sink, stream) = tracing_unbounded("mpsc_network_status");
		self.network_status_sinks.lock().push(interval, sink);
		stream
	}

	fn transaction_pool(&self) -> Arc<Self::TransactionPool> {
		self.transaction_pool.clone()
	}

	fn on_exit(&self) -> exit_future::Exit {
		self.task_manager.on_exit()
	}

	fn prometheus_registry(&self) -> Option<prometheus_endpoint::Registry> {
		self.prometheus_registry.clone()
	}
}

impl<TBl, TCl, TSc, TNetStatus, TNet, TTxPool, TOc> Future for
	Service<TBl, TCl, TSc, TNetStatus, TNet, TTxPool, TOc>
{
	type Output = Result<(), Error>;

	fn poll(self: Pin<&mut Self>, cx: &mut Context) -> Poll<Self::Output> {
		let this = Pin::into_inner(self);

		match Pin::new(&mut this.essential_failed_rx).poll_next(cx) {
			Poll::Pending => {},
			Poll::Ready(_) => {
				// Ready(None) should not be possible since we hold a live
				// sender.
				return Poll::Ready(Err(Error::Other("Essential task failed.".into())));
			}
		}

		// The service future never ends.
		Poll::Pending
	}
}

impl<TBl, TCl, TSc, TNetStatus, TNet, TTxPool, TOc> Spawn for
	Service<TBl, TCl, TSc, TNetStatus, TNet, TTxPool, TOc>
{
	fn spawn_obj(
		&self,
		future: FutureObj<'static, ()>
	) -> Result<(), SpawnError> {
		self.task_manager.spawn_handle().spawn("unnamed", future);
		Ok(())
	}
}

/// Builds a never-ending future that continuously polls the network.
///
/// The `status_sink` contain a list of senders to send a periodic network status to.
fn build_network_future<
	B: BlockT,
	C: BlockchainEvents<B>,
	H: sc_network::ExHashT
> (
	role: Role,
	mut network: sc_network::NetworkWorker<B, H>,
	client: Arc<C>,
	status_sinks: Arc<Mutex<status_sinks::StatusSinks<(NetworkStatus<B>, NetworkState)>>>,
	mut rpc_rx: TracingUnboundedReceiver<sc_rpc::system::Request<B>>,
	should_have_peers: bool,
	announce_imported_blocks: bool,
) -> impl Future<Output = ()> {
	let mut imported_blocks_stream = client.import_notification_stream().fuse();
	let mut finality_notification_stream = client.finality_notification_stream().fuse();

	futures::future::poll_fn(move |cx| {
		let before_polling = Instant::now();

		// We poll `imported_blocks_stream`.
		while let Poll::Ready(Some(notification)) = Pin::new(&mut imported_blocks_stream).poll_next(cx) {
			network.on_block_imported(notification.header, notification.is_new_best);

			if announce_imported_blocks {
				network.service().announce_block(notification.hash, Vec::new());
			}
		}

		// We poll `finality_notification_stream`, but we only take the last event.
		let mut last = None;
		while let Poll::Ready(Some(item)) = Pin::new(&mut finality_notification_stream).poll_next(cx) {
			last = Some(item);
		}
		if let Some(notification) = last {
			network.on_block_finalized(notification.hash, notification.header);
		}

		// Poll the RPC requests and answer them.
		while let Poll::Ready(Some(request)) = Pin::new(&mut rpc_rx).poll_next(cx) {
			match request {
				sc_rpc::system::Request::Health(sender) => {
					let _ = sender.send(sc_rpc::system::Health {
						peers: network.peers_debug_info().len(),
						is_syncing: network.service().is_major_syncing(),
						should_have_peers,
					});
				},
				sc_rpc::system::Request::LocalPeerId(sender) => {
					let _ = sender.send(network.local_peer_id().to_base58());
				},
				sc_rpc::system::Request::LocalListenAddresses(sender) => {
					let peer_id = network.local_peer_id().clone().into();
					let p2p_proto_suffix = sc_network::multiaddr::Protocol::P2p(peer_id);
					let addresses = network.listen_addresses()
						.map(|addr| addr.clone().with(p2p_proto_suffix.clone()).to_string())
						.collect();
					let _ = sender.send(addresses);
				},
				sc_rpc::system::Request::Peers(sender) => {
					let _ = sender.send(network.peers_debug_info().into_iter().map(|(peer_id, p)|
						sc_rpc::system::PeerInfo {
							peer_id: peer_id.to_base58(),
							roles: format!("{:?}", p.roles),
							protocol_version: p.protocol_version,
							best_hash: p.best_hash,
							best_number: p.best_number,
						}
					).collect());
				}
				sc_rpc::system::Request::NetworkState(sender) => {
					if let Some(network_state) = serde_json::to_value(&network.network_state()).ok() {
						let _ = sender.send(network_state);
					}
				}
				sc_rpc::system::Request::NetworkAddReservedPeer(peer_addr, sender) => {
					let x = network.add_reserved_peer(peer_addr)
						.map_err(sc_rpc::system::error::Error::MalformattedPeerArg);
					let _ = sender.send(x);
				}
				sc_rpc::system::Request::NetworkRemoveReservedPeer(peer_id, sender) => {
					let _ = match peer_id.parse::<PeerId>() {
						Ok(peer_id) => {
							network.remove_reserved_peer(peer_id);
							sender.send(Ok(()))
						}
						Err(e) => sender.send(Err(sc_rpc::system::error::Error::MalformattedPeerArg(
							e.to_string(),
						))),
					};
				}
				sc_rpc::system::Request::NodeRoles(sender) => {
					use sc_rpc::system::NodeRole;

					let node_role = match role {
						Role::Authority { .. } => NodeRole::Authority,
						Role::Light => NodeRole::LightClient,
						Role::Full => NodeRole::Full,
						Role::Sentry { .. } => NodeRole::Sentry,
					};

					let _ = sender.send(vec![node_role]);
				}
			};
		}

		// Interval report for the external API.
		status_sinks.lock().poll(cx, || {
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
			(status, state)
		});

		// Main network polling.
		if let Poll::Ready(Ok(())) = Pin::new(&mut network).poll(cx).map_err(|err| {
			warn!(target: "service", "Error in network: {:?}", err);
		}) {
			return Poll::Ready(());
		}

		// Now some diagnostic for performances.
		let polling_dur = before_polling.elapsed();
		log!(
			target: "service",
			if polling_dur >= Duration::from_secs(1) { Level::Warn } else { Level::Trace },
			"⚠️  Polling the network future took {:?}",
			polling_dur
		);

		Poll::Pending
	})
}

/// Overview status of the network.
#[derive(Clone)]
pub struct NetworkStatus<B: BlockT> {
	/// Current global sync state.
	pub sync_state: sc_network::SyncState,
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

#[cfg(not(target_os = "unknown"))]
// Wrapper for HTTP and WS servers that makes sure they are properly shut down.
mod waiting {
	pub struct HttpServer(pub Option<sc_rpc_server::HttpServer>);
	impl Drop for HttpServer {
		fn drop(&mut self) {
			if let Some(server) = self.0.take() {
				server.close_handle().close();
				server.wait();
			}
		}
	}

	pub struct WsServer(pub Option<sc_rpc_server::WsServer>);
	impl Drop for WsServer {
		fn drop(&mut self) {
			if let Some(server) = self.0.take() {
				server.close_handle().close();
				let _ = server.wait();
			}
		}
	}
}

/// Starts RPC servers that run in their own thread, and returns an opaque object that keeps them alive.
#[cfg(not(target_os = "unknown"))]
fn start_rpc_servers<H: FnMut(sc_rpc::DenyUnsafe) -> sc_rpc_server::RpcHandler<sc_rpc::Metadata>>(
	config: &Configuration,
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
						warn!("Unable to bind RPC server to {}. Trying random port.", address);
						address.set_port(0);
						start(&address)
					},
					_ => Err(e),
				})?),
			None => None,
		})
	}

	fn deny_unsafe(addr: &Option<SocketAddr>, methods: &RpcMethods) -> sc_rpc::DenyUnsafe {
		let is_exposed_addr = addr.map(|x| x.ip().is_loopback()).unwrap_or(false);
		match (is_exposed_addr, methods) {
			| (_, RpcMethods::Unsafe)
			| (false, RpcMethods::Auto) => sc_rpc::DenyUnsafe::No,
			_ => sc_rpc::DenyUnsafe::Yes
		}
	}

	Ok(Box::new((
		maybe_start_server(
			config.rpc_http,
			|address| sc_rpc_server::start_http(
				address,
				config.rpc_cors.as_ref(),
				gen_handler(deny_unsafe(&config.rpc_http, &config.rpc_methods)),
			),
		)?.map(|s| waiting::HttpServer(Some(s))),
		maybe_start_server(
			config.rpc_ws,
			|address| sc_rpc_server::start_ws(
				address,
				config.rpc_ws_max_connections,
				config.rpc_cors.as_ref(),
				gen_handler(deny_unsafe(&config.rpc_ws, &config.rpc_methods)),
			),
		)?.map(|s| waiting::WsServer(Some(s))),
	)))
}

/// Starts RPC servers that run in their own thread, and returns an opaque object that keeps them alive.
#[cfg(target_os = "unknown")]
fn start_rpc_servers<H: FnMut(sc_rpc::DenyUnsafe) -> sc_rpc_server::RpcHandler<sc_rpc::Metadata>>(
	_: &Configuration,
	_: H
) -> Result<Box<dyn std::any::Any + Send + Sync>, error::Error> {
	Ok(Box::new(()))
}

/// An RPC session. Used to perform in-memory RPC queries (ie. RPC queries that don't go through
/// the HTTP or WebSockets server).
#[derive(Clone)]
pub struct RpcSession {
	metadata: sc_rpc::Metadata,
}

impl RpcSession {
	/// Creates an RPC session.
	///
	/// The `sender` is stored inside the `RpcSession` and is used to communicate spontaneous JSON
	/// messages.
	///
	/// The `RpcSession` must be kept alive in order to receive messages on the sender.
	pub fn new(sender: futures01::sync::mpsc::Sender<String>) -> RpcSession {
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
}

/// Get transactions for propagation.
///
/// Function extracted to simplify the test and prevent creating `ServiceFactory`.
fn transactions_to_propagate<Pool, B, H, E>(pool: &Pool)
	-> Vec<(H, B::Extrinsic)>
where
	Pool: TransactionPool<Block=B, Hash=H, Error=E>,
	B: BlockT,
	H: std::hash::Hash + Eq + sp_runtime::traits::Member + sp_runtime::traits::MaybeSerialize,
	E: IntoPoolError + From<sp_transaction_pool::error::Error>,
{
	pool.ready()
		.filter(|t| t.is_propagable())
		.map(|t| {
			let hash = t.hash().clone();
			let ex: B::Extrinsic = t.data().clone();
			(hash, ex)
		})
		.collect()
}

impl<B, H, C, Pool, E> sc_network::config::TransactionPool<H, B> for
	TransactionPoolAdapter<C, Pool>
where
	C: sc_network::config::Client<B> + Send + Sync,
	Pool: 'static + TransactionPool<Block=B, Hash=H, Error=E>,
	B: BlockT,
	H: std::hash::Hash + Eq + sp_runtime::traits::Member + sp_runtime::traits::MaybeSerialize,
	E: 'static + IntoPoolError + From<sp_transaction_pool::error::Error>,
{
	fn transactions(&self) -> Vec<(H, B::Extrinsic)> {
		transactions_to_propagate(&*self.pool)
	}

	fn hash_of(&self, transaction: &B::Extrinsic) -> H {
		self.pool.hash_of(transaction)
	}

	fn import(
		&self,
		transaction: B::Extrinsic,
	) -> TransactionImportFuture {
		if !self.imports_external_transactions {
			debug!("Transaction rejected");
			Box::pin(futures::future::ready(TransactionImport::None));
		}

		let encoded = transaction.encode();
		let uxt = match Decode::decode(&mut &encoded[..]) {
			Ok(uxt) => uxt,
			Err(e) => {
				debug!("Transaction invalid: {:?}", e);
				return Box::pin(futures::future::ready(TransactionImport::Bad));
			}
		};

		let best_block_id = BlockId::hash(self.client.info().best_hash);

		let import_future = self.pool.submit_one(&best_block_id, sp_transaction_pool::TransactionSource::External, uxt);
		Box::pin(async move {
			match import_future.await {
				Ok(_) => TransactionImport::NewGood,
				Err(e) => match e.into_pool_error() {
					Ok(sp_transaction_pool::error::Error::AlreadyImported(_)) => TransactionImport::KnownGood,
					Ok(e) => {
						debug!("Error adding transaction to the pool: {:?}", e);
						TransactionImport::Bad
					}
					Err(e) => {
						debug!("Error converting pool error: {:?}", e);
						// it is not bad at least, just some internal node logic error, so peer is innocent.
						TransactionImport::KnownGood
					}
				}
			}
		})
	}

	fn on_broadcasted(&self, propagations: HashMap<H, Vec<String>>) {
		self.pool.on_broadcasted(propagations)
	}

	fn transaction(&self, hash: &H) -> Option<B::Extrinsic> {
		self.pool.ready_transaction(hash)
			.and_then(
				// Only propagable transactions should be resolved for network service.
				|tx| if tx.is_propagable() { Some(tx.data().clone()) } else { None }
			)
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use futures::executor::block_on;
	use sp_consensus::SelectChain;
	use sp_runtime::traits::BlindCheckable;
	use substrate_test_runtime_client::{prelude::*, runtime::{Extrinsic, Transfer}};
	use sc_transaction_pool::{BasicPool, FullChainApi};

	#[test]
	fn should_not_propagate_transactions_that_are_marked_as_such() {
		// given
		let (client, longest_chain) = TestClientBuilder::new().build_with_longest_chain();
		let client = Arc::new(client);
		let pool = Arc::new(BasicPool::new(
			Default::default(),
			Arc::new(FullChainApi::new(client.clone())),
			None,
		).0);
		let source = sp_runtime::transaction_validity::TransactionSource::External;
		let best = longest_chain.best_chain().unwrap();
		let transaction = Transfer {
			amount: 5,
			nonce: 0,
			from: AccountKeyring::Alice.into(),
			to: Default::default(),
		}.into_signed_tx();
		block_on(pool.submit_one(
			&BlockId::hash(best.hash()), source, transaction.clone()),
		).unwrap();
		block_on(pool.submit_one(
			&BlockId::hash(best.hash()), source, Extrinsic::IncludeData(vec![1])),
		).unwrap();
		assert_eq!(pool.status().ready, 2);

		// when
		let transactions = transactions_to_propagate(&*pool);

		// then
		assert_eq!(transactions.len(), 1);
		assert!(transactions[0].1.clone().check().is_ok());
		// this should not panic
		let _ = transactions[0].1.transfer();
	}
}
