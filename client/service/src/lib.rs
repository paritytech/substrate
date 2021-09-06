// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
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

//! Substrate service. Starts a thread that spins up the network, client, and extrinsic pool.
//! Manages communication between them.

#![warn(missing_docs)]
#![recursion_limit = "1024"]

pub mod chain_ops;
pub mod config;
pub mod error;

mod builder;
#[cfg(feature = "test-helpers")]
pub mod client;
#[cfg(not(feature = "test-helpers"))]
mod client;
mod metrics;
mod task_manager;

use std::{collections::HashMap, io, net::SocketAddr, pin::Pin, task::Poll};

use codec::{Decode, Encode};
use futures::{stream, Future, FutureExt, Stream, StreamExt};
use log::{debug, error, warn};
use parity_util_mem::MallocSizeOf;
use sc_network::PeerId;
use sc_utils::mpsc::TracingUnboundedReceiver;
use sp_runtime::{
	generic::BlockId,
	traits::{Block as BlockT, Header as HeaderT},
};

pub use self::{
	builder::{
		build_network, build_offchain_workers, new_client, new_db_backend, new_full_client,
		new_full_parts, new_light_parts, spawn_tasks, BuildNetworkParams, KeystoreContainer,
		NetworkStarter, NoopRpcExtensionBuilder, RpcExtensionBuilder, SpawnTasksParams,
		TFullBackend, TFullCallExecutor, TFullClient, TLightBackend, TLightBackendWithHash,
		TLightCallExecutor, TLightClient, TLightClientWithBackend,
	},
	client::{ClientConfig, LocalCallExecutor},
	error::Error,
};
pub use config::{
	BasePath, Configuration, DatabaseSource, KeepBlocks, PruningMode, Role, RpcMethods,
	TaskExecutor, TaskType, TransactionStorageMode,
};
pub use sc_chain_spec::{
	ChainSpec, ChainType, Extension as ChainSpecExtension, GenericChainSpec, NoExtension,
	Properties, RuntimeGenesis,
};
use sc_client_api::{blockchain::HeaderBackend, BlockchainEvents};
pub use sc_consensus::ImportQueue;
pub use sc_executor::NativeExecutionDispatch;
#[doc(hidden)]
pub use sc_network::config::{OnDemand, TransactionImport, TransactionImportFuture};
pub use sc_rpc::Metadata as RpcMetadata;
pub use sc_tracing::TracingReceiver;
pub use sc_transaction_pool::Options as TransactionPoolOptions;
pub use sc_transaction_pool_api::{error::IntoPoolError, InPoolTransaction, TransactionPool};
#[doc(hidden)]
pub use std::{ops::Deref, result::Result, sync::Arc};
pub use task_manager::{SpawnTaskHandle, TaskManager};

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

/// RPC handlers that can perform RPC queries.
#[derive(Clone)]
pub struct RpcHandlers(
	Arc<jsonrpc_core::MetaIoHandler<sc_rpc::Metadata, sc_rpc_server::RpcMiddleware>>,
);

impl RpcHandlers {
	/// Starts an RPC query.
	///
	/// The query is passed as a string and must be a JSON text similar to what an HTTP client
	/// would for example send.
	///
	/// Returns a `Future` that contains the optional response.
	///
	/// If the request subscribes you to events, the `Sender` in the `RpcSession` object is used to
	/// send back spontaneous events.
	pub fn rpc_query(
		&self,
		mem: &RpcSession,
		request: &str,
	) -> Pin<Box<dyn Future<Output = Option<String>> + Send>> {
		self.0.handle_request(request, mem.metadata.clone()).boxed()
	}

	/// Provides access to the underlying `MetaIoHandler`
	pub fn io_handler(
		&self,
	) -> Arc<jsonrpc_core::MetaIoHandler<sc_rpc::Metadata, sc_rpc_server::RpcMiddleware>> {
		self.0.clone()
	}
}

/// An incomplete set of chain components, but enough to run the chain ops subcommands.
pub struct PartialComponents<Client, Backend, SelectChain, ImportQueue, TransactionPool, Other> {
	/// A shared client instance.
	pub client: Arc<Client>,
	/// A shared backend instance.
	pub backend: Arc<Backend>,
	/// The chain task manager.
	pub task_manager: TaskManager,
	/// A keystore container instance..
	pub keystore_container: KeystoreContainer,
	/// A chain selection algorithm instance.
	pub select_chain: SelectChain,
	/// An import queue.
	pub import_queue: ImportQueue,
	/// A shared transaction pool.
	pub transaction_pool: Arc<TransactionPool>,
	/// Everything else that needs to be passed into the main build function.
	pub other: Other,
}

/// Builds a never-ending future that continuously polls the network.
///
/// The `status_sink` contain a list of senders to send a periodic network status to.
async fn build_network_future<
	B: BlockT,
	C: BlockchainEvents<B> + HeaderBackend<B>,
	H: sc_network::ExHashT,
>(
	role: Role,
	mut network: sc_network::NetworkWorker<B, H>,
	client: Arc<C>,
	mut rpc_rx: TracingUnboundedReceiver<sc_rpc::system::Request<B>>,
	should_have_peers: bool,
	announce_imported_blocks: bool,
) {
	let mut imported_blocks_stream = client.import_notification_stream().fuse();

	// Current best block at initialization, to report to the RPC layer.
	let starting_block = client.info().best_number;

	// Stream of finalized blocks reported by the client.
	let mut finality_notification_stream = {
		let mut finality_notification_stream = client.finality_notification_stream().fuse();

		// We tweak the `Stream` in order to merge together multiple items if they happen to be
		// ready. This way, we only get the latest finalized block.
		stream::poll_fn(move |cx| {
			let mut last = None;
			while let Poll::Ready(Some(item)) =
				Pin::new(&mut finality_notification_stream).poll_next(cx)
			{
				last = Some(item);
			}
			if let Some(last) = last {
				Poll::Ready(Some(last))
			} else {
				Poll::Pending
			}
		})
		.fuse()
	};

	loop {
		futures::select! {
			// List of blocks that the client has imported.
			notification = imported_blocks_stream.next() => {
				let notification = match notification {
					Some(n) => n,
					// If this stream is shut down, that means the client has shut down, and the
					// most appropriate thing to do for the network future is to shut down too.
					None => return,
				};

				if announce_imported_blocks {
					network.service().announce_block(notification.hash, None);
				}

				if notification.is_new_best {
					network.service().new_best_block_imported(
						notification.hash,
						notification.header.number().clone(),
					);
				}
			}

			// List of blocks that the client has finalized.
			notification = finality_notification_stream.select_next_some() => {
				network.on_block_finalized(notification.hash, notification.header);
			}

			// Answer incoming RPC requests.
			request = rpc_rx.select_next_some() => {
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
					sc_rpc::system::Request::NetworkReservedPeers(sender) => {
						let reserved_peers = network.reserved_peers();
						let reserved_peers = reserved_peers
							.map(|peer_id| peer_id.to_base58())
							.collect();

						let _ = sender.send(reserved_peers);
					}
					sc_rpc::system::Request::NodeRoles(sender) => {
						use sc_rpc::system::NodeRole;

						let node_role = match role {
							Role::Authority { .. } => NodeRole::Authority,
							Role::Light => NodeRole::LightClient,
							Role::Full => NodeRole::Full,
						};

						let _ = sender.send(vec![node_role]);
					}
					sc_rpc::system::Request::SyncState(sender) => {
						use sc_rpc::system::SyncState;

						let _ = sender.send(SyncState {
							starting_block: starting_block,
							current_block: client.info().best_number,
							highest_block: network.best_seen_block(),
						});
					}
				}
			}

			// The network worker has done something. Nothing special to do, but could be
			// used in the future to perform actions in response of things that happened on
			// the network.
			_ = (&mut network).fuse() => {}
		}
	}
}

// Wrapper for HTTP and WS servers that makes sure they are properly shut down.
#[cfg(not(target_os = "unknown"))]
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

	pub struct IpcServer(pub Option<sc_rpc_server::IpcServer>);
	impl Drop for IpcServer {
		fn drop(&mut self) {
			if let Some(server) = self.0.take() {
				server.close_handle().close();
				let _ = server.wait();
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

/// Starts RPC servers that run in their own thread, and returns an opaque object that keeps them
/// alive.
#[cfg(not(target_os = "unknown"))]
fn start_rpc_servers<
	H: FnMut(
		sc_rpc::DenyUnsafe,
		sc_rpc_server::RpcMiddleware,
	) -> Result<sc_rpc_server::RpcHandler<sc_rpc::Metadata>, Error>,
>(
	config: &Configuration,
	mut gen_handler: H,
	rpc_metrics: Option<sc_rpc_server::RpcMetrics>,
	server_metrics: sc_rpc_server::ServerMetrics,
) -> Result<Box<dyn std::any::Any + Send>, Error> {
	fn maybe_start_server<T, F>(
		address: Option<SocketAddr>,
		mut start: F,
	) -> Result<Option<T>, Error>
	where
		F: FnMut(&SocketAddr) -> Result<T, Error>,
	{
		address
			.map(|mut address| {
				start(&address).or_else(|e| match e {
					Error::Io(e) => match e.kind() {
						io::ErrorKind::AddrInUse | io::ErrorKind::PermissionDenied => {
							warn!("Unable to bind RPC server to {}. Trying random port.", address);
							address.set_port(0);
							start(&address)
						},
						_ => Err(e.into()),
					},
					e => Err(e),
				})
			})
			.transpose()
	}

	fn deny_unsafe(addr: &SocketAddr, methods: &RpcMethods) -> sc_rpc::DenyUnsafe {
		let is_exposed_addr = !addr.ip().is_loopback();
		match (is_exposed_addr, methods) {
			| (_, RpcMethods::Unsafe) | (false, RpcMethods::Auto) => sc_rpc::DenyUnsafe::No,
			_ => sc_rpc::DenyUnsafe::Yes,
		}
	}

	let rpc_method_names = sc_rpc_server::method_names(|m| gen_handler(sc_rpc::DenyUnsafe::No, m))?;
	Ok(Box::new((
		config
			.rpc_ipc
			.as_ref()
			.map(|path| {
				sc_rpc_server::start_ipc(
					&*path,
					gen_handler(
						sc_rpc::DenyUnsafe::No,
						sc_rpc_server::RpcMiddleware::new(
							rpc_metrics.clone(),
							rpc_method_names.clone(),
							"ipc",
						),
					)?,
					server_metrics.clone(),
				)
				.map_err(Error::from)
			})
			.transpose()?,
		maybe_start_server(config.rpc_http, |address| {
			sc_rpc_server::start_http(
				address,
				config.rpc_http_threads,
				config.rpc_cors.as_ref(),
				gen_handler(
					deny_unsafe(&address, &config.rpc_methods),
					sc_rpc_server::RpcMiddleware::new(
						rpc_metrics.clone(),
						rpc_method_names.clone(),
						"http",
					),
				)?,
				config.rpc_max_payload,
			)
			.map_err(Error::from)
		})?
		.map(|s| waiting::HttpServer(Some(s))),
		maybe_start_server(config.rpc_ws, |address| {
			sc_rpc_server::start_ws(
				address,
				config.rpc_ws_max_connections,
				config.rpc_cors.as_ref(),
				gen_handler(
					deny_unsafe(&address, &config.rpc_methods),
					sc_rpc_server::RpcMiddleware::new(
						rpc_metrics.clone(),
						rpc_method_names.clone(),
						"ws",
					),
				)?,
				config.rpc_max_payload,
				server_metrics.clone(),
			)
			.map_err(Error::from)
		})?
		.map(|s| waiting::WsServer(Some(s))),
	)))
}

/// Starts RPC servers that run in their own thread, and returns an opaque object that keeps them
/// alive.
#[cfg(target_os = "unknown")]
fn start_rpc_servers<
	H: FnMut(
		sc_rpc::DenyUnsafe,
		sc_rpc_server::RpcMiddleware,
	) -> Result<sc_rpc_server::RpcHandler<sc_rpc::Metadata>, Error>,
>(
	_: &Configuration,
	_: H,
	_: Option<sc_rpc_server::RpcMetrics>,
	_: sc_rpc_server::ServerMetrics,
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
	pub fn new(sender: futures::channel::mpsc::UnboundedSender<String>) -> RpcSession {
		RpcSession { metadata: sender.into() }
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
fn transactions_to_propagate<Pool, B, H, E>(pool: &Pool) -> Vec<(H, B::Extrinsic)>
where
	Pool: TransactionPool<Block = B, Hash = H, Error = E>,
	B: BlockT,
	H: std::hash::Hash + Eq + sp_runtime::traits::Member + sp_runtime::traits::MaybeSerialize,
	E: IntoPoolError + From<sc_transaction_pool_api::error::Error>,
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

impl<B, H, C, Pool, E> sc_network::config::TransactionPool<H, B> for TransactionPoolAdapter<C, Pool>
where
	C: sc_network::config::Client<B> + Send + Sync,
	Pool: 'static + TransactionPool<Block = B, Hash = H, Error = E>,
	B: BlockT,
	H: std::hash::Hash + Eq + sp_runtime::traits::Member + sp_runtime::traits::MaybeSerialize,
	E: 'static + IntoPoolError + From<sc_transaction_pool_api::error::Error>,
{
	fn transactions(&self) -> Vec<(H, B::Extrinsic)> {
		transactions_to_propagate(&*self.pool)
	}

	fn hash_of(&self, transaction: &B::Extrinsic) -> H {
		self.pool.hash_of(transaction)
	}

	fn import(&self, transaction: B::Extrinsic) -> TransactionImportFuture {
		if !self.imports_external_transactions {
			debug!("Transaction rejected");
			Box::pin(futures::future::ready(TransactionImport::None));
		}

		let encoded = transaction.encode();
		let uxt = match Decode::decode(&mut &encoded[..]) {
			Ok(uxt) => uxt,
			Err(e) => {
				debug!("Transaction invalid: {:?}", e);
				return Box::pin(futures::future::ready(TransactionImport::Bad))
			},
		};

		let best_block_id = BlockId::hash(self.client.info().best_hash);

		let import_future = self.pool.submit_one(
			&best_block_id,
			sc_transaction_pool_api::TransactionSource::External,
			uxt,
		);
		Box::pin(async move {
			match import_future.await {
				Ok(_) => TransactionImport::NewGood,
				Err(e) => match e.into_pool_error() {
					Ok(sc_transaction_pool_api::error::Error::AlreadyImported(_)) =>
						TransactionImport::KnownGood,
					Ok(e) => {
						debug!("Error adding transaction to the pool: {:?}", e);
						TransactionImport::Bad
					},
					Err(e) => {
						debug!("Error converting pool error: {:?}", e);
						// it is not bad at least, just some internal node logic error, so peer is
						// innocent.
						TransactionImport::KnownGood
					},
				},
			}
		})
	}

	fn on_broadcasted(&self, propagations: HashMap<H, Vec<String>>) {
		self.pool.on_broadcasted(propagations)
	}

	fn transaction(&self, hash: &H) -> Option<B::Extrinsic> {
		self.pool.ready_transaction(hash).and_then(
			// Only propagable transactions should be resolved for network service.
			|tx| if tx.is_propagable() { Some(tx.data().clone()) } else { None },
		)
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use futures::executor::block_on;
	use sc_transaction_pool::BasicPool;
	use sp_consensus::SelectChain;
	use sp_runtime::traits::BlindCheckable;
	use substrate_test_runtime_client::{
		prelude::*,
		runtime::{Extrinsic, Transfer},
	};

	#[test]
	fn should_not_propagate_transactions_that_are_marked_as_such() {
		// given
		let (client, longest_chain) = TestClientBuilder::new().build_with_longest_chain();
		let client = Arc::new(client);
		let spawner = sp_core::testing::TaskExecutor::new();
		let pool =
			BasicPool::new_full(Default::default(), true.into(), None, spawner, client.clone());
		let source = sp_runtime::transaction_validity::TransactionSource::External;
		let best = block_on(longest_chain.best_chain()).unwrap();
		let transaction = Transfer {
			amount: 5,
			nonce: 0,
			from: AccountKeyring::Alice.into(),
			to: Default::default(),
		}
		.into_signed_tx();
		block_on(pool.submit_one(&BlockId::hash(best.hash()), source, transaction.clone()))
			.unwrap();
		block_on(pool.submit_one(
			&BlockId::hash(best.hash()),
			source,
			Extrinsic::IncludeData(vec![1]),
		))
		.unwrap();
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
