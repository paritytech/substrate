// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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

use std::{collections::HashMap, net::SocketAddr};

use codec::{Decode, Encode};
use futures::{channel::mpsc, pin_mut, FutureExt, StreamExt};
use jsonrpsee::{core::Error as JsonRpseeError, RpcModule};
use log::{debug, error, warn};
use sc_client_api::{blockchain::HeaderBackend, BlockBackend, BlockchainEvents, ProofProvider};
use sc_network::{NetworkStateInfo, PeerId};
use sc_network_common::{
	config::MultiaddrWithPeerId,
	service::{NetworkBlock, NetworkPeers},
};
use sc_network_sync::service::chain_sync::ChainSyncInterfaceHandle;
use sc_utils::mpsc::TracingUnboundedReceiver;
use sp_blockchain::HeaderMetadata;
use sp_consensus::SyncOracle;
use sp_runtime::{
	generic::BlockId,
	traits::{Block as BlockT, Header as HeaderT},
};

pub use self::{
	builder::{
		build_network, build_offchain_workers, new_client, new_db_backend, new_full_client,
		new_full_parts, spawn_tasks, BuildNetworkParams, KeystoreContainer, NetworkStarter,
		SpawnTasksParams, TFullBackend, TFullCallExecutor, TFullClient,
	},
	client::{
		genesis::{BuildGenesisBlock, GenesisBlockBuilder},
		resolve_state_version_from_wasm, ClientConfig, LocalCallExecutor,
	},
	error::Error,
};
pub use config::{
	BasePath, BlocksPruning, Configuration, DatabaseSource, PruningMode, Role, RpcMethods, TaskType,
};
pub use sc_chain_spec::{
	ChainSpec, ChainType, Extension as ChainSpecExtension, GenericChainSpec, NoExtension,
	Properties, RuntimeGenesis,
};

pub use sc_consensus::ImportQueue;
pub use sc_executor::NativeExecutionDispatch;
pub use sc_network_common::sync::warp::WarpSyncParams;
#[doc(hidden)]
pub use sc_network_transactions::config::{TransactionImport, TransactionImportFuture};
pub use sc_rpc::{
	RandomIntegerSubscriptionId, RandomStringSubscriptionId, RpcSubscriptionIdProvider,
};
pub use sc_tracing::TracingReceiver;
pub use sc_transaction_pool::Options as TransactionPoolOptions;
pub use sc_transaction_pool_api::{error::IntoPoolError, InPoolTransaction, TransactionPool};
#[doc(hidden)]
pub use std::{ops::Deref, result::Result, sync::Arc};
pub use task_manager::{SpawnTaskHandle, Task, TaskManager, TaskRegistry, DEFAULT_GROUP_NAME};

const DEFAULT_PROTOCOL_ID: &str = "sup";

/// RPC handlers that can perform RPC queries.
#[derive(Clone)]
pub struct RpcHandlers(Arc<RpcModule<()>>);

impl RpcHandlers {
	/// Starts an RPC query.
	///
	/// The query is passed as a string and must be valid JSON-RPC request object.
	///
	/// Returns a response and a stream if the call successful, fails if the
	/// query could not be decoded as a JSON-RPC request object.
	///
	/// If the request subscribes you to events, the `stream` can be used to
	/// retrieve the events.
	pub async fn rpc_query(
		&self,
		json_query: &str,
	) -> Result<(String, mpsc::UnboundedReceiver<String>), JsonRpseeError> {
		self.0
			.raw_json_request(json_query)
			.await
			.map(|(method_res, recv)| (method_res.result, recv))
	}

	/// Provides access to the underlying `RpcModule`
	pub fn handle(&self) -> Arc<RpcModule<()>> {
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

/// Builds a future that continuously polls the network.
async fn build_network_future<
	B: BlockT,
	C: BlockchainEvents<B>
		+ HeaderBackend<B>
		+ BlockBackend<B>
		+ HeaderMetadata<B, Error = sp_blockchain::Error>
		+ ProofProvider<B>
		+ Send
		+ Sync
		+ 'static,
	H: sc_network_common::ExHashT,
>(
	network: sc_network::NetworkWorker<B, H, C>,
	client: Arc<C>,
	chain_sync_service: ChainSyncInterfaceHandle<B>,
	announce_imported_blocks: bool,
) {
	let mut imported_blocks_stream = client.import_notification_stream().fuse();

	// Stream of finalized blocks reported by the client.
	let mut finality_notification_stream = client.finality_notification_stream().fuse();

	let network_service = network.service().clone();

	let network_run = network.run().fuse();
	pin_mut!(network_run);

	loop {
		futures::select! {
			// List of blocks that the client has imported.
			notification = imported_blocks_stream.next() => {
				let notification = match notification {
					Some(n) => n,
					// If this stream is shut down, that means the client has shut down, and the
					// most appropriate thing to do for the network future is to shut down too.
					None => {
						debug!("Block import stream has terminated, shutting down the network future.");
						return
					},
				};

				if announce_imported_blocks {
					network_service.announce_block(notification.hash, None);
				}

				if notification.is_new_best {
					network_service.new_best_block_imported(
						notification.hash,
						*notification.header.number(),
					);
				}
			}

			// List of blocks that the client has finalized.
			notification = finality_notification_stream.select_next_some() => {
				chain_sync_service.on_block_finalized(notification.hash, *notification.header.number());
			}

			// Drive the network. Shut down the network future if `NetworkWorker` has terminated.
			_ = network_run => {
				debug!("`NetworkWorker` has terminated, shutting down the network future.");
				return
			}
		}
	}
}

/// Builds a future that processes system RPC requests.
async fn build_system_rpc_future<
	B: BlockT,
	C: BlockchainEvents<B>
		+ HeaderBackend<B>
		+ BlockBackend<B>
		+ HeaderMetadata<B, Error = sp_blockchain::Error>
		+ ProofProvider<B>
		+ Send
		+ Sync
		+ 'static,
	H: sc_network_common::ExHashT,
>(
	role: Role,
	network_service: Arc<sc_network::NetworkService<B, H>>,
	chain_sync_service: ChainSyncInterfaceHandle<B>,
	client: Arc<C>,
	mut rpc_rx: TracingUnboundedReceiver<sc_rpc::system::Request<B>>,
	should_have_peers: bool,
) {
	// Current best block at initialization, to report to the RPC layer.
	let starting_block = client.info().best_number;

	loop {
		// Answer incoming RPC requests.
		let Some(req) = rpc_rx.next().await else {
			debug!("RPC requests stream has terminated, shutting down the system RPC future.");
			return;
		};

		match req {
			sc_rpc::system::Request::Health(sender) => {
				let peers = network_service.peers_debug_info().await;
				if let Ok(peers) = peers {
					let _ = sender.send(sc_rpc::system::Health {
						peers: peers.len(),
						is_syncing: network_service.is_major_syncing(),
						should_have_peers,
					});
				} else {
					break
				}
			},
			sc_rpc::system::Request::LocalPeerId(sender) => {
				let _ = sender.send(network_service.local_peer_id().to_base58());
			},
			sc_rpc::system::Request::LocalListenAddresses(sender) => {
				let peer_id = network_service.local_peer_id().into();
				let p2p_proto_suffix = sc_network::multiaddr::Protocol::P2p(peer_id);
				let addresses = network_service
					.listen_addresses()
					.iter()
					.map(|addr| addr.clone().with(p2p_proto_suffix.clone()).to_string())
					.collect();
				let _ = sender.send(addresses);
			},
			sc_rpc::system::Request::Peers(sender) => {
				let peers = network_service.peers_debug_info().await;
				if let Ok(peers) = peers {
					let _ = sender.send(
						peers
							.into_iter()
							.map(|(peer_id, p)| sc_rpc::system::PeerInfo {
								peer_id: peer_id.to_base58(),
								roles: format!("{:?}", p.roles),
								best_hash: p.best_hash,
								best_number: p.best_number,
							})
							.collect(),
					);
				} else {
					break
				}
			},
			sc_rpc::system::Request::NetworkState(sender) => {
				let network_state = network_service.network_state().await;
				if let Ok(network_state) = network_state {
					if let Ok(network_state) = serde_json::to_value(network_state) {
						let _ = sender.send(network_state);
					}
				} else {
					break
				}
			},
			sc_rpc::system::Request::NetworkAddReservedPeer(peer_addr, sender) => {
				let result = match MultiaddrWithPeerId::try_from(peer_addr) {
					Ok(peer) => network_service.add_reserved_peer(peer),
					Err(err) => Err(err.to_string()),
				};
				let x = result.map_err(sc_rpc::system::error::Error::MalformattedPeerArg);
				let _ = sender.send(x);
			},
			sc_rpc::system::Request::NetworkRemoveReservedPeer(peer_id, sender) => {
				let _ = match peer_id.parse::<PeerId>() {
					Ok(peer_id) => {
						network_service.remove_reserved_peer(peer_id);
						sender.send(Ok(()))
					},
					Err(e) => sender.send(Err(sc_rpc::system::error::Error::MalformattedPeerArg(
						e.to_string(),
					))),
				};
			},
			sc_rpc::system::Request::NetworkReservedPeers(sender) => {
				let reserved_peers = network_service.reserved_peers().await;
				if let Ok(reserved_peers) = reserved_peers {
					let reserved_peers =
						reserved_peers.iter().map(|peer_id| peer_id.to_base58()).collect();
					let _ = sender.send(reserved_peers);
				} else {
					break
				}
			},
			sc_rpc::system::Request::NodeRoles(sender) => {
				use sc_rpc::system::NodeRole;

				let node_role = match role {
					Role::Authority { .. } => NodeRole::Authority,
					Role::Full => NodeRole::Full,
				};

				let _ = sender.send(vec![node_role]);
			},
			sc_rpc::system::Request::SyncState(sender) => {
				use sc_rpc::system::SyncState;

				let best_number = client.info().best_number;

				let Ok(status) = chain_sync_service.status().await else {
					debug!("`ChainSync` has terminated, shutting down the system RPC future.");
					return
				};

				let _ = sender.send(SyncState {
					starting_block,
					current_block: best_number,
					highest_block: status.best_seen_block.unwrap_or(best_number),
				});
			},
		}
	}
	debug!("`NetworkWorker` has terminated, shutting down the system RPC future.");
}

// Wrapper for HTTP and WS servers that makes sure they are properly shut down.
mod waiting {
	pub struct Server(pub Option<sc_rpc_server::Server>);

	impl Drop for Server {
		fn drop(&mut self) {
			if let Some(server) = self.0.take() {
				// This doesn't not wait for the server to be stopped but fires the signal.
				let _ = server.stop();
			}
		}
	}
}

/// Starts RPC servers.
fn start_rpc_servers<R>(
	config: &Configuration,
	gen_rpc_module: R,
	rpc_id_provider: Option<Box<dyn RpcSubscriptionIdProvider>>,
) -> Result<Box<dyn std::any::Any + Send + Sync>, error::Error>
where
	R: Fn(sc_rpc::DenyUnsafe) -> Result<RpcModule<()>, Error>,
{
	fn deny_unsafe(addr: SocketAddr, methods: &RpcMethods) -> sc_rpc::DenyUnsafe {
		let is_exposed_addr = !addr.ip().is_loopback();
		match (is_exposed_addr, methods) {
			| (_, RpcMethods::Unsafe) | (false, RpcMethods::Auto) => sc_rpc::DenyUnsafe::No,
			_ => sc_rpc::DenyUnsafe::Yes,
		}
	}

	let (max_request_size, ws_max_response_size, http_max_response_size) =
		legacy_cli_parsing(config);

	let random_port = |mut addr: SocketAddr| {
		addr.set_port(0);
		addr
	};

	let ws_addr = config
		.rpc_ws
		.unwrap_or_else(|| "127.0.0.1:9944".parse().expect("valid sockaddr; qed"));
	let ws_addr2 = random_port(ws_addr);

	let http_addr = config
		.rpc_http
		.unwrap_or_else(|| "127.0.0.1:9933".parse().expect("valid sockaddr; qed"));
	let http_addr2 = random_port(http_addr);

	let metrics = sc_rpc_server::RpcMetrics::new(config.prometheus_registry())?;

	let server_config = sc_rpc_server::WsConfig {
		max_connections: config.rpc_ws_max_connections,
		max_payload_in_mb: max_request_size,
		max_payload_out_mb: ws_max_response_size,
		max_subs_per_conn: config.rpc_max_subs_per_conn,
	};

	let http_fut = sc_rpc_server::start_http(
		[http_addr, http_addr2],
		config.rpc_cors.as_ref(),
		max_request_size,
		http_max_response_size,
		metrics.clone(),
		gen_rpc_module(deny_unsafe(http_addr, &config.rpc_methods))?,
		config.tokio_handle.clone(),
	);

	let ws_fut = sc_rpc_server::start(
		[ws_addr, ws_addr2],
		config.rpc_cors.as_ref(),
		server_config.clone(),
		metrics.clone(),
		gen_rpc_module(deny_unsafe(ws_addr, &config.rpc_methods))?,
		config.tokio_handle.clone(),
		rpc_id_provider,
	);

	match tokio::task::block_in_place(|| {
		config.tokio_handle.block_on(futures::future::try_join(http_fut, ws_fut))
	}) {
		Ok((http, ws)) => Ok(Box::new((waiting::Server(Some(http)), waiting::Server(Some(ws))))),
		Err(e) => Err(Error::Application(e)),
	}
}

/// Transaction pool adapter.
pub struct TransactionPoolAdapter<C, P> {
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

impl<B, H, C, Pool, E> sc_network_transactions::config::TransactionPool<H, B>
	for TransactionPoolAdapter<C, Pool>
where
	C: HeaderBackend<B>
		+ BlockBackend<B>
		+ HeaderMetadata<B, Error = sp_blockchain::Error>
		+ ProofProvider<B>
		+ Send
		+ Sync
		+ 'static,
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
						debug!("Error converting pool error: {}", e);
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

fn legacy_cli_parsing(config: &Configuration) -> (Option<usize>, Option<usize>, Option<usize>) {
	let ws_max_response_size = match (
		config.ws_max_out_buffer_capacity,
		config.rpc_max_response_size,
	) {
		(Some(legacy_max), max) => {
			eprintln!("DEPRECATED: `--ws_max_out_buffer_capacity` has been removed; use `rpc-max-response-size or rpc-max-request-size` instead");
			eprintln!("Setting WS `rpc-max-response-size` to `max(ws_max_out_buffer_capacity, rpc_max_response_size)`");
			Some(std::cmp::max(legacy_max, max.unwrap_or(0)))
		},
		(None, Some(m)) => Some(m),
		(None, None) => None,
	};

	let max_request_size = match (config.rpc_max_payload, config.rpc_max_request_size) {
		(Some(legacy_max), max) => {
			eprintln!("DEPRECATED: `--rpc_max_payload` has been removed use `rpc-max-response-size or rpc-max-request-size` instead");
			eprintln!(
				"Setting `rpc-max-response-size` to `max(rpc_max_payload, rpc_max_request_size)`"
			);
			Some(std::cmp::max(legacy_max, max.unwrap_or(0)))
		},
		(None, Some(max)) => Some(max),
		(None, None) => None,
	};

	let http_max_response_size = match (config.rpc_max_payload, config.rpc_max_response_size) {
		(Some(legacy_max), max) => {
			eprintln!("DEPRECATED: `--rpc_max_payload` has been removed use `rpc-max-response-size or rpc-max-request-size` instead");
			eprintln!(
				"Setting HTTP `rpc-max-response-size` to `max(rpc_max_payload, rpc_max_response_size)`"
			);
			Some(std::cmp::max(legacy_max, max.unwrap_or(0)))
		},
		(None, Some(max)) => Some(max),
		(None, None) => None,
	};

	if config.rpc_ipc.is_some() {
		eprintln!("DEPRECATED: `--ipc-path` has no effect anymore IPC support has been removed");
	}

	(max_request_size, ws_max_response_size, http_max_response_size)
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
			to: AccountKeyring::Bob.into(),
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
