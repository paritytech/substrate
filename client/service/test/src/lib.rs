// This file is part of Substrate.

// Copyright (C) 2018-2022 Parity Technologies (UK) Ltd.
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

//! Service integration test utils.

use futures::{task::Poll, Future, TryFutureExt as _};
use log::{debug, info};
use parking_lot::Mutex;
use sc_client_api::{Backend, CallExecutor};
use sc_network::{
	config::{NetworkConfiguration, TransportConfig},
	multiaddr, Multiaddr,
};
use sc_network_common::service::{NetworkBlock, NetworkPeers, NetworkStateInfo};
use sc_service::{
	client::Client,
	config::{BasePath, DatabaseSource, KeystoreConfig},
	BlocksPruning, ChainSpecExtension, Configuration, Error, GenericChainSpec, Role,
	RuntimeGenesis, SpawnTaskHandle, TaskManager,
};
use sc_transaction_pool_api::TransactionPool;
use sp_api::BlockId;
use sp_blockchain::HeaderBackend;
use sp_runtime::traits::Block as BlockT;
use std::{iter, net::Ipv4Addr, pin::Pin, sync::Arc, task::Context, time::Duration};
use tempfile::TempDir;
use tokio::{runtime::Runtime, time};

#[cfg(test)]
mod client;

/// Maximum duration of single wait call.
const MAX_WAIT_TIME: Duration = Duration::from_secs(60 * 3);

struct TestNet<G, E, F, U> {
	runtime: Runtime,
	authority_nodes: Vec<(usize, F, U, Multiaddr)>,
	full_nodes: Vec<(usize, F, U, Multiaddr)>,
	chain_spec: GenericChainSpec<G, E>,
	base_port: u16,
	nodes: usize,
}

impl<G, E, F, U> Drop for TestNet<G, E, F, U> {
	fn drop(&mut self) {
		// Drop the nodes before dropping the runtime, as the runtime otherwise waits for all
		// futures to be ended and we run into a dead lock.
		self.full_nodes.drain(..);
		self.authority_nodes.drain(..);
	}
}

pub trait TestNetNode:
	Clone + Future<Output = Result<(), sc_service::Error>> + Send + 'static
{
	type Block: BlockT;
	type Backend: Backend<Self::Block>;
	type Executor: CallExecutor<Self::Block> + Send + Sync;
	type RuntimeApi: Send + Sync;
	type TransactionPool: TransactionPool<Block = Self::Block>;

	fn client(&self) -> Arc<Client<Self::Backend, Self::Executor, Self::Block, Self::RuntimeApi>>;
	fn transaction_pool(&self) -> Arc<Self::TransactionPool>;
	fn network(
		&self,
	) -> Arc<sc_network::NetworkService<Self::Block, <Self::Block as BlockT>::Hash>>;
	fn spawn_handle(&self) -> SpawnTaskHandle;
}

pub struct TestNetComponents<TBl: BlockT, TBackend, TExec, TRtApi, TExPool> {
	task_manager: Arc<Mutex<TaskManager>>,
	client: Arc<Client<TBackend, TExec, TBl, TRtApi>>,
	transaction_pool: Arc<TExPool>,
	network: Arc<sc_network::NetworkService<TBl, <TBl as BlockT>::Hash>>,
}

impl<TBl: BlockT, TBackend, TExec, TRtApi, TExPool>
	TestNetComponents<TBl, TBackend, TExec, TRtApi, TExPool>
{
	pub fn new(
		task_manager: TaskManager,
		client: Arc<Client<TBackend, TExec, TBl, TRtApi>>,
		network: Arc<sc_network::NetworkService<TBl, <TBl as BlockT>::Hash>>,
		transaction_pool: Arc<TExPool>,
	) -> Self {
		Self { client, transaction_pool, network, task_manager: Arc::new(Mutex::new(task_manager)) }
	}
}

impl<TBl: BlockT, TBackend, TExec, TRtApi, TExPool> Clone
	for TestNetComponents<TBl, TBackend, TExec, TRtApi, TExPool>
{
	fn clone(&self) -> Self {
		Self {
			task_manager: self.task_manager.clone(),
			client: self.client.clone(),
			transaction_pool: self.transaction_pool.clone(),
			network: self.network.clone(),
		}
	}
}

impl<TBl: BlockT, TBackend, TExec, TRtApi, TExPool> Future
	for TestNetComponents<TBl, TBackend, TExec, TRtApi, TExPool>
{
	type Output = Result<(), sc_service::Error>;

	fn poll(self: Pin<&mut Self>, cx: &mut Context) -> Poll<Self::Output> {
		Pin::new(&mut self.task_manager.lock().future()).poll(cx)
	}
}

impl<TBl, TBackend, TExec, TRtApi, TExPool> TestNetNode
	for TestNetComponents<TBl, TBackend, TExec, TRtApi, TExPool>
where
	TBl: BlockT,
	TBackend: sc_client_api::Backend<TBl> + Send + Sync + 'static,
	TExec: CallExecutor<TBl> + Send + Sync + 'static,
	TRtApi: Send + Sync + 'static,
	TExPool: TransactionPool<Block = TBl> + Send + Sync + 'static,
{
	type Block = TBl;
	type Backend = TBackend;
	type Executor = TExec;
	type RuntimeApi = TRtApi;
	type TransactionPool = TExPool;

	fn client(&self) -> Arc<Client<Self::Backend, Self::Executor, Self::Block, Self::RuntimeApi>> {
		self.client.clone()
	}
	fn transaction_pool(&self) -> Arc<Self::TransactionPool> {
		self.transaction_pool.clone()
	}
	fn network(
		&self,
	) -> Arc<sc_network::NetworkService<Self::Block, <Self::Block as BlockT>::Hash>> {
		self.network.clone()
	}
	fn spawn_handle(&self) -> SpawnTaskHandle {
		self.task_manager.lock().spawn_handle()
	}
}

impl<G, E, F, U> TestNet<G, E, F, U>
where
	F: Clone + Send + 'static,
	U: Clone + Send + 'static,
{
	pub fn run_until_all_full<FP>(&mut self, full_predicate: FP)
	where
		FP: Send + Fn(usize, &F) -> bool + 'static,
	{
		let full_nodes = self.full_nodes.clone();
		let future = async move {
			let mut interval = time::interval(Duration::from_millis(100));
			loop {
				interval.tick().await;

				if full_nodes
					.iter()
					.all(|&(ref id, ref service, _, _)| full_predicate(*id, service))
				{
					break
				}
			}
		};

		if self
			.runtime
			.block_on(async move { time::timeout(MAX_WAIT_TIME, future).await })
			.is_err()
		{
			panic!("Waited for too long");
		}
	}
}

fn node_config<
	G: RuntimeGenesis + 'static,
	E: ChainSpecExtension + Clone + 'static + Send + Sync,
>(
	index: usize,
	spec: &GenericChainSpec<G, E>,
	role: Role,
	tokio_handle: tokio::runtime::Handle,
	key_seed: Option<String>,
	base_port: u16,
	root: &TempDir,
) -> Configuration {
	let root = root.path().join(format!("node-{}", index));

	let mut network_config = NetworkConfiguration::new(
		format!("Node {}", index),
		"network/test/0.1",
		Default::default(),
		None,
	);

	network_config.allow_non_globals_in_dht = true;

	network_config.listen_addresses.push(
		iter::once(multiaddr::Protocol::Ip4(Ipv4Addr::new(127, 0, 0, 1)))
			.chain(iter::once(multiaddr::Protocol::Tcp(base_port + index as u16)))
			.collect(),
	);

	network_config.transport =
		TransportConfig::Normal { enable_mdns: false, allow_private_ipv4: true };

	Configuration {
		impl_name: String::from("network-test-impl"),
		impl_version: String::from("0.1"),
		role,
		tokio_handle,
		transaction_pool: Default::default(),
		network: network_config,
		keystore_remote: Default::default(),
		keystore: KeystoreConfig::Path { path: root.join("key"), password: None },
		database: DatabaseSource::RocksDb { path: root.join("db"), cache_size: 128 },
		state_cache_size: 16777216,
		state_cache_child_ratio: None,
		state_pruning: Default::default(),
		blocks_pruning: BlocksPruning::All,
		chain_spec: Box::new((*spec).clone()),
		wasm_method: sc_service::config::WasmExecutionMethod::Interpreted,
		wasm_runtime_overrides: Default::default(),
		execution_strategies: Default::default(),
		rpc_http: None,
		rpc_ipc: None,
		rpc_ws: None,
		rpc_ws_max_connections: None,
		rpc_cors: None,
		rpc_methods: Default::default(),
		rpc_max_payload: None,
		rpc_max_request_size: None,
		rpc_max_response_size: None,
		rpc_id_provider: None,
		rpc_max_subs_per_conn: None,
		ws_max_out_buffer_capacity: None,
		prometheus_config: None,
		telemetry_endpoints: None,
		default_heap_pages: None,
		offchain_worker: Default::default(),
		force_authoring: false,
		disable_grandpa: false,
		dev_key_seed: key_seed,
		tracing_targets: None,
		tracing_receiver: Default::default(),
		max_runtime_instances: 8,
		announce_block: true,
		base_path: Some(BasePath::new(root)),
		informant_output_format: Default::default(),
		runtime_cache_size: 2,
	}
}

impl<G, E, F, U> TestNet<G, E, F, U>
where
	F: TestNetNode,
	E: ChainSpecExtension + Clone + 'static + Send + Sync,
	G: RuntimeGenesis + 'static,
{
	fn new(
		temp: &TempDir,
		spec: GenericChainSpec<G, E>,
		full: impl Iterator<Item = impl FnOnce(Configuration) -> Result<(F, U), Error>>,
		authorities: impl Iterator<Item = (String, impl FnOnce(Configuration) -> Result<(F, U), Error>)>,
		base_port: u16,
	) -> TestNet<G, E, F, U> {
		sp_tracing::try_init_simple();
		fdlimit::raise_fd_limit();
		let runtime = Runtime::new().expect("Error creating tokio runtime");
		let mut net = TestNet {
			runtime,
			authority_nodes: Default::default(),
			full_nodes: Default::default(),
			chain_spec: spec,
			base_port,
			nodes: 0,
		};
		net.insert_nodes(temp, full, authorities);
		net
	}

	fn insert_nodes(
		&mut self,
		temp: &TempDir,
		full: impl Iterator<Item = impl FnOnce(Configuration) -> Result<(F, U), Error>>,
		authorities: impl Iterator<Item = (String, impl FnOnce(Configuration) -> Result<(F, U), Error>)>,
	) {
		let handle = self.runtime.handle().clone();

		for (key, authority) in authorities {
			let node_config = node_config(
				self.nodes,
				&self.chain_spec,
				Role::Authority,
				handle.clone(),
				Some(key),
				self.base_port,
				temp,
			);
			let addr = node_config.network.listen_addresses.first().unwrap().clone();
			let (service, user_data) =
				authority(node_config).expect("Error creating test node service");

			handle.spawn(service.clone().map_err(|_| ()));
			let addr =
				addr.with(multiaddr::Protocol::P2p((service.network().local_peer_id()).into()));
			self.authority_nodes.push((self.nodes, service, user_data, addr));
			self.nodes += 1;
		}

		for full in full {
			let node_config = node_config(
				self.nodes,
				&self.chain_spec,
				Role::Full,
				handle.clone(),
				None,
				self.base_port,
				temp,
			);
			let addr = node_config.network.listen_addresses.first().unwrap().clone();
			let (service, user_data) = full(node_config).expect("Error creating test node service");

			handle.spawn(service.clone().map_err(|_| ()));
			let addr =
				addr.with(multiaddr::Protocol::P2p((service.network().local_peer_id()).into()));
			self.full_nodes.push((self.nodes, service, user_data, addr));
			self.nodes += 1;
		}
	}
}

fn tempdir_with_prefix(prefix: &str) -> TempDir {
	tempfile::Builder::new()
		.prefix(prefix)
		.tempdir()
		.expect("Error creating test dir")
}

pub fn connectivity<G, E, Fb, F>(spec: GenericChainSpec<G, E>, full_builder: Fb)
where
	E: ChainSpecExtension + Clone + 'static + Send + Sync,
	G: RuntimeGenesis + 'static,
	Fb: Fn(Configuration) -> Result<F, Error>,
	F: TestNetNode,
{
	const NUM_FULL_NODES: usize = 5;

	let expected_full_connections = NUM_FULL_NODES - 1;

	{
		let temp = tempdir_with_prefix("substrate-connectivity-test");
		{
			let mut network = TestNet::new(
				&temp,
				spec.clone(),
				(0..NUM_FULL_NODES).map(|_| |cfg| full_builder(cfg).map(|s| (s, ()))),
				// Note: this iterator is empty but we can't just use `iter::empty()`, otherwise
				// the type of the closure cannot be inferred.
				(0..0).map(|_| (String::new(), { |cfg| full_builder(cfg).map(|s| (s, ())) })),
				30400,
			);
			info!("Checking star topology");
			let first_address = network.full_nodes[0].3.clone();
			for (_, service, _, _) in network.full_nodes.iter().skip(1) {
				service
					.network()
					.add_reserved_peer(first_address.to_string())
					.expect("Error adding reserved peer");
			}

			network.run_until_all_full(move |_index, service| {
				let connected = service.network().sync_num_connected();
				debug!("Got {}/{} full connections...", connected, expected_full_connections);
				connected == expected_full_connections
			});
		};

		temp.close().expect("Error removing temp dir");
	}
	{
		let temp = tempdir_with_prefix("substrate-connectivity-test");
		{
			let mut network = TestNet::new(
				&temp,
				spec,
				(0..NUM_FULL_NODES).map(|_| |cfg| full_builder(cfg).map(|s| (s, ()))),
				// Note: this iterator is empty but we can't just use `iter::empty()`, otherwise
				// the type of the closure cannot be inferred.
				(0..0).map(|_| (String::new(), { |cfg| full_builder(cfg).map(|s| (s, ())) })),
				30400,
			);
			info!("Checking linked topology");
			let mut address = network.full_nodes[0].3.clone();
			for i in 0..NUM_FULL_NODES {
				if i != 0 {
					if let Some((_, service, _, node_id)) = network.full_nodes.get(i) {
						service
							.network()
							.add_reserved_peer(address.to_string())
							.expect("Error adding reserved peer");
						address = node_id.clone();
					}
				}
			}

			network.run_until_all_full(move |_index, service| {
				let connected = service.network().sync_num_connected();
				debug!("Got {}/{} full connections...", connected, expected_full_connections);
				connected == expected_full_connections
			});
		}
		temp.close().expect("Error removing temp dir");
	}
}

pub fn sync<G, E, Fb, F, B, ExF, U>(
	spec: GenericChainSpec<G, E>,
	full_builder: Fb,
	mut make_block_and_import: B,
	mut extrinsic_factory: ExF,
) where
	Fb: Fn(Configuration) -> Result<(F, U), Error>,
	F: TestNetNode,
	B: FnMut(&F, &mut U),
	ExF: FnMut(&F, &U) -> <F::Block as BlockT>::Extrinsic,
	U: Clone + Send + 'static,
	E: ChainSpecExtension + Clone + 'static + Send + Sync,
	G: RuntimeGenesis + 'static,
{
	const NUM_FULL_NODES: usize = 10;
	const NUM_BLOCKS: usize = 512;
	let temp = tempdir_with_prefix("substrate-sync-test");
	let mut network = TestNet::new(
		&temp,
		spec,
		(0..NUM_FULL_NODES).map(|_| |cfg| full_builder(cfg)),
		// Note: this iterator is empty but we can't just use `iter::empty()`, otherwise
		// the type of the closure cannot be inferred.
		(0..0).map(|_| (String::new(), { |cfg| full_builder(cfg) })),
		30500,
	);
	info!("Checking block sync");
	let first_address = {
		let &mut (_, ref first_service, ref mut first_user_data, _) = &mut network.full_nodes[0];
		for i in 0..NUM_BLOCKS {
			if i % 128 == 0 {
				info!("Generating #{}", i + 1);
			}

			make_block_and_import(first_service, first_user_data);
		}
		let info = network.full_nodes[0].1.client().info();
		network.full_nodes[0]
			.1
			.network()
			.new_best_block_imported(info.best_hash, info.best_number);
		network.full_nodes[0].3.clone()
	};

	info!("Running sync");
	for (_, service, _, _) in network.full_nodes.iter().skip(1) {
		service
			.network()
			.add_reserved_peer(first_address.to_string())
			.expect("Error adding reserved peer");
	}

	network.run_until_all_full(|_index, service| {
		service.client().info().best_number == (NUM_BLOCKS as u32).into()
	});

	info!("Checking extrinsic propagation");
	let first_service = network.full_nodes[0].1.clone();
	let first_user_data = &network.full_nodes[0].2;
	let best_block = BlockId::number(first_service.client().info().best_number);
	let extrinsic = extrinsic_factory(&first_service, first_user_data);
	let source = sc_transaction_pool_api::TransactionSource::External;

	futures::executor::block_on(first_service.transaction_pool().submit_one(
		&best_block,
		source,
		extrinsic,
	))
	.expect("failed to submit extrinsic");

	network.run_until_all_full(|_index, service| service.transaction_pool().ready().count() == 1);
}

pub fn consensus<G, E, Fb, F>(
	spec: GenericChainSpec<G, E>,
	full_builder: Fb,
	authorities: impl IntoIterator<Item = String>,
) where
	Fb: Fn(Configuration) -> Result<F, Error>,
	F: TestNetNode,
	E: ChainSpecExtension + Clone + 'static + Send + Sync,
	G: RuntimeGenesis + 'static,
{
	const NUM_FULL_NODES: usize = 10;
	const NUM_BLOCKS: usize = 10; // 10 * 2 sec block production time = ~20 seconds
	let temp = tempdir_with_prefix("substrate-consensus-test");
	let mut network = TestNet::new(
		&temp,
		spec,
		(0..NUM_FULL_NODES / 2).map(|_| |cfg| full_builder(cfg).map(|s| (s, ()))),
		authorities
			.into_iter()
			.map(|key| (key, { |cfg| full_builder(cfg).map(|s| (s, ())) })),
		30600,
	);

	info!("Checking consensus");
	let first_address = network.authority_nodes[0].3.clone();
	for (_, service, _, _) in network.full_nodes.iter() {
		service
			.network()
			.add_reserved_peer(first_address.to_string())
			.expect("Error adding reserved peer");
	}
	for (_, service, _, _) in network.authority_nodes.iter().skip(1) {
		service
			.network()
			.add_reserved_peer(first_address.to_string())
			.expect("Error adding reserved peer");
	}
	network.run_until_all_full(|_index, service| {
		service.client().info().finalized_number >= (NUM_BLOCKS as u32 / 2).into()
	});

	info!("Adding more peers");
	network.insert_nodes(
		&temp,
		(0..NUM_FULL_NODES / 2).map(|_| |cfg| full_builder(cfg).map(|s| (s, ()))),
		// Note: this iterator is empty but we can't just use `iter::empty()`, otherwise
		// the type of the closure cannot be inferred.
		(0..0).map(|_| (String::new(), { |cfg| full_builder(cfg).map(|s| (s, ())) })),
	);
	for (_, service, _, _) in network.full_nodes.iter() {
		service
			.network()
			.add_reserved_peer(first_address.to_string())
			.expect("Error adding reserved peer");
	}

	network.run_until_all_full(|_index, service| {
		service.client().info().finalized_number >= (NUM_BLOCKS as u32).into()
	});
}
