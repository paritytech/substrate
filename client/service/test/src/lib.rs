// Copyright 2018-2020 Parity Technologies (UK) Ltd.
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

//! Service integration test utils.

use std::iter;
use std::sync::{Arc, Mutex, MutexGuard};
use std::net::Ipv4Addr;
use std::pin::Pin;
use std::time::Duration;
use std::task::{Poll, Context};
use log::info;
use tempfile::TempDir;
use tokio::runtime::Runtime;
use futures::prelude::*;
use futures::future::ready;
use async_std::stream::interval;
use async_std::prelude::FutureExt;
use sc_service::{
	AbstractService,
	ChainSpec,
	Configuration,
	config::{DatabaseConfig, KeystoreConfig},
	Roles,
	Error,
};
use sc_network::{multiaddr, Multiaddr, NetworkStateInfo};
use sc_network::config::{NetworkConfiguration, TransportConfig, NodeKeyConfig, Secret, NonReservedPeerMode};
use sp_runtime::{generic::BlockId, traits::Block as BlockT};
use sp_transaction_pool::TransactionPool;

/// Maximum duration of single wait call.
const MAX_WAIT_TIME: Duration = Duration::from_secs(60 * 3);

struct TestNet<G, E, F, L, U> {
	runtime: Runtime,
	authority_nodes: Vec<(usize, SyncService<F>, U, Multiaddr)>,
	full_nodes: Vec<(usize, SyncService<F>, U, Multiaddr)>,
	light_nodes: Vec<(usize, SyncService<L>, Multiaddr)>,
	chain_spec: ChainSpec<G, E>,
	base_port: u16,
	nodes: usize,
}

/// Wraps around an `Arc<Service>` and implements `Future`.
pub struct SyncService<T>(Arc<Mutex<T>>);

impl<T> SyncService<T> {
	pub fn get(&self) -> MutexGuard<T> {
		self.0.lock().unwrap()
	}
}

impl<T> Clone for SyncService<T> {
	fn clone(&self) -> Self {
		Self(self.0.clone())
	}
}

impl<T> From<T> for SyncService<T> {
	fn from(service: T) -> Self {
		SyncService(Arc::new(Mutex::new(service)))
	}
}

impl<T: futures::Future<Output=Result<(), sc_service::Error>> + Unpin> Future for SyncService<T> {
	type Output = Result<(), sc_service::Error>;

	fn poll(self: Pin<&mut Self>, cx: &mut Context) -> Poll<Self::Output> {
		Pin::new(&mut *self.get()).poll(cx)
	}
}

impl<G, E, F, L, U> TestNet<G, E, F, L, U>
where F: Send + 'static, L: Send +'static, U: Clone + Send + 'static
{
	pub fn run_until_all_full<FP, LP>(
		&mut self,
		full_predicate: FP,
		light_predicate: LP,
	)
		where
			FP: Send + Fn(usize, &SyncService<F>) -> bool + 'static,
			LP: Send + Fn(usize, &SyncService<L>) -> bool + 'static,
	{
		let full_nodes = self.full_nodes.clone();
		let light_nodes = self.light_nodes.clone();
		let interval = interval(Duration::from_millis(100))
			.take_while(move |_| {
				let num_full_ready = full_nodes.iter().filter(|&(ref id, ref service, _, _)|
					full_predicate(*id, service)
				).count();

				let num_light_ready = light_nodes.iter().filter(|&(ref id, ref service, _)|
					light_predicate(*id, service)
				).count();

				info!(
					"Full nodes ready: {}/{}; Light nodes ready: {}/{}",
					num_full_ready, full_nodes.len(),
					num_light_ready, light_nodes.len(),
				);

				let full_ready = num_full_ready == full_nodes.len();
				let light_ready = num_light_ready == light_nodes.len();

				ready(!(light_ready && full_ready))
			})
			.for_each(|_| ready(()))
			.timeout(MAX_WAIT_TIME);

		match self.runtime.block_on(interval) {
			Ok(()) => {},
			Err(_) => panic!("Waited for too long"),
		}
	}
}

fn node_config<G, E: Clone> (
	index: usize,
	spec: &ChainSpec<G, E>,
	role: Roles,
	task_executor: Arc<dyn Fn(Pin<Box<dyn futures::Future<Output = ()> + Send>>) + Send + Sync>,
	key_seed: Option<String>,
	base_port: u16,
	root: &TempDir,
) -> Configuration<G, E>
{
	let root = root.path().join(format!("node-{}", index));

	let config_path = Some(root.join("network"));
	let net_config_path = config_path.clone();

	let network_config = NetworkConfiguration {
		config_path,
		net_config_path,
		listen_addresses: vec! [
			iter::once(multiaddr::Protocol::Ip4(Ipv4Addr::new(127, 0, 0, 1)))
				.chain(iter::once(multiaddr::Protocol::Tcp(base_port + index as u16)))
				.collect()
		],
		public_addresses: vec![],
		boot_nodes: vec![],
		node_key: NodeKeyConfig::Ed25519(Secret::New),
		in_peers: 50,
		out_peers: 450,
		reserved_nodes: vec![],
		non_reserved_mode: NonReservedPeerMode::Accept,
		sentry_nodes: vec![],
		client_version: "network/test/0.1".to_owned(),
		node_name: "unknown".to_owned(),
		transport: TransportConfig::Normal {
			enable_mdns: false,
			allow_private_ipv4: true,
			wasm_external_transport: None,
			use_yamux_flow_control: true,
		},
		max_parallel_downloads: NetworkConfiguration::default().max_parallel_downloads,
	};

	Configuration {
		impl_name: "network-test-impl",
		impl_version: "0.1",
		impl_commit: "",
		roles: role,
		task_executor: Some(task_executor),
		transaction_pool: Default::default(),
		network: network_config,
		keystore: KeystoreConfig::Path {
			path: root.join("key"),
			password: None
		},
		config_dir: Some(root.clone()),
		database: Some(DatabaseConfig::Path {
			path: root.join("db"),
			cache_size: None
		}),
		state_cache_size: 16777216,
		state_cache_child_ratio: None,
		pruning: Default::default(),
		chain_spec: Some((*spec).clone()),
		name: format!("Node {}", index),
		wasm_method: sc_service::config::WasmExecutionMethod::Interpreted,
		execution_strategies: Default::default(),
		rpc_http: None,
		rpc_ws: None,
		rpc_ws_max_connections: None,
		rpc_cors: None,
		prometheus_port: None,
		telemetry_endpoints: None,
		telemetry_external_transport: None,
		default_heap_pages: None,
		offchain_worker: false,
		sentry_mode: false,
		force_authoring: false,
		disable_grandpa: false,
		dev_key_seed: key_seed,
		tracing_targets: None,
		tracing_receiver: Default::default(),
	}
}

impl<G, E, F, L, U> TestNet<G, E, F, L, U> where
	F: AbstractService,
	L: AbstractService,
	E: Clone,
{
	fn new(
		temp: &TempDir,
		spec: ChainSpec<G, E>,
		full: impl Iterator<Item = impl FnOnce(Configuration<G, E>) -> Result<(F, U), Error>>,
		light: impl Iterator<Item = impl FnOnce(Configuration<G, E>) -> Result<L, Error>>,
		authorities: impl Iterator<Item = (
			String,
			impl FnOnce(Configuration<G, E>) -> Result<(F, U), Error>
		)>,
		base_port: u16
	) -> TestNet<G, E, F, L, U> {
		let _ = env_logger::try_init();
		fdlimit::raise_fd_limit();
		let runtime = Runtime::new().expect("Error creating tokio runtime");
		let mut net = TestNet {
			runtime,
			authority_nodes: Default::default(),
			full_nodes: Default::default(),
			light_nodes: Default::default(),
			chain_spec: spec,
			base_port,
			nodes: 0,
		};
		net.insert_nodes(temp, full, light, authorities);
		net
	}

	fn insert_nodes(
		&mut self,
		temp: &TempDir,
		full: impl Iterator<Item = impl FnOnce(Configuration<G, E>) -> Result<(F, U), Error>>,
		light: impl Iterator<Item = impl FnOnce(Configuration<G, E>) -> Result<L, Error>>,
		authorities: impl Iterator<Item = (String, impl FnOnce(Configuration<G, E>) -> Result<(F, U), Error>)>
	) {
		let handle = self.runtime.handle();

		for (key, authority) in authorities {
			let task_executor = {
				let handle = handle.clone();
				Arc::new(move |fut| { handle.spawn(fut); })
			};
			let node_config = node_config(
				self.nodes,
				&self.chain_spec,
				Roles::AUTHORITY,
				task_executor,
				Some(key),
				self.base_port,
				&temp,
			);
			let addr = node_config.network.listen_addresses.iter().next().unwrap().clone();
			let (service, user_data) = authority(node_config).expect("Error creating test node service");
			let service = SyncService::from(service);

			handle.spawn(service.clone().map_err(|_| ()));
			let addr = addr.with(multiaddr::Protocol::P2p(service.get().network().local_peer_id().into()));
			self.authority_nodes.push((self.nodes, service, user_data, addr));
			self.nodes += 1;
		}

		for full in full {
			let task_executor = {
				let handle = handle.clone();
				Arc::new(move |fut| { handle.spawn(fut); })
			};
			let node_config = node_config(self.nodes, &self.chain_spec, Roles::FULL, task_executor, None, self.base_port, &temp);
			let addr = node_config.network.listen_addresses.iter().next().unwrap().clone();
			let (service, user_data) = full(node_config).expect("Error creating test node service");
			let service = SyncService::from(service);

			handle.spawn(service.clone().map_err(|_| ()));
			let addr = addr.with(multiaddr::Protocol::P2p(service.get().network().local_peer_id().into()));
			self.full_nodes.push((self.nodes, service, user_data, addr));
			self.nodes += 1;
		}

		for light in light {
			let task_executor = {
				let handle = handle.clone();
				Arc::new(move |fut| { handle.spawn(fut); })
			};
			let node_config = node_config(self.nodes, &self.chain_spec, Roles::LIGHT, task_executor, None, self.base_port, &temp);
			let addr = node_config.network.listen_addresses.iter().next().unwrap().clone();
			let service = SyncService::from(light(node_config).expect("Error creating test node service"));

			handle.spawn(service.clone().map_err(|_| ()));
			let addr = addr.with(multiaddr::Protocol::P2p(service.get().network().local_peer_id().into()));
			self.light_nodes.push((self.nodes, service, addr));
			self.nodes += 1;
		}
	}
}

fn tempdir_with_prefix(prefix: &str) -> TempDir {
	tempfile::Builder::new().prefix(prefix).tempdir().expect("Error creating test dir")
}

pub fn connectivity<G, E, Fb, F, Lb, L>(
	spec: ChainSpec<G, E>,
	full_builder: Fb,
	light_builder: Lb,
) where
	E: Clone,
	Fb: Fn(Configuration<G, E>) -> Result<F, Error>,
	F: AbstractService,
	Lb: Fn(Configuration<G, E>) -> Result<L, Error>,
	L: AbstractService,
{
	const NUM_FULL_NODES: usize = 5;
	const NUM_LIGHT_NODES: usize = 5;

	let expected_full_connections = NUM_FULL_NODES - 1 + NUM_LIGHT_NODES;
	let expected_light_connections = NUM_FULL_NODES;

	{
		let temp = tempdir_with_prefix("substrate-connectivity-test");
		let mut network = TestNet::new(
			&temp,
			spec.clone(),
			(0..NUM_FULL_NODES).map(|_| { |cfg| full_builder(cfg).map(|s| (s, ())) }),
			(0..NUM_LIGHT_NODES).map(|_| { |cfg| light_builder(cfg) }),
			// Note: this iterator is empty but we can't just use `iter::empty()`, otherwise
			// the type of the closure cannot be inferred.
			(0..0).map(|_| (String::new(), { |cfg| full_builder(cfg).map(|s| (s, ())) })),
			30400,
		);
		info!("Checking star topology");
		let first_address = network.full_nodes[0].3.clone();
		for (_, service, _, _) in network.full_nodes.iter().skip(1) {
			service.get().network().add_reserved_peer(first_address.to_string())
				.expect("Error adding reserved peer");
		}
		for (_, service, _) in network.light_nodes.iter() {
			service.get().network().add_reserved_peer(first_address.to_string())
				.expect("Error adding reserved peer");
		}

		network.run_until_all_full(
			move |_index, service| service.get().network().num_connected()
				== expected_full_connections,
			move |_index, service| service.get().network().num_connected()
				== expected_light_connections,
		);

		network.runtime.shutdown_timeout(Duration::from_secs(0));
		temp.close().expect("Error removing temp dir");
	}
	{
		let temp = tempdir_with_prefix("substrate-connectivity-test");
		let mut network = TestNet::new(
			&temp,
			spec,
			(0..NUM_FULL_NODES).map(|_| { |cfg| full_builder(cfg).map(|s| (s, ())) }),
			(0..NUM_LIGHT_NODES).map(|_| { |cfg| light_builder(cfg) }),
			// Note: this iterator is empty but we can't just use `iter::empty()`, otherwise
			// the type of the closure cannot be inferred.
			(0..0).map(|_| (String::new(), { |cfg| full_builder(cfg).map(|s| (s, ())) })),
			30400,
		);
		info!("Checking linked topology");
		let mut address = network.full_nodes[0].3.clone();
		let max_nodes = std::cmp::max(NUM_FULL_NODES, NUM_LIGHT_NODES);
		for i in 0..max_nodes {
			if i != 0 {
				if let Some((_, service, _, node_id)) = network.full_nodes.get(i) {
					service.get().network().add_reserved_peer(address.to_string())
						.expect("Error adding reserved peer");
					address = node_id.clone();
				}
			}

			if let Some((_, service, node_id)) = network.light_nodes.get(i) {
				service.get().network().add_reserved_peer(address.to_string())
					.expect("Error adding reserved peer");
				address = node_id.clone();
			}
		}

		network.run_until_all_full(
			move |_index, service| service.get().network().num_connected()
				== expected_full_connections,
			move |_index, service| service.get().network().num_connected()
				== expected_light_connections,
		);
		temp.close().expect("Error removing temp dir");
	}
}

pub fn sync<G, E, Fb, F, Lb, L, B, ExF, U>(
	spec: ChainSpec<G, E>,
	full_builder: Fb,
	light_builder: Lb,
	mut make_block_and_import: B,
	mut extrinsic_factory: ExF
) where
	Fb: Fn(Configuration<G, E>) -> Result<(F, U), Error>,
	F: AbstractService,
	Lb: Fn(Configuration<G, E>) -> Result<L, Error>,
	L: AbstractService,
	B: FnMut(&F, &mut U),
	ExF: FnMut(&F, &U) -> <F::Block as BlockT>::Extrinsic,
	U: Clone + Send + 'static,
	E: Clone,
{
	const NUM_FULL_NODES: usize = 10;
	// FIXME: BABE light client support is currently not working.
	const NUM_LIGHT_NODES: usize = 10;
	const NUM_BLOCKS: usize = 512;
	let temp = tempdir_with_prefix("substrate-sync-test");
	let mut network = TestNet::new(
		&temp,
		spec.clone(),
		(0..NUM_FULL_NODES).map(|_| { |cfg| full_builder(cfg) }),
		(0..NUM_LIGHT_NODES).map(|_| { |cfg| light_builder(cfg) }),
		// Note: this iterator is empty but we can't just use `iter::empty()`, otherwise
		// the type of the closure cannot be inferred.
		(0..0).map(|_| (String::new(), { |cfg| full_builder(cfg) })),
		30500,
	);
	info!("Checking block sync");
	let first_address = {
		let &mut (_, ref first_service, ref mut first_user_data, _) = &mut network.full_nodes[0];
		for i in 0 .. NUM_BLOCKS {
			if i % 128 == 0 {
				info!("Generating #{}", i + 1);
			}

			make_block_and_import(&first_service.get(), first_user_data);
		}
		network.full_nodes[0].3.clone()
	};

	info!("Running sync");
	for (_, service, _, _) in network.full_nodes.iter().skip(1) {
		service.get().network().add_reserved_peer(first_address.to_string()).expect("Error adding reserved peer");
	}
	for (_, service, _) in network.light_nodes.iter() {
		service.get().network().add_reserved_peer(first_address.to_string()).expect("Error adding reserved peer");
	}
	network.run_until_all_full(
		|_index, service|
			service.get().client().chain_info().best_number == (NUM_BLOCKS as u32).into(),
		|_index, service|
			service.get().client().chain_info().best_number == (NUM_BLOCKS as u32).into(),
	);

	info!("Checking extrinsic propagation");
	let first_service = network.full_nodes[0].1.clone();
	let first_user_data = &network.full_nodes[0].2;
	let best_block = BlockId::number(first_service.get().client().chain_info().best_number);
	let extrinsic = extrinsic_factory(&first_service.get(), first_user_data);
	futures::executor::block_on(first_service.get().transaction_pool().submit_one(&best_block, extrinsic)).unwrap();
	network.run_until_all_full(
		|_index, service| service.get().transaction_pool().ready().count() == 1,
		|_index, _service| true,
	);
}

pub fn consensus<G, E, Fb, F, Lb, L>(
	spec: ChainSpec<G, E>,
	full_builder: Fb,
	light_builder: Lb,
	authorities: impl IntoIterator<Item = String>
) where
	Fb: Fn(Configuration<G, E>) -> Result<F, Error>,
	F: AbstractService,
	Lb: Fn(Configuration<G, E>) -> Result<L, Error>,
	L: AbstractService,
	E: Clone,
{
	const NUM_FULL_NODES: usize = 10;
	const NUM_LIGHT_NODES: usize = 10;
	const NUM_BLOCKS: usize = 10; // 10 * 2 sec block production time = ~20 seconds
	let temp = tempdir_with_prefix("substrate-consensus-test");
	let mut network = TestNet::new(
		&temp,
		spec.clone(),
		(0..NUM_FULL_NODES / 2).map(|_| { |cfg| full_builder(cfg).map(|s| (s, ())) }),
		(0..NUM_LIGHT_NODES / 2).map(|_| { |cfg| light_builder(cfg) }),
		authorities.into_iter().map(|key| (key, { |cfg| full_builder(cfg).map(|s| (s, ())) })),
		30600,
	);

	info!("Checking consensus");
	let first_address = network.authority_nodes[0].3.clone();
	for (_, service, _, _) in network.full_nodes.iter() {
		service.get().network().add_reserved_peer(first_address.to_string()).expect("Error adding reserved peer");
	}
	for (_, service, _) in network.light_nodes.iter() {
		service.get().network().add_reserved_peer(first_address.to_string()).expect("Error adding reserved peer");
	}
	for (_, service, _, _) in network.authority_nodes.iter().skip(1) {
		service.get().network().add_reserved_peer(first_address.to_string()).expect("Error adding reserved peer");
	}
	network.run_until_all_full(
		|_index, service|
			service.get().client().chain_info().finalized_number >= (NUM_BLOCKS as u32 / 2).into(),
		|_index, service|
			service.get().client().chain_info().best_number >= (NUM_BLOCKS as u32 / 2).into(),
	);

	info!("Adding more peers");
	network.insert_nodes(
		&temp,
		(0..NUM_FULL_NODES / 2).map(|_| { |cfg| full_builder(cfg).map(|s| (s, ())) }),
		(0..NUM_LIGHT_NODES / 2).map(|_| { |cfg| light_builder(cfg) }),
		// Note: this iterator is empty but we can't just use `iter::empty()`, otherwise
		// the type of the closure cannot be inferred.
		(0..0).map(|_| (String::new(), { |cfg| full_builder(cfg).map(|s| (s, ())) })),
	);
	for (_, service, _, _) in network.full_nodes.iter() {
		service.get().network().add_reserved_peer(first_address.to_string()).expect("Error adding reserved peer");
	}
	for (_, service, _) in network.light_nodes.iter() {
		service.get().network().add_reserved_peer(first_address.to_string()).expect("Error adding reserved peer");
	}
	network.run_until_all_full(
		|_index, service|
			service.get().client().chain_info().finalized_number >= (NUM_BLOCKS as u32).into(),
		|_index, service|
			service.get().client().chain_info().best_number >= (NUM_BLOCKS as u32).into(),
	);
}
