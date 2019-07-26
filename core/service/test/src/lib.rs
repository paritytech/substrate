// Copyright 2018-2019 Parity Technologies (UK) Ltd.
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
use std::time::Duration;
use std::collections::HashMap;
use log::info;
use futures::{Future, Stream, Poll};
use tempdir::TempDir;
use tokio::{runtime::Runtime, prelude::FutureExt};
use tokio::timer::Interval;
use service::{
	ServiceFactory,
	Configuration,
	FactoryFullConfiguration,
	FactoryChainSpec,
	Roles,
	FactoryExtrinsic,
};
use network::{multiaddr, Multiaddr};
use network::config::{NetworkConfiguration, TransportConfig, NodeKeyConfig, Secret, NonReservedPeerMode};
use sr_primitives::generic::BlockId;
use consensus::{BlockImportParams, BlockImport};

/// Maximum duration of single wait call.
const MAX_WAIT_TIME: Duration = Duration::from_secs(60 * 3);

struct TestNet<F: ServiceFactory> {
	runtime: Runtime,
	authority_nodes: Vec<(usize, SyncService<F::FullService>, Multiaddr)>,
	full_nodes: Vec<(usize, SyncService<F::FullService>, Multiaddr)>,
	light_nodes: Vec<(usize, SyncService<F::LightService>, Multiaddr)>,
	chain_spec: FactoryChainSpec<F>,
	base_port: u16,
	nodes: usize,
}

/// Wraps around an `Arc<Service>>` and implements `Future`.
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

impl<T: Future<Item=(), Error=()>> Future for SyncService<T> {
	type Item = ();
	type Error = ();

	fn poll(&mut self) -> Poll<Self::Item, Self::Error> {
		self.0.lock().unwrap().poll()
	}
}

impl<F: ServiceFactory> TestNet<F> {
	pub fn run_until_all_full<FP, LP>(
		&mut self,
		full_predicate: FP,
		light_predicate: LP,
	)
		where
			FP: Send + Fn(usize, &SyncService<F::FullService>) -> bool + 'static,
			LP: Send + Fn(usize, &SyncService<F::LightService>) -> bool + 'static,
	{
		let full_nodes = self.full_nodes.clone();
		let light_nodes = self.light_nodes.clone();
		let interval = Interval::new_interval(Duration::from_millis(100))
			.map_err(|_| ())
			.for_each(move |_| {
				let full_ready = full_nodes.iter().all(|&(ref id, ref service, _)|
					full_predicate(*id, service)
				);

				if !full_ready {
					return Ok(());
				}

				let light_ready = light_nodes.iter().all(|&(ref id, ref service, _)|
					light_predicate(*id, service)
				);

				if !light_ready {
					Ok(())
				} else {
					Err(())
				}
			})
			.timeout(MAX_WAIT_TIME);

		match self.runtime.block_on(interval) {
			Ok(()) => unreachable!("interval always fails; qed"),
			Err(ref err) if err.is_inner() => (),
			Err(_) => panic!("Waited for too long"),
		}
	}
}

fn node_config<F: ServiceFactory> (
	index: usize,
	spec: &FactoryChainSpec<F>,
	role: Roles,
	key_seed: Option<String>,
	base_port: u16,
	root: &TempDir,
) -> FactoryFullConfiguration<F>
{
	let root = root.path().join(format!("node-{}", index));
	let mut keys = Vec::new();
	if let Some(seed) = key_seed {
		keys.push(seed);
	}

	let config_path = Some(String::from(root.join("network").to_str().unwrap()));
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
		client_version: "network/test/0.1".to_owned(),
		node_name: "unknown".to_owned(),
		transport: TransportConfig::Normal {
			enable_mdns: false,
			wasm_external_transport: None,
		},
	};

	Configuration {
		impl_name: "network-test-impl",
		impl_version: "0.1",
		impl_commit: "",
		roles: role,
		transaction_pool: Default::default(),
		network: network_config,
		keystore_path: Some(root.join("key")),
		database_path: root.join("db"),
		database_cache_size: None,
		state_cache_size: 16777216,
		state_cache_child_ratio: None,
		pruning: Default::default(),
		keys: keys,
		chain_spec: (*spec).clone(),
		custom: Default::default(),
		name: format!("Node {}", index),
		execution_strategies: Default::default(),
		rpc_http: None,
		rpc_ws: None,
		rpc_ws_max_connections: None,
		rpc_cors: None,
		telemetry_endpoints: None,
		telemetry_external_transport: None,
		default_heap_pages: None,
		offchain_worker: false,
		force_authoring: false,
		disable_grandpa: false,
		grandpa_voter: false,
		password: "".to_string().into(),
	}
}

impl<F: ServiceFactory> TestNet<F> where
	F::FullService: Future<Item=(), Error=()>,
	F::LightService: Future<Item=(), Error=()>
{
	fn new(
		temp: &TempDir,
		spec: FactoryChainSpec<F>,
		full: usize,
		light: usize,
		authorities: Vec<String>,
		base_port: u16
	) -> TestNet<F> {
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

	fn insert_nodes(&mut self, temp: &TempDir, full: usize, light: usize, authorities: Vec<String>) {
		let mut nodes = self.nodes;
		let base_port = self.base_port;
		let spec = &self.chain_spec;
		let executor = self.runtime.executor();
		self.authority_nodes.extend(authorities.iter().enumerate().map(|(index, key)| {
			let node_config = node_config::<F>(
				index,
				&spec,
				Roles::AUTHORITY,
				Some(key.clone()),
				base_port,
				&temp,
			);
			let addr = node_config.network.listen_addresses.iter().next().unwrap().clone();
			let service = SyncService::from(F::new_full(node_config).expect("Error creating test node service"));

			executor.spawn(service.clone());
			let addr = addr.with(multiaddr::Protocol::P2p(service.get().network().local_peer_id().into()));
			((index + nodes), service, addr)
		}));
		nodes += authorities.len();

		self.full_nodes.extend((nodes..nodes + full).map(|index| {
			let node_config = node_config::<F>(index, &spec, Roles::FULL, None, base_port, &temp);
			let addr = node_config.network.listen_addresses.iter().next().unwrap().clone();
			let service = SyncService::from(F::new_full(node_config).expect("Error creating test node service"));

			executor.spawn(service.clone());
			let addr = addr.with(multiaddr::Protocol::P2p(service.get().network().local_peer_id().into()));
			(index, service, addr)
		}));
		nodes += full;

		self.light_nodes.extend((nodes..nodes + light).map(|index| {
			let node_config = node_config::<F>(index, &spec, Roles::LIGHT, None, base_port, &temp);
			let addr = node_config.network.listen_addresses.iter().next().unwrap().clone();
			let service = SyncService::from(F::new_light(node_config).expect("Error creating test node service"));

			executor.spawn(service.clone());
			let addr = addr.with(multiaddr::Protocol::P2p(service.get().network().local_peer_id().into()));
			(index, service, addr)
		}));
		nodes += light;

		self.nodes = nodes;
	}
}

pub fn connectivity<F: ServiceFactory>(spec: FactoryChainSpec<F>) where
	F::FullService: Future<Item=(), Error=()>,
	F::LightService: Future<Item=(), Error=()>,
{
	const NUM_FULL_NODES: usize = 5;
	const NUM_LIGHT_NODES: usize = 5;
	{
		let temp = TempDir::new("substrate-connectivity-test").expect("Error creating test dir");
		let runtime = {
			let mut network = TestNet::<F>::new(
				&temp,
				spec.clone(),
				NUM_FULL_NODES,
				NUM_LIGHT_NODES,
				vec![],
				30400,
			);
			info!("Checking star topology");
			let first_address = network.full_nodes[0].2.clone();
			for (_, service, _) in network.full_nodes.iter().skip(1) {
				service.get().network().add_reserved_peer(first_address.to_string()).expect("Error adding reserved peer");
			}
			for (_, service, _) in network.light_nodes.iter() {
				service.get().network().add_reserved_peer(first_address.to_string()).expect("Error adding reserved peer");
			}
			network.run_until_all_full(
				|_index, service| service.get().network().num_connected() == NUM_FULL_NODES - 1
					+ NUM_LIGHT_NODES,
				|_index, service| service.get().network().num_connected() == NUM_FULL_NODES,
			);
			network.runtime
		};

		runtime.shutdown_now().wait().expect("Error shutting down runtime");

		temp.close().expect("Error removing temp dir");
	}
	{
		let temp = TempDir::new("substrate-connectivity-test").expect("Error creating test dir");
		{
			let mut network = TestNet::<F>::new(
				&temp,
				spec,
				NUM_FULL_NODES,
				NUM_LIGHT_NODES,
				vec![],
				30400,
			);
			info!("Checking linked topology");
			let mut address = network.full_nodes[0].2.clone();
			let max_nodes = std::cmp::max(NUM_FULL_NODES, NUM_LIGHT_NODES);
			for i in 0..max_nodes {
				if i != 0 {
					if let Some((_, service, node_id)) = network.full_nodes.get(i) {
						service.get().network().add_reserved_peer(address.to_string()).expect("Error adding reserved peer");
						address = node_id.clone();
					}
				}

				if let Some((_, service, node_id)) = network.light_nodes.get(i) {
					service.get().network().add_reserved_peer(address.to_string()).expect("Error adding reserved peer");
					address = node_id.clone();
				}
			}
			network.run_until_all_full(
				|_index, service| service.get().network().num_connected() == NUM_FULL_NODES - 1
					+ NUM_LIGHT_NODES,
				|_index, service| service.get().network().num_connected() == NUM_FULL_NODES,
			);
		}
		temp.close().expect("Error removing temp dir");
	}
}

pub fn sync<F, B, E>(spec: FactoryChainSpec<F>, mut block_factory: B, mut extrinsic_factory: E) where
	F: ServiceFactory,
	F::FullService: Future<Item=(), Error=()>,
	F::LightService: Future<Item=(), Error=()>,
	B: FnMut(&SyncService<F::FullService>) -> BlockImportParams<F::Block>,
	E: FnMut(&SyncService<F::FullService>) -> FactoryExtrinsic<F>,
{
	const NUM_FULL_NODES: usize = 10;
	// FIXME: BABE light client support is currently not working.
	const NUM_LIGHT_NODES: usize = 0;
	const NUM_BLOCKS: usize = 512;
	let temp = TempDir::new("substrate-sync-test").expect("Error creating test dir");
	let mut network = TestNet::<F>::new(
		&temp,
		spec.clone(),
		NUM_FULL_NODES,
		NUM_LIGHT_NODES,
		vec![],
		30500,
	);
	info!("Checking block sync");
	let first_address = {
		let first_service = &network.full_nodes[0].1;
		let mut client = first_service.get().client();
		for i in 0 .. NUM_BLOCKS {
			if i % 128 == 0 {
				info!("Generating #{}", i);
			}
			let import_data = block_factory(&first_service);
			client.import_block(import_data, HashMap::new()).expect("Error importing test block");
		}
		network.full_nodes[0].2.clone()
	};

	info!("Running sync");
	for (_, service, _) in network.full_nodes.iter().skip(1) {
		service.get().network().add_reserved_peer(first_address.to_string()).expect("Error adding reserved peer");
	}
	for (_, service, _) in network.light_nodes.iter() {
		service.get().network().add_reserved_peer(first_address.to_string()).expect("Error adding reserved peer");
	}
	network.run_until_all_full(
		|_index, service|
			service.get().client().info().chain.best_number == (NUM_BLOCKS as u32).into(),
		|_index, service|
			service.get().client().info().chain.best_number == (NUM_BLOCKS as u32).into(),
	);

	info!("Checking extrinsic propagation");
	let first_service = network.full_nodes[0].1.clone();
	let best_block = BlockId::number(first_service.get().client().info().chain.best_number);
	let extrinsic = extrinsic_factory(&first_service);
	first_service.get().transaction_pool().submit_one(&best_block, extrinsic).unwrap();
	network.run_until_all_full(
		|_index, service| service.get().transaction_pool().ready().count() == 1,
		|_index, _service| true,
	);
}

pub fn consensus<F>(spec: FactoryChainSpec<F>, authorities: Vec<String>) where
	F: ServiceFactory,
	F::FullService: Future<Item=(), Error=()>,
	F::LightService: Future<Item=(), Error=()>,
{
	const NUM_FULL_NODES: usize = 10;
	const NUM_LIGHT_NODES: usize = 0;
	const NUM_BLOCKS: usize = 10; // 10 * 2 sec block production time = ~20 seconds
	let temp = TempDir::new("substrate-conensus-test").expect("Error creating test dir");
	let mut network = TestNet::<F>::new(
		&temp,
		spec.clone(),
		NUM_FULL_NODES / 2,
		NUM_LIGHT_NODES / 2,
		authorities,
		30600,
	);

	info!("Checking consensus");
	let first_address = network.authority_nodes[0].2.clone();
	for (_, service, _) in network.full_nodes.iter() {
		service.get().network().add_reserved_peer(first_address.to_string()).expect("Error adding reserved peer");
	}
	for (_, service, _) in network.light_nodes.iter() {
		service.get().network().add_reserved_peer(first_address.to_string()).expect("Error adding reserved peer");
	}
	for (_, service, _) in network.authority_nodes.iter().skip(1) {
		service.get().network().add_reserved_peer(first_address.to_string()).expect("Error adding reserved peer");
	}
	network.run_until_all_full(
		|_index, service|
			service.get().client().info().chain.finalized_number >= (NUM_BLOCKS as u32 / 2).into(),
		|_index, service|
			service.get().client().info().chain.best_number >= (NUM_BLOCKS as u32 / 2).into(),
	);

	info!("Adding more peers");
	network.insert_nodes(&temp, NUM_FULL_NODES / 2, NUM_LIGHT_NODES / 2, vec![]);
	for (_, service, _) in network.full_nodes.iter() {
		service.get().network().add_reserved_peer(first_address.to_string()).expect("Error adding reserved peer");
	}
	for (_, service, _) in network.light_nodes.iter() {
		service.get().network().add_reserved_peer(first_address.to_string()).expect("Error adding reserved peer");
	}
	network.run_until_all_full(
		|_index, service|
			service.get().client().info().chain.finalized_number >= (NUM_BLOCKS as u32).into(),
		|_index, service|
			service.get().client().info().chain.best_number >= (NUM_BLOCKS as u32).into(),
	);
}
