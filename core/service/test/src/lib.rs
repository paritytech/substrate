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
use std::sync::Arc;
use std::net::Ipv4Addr;
use std::time::Duration;
use std::collections::HashMap;
use log::info;
use futures::{Future, Stream};
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
use network::{multiaddr, Multiaddr, SyncProvider, ManageNetwork};
use network::config::{NetworkConfiguration, NodeKeyConfig, Secret, NonReservedPeerMode};
use sr_primitives::generic::BlockId;
use consensus::{ImportBlock, BlockImport};

/// Maximum duration of single wait call.
const MAX_WAIT_TIME: Duration = Duration::from_secs(60 * 3);

struct TestNet<F: ServiceFactory> {
	runtime: Runtime,
	authority_nodes: Vec<(u32, Arc<F::FullService>, Multiaddr)>,
	full_nodes: Vec<(u32, Arc<F::FullService>, Multiaddr)>,
	light_nodes: Vec<(u32, Arc<F::LightService>, Multiaddr)>,
	chain_spec: FactoryChainSpec<F>,
	base_port: u16,
	nodes: usize,
}

impl<F: ServiceFactory> TestNet<F> {
	pub fn run_until_all_full<FP, LP>(
		&mut self,
		full_predicate: FP,
		light_predicate: LP,
	)
		where
			FP: Send + Sync + Fn(u32, &F::FullService) -> bool + 'static,
			LP: Send + Sync + Fn(u32, &F::LightService) -> bool + 'static,
	{
		let full_nodes = self.full_nodes.clone();
		let light_nodes = self.light_nodes.clone();
		let interval = Interval::new_interval(Duration::from_millis(100))
			.map_err(|_| ())
			.for_each(move |_| {
				let full_ready = full_nodes.iter().all(|&(ref id, ref service, _)| full_predicate(*id, service));
				if !full_ready {
					return Ok(());
				}

				let light_ready = light_nodes.iter().all(|&(ref id, ref service, _)| light_predicate(*id, service));
				if !light_ready {
					return Ok(());
				}

				Err(())
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
	index: u32,
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
		enable_mdns: false,
		wasm_external_transport: None,
	};

	Configuration {
		impl_name: "network-test-impl",
		impl_version: "0.1",
		impl_commit: "",
		roles: role,
		transaction_pool: Default::default(),
		network: network_config,
		keystore_path: root.join("key").to_str().unwrap().into(),
		database_path: root.join("db").to_str().unwrap().into(),
		database_cache_size: None,
		state_cache_size: 16777216,
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
		default_heap_pages: None,
		offchain_worker: false,
		force_authoring: false,
		disable_grandpa: false,
		password: "".to_string(),
	}
}

impl<F: ServiceFactory> TestNet<F> {
	fn new(temp: &TempDir, spec: FactoryChainSpec<F>, full: u32, light: u32, authorities: Vec<String>, base_port: u16) -> TestNet<F> {
		let _ = ::env_logger::try_init();
		::fdlimit::raise_fd_limit();
		let runtime = Runtime::new().expect("Error creating tokio runtime");
		let mut net = TestNet {
			runtime,
			authority_nodes: Default::default(),
			full_nodes: Default::default(),
			light_nodes: Default::default(),
			chain_spec: spec.clone(),
			base_port,
			nodes: 0,
		};
		net.insert_nodes(temp, full, light, authorities);
		net
	}

	fn insert_nodes(&mut self, temp: &TempDir, full: u32, light: u32, authorities: Vec<String>) {
		let mut nodes = self.nodes;
		let base_port = self.base_port;
		let spec = self.chain_spec.clone();
		let executor = self.runtime.executor();
		self.authority_nodes.extend(authorities.iter().enumerate().map(|(index, key)| {
			let node_config = node_config::<F>(index as u32, &spec, Roles::AUTHORITY, Some(key.clone()), base_port, &temp);
			let addr = node_config.network.listen_addresses.iter().next().unwrap().clone();
			let service = Arc::new(F::new_full(node_config, executor.clone())
				.expect("Error creating test node service"));
			let addr = addr.with(multiaddr::Protocol::P2p(service.network().local_peer_id().into()));
			((index + nodes) as u32, service, addr)
		}));
		nodes += authorities.len();

		self.full_nodes.extend((nodes..nodes + full as usize).map(|index| {
			let node_config = node_config::<F>(index as u32, &spec, Roles::FULL, None, base_port, &temp);
			let addr = node_config.network.listen_addresses.iter().next().unwrap().clone();
			let service = Arc::new(F::new_full(node_config, executor.clone())
				.expect("Error creating test node service"));
			let addr = addr.with(multiaddr::Protocol::P2p(service.network().local_peer_id().into()));
			(index as u32, service, addr)
		}));
		nodes += full as usize;

		self.light_nodes.extend((nodes..nodes + light as usize).map(|index| {
			let node_config = node_config::<F>(index as u32, &spec, Roles::LIGHT, None, base_port, &temp);
			let addr = node_config.network.listen_addresses.iter().next().unwrap().clone();
			let service = Arc::new(F::new_light(node_config, executor.clone())
				.expect("Error creating test node service"));
			let addr = addr.with(multiaddr::Protocol::P2p(service.network().local_peer_id().into()));
			(index as u32, service, addr)
		}));
		nodes += light as usize;

		self.nodes = nodes;
	}
}

pub fn connectivity<F: ServiceFactory>(spec: FactoryChainSpec<F>) {
	const NUM_FULL_NODES: u32 = 5;
	const NUM_LIGHT_NODES: u32 = 5;
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
				service.network().add_reserved_peer(first_address.to_string()).expect("Error adding reserved peer");
			}
			for (_, service, _) in network.light_nodes.iter() {
				service.network().add_reserved_peer(first_address.to_string()).expect("Error adding reserved peer");
			}
			network.run_until_all_full(
				|_index, service| service.network().peers_debug_info().len() == NUM_FULL_NODES as usize - 1
					+ NUM_LIGHT_NODES as usize,
				|_index, service| service.network().peers_debug_info().len() == NUM_FULL_NODES as usize,
			);
			network.runtime
		};

		runtime.shutdown_on_idle().wait().expect("Error shutting down runtime");

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
			let max_nodes = ::std::cmp::max(NUM_FULL_NODES, NUM_LIGHT_NODES);
			for i in 0..max_nodes {
				if i != 0 {
					if let Some((_, service, node_id)) = network.full_nodes.get(i as usize) {
						service.network().add_reserved_peer(address.to_string()).expect("Error adding reserved peer");
						address = node_id.clone();
					}
				}

				if let Some((_, service, node_id)) = network.light_nodes.get(i as usize) {
					service.network().add_reserved_peer(address.to_string()).expect("Error adding reserved peer");
					address = node_id.clone();
				}
			}
			network.run_until_all_full(
				|_index, service| service.network().peers_debug_info().len() == NUM_FULL_NODES as usize - 1
					+ NUM_LIGHT_NODES as usize,
				|_index, service| service.network().peers_debug_info().len() == NUM_FULL_NODES as usize,
			);
		}
		temp.close().expect("Error removing temp dir");
	}
}

pub fn sync<F, B, E>(
	spec: FactoryChainSpec<F>,
	mut block_factory: B,
	mut extrinsic_factory: E,
)
where
	F: ServiceFactory,
	B: FnMut(&F::FullService) -> ImportBlock<F::Block>,
	E: FnMut(&F::FullService) -> FactoryExtrinsic<F>,
{
	const NUM_FULL_NODES: u32 = 10;
	const NUM_LIGHT_NODES: u32 = 10;
	const NUM_BLOCKS: u32 = 512;
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
		for i in 0 .. NUM_BLOCKS {
			if i % 128 == 0 {
				info!("Generating #{}", i);
			}
			let import_data = block_factory(&first_service);
			first_service.client().import_block(import_data, HashMap::new()).expect("Error importing test block");
		}
		network.full_nodes[0].2.clone()
	};
	info!("Running sync");
	for (_, service, _) in network.full_nodes.iter().skip(1) {
		service.network().add_reserved_peer(first_address.to_string()).expect("Error adding reserved peer");
	}
	for (_, service, _) in network.light_nodes.iter() {
		service.network().add_reserved_peer(first_address.to_string()).expect("Error adding reserved peer");
	}
	network.run_until_all_full(
		|_index, service|
			service.client().info().chain.best_number == NUM_BLOCKS.into(),
		|_index, service|
			service.client().info().chain.best_number == NUM_BLOCKS.into(),
	);
	info!("Checking extrinsic propagation");
	let first_service = network.full_nodes[0].1.clone();
	let best_block = BlockId::number(first_service.client().info().chain.best_number);
	first_service.transaction_pool().submit_one(&best_block, extrinsic_factory(&first_service)).unwrap();
	network.run_until_all_full(
		|_index, service| service.transaction_pool().ready().count() == 1,
		|_index, _service| true,
	);
}

pub fn consensus<F>(spec: FactoryChainSpec<F>, authorities: Vec<String>)
	where
		F: ServiceFactory,
{
	const NUM_FULL_NODES: u32 = 10;
	const NUM_LIGHT_NODES: u32 = 0;
	const NUM_BLOCKS: u32 = 10; // 10 * 2 sec block production time = ~20 seconds
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
		service.network().add_reserved_peer(first_address.to_string()).expect("Error adding reserved peer");
	}
	for (_, service, _) in network.light_nodes.iter() {
		service.network().add_reserved_peer(first_address.to_string()).expect("Error adding reserved peer");
	}
	for (_, service, _) in network.authority_nodes.iter().skip(1) {
		service.network().add_reserved_peer(first_address.to_string()).expect("Error adding reserved peer");
	}
	network.run_until_all_full(
		|_index, service|
			service.client().info().chain.finalized_number >= (NUM_BLOCKS / 2).into(),
		|_index, service|
			service.client().info().chain.best_number >= (NUM_BLOCKS / 2).into(),
	);
	info!("Adding more peers");
	network.insert_nodes(&temp, NUM_FULL_NODES / 2, NUM_LIGHT_NODES / 2, vec![]);
	for (_, service, _) in network.full_nodes.iter() {
		service.network().add_reserved_peer(first_address.to_string()).expect("Error adding reserved peer");
	}
	for (_, service, _) in network.light_nodes.iter() {
		service.network().add_reserved_peer(first_address.to_string()).expect("Error adding reserved peer");
	}
	network.run_until_all_full(
		|_index, service|
			service.client().info().chain.finalized_number >= NUM_BLOCKS.into(),
		|_index, service|
			service.client().info().chain.best_number >= NUM_BLOCKS.into(),
	);
}
