// Copyright 2018 Parity Technologies (UK) Ltd.
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

#[macro_use]
extern crate log;
extern crate tempdir;
extern crate tokio;
extern crate futures;
extern crate env_logger;
extern crate fdlimit;
extern crate substrate_service as service;
extern crate substrate_network as network;
extern crate substrate_primitives as primitives;
extern crate substrate_client as client;
extern crate sr_primitives;
use std::iter;
use std::sync::Arc;
use std::net::Ipv4Addr;
use std::time::Duration;
use futures::Stream;
use tempdir::TempDir;
use tokio::runtime::Runtime;
use tokio::timer::Interval;
use primitives::blake2_256;
use service::{
	ServiceFactory,
	ExecutionStrategy,
	Configuration,
	FactoryFullConfiguration,
	FactoryChainSpec,
	Roles,
	FactoryExtrinsic,
};
use network::{NetworkConfiguration, NonReservedPeerMode, Protocol, SyncProvider, ManageNetwork};
use client::{BlockOrigin, JustifiedHeader};
use sr_primitives::traits::As;

struct TestNet<F: ServiceFactory> {
	runtime: Runtime,
	authority_nodes: Arc<Vec<(u32, F::FullService)>>,
	full_nodes: Arc<Vec<(u32, F::FullService)>>,
	_light_nodes: Arc<Vec<(u32, F::LightService)>>,
}

impl<F: ServiceFactory> TestNet<F> {
	pub fn run_until_all_full<P: Send + Sync + Fn(u32, &F::FullService) -> bool + 'static>(&mut self, predicate: P) {
		let full_nodes = self.full_nodes.clone();
		let interval = Interval::new_interval(Duration::from_millis(100)).map_err(|_| ()).for_each(move |_| {
			if full_nodes.iter().all(|&(ref id, ref service)| predicate(*id, service)) {
				Err(())
			} else {
				Ok(())
			}
		});
		self.runtime.block_on(interval).ok();
	}
}

fn node_private_key_string(index: u32) -> String {
	format!("N{}", index)
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

	let network_config = NetworkConfiguration {
		config_path: Some(root.join("network").to_str().unwrap().into()),
		net_config_path: Some(root.join("network").to_str().unwrap().into()),
		listen_addresses: vec! [
			iter::once(Protocol::Ip4(Ipv4Addr::new(127, 0, 0, 1)))
				.chain(iter::once(Protocol::Tcp(base_port + index as u16)))
				.collect()
		],
		public_addresses: vec![],
		boot_nodes: vec![],
		use_secret: Some(blake2_256(node_private_key_string(index).as_bytes())),
		min_peers: 25,
		max_peers: 500,
		reserved_nodes: vec![],
		non_reserved_mode: NonReservedPeerMode::Accept,
		client_version: "network/test/0.1".to_owned(),
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
		pruning: Default::default(),
		keys: keys,
		chain_spec: (*spec).clone(),
		custom: Default::default(),
		name: format!("Node {}", index),
		block_execution_strategy: ExecutionStrategy::NativeWhenPossible,
		api_execution_strategy: ExecutionStrategy::NativeWhenPossible,
		rpc_http: None,
		rpc_ws: None,
		telemetry_url: None,
	}
}

impl<F: ServiceFactory> TestNet<F> {
	fn new(temp: &TempDir, spec: FactoryChainSpec<F>, full: u32, light: u32, authorities: Vec<String>, base_port: u16) -> TestNet<F> {
		::env_logger::init().ok();
		::fdlimit::raise_fd_limit();
		let runtime = Runtime::new().expect("Error creating tokio runtime");
		let authority_nodes = authorities.iter().enumerate().map(|(index, key)| (index as u32,
			F::new_full(node_config::<F>(index as u32, &spec, Roles::AUTHORITY, Some(key.clone()), base_port, &temp), runtime.executor())
				.expect("Error creating test node service"))
		).collect();

		let authorities = authorities.len() as u32;
		let full_nodes = (authorities..full + authorities).map(|index| (index,
			F::new_full(node_config::<F>(index, &spec, Roles::FULL, None, base_port, &temp), runtime.executor())
				.expect("Error creating test node service"))
		).collect();

		let light_nodes = (full + authorities..full + authorities + light).map(|index| (index,
			F::new_light(node_config::<F>(index, &spec, Roles::LIGHT, None, base_port, &temp), runtime.executor())
				.expect("Error creating test node service"))
		).collect();

		TestNet {
			runtime,
			authority_nodes: Arc::new(authority_nodes),
			full_nodes: Arc::new(full_nodes),
			_light_nodes: Arc::new(light_nodes),
		}
	}
}

pub fn connectivity<F: ServiceFactory>(spec: FactoryChainSpec<F>) {
	const NUM_NODES: u32 = 10;
	{
		let temp = TempDir::new("substrate-connectivity-test").expect("Error creating test dir");
		{
			let mut network = TestNet::<F>::new(&temp, spec.clone(), NUM_NODES, 0, vec![], 30400);
			info!("Checking star topology");
			let first_address = network.full_nodes[0].1.network().node_id().unwrap();
			for (_, service) in network.full_nodes.iter().skip(1) {
				service.network().add_reserved_peer(first_address.clone()).expect("Error adding reserved peer");
			}
			network.run_until_all_full(|_index, service|
				service.network().status().num_peers == NUM_NODES as usize - 1
			);
		}
		temp.close().expect("Error removing temp dir");
	}
	{
		let temp = TempDir::new("substrate-connectivity-test").expect("Error creating test dir");
		{
			let mut network = TestNet::<F>::new(&temp, spec, NUM_NODES as u32, 0, vec![], 30400);
			info!("Checking linked topology");
			let mut address = network.full_nodes[0].1.network().node_id().unwrap();
			for (_, service) in network.full_nodes.iter().skip(1) {
				service.network().add_reserved_peer(address.clone()).expect("Error adding reserved peer");
				address = service.network().node_id().unwrap();
			}
			network.run_until_all_full(|_index, service| {
				service.network().status().num_peers == NUM_NODES as usize - 1
			});
		}
		temp.close().expect("Error removing temp dir");
	}
}

pub fn sync<F, B>(spec: FactoryChainSpec<F>, block_factory: B)
where
	F: ServiceFactory,
	B: Fn(&F::FullService) -> (JustifiedHeader<F::Block>, Option<Vec<FactoryExtrinsic<F>>>),
{
	const NUM_NODES: u32 = 10;
	const NUM_BLOCKS: usize = 512;
	let temp = TempDir::new("substrate-sync-test").expect("Error creating test dir");
	let mut network = TestNet::<F>::new(&temp, spec.clone(), NUM_NODES, 0, vec![], 30500);
	info!("Checking block sync");
	let first_address = {
		let first_service = &network.full_nodes[0].1;
		for i in 0 .. NUM_BLOCKS {
			if i % 128 == 0 {
				info!("Generating #{}", i);
			}
			let (header, body) = block_factory(&first_service);
			first_service.client().import_block(BlockOrigin::File, header, body, true).expect("Error importing test block");
		}
		first_service.network().node_id().unwrap()
	};
	info!("Running sync");
	for (_, service) in network.full_nodes.iter().skip(1) {
		service.network().add_reserved_peer(first_address.clone()).expect("Error adding reserved peer");
	}
	network.run_until_all_full(|_index, service| {
		service.client().info().unwrap().chain.best_number == As::sa(NUM_BLOCKS as u64)
	});
}

pub fn consensus<F>(spec: FactoryChainSpec<F>, authorities: Vec<String>)
where
	F: ServiceFactory,
{
	const NUM_NODES: u32 = 10;
	const NUM_BLOCKS: u64 = 200;
	info!("Checking consensus");
	let temp = TempDir::new("substrate-conensus-test").expect("Error creating test dir");
	let mut network = TestNet::<F>::new(&temp, spec.clone(), NUM_NODES, 0, authorities, 30600);
	let first_address = network.authority_nodes[0].1.network().node_id().unwrap();
	for (_, service) in network.full_nodes.iter() {
		service.network().add_reserved_peer(first_address.clone()).expect("Error adding reserved peer");
	}
	for (_, service) in network.authority_nodes.iter().skip(1) {
		service.network().add_reserved_peer(first_address.clone()).expect("Error adding reserved peer");
	}
	network.run_until_all_full(|_index, service| {
		service.client().info().unwrap().chain.finalized_number >= As::sa(NUM_BLOCKS)
	});
}
