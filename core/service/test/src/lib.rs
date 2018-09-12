// Copyright 2017 Parity Technologies (UK) Ltd.
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

extern crate tempdir;
extern crate tokio;
extern crate futures;
extern crate env_logger;
extern crate substrate_service as service;
extern crate substrate_network as network;
extern crate substrate_primitives as primitives;

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
};
use network::{NetworkConfiguration, NonReservedPeerMode, Secret, AddrComponent, SyncProvider, ManageNetwork};

struct TestNet<F: ServiceFactory> {
	runtime: Runtime,
	_authority_nodes: Arc<Vec<(u32, F::FullService)>>,
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
		self.runtime.block_on(interval).expect("Error running tokio runtime");
	}
}

fn node_private_key_string(index: u32) -> String {
	format!("N{}", index)
}

fn node_config<F: ServiceFactory> (index: u32, spec: &FactoryChainSpec<F>, role: Roles, root: &TempDir) -> FactoryFullConfiguration<F> {
	let root = root.path().join(format!("node-{}", index));
	let mut keys = Vec::new();
	if role == Roles::AUTHORITY {
		keys.push(node_private_key_string(index));
	}

	let network_config = NetworkConfiguration {
		config_path: Some(root.join("network").to_str().unwrap().into()),
		net_config_path: Some(root.join("network").to_str().unwrap().into()),
		listen_addresses: vec! [
			iter::once(AddrComponent::IP4(Ipv4Addr::new(127, 0, 0, 1)))
				.chain(iter::once(AddrComponent::TCP(30400 + index as u16)))
				.collect()
		],
		public_addresses: vec![],
		boot_nodes: vec![],
		use_secret: Secret::from_slice(&blake2_256(node_private_key_string(index).as_bytes())),
		min_peers: 5,
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
		extrinsic_pool: Default::default(),
		network: network_config,
		keystore_path: root.join("key").to_str().unwrap().into(),
		database_path: root.join("db").to_str().unwrap().into(),
		pruning: Default::default(),
		keys: keys,
		chain_spec: (*spec).clone(),
		custom: Default::default(),
		name: format!("Node {}", index),
		execution_strategy: ExecutionStrategy::Both,
		rpc_http: None,
		rpc_ws: None,
		telemetry_url: None,
	}
}

impl<F: ServiceFactory> TestNet<F> {
	fn new(temp: &TempDir, spec: FactoryChainSpec<F>, full: u32, light: u32, authorities: u32) -> TestNet<F> {
		::env_logger::init().ok();
		let runtime = Runtime::new().expect("Error creating tokio runtime");
		let authority_nodes = (0..authorities).map(|index| (index,
			F::new_full(node_config::<F>(index, &spec, Roles::AUTHORITY, &temp), runtime.executor())
				.expect("Error creating test node service"))
		).collect();

		let full_nodes = (authorities..full + authorities).map(|index| (index,
			F::new_full(node_config::<F>(index, &spec, Roles::FULL, &temp), runtime.executor())
				.expect("Error creating test node service"))
		).collect();

		let light_nodes = (full + authorities..full + authorities + light).map(|index| (index,
			F::new_light(node_config::<F>(index, &spec, Roles::LIGHT, &temp), runtime.executor())
				.expect("Error creating test node service"))
		).collect();

		TestNet {
			runtime,
			_authority_nodes: Arc::new(authority_nodes),
			full_nodes: Arc::new(full_nodes),
			_light_nodes: Arc::new(light_nodes),
		}
	}
}

pub fn connectivity_test<F: ServiceFactory>(spec: FactoryChainSpec<F>) {
	let temp = TempDir::new("substrate-connectivity-test").expect("Error creating test dir");
	let mut network = TestNet::<F>::new(&temp, spec, 25, 0, 0);
	let first_address = network.full_nodes[0].1.network().node_id().unwrap();
	println!("Center node ID: {}", first_address);
	for (_, service) in network.full_nodes.iter().skip(1) {
		service.network().add_reserved_peer(first_address.clone()).expect("Error adding reserved peer");
	}
	network.run_until_all_full(|_index, service| {
		service.network().status().num_peers == 24
	});
}
