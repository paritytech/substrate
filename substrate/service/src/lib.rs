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

//! Substrate service. Starts a thread that spins the network, the client and the extrinsic pool.
//! Manages communication between them.

#![warn(unused_extern_crates)]

extern crate futures;
extern crate exit_future;
extern crate serde;
extern crate serde_json;
extern crate substrate_keystore as keystore;
extern crate substrate_primitives as primitives;
extern crate substrate_runtime_primitives as runtime_primitives;
extern crate substrate_network as network;
extern crate substrate_executor;
extern crate substrate_client as client;
extern crate substrate_client_db as client_db;
extern crate substrate_codec as codec;
extern crate substrate_extrinsic_pool as extrinsic_pool;
extern crate substrate_rpc;
extern crate substrate_rpc_servers as rpc;
extern crate target_info;
extern crate tokio;

#[macro_use]
extern crate substrate_telemetry as tel;
#[macro_use]
extern crate error_chain;
#[macro_use]
extern crate slog;	// needed until we can reexport `slog_info` from `substrate_telemetry`
#[macro_use]
extern crate log;
#[macro_use]
extern crate serde_derive;

mod components;
mod error;
mod config;
mod chain_spec;
pub mod chain_ops;

use std::io;
use std::net::SocketAddr;
use std::sync::Arc;
use futures::prelude::*;
use keystore::Store as Keystore;
use client::BlockchainEvents;
use network::ManageNetwork;
use runtime_primitives::traits::{Header, As};
use exit_future::Signal;
use tokio::runtime::TaskExecutor;
use substrate_executor::NativeExecutor;

pub use self::error::{ErrorKind, Error};
pub use config::{Configuration, Roles, PruningMode};
pub use chain_spec::ChainSpec;
pub use extrinsic_pool::txpool::{Options as ExtrinsicPoolOptions};
pub use extrinsic_pool::api::{ExtrinsicPool as ExtrinsicPoolApi};
pub use client::ExecutionStrategy;

pub use components::{ServiceFactory, FullBackend, FullExecutor, LightBackend,
	LightExecutor, ExtrinsicPool, Components, PoolApi, ComponentClient,
	ComponentBlock, FullClient, LightClient, FullComponents, LightComponents,
	CodeExecutor, NetworkService, FactoryChainSpec, FactoryBlock,
	FactoryFullConfiguration, RuntimeGenesis, FactoryGenesis,
};

/// Substrate service.
pub struct Service<Components: components::Components> {
	client: Arc<ComponentClient<Components>>,
	network: Arc<components::NetworkService<Components::Factory>>,
	extrinsic_pool: Arc<Components::ExtrinsicPool>,
	keystore: Keystore,
	signal: Option<Signal>,
	_rpc_http: Option<rpc::HttpServer>,
	_rpc_ws: Option<rpc::WsServer>,
	_telemetry: Option<tel::Telemetry>,
}

/// Creates bare client without any networking.
pub fn new_client<Factory: components::ServiceFactory>(config: FactoryFullConfiguration<Factory>)
	-> Result<Arc<ComponentClient<components::FullComponents<Factory>>>, error::Error>
{
	let executor = NativeExecutor::with_heap_pages(config.min_heap_pages, config.max_heap_pages);
	let (client, _) = components::FullComponents::<Factory>::build_client(
		&config,
		executor,
	)?;
	Ok(client)
}

impl<Components> Service<Components>
	where
		Components: components::Components,
{
	/// Creates a new service.
	pub fn new(
		config: FactoryFullConfiguration<Components::Factory>,
		task_executor: TaskExecutor,
	)
		-> Result<Self, error::Error>
	{
		let (signal, exit) = ::exit_future::signal();

		// Create client
		let executor = NativeExecutor::with_heap_pages(config.min_heap_pages, config.max_heap_pages);

		let mut keystore = Keystore::open(config.keystore_path.as_str().into())?;
		for seed in &config.keys {
			keystore.generate_from_seed(seed)?;
		}

		if keystore.contents()?.is_empty() {
			let key = keystore.generate("")?;
			info!("Generated a new keypair: {:?}", key.public());
		}

		let (client, on_demand) = Components::build_client(&config, executor)?;
		let best_header = client.best_block_header()?;

		let version = config.full_version();
		info!("Best block: #{}", best_header.number());
		telemetry!("node.start"; "height" => best_header.number().as_(), "best" => ?best_header.hash());

		let network_protocol = <Components::Factory>::build_network_protocol(&config)?;
		let extrinsic_pool = Arc::new(
			Components::build_extrinsic_pool(config.extrinsic_pool, client.clone())?
		);
		let extrinsic_pool_adapter = extrinsic_pool.clone();

		let network_params = network::Params {
			config: network::ProtocolConfig {
				roles: config.roles,
			},
			network_config: config.network,
			chain: client.clone(),
			on_demand: on_demand.clone()
				.map(|d| d as Arc<network::OnDemandService<ComponentBlock<Components>>>),
			transaction_pool: extrinsic_pool_adapter,
			specialization: network_protocol,
		};

		let network = network::Service::new(network_params, Components::Factory::NETWORK_PROTOCOL_ID)?;
		on_demand.map(|on_demand| on_demand.set_service_link(Arc::downgrade(&network)));

		network.start_network();

		{
			// block notifications
			let network = network.clone();
			let txpool = extrinsic_pool.clone();

			let events = client.import_notification_stream()
				.for_each(move |notification| {
					network.on_block_imported(notification.hash, &notification.header);
					txpool.prune_imported(&notification.hash);
					Ok(())
				})
				.select(exit.clone())
				.then(|_| Ok(()));
			task_executor.spawn(events);
		}

		{
			// extrinsic notifications
			let network = network.clone();
			let events = extrinsic_pool.api().import_notification_stream()
				// TODO [ToDr] Consider throttling?
				.for_each(move |_| {
					network.trigger_repropagate();
					Ok(())
				})
				.select(exit.clone())
				.then(|_| Ok(()));

			task_executor.spawn(events);
		}

		// RPC
		let rpc_config = RpcConfig {
			chain_name: config.chain_spec.name().to_string(),
			impl_name: config.impl_name,
			impl_version: config.impl_version,
		};

		let (rpc_http, rpc_ws) = {
			let handler = || {
				let client = client.clone();
				let chain = rpc::apis::chain::Chain::new(client.clone(), task_executor.clone());
				let author = rpc::apis::author::Author::new(client.clone(), extrinsic_pool.api(), task_executor.clone());
				rpc::rpc_handler::<ComponentBlock<Components>, _, _, _, _>(
					client,
					chain,
					author,
					rpc_config.clone(),
					)
			};
			(
				maybe_start_server(config.rpc_http, |address| rpc::start_http(address, handler()))?,
				maybe_start_server(config.rpc_ws, |address| rpc::start_ws(address, handler()))?,
			)
		};

		// Telemetry
		let telemetry = match config.telemetry_url {
			Some(url) => {
				let name = config.name.clone();
				let impl_name = config.impl_name.to_owned();
				let version = version.clone();
				let chain_name = config.chain_spec.name().to_owned();
				Some(tel::init_telemetry(tel::TelemetryConfig {
					url: url,
					on_connect: Box::new(move || {
						telemetry!("system.connected";
								   "name" => name.clone(),
								   "implementation" => impl_name.clone(),
								   "version" => version.clone(),
								   "config" => "",
								   "chain" => chain_name.clone(),
								   );
					}),
				}))
			},
			None => None,
		};

		Ok(Service {
			client: client,
			network: network,
			extrinsic_pool: extrinsic_pool,
			signal: Some(signal),
			keystore: keystore,
			_rpc_http: rpc_http,
			_rpc_ws: rpc_ws,
			_telemetry: telemetry,
		})
	}

	/// Get shared client instance.
	pub fn client(&self) -> Arc<ComponentClient<Components>> {
		self.client.clone()
	}

	/// Get shared network instance.
	pub fn network(&self) -> Arc<components::NetworkService<Components::Factory>> {
		self.network.clone()
	}

	/// Get shared extrinsic pool instance.
	pub fn extrinsic_pool(&self) -> Arc<PoolApi<Components>> {
		self.extrinsic_pool.api()
	}

	/// Get shared keystore.
	pub fn keystore(&self) -> &Keystore {
		&self.keystore
	}
}

impl<Components> Drop for Service<Components> where Components: components::Components {
	fn drop(&mut self) {
		debug!(target: "service", "Substrate service shutdown");

		self.network.stop_network();

		if let Some(signal) = self.signal.take() {
			signal.fire();
		}
	}
}

fn maybe_start_server<T, F>(address: Option<SocketAddr>, start: F) -> Result<Option<T>, io::Error> where
	F: Fn(&SocketAddr) -> Result<T, io::Error>,
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

#[derive(Clone)]
struct RpcConfig {
	chain_name: String,
	impl_name: &'static str,
	impl_version: &'static str,
}

impl substrate_rpc::system::SystemApi for RpcConfig {
	fn system_name(&self) -> substrate_rpc::system::error::Result<String> {
		Ok(self.impl_name.into())
	}

	fn system_version(&self) -> substrate_rpc::system::error::Result<String> {
		Ok(self.impl_version.into())
	}

	fn system_chain(&self) -> substrate_rpc::system::error::Result<String> {
		Ok(self.chain_name.clone())
	}
}
