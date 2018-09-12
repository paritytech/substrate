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

// tag::description[]
//! Substrate service. Starts a thread that spins the network, the client and the extrinsic pool.
//! Manages communication between them.
// end::description[]

#![warn(unused_extern_crates)]

extern crate futures;
extern crate exit_future;
extern crate serde;
extern crate serde_json;
extern crate substrate_keystore as keystore;
extern crate substrate_primitives as primitives;
extern crate sr_primitives as runtime_primitives;
extern crate substrate_network as network;
extern crate substrate_executor;
extern crate substrate_client as client;
extern crate substrate_client_db as client_db;
extern crate parity_codec as codec;
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
mod chain_spec;
pub mod config;
pub mod chain_ops;

use std::io;
use std::net::SocketAddr;
use std::sync::Arc;
use std::collections::HashMap;
use futures::prelude::*;
use keystore::Store as Keystore;
use client::BlockchainEvents;
use runtime_primitives::traits::{Header, As};
use runtime_primitives::generic::BlockId;
use exit_future::Signal;
use tokio::runtime::TaskExecutor;
use substrate_executor::NativeExecutor;
use codec::{Encode, Decode};

pub use self::error::{ErrorKind, Error};
pub use config::{Configuration, Roles, PruningMode};
pub use chain_spec::ChainSpec;
pub use extrinsic_pool::{Pool as ExtrinsicPool, Options as ExtrinsicPoolOptions, ChainApi, VerifiedTransaction, IntoPoolError};
pub use client::ExecutionStrategy;

pub use components::{ServiceFactory, FullBackend, FullExecutor, LightBackend,
	LightExecutor, Components, PoolApi, ComponentClient,
	ComponentBlock, FullClient, LightClient, FullComponents, LightComponents,
	CodeExecutor, NetworkService, FactoryChainSpec, FactoryBlock,
	FactoryFullConfiguration, RuntimeGenesis, FactoryGenesis,
	ComponentExHash, ComponentExtrinsic,
};

/// Substrate service.
pub struct Service<Components: components::Components> {
	client: Arc<ComponentClient<Components>>,
	network: Option<Arc<components::NetworkService<Components::Factory>>>,
	extrinsic_pool: Arc<ExtrinsicPool<Components::ExtrinsicPoolApi>>,
	keystore: Keystore,
	exit: ::exit_future::Exit,
	signal: Option<Signal>,
	_rpc_http: Option<rpc::HttpServer>,
	_rpc_ws: Option<rpc::WsServer>,
	_telemetry: Option<tel::Telemetry>,
}

/// Creates bare client without any networking.
pub fn new_client<Factory: components::ServiceFactory>(config: FactoryFullConfiguration<Factory>)
	-> Result<Arc<ComponentClient<components::FullComponents<Factory>>>, error::Error>
{
	let executor = NativeExecutor::new();
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
		let executor = NativeExecutor::new();

		let mut keystore = Keystore::open(config.keystore_path.as_str().into())?;
		for seed in &config.keys {
			keystore.generate_from_seed(seed)?;
		}

		// Keep the public key for telemetry
		let public_key = match keystore.contents()?.get(0) {
			Some(public_key) => public_key.clone(),
			None => {
				let key = keystore.generate("")?;
				let public_key = key.public();
				info!("Generated a new keypair: {:?}", public_key);

				public_key
			}
		};

		let (client, on_demand) = Components::build_client(&config, executor)?;
		let best_header = client.best_block_header()?;

		let version = config.full_version();
		info!("Best block: #{}", best_header.number());
		telemetry!("node.start"; "height" => best_header.number().as_(), "best" => ?best_header.hash());

		let network_protocol = <Components::Factory>::build_network_protocol(&config)?;
		let extrinsic_pool = Arc::new(
			Components::build_extrinsic_pool(config.extrinsic_pool, client.clone())?
		);
		let extrinsic_pool_adapter = ExtrinsicPoolAdapter::<Components> {
			imports_external_transactions: !config.roles == Roles::LIGHT,
			pool: extrinsic_pool.clone(),
			client: client.clone(),
		 };

		let network_params = network::Params {
			config: network::ProtocolConfig {
				roles: config.roles,
			},
			network_config: config.network,
			chain: client.clone(),
			on_demand: on_demand.clone()
				.map(|d| d as Arc<network::OnDemandService<ComponentBlock<Components>>>),
			transaction_pool: Arc::new(extrinsic_pool_adapter),
			specialization: network_protocol,
		};

		let network = network::Service::new(network_params, Components::Factory::NETWORK_PROTOCOL_ID)?;
		on_demand.map(|on_demand| on_demand.set_service_link(Arc::downgrade(&network)));

		{
			// block notifications
			let network = network.clone();
			let txpool = extrinsic_pool.clone();

			let events = client.import_notification_stream()
				.for_each(move |notification| {
					network.on_block_imported(notification.hash, &notification.header);
					txpool.cull(&BlockId::hash(notification.hash))
						.map_err(|e| warn!("Error removing extrinsics: {:?}", e))?;
					Ok(())
				})
				.select(exit.clone())
				.then(|_| Ok(()));
			task_executor.spawn(events);
		}

		{
			// extrinsic notifications
			let network = network.clone();
			let events = extrinsic_pool.import_notification_stream()
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
				let state = rpc::apis::state::State::new(client.clone(), task_executor.clone());
				let author = rpc::apis::author::Author::new(client.clone(), extrinsic_pool.clone(), task_executor.clone());
				rpc::rpc_handler::<ComponentBlock<Components>, ComponentExHash<Components>, _, _, _, _, _>(
					state,
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
				let is_authority = config.roles == Roles::AUTHORITY;
				let pubkey = format!("{}", public_key);
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
							"pubkey" => &pubkey,
							"authority" => is_authority
						);
					}),
				}))
			},
			None => None,
		};

		Ok(Service {
			client: client,
			network: Some(network),
			extrinsic_pool: extrinsic_pool,
			signal: Some(signal),
			keystore: keystore,
			exit,
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
		self.network.as_ref().expect("self.network always Some").clone()
	}

	/// Get shared extrinsic pool instance.
	pub fn extrinsic_pool(&self) -> Arc<ExtrinsicPool<Components::ExtrinsicPoolApi>> {
		self.extrinsic_pool.clone()
	}

	/// Get shared keystore.
	pub fn keystore(&self) -> &Keystore {
		&self.keystore
	}

	/// Get a handle to a future that will resolve on exit.
	pub fn on_exit(&self) -> ::exit_future::Exit {
		self.exit.clone()
	}
}

impl<Components> Drop for Service<Components> where Components: components::Components {
	fn drop(&mut self) {
		debug!(target: "service", "Substrate service shutdown");

		drop(self.network.take());

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

/// Transaction pool adapter.
pub struct ExtrinsicPoolAdapter<C: Components> {
	imports_external_transactions: bool,
	pool: Arc<ExtrinsicPool<C::ExtrinsicPoolApi>>,
	client: Arc<ComponentClient<C>>,
}

impl<C: Components> ExtrinsicPoolAdapter<C> {
	fn best_block_id(&self) -> Option<BlockId<ComponentBlock<C>>> {
		self.client.info()
			.map(|info| BlockId::hash(info.chain.best_hash))
			.map_err(|e| {
				debug!("Error getting best block: {:?}", e);
			})
			.ok()
	}
}

impl<C: Components> network::TransactionPool<ComponentExHash<C>, ComponentBlock<C>> for ExtrinsicPoolAdapter<C> {
	fn transactions(&self) -> Vec<(ComponentExHash<C>, ComponentExtrinsic<C>)> {
		let best_block_id = match self.best_block_id() {
			Some(id) => id,
			None => return vec![],
		};
		self.pool.cull_and_get_pending(&best_block_id, |pending| pending
			.map(|t| {
				let hash = t.hash().clone();
				let ex: ComponentExtrinsic<C> = t.original.clone();
				(hash, ex)
			})
			.collect()
		).unwrap_or_else(|e| {
			warn!("Error retrieving pending set: {}", e);
			vec![]
		})
	}

	fn import(&self, transaction: &ComponentExtrinsic<C>) -> Option<ComponentExHash<C>> {
		if !self.imports_external_transactions {
			return None;
		}

		let encoded = transaction.encode();
		if let Some(uxt) = Decode::decode(&mut &encoded[..]) {
			let best_block_id = self.best_block_id()?;
			match self.pool.submit_one(&best_block_id, uxt) {
				Ok(xt) => Some(*xt.hash()),
				Err(e) => match e.into_pool_error() {
					Ok(e) => match e.kind() {
						extrinsic_pool::ErrorKind::AlreadyImported(hash) =>
							Some(::std::str::FromStr::from_str(&hash).map_err(|_| {})
								.expect("Hash string is always valid")),
						_ => {
							debug!("Error adding transaction to the pool: {:?}", e);
							None
						},
					},
					Err(e) => {
						debug!("Error converting pool error: {:?}", e);
						None
					}
				}
			}
		} else {
			debug!("Error decoding transaction");
			None
		}
	}

	fn on_broadcasted(&self, propagations: HashMap<ComponentExHash<C>, Vec<String>>) {
		self.pool.on_broadcasted(propagations)
	}
}
