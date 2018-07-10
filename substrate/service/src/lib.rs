// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! Substrate service. Starts a thread that spins the network, the client and the extrinsic pool.
//! Manages communication between them.

extern crate futures;
extern crate ed25519;
extern crate clap;
extern crate exit_future;
extern crate serde;
extern crate serde_json;
extern crate substrate_keystore as keystore;
extern crate substrate_primitives as primitives;
extern crate substrate_runtime_primitives as runtime_primitives;
extern crate substrate_network as network;
extern crate substrate_codec as codec;
extern crate substrate_executor;
extern crate substrate_state_machine as state_machine;
extern crate substrate_client as client;
extern crate substrate_client_db as client_db;
extern crate substrate_extrinsic_pool as extrinsic_pool;
extern crate tokio;

#[macro_use]
extern crate substrate_telemetry;
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

use std::sync::Arc;
use futures::prelude::*;
use keystore::Store as Keystore;
use client::BlockchainEvents;
use network::ManageNetwork;
use runtime_primitives::BuildStorage;
use runtime_primitives::traits::{Header, As};
use exit_future::Signal;
use tokio::runtime::TaskExecutor;
use serde::{Serialize, de::DeserializeOwned};

pub use self::error::{ErrorKind, Error};
pub use config::{Configuration, Role, PruningMode};
pub use chain_spec::ChainSpec;

use self::components::{Components, ServiceFactory, SharedPool, ComponentClient, ComponentBlock, ExtrinsicPool};

pub trait RuntimeGenesis: Serialize + DeserializeOwned + BuildStorage {}
impl<T: Serialize + DeserializeOwned + BuildStorage> RuntimeGenesis for T {}

/// Substrate service.
pub struct Service<Components: components::Components> {
	client: Arc<ComponentClient<Components>>,
	network: Arc<components::NetworkService<Components::Factory>>,
	extrinsic_pool: <Components::Factory as ServiceFactory>::ExtrinsicPool,
	signal: Option<Signal>,
}

/// Creates light client and register protocol with the network service
pub fn new_light<Factory: components::ServiceFactory>(
	config: Configuration<Factory::Genesis>,
	executor: TaskExecutor
	) -> Result<Service<components::LightComponents<Factory>>, error::Error>
{
	Service::<components::LightComponents<Factory>>::new(config, executor)
}

/// Creates full client and register protocol with the network service
pub fn new_full<Factory: components::ServiceFactory>(
	config: Configuration<Factory::Genesis>,
	executor: TaskExecutor
	) -> Result<Service<components::FullComponents<Factory>>, error::Error>
{
	Service::<components::FullComponents<Factory>>::new(config, executor)
}

/// Creates bare client without any networking.
pub fn new_client<Factory: components::ServiceFactory>(config: Configuration<Factory::Genesis>)
	-> Result<Arc<ComponentClient<components::FullComponents<Factory>>>, error::Error>
{
	let db_settings = client_db::DatabaseSettings {
		cache_size: None,
		path: config.database_path.into(),
		pruning: config.pruning,
	};
	let executor = components::CodeExecutor::<Factory>::default();
	let (client, _) = components::FullComponents::<Factory>::build_client(db_settings, executor, &config.chain_spec)?;
	Ok(client)
}

impl<Components> Service<Components>
	where
		Components: components::Components,
		client::error::Error: From<<<<Components as components::Components>::Backend as client::backend::Backend<<<Components as components::Components>::Factory as components::ServiceFactory>::Block>>::State as state_machine::Backend>::Error>
{
	/// Creates and register protocol with the network service
	fn new(config: Configuration<<Components::Factory as ServiceFactory>::Genesis>, task_executor: TaskExecutor) -> Result<Self, error::Error> {
		let (signal, exit) = ::exit_future::signal();

		// Create client
		let executor = components::CodeExecutor::<Components::Factory>::default();

		let mut keystore = Keystore::open(config.keystore_path.into())?;
		for seed in &config.keys {
			keystore.generate_from_seed(seed)?;
		}

		if keystore.contents()?.is_empty() {
			let key = keystore.generate("")?;
			info!("Generated a new keypair: {:?}", key.public());
		}

		let db_settings = client_db::DatabaseSettings {
			cache_size: None,
			path: config.database_path.into(),
			pruning: config.pruning,
		};

		let (client, on_demand) = Components::build_client(db_settings, executor, &config.chain_spec)?;
		let best_header = client.best_block_header()?;

		info!("Best block: #{}", best_header.number());
		telemetry!("node.start"; "height" => best_header.number().as_(), "best" => ?best_header.hash());

		let extrinsic_pool = Components::build_extrinsic_pool(&config.extrinsic_pool, client.clone())?;
		let extrinsic_pool_adapter = extrinsic_pool.as_network_pool();
		let network_params = network::Params {
			config: network::ProtocolConfig {
				roles: config.roles,
			},
			network_config: config.network,
			chain: client.clone(),
			on_demand: on_demand.clone().map(|d| d as Arc<network::OnDemandService<ComponentBlock<Components>>>),
			transaction_pool: extrinsic_pool_adapter,
			specialization: <Components::Factory as ServiceFactory>::NetworkProtocol::default(),
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

		Ok(Service {
			client: client,
			network: network,
			extrinsic_pool: extrinsic_pool,
			signal: Some(signal),
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
	pub fn extrinsic_pool(&self) -> Arc<SharedPool<Components::Factory>> {
		self.extrinsic_pool.as_pool()
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
