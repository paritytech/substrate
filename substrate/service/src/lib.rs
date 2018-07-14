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
use runtime_primitives::traits::{Header, As};
use exit_future::Signal;
use tokio::runtime::TaskExecutor;

pub use self::error::{ErrorKind, Error};
pub use config::{Configuration, Role, PruningMode};
pub use chain_spec::ChainSpec;
pub use extrinsic_pool::txpool::{Options as ExtrinsicPoolOptions};
pub use extrinsic_pool::api::{ExtrinsicPool as ExtrinsicPoolApi};

pub use components::{ServiceFactory, FullBackend, FullExecutor, LightBackend,
	LightExecutor, ExtrinsicPool, Components, PoolApi, ComponentClient,
	ComponentBlock, FullClient, LightClient, FullComponents, LightComponents,
	CodeExecutor, NetworkService, FactoryChainSpec, FactoryBlock, RuntimeGenesis,
};

/// Substrate service.
pub struct Service<Components: components::Components> {
	client: Arc<ComponentClient<Components>>,
	network: Arc<components::NetworkService<Components::Factory>>,
	extrinsic_pool: Arc<Components::ExtrinsicPool>,
	keystore: Keystore,
	signal: Option<Signal>,
}

/// Creates bare client without any networking.
pub fn new_client<Factory: components::ServiceFactory>(config: Configuration<Factory::Genesis>)
	-> Result<Arc<ComponentClient<components::FullComponents<Factory>>>, error::Error>
{
	let executor = components::CodeExecutor::<Factory>::default();
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
		config: Configuration<<Components::Factory as ServiceFactory>::Genesis>,
		task_executor: TaskExecutor
	)
		-> Result<Self, error::Error>
	{
		let (signal, exit) = ::exit_future::signal();

		// Create client
		let executor = components::CodeExecutor::<Components::Factory>::default();

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

		info!("Best block: #{}", best_header.number());
		telemetry!("node.start"; "height" => best_header.number().as_(), "best" => ?best_header.hash());

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

		Ok(Service {
			client: client,
			network: network,
			extrinsic_pool: extrinsic_pool,
			signal: Some(signal),
			keystore: keystore,
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
