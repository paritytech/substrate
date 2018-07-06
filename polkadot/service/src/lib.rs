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

//! Polkadot service. Starts a thread that spins the network, the client and the transaction pool.
//! Manages communication between them.

extern crate futures;
extern crate ed25519;
extern crate clap;
extern crate exit_future;
extern crate serde;
extern crate serde_json;
extern crate polkadot_primitives;
extern crate polkadot_runtime;
extern crate polkadot_executor;
extern crate polkadot_api;
extern crate polkadot_consensus as consensus;
extern crate polkadot_transaction_pool as transaction_pool;
extern crate polkadot_network;
extern crate substrate_keystore as keystore;
extern crate substrate_primitives as primitives;
extern crate substrate_runtime_primitives as runtime_primitives;
extern crate substrate_network as network;
extern crate substrate_codec as codec;
extern crate substrate_executor;
extern crate substrate_state_machine as state_machine;
extern crate substrate_client as client;
extern crate substrate_client_db as client_db;
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
#[macro_use]
extern crate hex_literal;

mod components;
mod error;
mod config;
mod chain_spec;

use std::sync::Arc;
use futures::prelude::*;
use transaction_pool::TransactionPool;
use keystore::Store as Keystore;
use polkadot_api::PolkadotApi;
use polkadot_primitives::{Block, BlockId, Hash};
use client::{Client, BlockchainEvents};
use network::ManageNetwork;
use exit_future::Signal;
use polkadot_network::{NetworkService, PolkadotProtocol};
use tokio::runtime::TaskExecutor;

pub use self::error::{ErrorKind, Error};
pub use self::components::{Components, FullComponents, LightComponents};
pub use config::{Configuration, Role, PruningMode};
pub use chain_spec::ChainSpec;

/// Polkadot service.
pub struct Service<Components: components::Components> {
	client: Arc<Client<Components::Backend, Components::Executor, Block>>,
	network: Arc<NetworkService>,
	transaction_pool: Arc<TransactionPool<Components::Api>>,
	signal: Option<Signal>,
	_consensus: Option<consensus::Service>,
}

/// Creates light client and register protocol with the network service
pub fn new_light(config: Configuration, executor: TaskExecutor) -> Result<Service<components::LightComponents>, error::Error> {
	Service::new(components::LightComponents, config, executor)
}

/// Creates full client and register protocol with the network service
pub fn new_full(config: Configuration, executor: TaskExecutor) -> Result<Service<components::FullComponents>, error::Error> {
	let is_validator = (config.roles & Role::AUTHORITY) == Role::AUTHORITY;
	Service::new(components::FullComponents { is_validator }, config, executor)
}

/// Creates bare client without any networking.
pub fn new_client(config: Configuration) -> Result<Arc<Client<
		<components::FullComponents as Components>::Backend,
		<components::FullComponents as Components>::Executor,
		Block>>,
	error::Error>
{
	let db_settings = client_db::DatabaseSettings {
		cache_size: None,
		path: config.database_path.into(),
		pruning: config.pruning,
	};
	let executor = polkadot_executor::Executor::new();
	let is_validator = (config.roles & Role::AUTHORITY) == Role::AUTHORITY;
	let components = components::FullComponents { is_validator };
	let (client, _) = components.build_client(db_settings, executor, &config.chain_spec)?;
	Ok(client)
}

impl<Components> Service<Components>
	where
		Components: components::Components,
		client::error::Error: From<<<<Components as components::Components>::Backend as client::backend::Backend<Block>>::State as state_machine::Backend>::Error>,
{
	/// Creates and register protocol with the network service
	fn new(components: Components, config: Configuration, task_executor: TaskExecutor) -> Result<Self, error::Error> {
		let (signal, exit) = ::exit_future::signal();

		// Create client
		let executor = polkadot_executor::Executor::new();

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

		let (client, on_demand) = components.build_client(db_settings, executor, &config.chain_spec)?;
		let api = components.build_api(client.clone());
		let best_header = client.best_block_header()?;

		info!("Best block: #{}", best_header.number);
		telemetry!("node.start"; "height" => best_header.number, "best" => ?best_header.hash());

		let transaction_pool = Arc::new(TransactionPool::new(config.transaction_pool, api.clone()));
		let transaction_pool_adapter = components.build_network_tx_pool(client.clone(), transaction_pool.clone());
		let network_params = network::Params {
			config: network::ProtocolConfig {
				roles: config.roles,
			},
			network_config: config.network,
			chain: client.clone(),
			on_demand: on_demand.clone().map(|d| d as Arc<network::OnDemandService<Block>>),
			transaction_pool: transaction_pool_adapter,
			specialization: PolkadotProtocol::new(),
		};

		let network = network::Service::new(network_params, ::polkadot_network::DOT_PROTOCOL_ID)?;
		on_demand.map(|on_demand| on_demand.set_service_link(Arc::downgrade(&network)));

		network.start_network();

		{
			// block notifications
			let network = network.clone();
			let txpool = transaction_pool.clone();

			let events = client.import_notification_stream()
				.for_each(move |notification| {
					network.on_block_imported(notification.hash, &notification.header);
					prune_imported(&*txpool, notification.hash);
					Ok(())
				})
				.select(exit.clone())
				.then(|_| Ok(()));
			task_executor.spawn(events);
		}

		{
			// transaction notifications
			let network = network.clone();
			let events = transaction_pool.import_notification_stream()
				// TODO [ToDr] Consider throttling?
				.for_each(move |_| {
					network.trigger_repropagate();
					Ok(())
				})
				.select(exit.clone())
				.then(|_| Ok(()));

			task_executor.spawn(events);
		}

		// Spin consensus service if configured
		let consensus_service = components.build_consensus(
			client.clone(),
			network.clone(),
			transaction_pool.clone(),
			&keystore,
			task_executor,
		)?;

		Ok(Service {
			client: client,
			network: network,
			transaction_pool: transaction_pool,
			signal: Some(signal),
			_consensus: consensus_service,
		})
	}

	/// Get shared client instance.
	pub fn client(&self) -> Arc<Client<Components::Backend, Components::Executor, Block>> {
		self.client.clone()
	}

	/// Get shared network instance.
	pub fn network(&self) -> Arc<NetworkService> {
		self.network.clone()
	}

	/// Get shared transaction pool instance.
	pub fn transaction_pool(&self) -> Arc<TransactionPool<Components::Api>> {
		self.transaction_pool.clone()
	}
}

/// Produce a task which prunes any finalized transactions from the pool.
pub fn prune_imported<A>(pool: &TransactionPool<A>, hash: Hash)
	where A: PolkadotApi,
{
	let block = BlockId::hash(hash);
	if let Err(e) = pool.cull(block) {
		warn!("Culling error: {:?}", e);
	}

	if let Err(e) = pool.retry_verification(block) {
		warn!("Re-verifying error: {:?}", e);
	}
}

impl<Components> Drop for Service<Components> where Components: components::Components {
	fn drop(&mut self) {
		debug!(target: "service", "Polkadot service shutdown");

		self.network.stop_network();

		if let Some(signal) = self.signal.take() {
			signal.fire();
		}
	}
}
