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
extern crate parking_lot;
extern crate tokio_timer;
extern crate polkadot_primitives;
extern crate polkadot_runtime;
extern crate polkadot_executor;
extern crate polkadot_api;
extern crate polkadot_consensus as consensus;
extern crate polkadot_transaction_pool as transaction_pool;
extern crate polkadot_keystore as keystore;
extern crate substrate_client as client;
extern crate substrate_light as light_client;
extern crate substrate_runtime_io as runtime_io;
extern crate substrate_primitives as primitives;
extern crate substrate_network as network;
extern crate substrate_codec as codec;
extern crate substrate_executor;

extern crate exit_future;
extern crate tokio_core;

#[macro_use]
extern crate error_chain;
#[macro_use]
extern crate log;
#[macro_use]
extern crate hex_literal;

mod error;
mod chain_config;
mod client_adapter;
mod config;

use std::sync::Arc;
use std::thread;
use futures::prelude::*;
use parking_lot::Mutex;
use tokio_core::reactor::Core;
use codec::Slicable;
use transaction_pool::TransactionPool;
use keystore::Store as Keystore;
use polkadot_runtime::BuildExternalities;
use client_adapter::Client;
use client::{genesis, BlockchainEvents, ChainHead, ChainData, StateData, ContractCaller};
use network::ManageNetwork;
use exit_future::Signal;

pub use self::error::{ErrorKind, Error};
pub use chain_config::ChainConfig;
pub use config::{Configuration, Role, ChainSpec};

/// Polkadot service.
pub struct Service {
	thread: Option<thread::JoinHandle<()>>,
	client: Client,
	network: Arc<network::Service>,
	transaction_pool: Arc<Mutex<TransactionPool>>,
	signal: Option<Signal>,
	_consensus: Option<consensus::Service>,
}

impl Service {
	/// Creates and register protocol with the network service
	pub fn new(mut config: Configuration) -> Result<Service, error::Error> {
		use std::sync::Barrier;

		let (signal, exit) = ::exit_future::signal();

		// Create client
		let executor = polkadot_executor::Executor::new();
		let mut storage = Default::default();

		let mut keystore = Keystore::open(config.keystore_path.into())?;
		for seed in &config.keys {
			keystore.generate_from_seed(seed)?;
		}

		if keystore.contents()?.is_empty() {
			let key = keystore.generate("")?;
			info!("Generated a new keypair: {:?}", key.public());
		}

		let ChainConfig { genesis_config, boot_nodes } = match config.chain_spec {
			ChainSpec::Development => chain_config::local_testnet_config(),
			ChainSpec::PoC1Testnet => chain_config::poc_1_testnet_config(),
		};
		config.network.boot_nodes.extend(boot_nodes);

		let prepare_genesis = || {
			storage = genesis_config.build_externalities();
			let block = genesis::construct_genesis_block(&storage);
			(primitives::block::Header::decode(&mut block.header.encode().as_ref()).expect("to_vec() always gives a valid serialisation; qed"), storage.into_iter().collect())
		};

		let client = if config.roles & Role::LIGHT == Role::LIGHT {
			Client::Light(Arc::new(light_client::new_in_mem()?))
		} else {
			Client::Full(Arc::new(client::new_in_mem(executor, prepare_genesis)?))
		};
		let best_header = client.chain_head().best_block_header()?;
		info!("Starting Polkadot. Best block is #{}", best_header.number);
		let transaction_pool = Arc::new(Mutex::new(TransactionPool::new(config.transaction_pool)));
		let transaction_pool_adapter = client.create_transaction_pool_adapter(transaction_pool.clone());

		let network_params = network::Params {
			config: network::ProtocolConfig {
				roles: config.roles,
			},
			network_config: config.network,
			transaction_pool: transaction_pool_adapter,
		};
		let (network, network_consensus) = client.create_network_service(network_params)?;

		let barrier = ::std::sync::Arc::new(Barrier::new(2));

		let thread = {
			let client = client.clone();
			let network = network.clone();
			let txpool = transaction_pool.clone();

			let thread_barrier = barrier.clone();
			thread::spawn(move || {
				network.start_network();

				thread_barrier.wait();
				let mut core = Core::new().expect("tokio::Core could not be created");
				let events = client.chain_events().import_notification_stream().for_each(move |notification| {
					network.on_block_imported(notification.hash, &notification.header);
					client.prune_imported(&*txpool, notification.hash);

					Ok(())
				});

				core.handle().spawn(events);
				if let Err(e) = core.run(exit) {
					debug!("Polkadot service event loop shutdown with {:?}", e);
				}
				debug!("Polkadot service shutdown");
			})
		};

		// wait for the network to start up before starting the consensus
		// service.
		barrier.wait();

		// Spin consensus service if configured
		let consensus_service = match (client.clone(), network_consensus) {
			(Client::Full(ref client), Some(ref network_consensus)) if config.roles & Role::VALIDATOR == Role::VALIDATOR => {
				// Load the first available key. Code above makes sure it exisis.
				let key = keystore.load(&keystore.contents()?[0], "")?;
				info!("Using authority key {:?}", key.public());
				Some(consensus::Service::new(client.clone(), network_consensus.clone(), transaction_pool.clone(), key))
			},
			_ => None,
		};

		Ok(Service {
			thread: Some(thread),
			client: client,
			network: network,
			transaction_pool: transaction_pool,
			signal: Some(signal),
			_consensus: consensus_service,
		})
	}

	/// Get shared blockchain events instance.
	pub fn chain_events(&self) -> Arc<BlockchainEvents> {
		self.client.chain_events()
	}

	/// Get shared chain head instance.
	pub fn chain_head(&self) -> Arc<ChainHead> {
		self.client.chain_head()
	}

	/// Get shared chain data instance.
	pub fn chain_data(&self) -> Arc<ChainData> {
		self.client.chain_data()
	}

	/// Get shared state data instance.
	pub fn state_data(&self) -> Arc<StateData> {
		self.client.state_data()
	}

	/// Get shared contract caller instance.
	pub fn contract_caller(&self) -> Arc<ContractCaller> {
		self.client.contract_caller()
	}

	/// Get shared network instance.
	pub fn network(&self) -> Arc<network::Service> {
		self.network.clone()
	}

	/// Get shared transaction pool instance.
	pub fn transaction_pool(&self) -> Arc<Mutex<TransactionPool>> {
		self.transaction_pool.clone()
	}
}

impl Drop for Service {
	fn drop(&mut self) {
		self.network.stop_network();

		if let Some(signal) = self.signal.take() {
			signal.fire();
		}

		if let Some(thread) = self.thread.take() {
			thread.join().expect("The service thread has panicked");
		}
	}
}
