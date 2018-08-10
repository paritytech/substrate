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
extern crate blitz_primitives;
extern crate blitz_runtime;
extern crate blitz_executor;
extern crate blitz_network;
extern crate blitz_state;
// extern crate polkadot_api;
// extern crate polkadot_consensus as consensus;
// extern crate polkadot_transaction_pool as transaction_pool;
extern crate substrate_client as client;
extern crate substrate_runtime_io as runtime_io;
extern crate substrate_primitives as primitives;
extern crate substrate_network as network;
extern crate substrate_codec as codec;
extern crate substrate_client_db as client_db;
extern crate substrate_executor;
extern crate substrate_keystore as keystore;

extern crate exit_future;
extern crate tokio_core;

#[macro_use]
extern crate error_chain;
#[macro_use]
extern crate log;
#[macro_use]
extern crate hex_literal;

mod error;
mod config;

use blitz_primitives::RoundId;
use std::sync::Arc;
use std::thread;
use futures::prelude::*;
use parking_lot::Mutex;
use tokio_core::reactor::Core;
use codec::Slicable;
use primitives::block::{Id as BlockId, Extrinsic, ExtrinsicHash, HeaderHash};
use primitives::{AuthorityId, hashing};
// use transaction_pool::TransactionPool;
use substrate_executor::NativeExecutor;
use blitz_executor::Executor as LocalDispatch;
use keystore::Store as Keystore;
// use polkadot_api::PolkadotApi;
use blitz_runtime::{GenesisConfig, ConsensusConfig, CouncilConfig, DemocracyConfig,
	SessionConfig, StakingConfig, BuildExternalities};
use client::{genesis, BlockchainEvents};
use network::ManageNetwork;
use blitz_network::NetworkService;
use exit_future::Signal;
use blitz_state::GlobalState;

pub use self::error::{ErrorKind, Error};
pub use config::{Configuration, Role, ChainSpec};

type Client = client::Client<client_db::Backend, NativeExecutor<LocalDispatch>>;

/// Blitz service.
pub struct Service {
	thread: Option<thread::JoinHandle<()>>,
	client: Arc<Client>,
	network: Arc<NetworkService>,
	// transaction_pool: Arc<Mutex<TransactionPool>>,
	signal: Option<Signal>,
	// _consensus: Option<consensus::Service>,
	global_state: GlobalState,
}

impl Service {
	/// Creates and register protocol with the network service
	pub fn new(mut config: Configuration) -> Result<Service, error::Error> {
		use std::sync::Barrier;

		let (signal, exit) = ::exit_future::signal();

		// Create client
		let executor = blitz_executor::Executor::new();
		let mut storage = Default::default();

		let mut keystore = Keystore::open(config.keystore_path.into())?;
		for seed in &config.keys {
			keystore.generate_from_seed(seed)?;
		}

		if keystore.contents()?.is_empty() {
			let key = keystore.generate("")?;
			info!("Generated a new keypair: {:?}", key.public());
		}

		let prepare_genesis = || {
			// storage = genesis_config.build_externalities();
			let block = genesis::construct_genesis_block(&storage);
			(primitives::block::Header::decode(&mut block.header.encode().as_ref()).expect("to_vec() always gives a valid serialisation; qed"), storage.into_iter().collect())
		};

		let db_settings = client_db::DatabaseSettings {
			cache_size: None,
			path: config.database_path.into(),
		};

		let client = Arc::new(client_db::new_client(db_settings, executor, prepare_genesis)?);
		let best_header = client.best_block_header()?;
		info!("Starting Polkadot. Best block is #{}", best_header.number);

		struct DummyPool;

		impl network::TransactionPool for DummyPool {
			fn transactions(&self) -> Vec<(ExtrinsicHash, Vec<u8>)> { Default::default() }
			/// Import a transction into the pool.
			fn import(&self, transaction: &[u8]) -> Option<ExtrinsicHash> { None }
		}
		let transaction_pool = Arc::new(DummyPool);

		let network_params = network::Params {
			config: network::ProtocolConfig {
				roles: config.roles,
			},
			network_config: config.network,
			chain: client.clone(),
			// transaction_pool: transaction_pool_adapter,
			transaction_pool: transaction_pool.clone(),
			specialization: BlitzProtocol::default(),
		};

		let network = network::Service::new(network_params, blitz_network::BLITZ_PROTOCOL_ID)?;
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
				let events = client.import_notification_stream().for_each(move |notification| {
					network.on_block_imported(notification.hash, &notification.header);
					// prune_imported(&*client, &*txpool, notification.hash);

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

		Ok(Service {
			thread: Some(thread),
			client: client,
			network: network,
			// transaction_pool: transaction_pool,
			signal: Some(signal),
			// _consensus: consensus_service,
			global_state: GlobalState::default(),
		})
	}

	/// Get shared client instance.
	pub fn client(&self) -> Arc<Client> {
		self.client.clone()
	}

	/// Get shared network instance.
	pub fn network(&self) -> Arc<NetworkService> {
		self.network.clone()
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
