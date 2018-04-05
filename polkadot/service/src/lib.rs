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
extern crate substrate_primitives as primitives;
extern crate substrate_network as network;
extern crate substrate_codec as codec;
extern crate substrate_executor;

extern crate tokio_core;
extern crate substrate_keyring;
extern crate substrate_client as client;

#[macro_use]
extern crate error_chain;
#[macro_use]
extern crate log;

mod error;
mod config;

use std::sync::Arc;
use std::thread;
use futures::prelude::*;
use parking_lot::Mutex;
use tokio_core::reactor::Core;
use codec::Slicable;
use primitives::block::{Id as BlockId, TransactionHash};
use transaction_pool::TransactionPool;
use substrate_keyring::Keyring;
use substrate_executor::NativeExecutor;
use polkadot_executor::Executor as LocalDispatch;
use keystore::Store as Keystore;
use polkadot_api::PolkadotApi;
use polkadot_runtime::genesismap::{additional_storage_with_genesis, GenesisConfig};
use client::{genesis, BlockchainEvents};
use client::in_mem::Backend as InMemory;
use network::ManageNetwork;

pub use self::error::{ErrorKind, Error};
pub use config::{Configuration, Role};

type Client = client::Client<InMemory, NativeExecutor<LocalDispatch>>;


/// Polkadot service.
pub struct Service {
	thread: Option<thread::JoinHandle<()>>,
	client: Arc<Client>,
	network: Arc<network::Service>,
	transaction_pool: Arc<Mutex<TransactionPool>>,
	_consensus: Option<consensus::Service>,
}

struct TransactionPoolAdapter {
	pool: Arc<Mutex<TransactionPool>>,
	client: Arc<Client>,
}

impl network::TransactionPool for TransactionPoolAdapter {
	fn transactions(&self) -> Vec<(TransactionHash, Vec<u8>)> {
		let best_block = match self.client.info() {
			Ok(info) => info.chain.best_hash,
			Err(e) => {
				debug!("Error getting best block: {:?}", e);
				return Vec::new();
			}
		};
		let id = self.client.check_id(BlockId::Hash(best_block)).expect("Best block is always valid; qed.");
		let ready = transaction_pool::Ready::create(id, &*self.client);
		self.pool.lock().pending(ready).map(|t| {
			let hash = ::primitives::Hash::from(&t.hash()[..]);
			let tx = codec::Slicable::encode(t.as_transaction());
			(hash, tx)
		}).collect()
	}

	fn import(&self, transaction: &[u8]) -> Option<TransactionHash> {
		if let Some(tx) = codec::Slicable::decode(&mut &transaction[..]) {
			match self.pool.lock().import(tx) {
				Ok(t) => Some(t.hash()[..].into()),
				Err(e) => match *e.kind() {
					transaction_pool::ErrorKind::AlreadyImported(hash) => Some(hash[..].into()),
					_ => {
						debug!("Error adding transaction to the pool: {:?}", e);
						None
					},
				}
			}
		} else {
			debug!("Error decoding transaction");
			None
		}
	}
}

impl Service {
	/// Creates and register protocol with the network service
	pub fn new(config: Configuration) -> Result<Service, error::Error> {
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

		let genesis_config = GenesisConfig {
			validators: vec![Keyring::Alice.into(), Keyring::Bob.into(), Keyring::Charlie.into()],
			authorities: vec![Keyring::Alice.into(), Keyring::Bob.into(), Keyring::Charlie.into()],
			balances: vec![
				(Keyring::One.into(), 1u64 << 63),
				(Keyring::Two.into(), 1u64 << 63),
				(Keyring::Alice.into(), 1u64 << 63),
				(Keyring::Bob.into(), 1u64 << 63),
				(Keyring::Charlie.into(), 1u64 << 63),
			].into_iter().collect(),
			block_time: 5,			// 5 second block time.
			session_length: 720,	// that's 1 hour per session.
			sessions_per_era: 24,	// 24 hours per era.
			bonding_duration: 90,	// 90 days per bond.
			approval_ratio: 667,	// 66.7% approvals required for legislation.
		};
		let prepare_genesis = || {
			storage = genesis_config.genesis_map();
			let block = genesis::construct_genesis_block(&storage);
			storage.extend(additional_storage_with_genesis(&block));
			(primitives::block::Header::decode(&mut block.header.encode().as_ref()).expect("to_vec() always gives a valid serialisation; qed"), storage.into_iter().collect())
		};

		let client = Arc::new(client::new_in_mem(executor, prepare_genesis)?);
		let best_header = client.header(&BlockId::Hash(client.info()?.chain.best_hash))?.expect("Best header always exists; qed");
		info!("Starting Polkadot. Best block is #{}", best_header.number);
		let transaction_pool = Arc::new(Mutex::new(TransactionPool::new(config.transaction_pool)));
		let transaction_pool_adapter = Arc::new(TransactionPoolAdapter {
			pool: transaction_pool.clone(),
			client: client.clone(),
		});
		let network_params = network::Params {
			config: network::ProtocolConfig {
				roles: config.roles,
			},
			network_config: config.network,
			chain: client.clone(),
			transaction_pool: transaction_pool_adapter,
		};
		let network = network::Service::new(network_params)?;

		// Spin consensus service if configured
		let consensus_service = if config.roles & Role::VALIDATOR == Role::VALIDATOR {
			// Load the first available key. Code above makes sure it exisis.
			let key = keystore.load(&keystore.contents()?[0], "")?;
			info!("Using authority key {:?}", key.public());
			Some(consensus::Service::new(client.clone(), network.clone(), transaction_pool.clone(), key, &best_header))
		} else {
			None
		};

		let thread_client = client.clone();
		let thread_network = network.clone();
		let thread = thread::spawn(move || {
			thread_network.start_network();
			let mut core = Core::new().expect("tokio::Core could not be created");
			let events = thread_client.import_notification_stream().for_each(|notification| {
				thread_network.on_block_imported(&notification.header);
				Ok(())
			});
			if let Err(e) = core.run(events) {
				debug!("Polkadot service event loop shutdown with {:?}", e);
			}
			debug!("Polkadot service shutdown");
		});
		Ok(Service {
			thread: Some(thread),
			client: client,
			network: network,
			transaction_pool: transaction_pool,
			_consensus: consensus_service,
		})
	}

	/// Get shared client instance.
	pub fn client(&self) -> Arc<Client> {
		self.client.clone()
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
		self.client.stop_notifications();
		self.network.stop_network();
		if let Some(thread) = self.thread.take() {
			thread.join().expect("The service thread has panicked");
		}
	}
}

