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
extern crate tokio_timer;
extern crate polkadot_primitives;
extern crate polkadot_runtime;
extern crate polkadot_executor;
extern crate polkadot_api;
extern crate polkadot_consensus as consensus;
extern crate polkadot_transaction_pool as transaction_pool;
extern crate polkadot_keystore as keystore;
extern crate substrate_runtime_io as runtime_io;
extern crate substrate_primitives as primitives;
extern crate substrate_runtime_primitives as runtime_primitives;
extern crate substrate_network as network;
extern crate substrate_codec as codec;
extern crate substrate_executor;
extern crate substrate_state_machine as state_machine;

extern crate tokio_core;
extern crate substrate_client as client;
extern crate substrate_client_db as client_db;

#[macro_use]
extern crate polkadot_telemetry;
#[macro_use]
extern crate error_chain;
#[macro_use]
extern crate slog;	// needed until we can reexport `slog_info` from `polkadot_telemetry`
#[macro_use]
extern crate log;

mod error;
mod config;

use runtime_primitives::MakeStorage;
use std::collections::HashMap;
use std::sync::Arc;
use std::thread;
use futures::prelude::*;
use tokio_core::reactor::Core;
use codec::Slicable;
use transaction_pool::TransactionPool;
use substrate_executor::NativeExecutor;
use polkadot_executor::Executor as LocalDispatch;
use keystore::Store as Keystore;
use polkadot_api::PolkadotApi;
use polkadot_primitives::{Block, BlockId, Hash};
use client::backend::Backend;
use client::{Client, BlockchainEvents, CallExecutor};
use network::ManageNetwork;
use exit_future::Signal;

pub use self::error::{ErrorKind, Error};
pub use config::{Configuration, Role};

type CodeExecutor = NativeExecutor<LocalDispatch>;

/// Polkadot service.
pub struct Service<B, E> {
	thread: Option<thread::JoinHandle<()>>,
	client: Arc<Client<B, E, Block>>,
	network: Arc<network::Service<Block>>,
	transaction_pool: Arc<TransactionPool>,
	signal: Option<Signal>,
	_consensus: Option<consensus::Service>,
}

struct TransactionPoolAdapter<B, E, A> where A: Send + Sync, E: Send + Sync {
	pool: Arc<TransactionPool>,
	client: Arc<Client<B, E, Block>>,
	api: Arc<A>,
}

impl<B, E, A> network::TransactionPool<Block> for TransactionPoolAdapter<B, E, A>
	where
		B: Backend<Block> + Send + Sync,
		E: client::CallExecutor<Block> + Send + Sync,
		client::error::Error: From<<<B as Backend<Block>>::State as state_machine::backend::Backend>::Error>,
		A: PolkadotApi + Send + Sync,
{
	fn transactions(&self) -> Vec<(Hash, Vec<u8>)> {
		let best_block = match self.client.info() {
			Ok(info) => info.chain.best_hash,
			Err(e) => {
				debug!("Error getting best block: {:?}", e);
				return Vec::new();
			}
		};

		let id = match self.api.check_id(BlockId::hash(best_block)) {
			Ok(id) => id,
			Err(_) => return Vec::new(),
		};

		let ready = transaction_pool::Ready::create(id, &*self.api);

		self.pool.cull_and_get_pending(ready, |pending| pending
			.map(|t| {
				let hash = t.hash().clone();
				(hash, t.primitive_extrinsic())
			})
			.collect()
		)
	}

	fn import(&self, transaction: &Vec<u8>) -> Option<Hash> {
		let encoded = transaction.encode();
		if let Some(uxt) = codec::Slicable::decode(&mut &encoded[..]) {
			match self.pool.import_unchecked_extrinsic(uxt) {
				Ok(xt) => Some(*xt.hash()),
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

	fn on_broadcasted(&self, propagations: HashMap<Hash, Vec<String>>) {
		self.pool.on_broadcasted(propagations)
	}
}

/// Creates light client and register protocol with the network service
pub fn new_light(config: Configuration)
	-> Result<
		Service<
			client::light::Backend<Block>,
			client::RemoteCallExecutor<client::light::Backend<Block>, network::OnDemand<Block, network::Service<Block>>>
		>,
		error::Error,
	> {
	Service::new(
		move |_, executor, genesis_storage: MakeStorage| {
			let client_backend = client::light::new_light_backend();
			let fetch_checker = Arc::new(client::light::new_fetch_checker(client_backend.clone(), executor));
			let fetcher = Arc::new(network::OnDemand::new(fetch_checker));
			let client = client::light::new_light(client_backend, fetcher.clone(), genesis_storage)?;
			Ok((Arc::new(client), Some(fetcher)))
		},
		|client| Arc::new(polkadot_api::light::RemotePolkadotApiWrapper(client.clone())),
		|_client, _network, _tx_pool, _keystore| Ok(None),
		config
	)
}

/// Creates full client and register protocol with the network service
pub fn new_full(config: Configuration) -> Result<Service<client_db::Backend<Block>, client::LocalCallExecutor<client_db::Backend<Block>, CodeExecutor>>, error::Error> {
	let is_validator = (config.roles & Role::VALIDATOR) == Role::VALIDATOR;
	Service::new(|db_settings, executor, genesis_storage: MakeStorage|
		Ok((Arc::new(client_db::new_client(db_settings, executor, genesis_storage)?), None)),
		|client| client,
		|client, network, tx_pool, keystore| {
			if !is_validator {
				return Ok(None);
			}

			// Load the first available key. Code above makes sure it exisis.
			let key = keystore.load(&keystore.contents()?[0], "")?;
			info!("Using authority key {:?}", key.public());
			Ok(Some(consensus::Service::new(
				client.clone(),
				client.clone(),
				network.clone(),
				tx_pool.clone(),
				::std::time::Duration::from_millis(4000), // TODO: dynamic
				key,
			)))
		},
		config)
}

impl<B, E> Service<B, E>
	where
		B: Backend<Block> + Send + Sync + 'static,
		E: CallExecutor<Block> + Send + Sync + 'static,
		client::error::Error: From<<<B as Backend<Block>>::State as state_machine::backend::Backend>::Error>
{
	/// Creates and register protocol with the network service
	fn new<F, G, C, A>(client_creator: F, api_creator: G, consensus_creator: C, config: Configuration) -> Result<Self, error::Error>
		where
			F: FnOnce(
					client_db::DatabaseSettings,
					CodeExecutor,
					MakeStorage,
				) -> Result<(Arc<Client<B, E, Block>>, Option<Arc<network::OnDemand<Block, network::Service<Block>>>>), error::Error>,
			G: Fn(
					Arc<Client<B, E, Block>>,
				) -> Arc<A>,
			C: Fn(
					Arc<Client<B, E, Block>>,
					Arc<network::Service<Block>>,
					Arc<TransactionPool>,
					&Keystore
				) -> Result<Option<consensus::Service>, error::Error>,
			A: PolkadotApi + Send + Sync + 'static,
	{
		use std::sync::Barrier;

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
		};

		let (client, on_demand) = client_creator(db_settings, executor, config.genesis_storage)?;
		let api = api_creator(client.clone());
		let best_header = client.best_block_header()?;
		info!("Best block is #{}", best_header.number);
		telemetry!("node.start"; "height" => best_header.number, "best" => ?best_header.hash());
		let transaction_pool = Arc::new(TransactionPool::new(config.transaction_pool));
		let transaction_pool_adapter = Arc::new(TransactionPoolAdapter {
			pool: transaction_pool.clone(),
			client: client.clone(),
			api: api.clone(),
		});
		let network_params = network::Params {
			config: network::ProtocolConfig {
				roles: config.roles,
			},
			network_config: config.network,
			chain: client.clone(),
			on_demand: on_demand.clone().map(|d| d as Arc<network::OnDemandService>),
			transaction_pool: transaction_pool_adapter,
		};
		let network = network::Service::new(network_params)?;
		let barrier = ::std::sync::Arc::new(Barrier::new(2));
		on_demand.map(|on_demand| on_demand.set_service_link(Arc::downgrade(&network)));

		let thread = {
			let client = client.clone();
			let network = network.clone();
			let txpool = transaction_pool.clone();

			let thread_barrier = barrier.clone();
			thread::spawn(move || {
				network.start_network();

				thread_barrier.wait();
				let mut core = Core::new().expect("tokio::Core could not be created");

				// block notifications
				let network1 = network.clone();
				let txpool1 = txpool.clone();

				let events = client.import_notification_stream()
					.for_each(move |notification| {
						network1.on_block_imported(notification.hash, &notification.header);
						prune_imported(&*api, &*txpool1, notification.hash);
						Ok(())
					});
				core.handle().spawn(events);

				// transaction notifications
				let events = txpool.import_notification_stream()
					// TODO [ToDr] Consider throttling?
					.for_each(move |_| {
						network.trigger_repropagate();
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
		let consensus_service = consensus_creator(client.clone(), network.clone(), transaction_pool.clone(), &keystore)?;

		Ok(Service {
			thread: Some(thread),
			client: client,
			network: network,
			transaction_pool: transaction_pool,
			signal: Some(signal),
			_consensus: consensus_service,
		})
	}

	/// Get shared client instance.
	pub fn client(&self) -> Arc<Client<B, E, Block>> {
		self.client.clone()
	}

	/// Get shared network instance.
	pub fn network(&self) -> Arc<network::Service<Block>> {
		self.network.clone()
	}

	/// Get shared transaction pool instance.
	pub fn transaction_pool(&self) -> Arc<TransactionPool> {
		self.transaction_pool.clone()
	}
}

/// Produce a task which prunes any finalized transactions from the pool.
pub fn prune_imported<A>(api: &A, pool: &TransactionPool, hash: Hash)
	where
		A: PolkadotApi,
{
	match api.check_id(BlockId::hash(hash)) {
		Ok(id) => {
			let ready = transaction_pool::Ready::create(id, api);
			pool.cull(None, ready);
		},
		Err(e) => warn!("Failed to check block id: {:?}", e),
	}
}

impl<B, E> Drop for Service<B, E> {
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
