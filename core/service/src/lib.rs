// Copyright 2017-2018 Parity Technologies (UK) Ltd.
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

//! Substrate service. Starts a thread that spins up the network, client, and extrinsic pool.
//! Manages communication between them.

#![warn(unused_extern_crates)]

extern crate futures;
extern crate exit_future;
extern crate serde;
extern crate serde_json;
extern crate parking_lot;
extern crate substrate_keystore as keystore;
extern crate substrate_primitives as primitives;
extern crate sr_primitives as runtime_primitives;
extern crate substrate_consensus_common as consensus_common;
extern crate substrate_network as network;
extern crate substrate_executor;
extern crate substrate_client as client;
extern crate substrate_client_db as client_db;
extern crate parity_codec as codec;
extern crate substrate_transaction_pool as transaction_pool;
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

#[cfg(test)]
extern crate substrate_test_client;

mod components;
mod error;
mod chain_spec;
pub mod config;
pub mod chain_ops;

use std::io;
use std::net::SocketAddr;
use std::collections::HashMap;
#[doc(hidden)]
pub use std::{ops::Deref, result::Result, sync::Arc};
use futures::prelude::*;
use keystore::Store as Keystore;
use client::BlockchainEvents;
use runtime_primitives::generic::BlockId;
use runtime_primitives::traits::{Header, As};
use exit_future::Signal;
#[doc(hidden)]
pub use tokio::runtime::TaskExecutor;
use substrate_executor::NativeExecutor;
use codec::{Encode, Decode};

pub use self::error::{ErrorKind, Error};
pub use config::{Configuration, Roles, PruningMode};
pub use chain_spec::{ChainSpec, Properties};
pub use transaction_pool::txpool::{self, Pool as TransactionPool, Options as TransactionPoolOptions, ChainApi, IntoPoolError};
pub use client::ExecutionStrategy;

pub use components::{ServiceFactory, FullBackend, FullExecutor, LightBackend,
	LightExecutor, Components, PoolApi, ComponentClient,
	ComponentBlock, FullClient, LightClient, FullComponents, LightComponents,
	CodeExecutor, NetworkService, FactoryChainSpec, FactoryBlock,
	FactoryFullConfiguration, RuntimeGenesis, FactoryGenesis,
	ComponentExHash, ComponentExtrinsic, FactoryExtrinsic
};
use components::{StartRPC, MaintainTransactionPool};
#[doc(hidden)]
pub use network::OnDemand;

const DEFAULT_PROTOCOL_ID: &'static str = "sup";

/// Substrate service.
pub struct Service<Components: components::Components> {
	client: Arc<ComponentClient<Components>>,
	network: Option<Arc<components::NetworkService<Components::Factory>>>,
	transaction_pool: Arc<TransactionPool<Components::TransactionPoolApi>>,
	keystore: Keystore,
	exit: ::exit_future::Exit,
	signal: Option<Signal>,
	/// Configuration of this Service
	pub config: FactoryFullConfiguration<Components::Factory>,
	_rpc: Box<::std::any::Any + Send + Sync>,
	_telemetry: Option<Arc<tel::Telemetry>>,
}

/// Creates bare client without any networking.
pub fn new_client<Factory: components::ServiceFactory>(config: &FactoryFullConfiguration<Factory>)
	-> Result<Arc<ComponentClient<components::FullComponents<Factory>>>, error::Error>
{
	let executor = NativeExecutor::new();
	let (client, _) = components::FullComponents::<Factory>::build_client(
		config,
		executor,
	)?;
	Ok(client)
}

impl<Components: components::Components> Service<Components> {
	/// Creates a new service.
	pub fn new(
		mut config: FactoryFullConfiguration<Components::Factory>,
		task_executor: TaskExecutor,
	)
		-> Result<Self, error::Error>
	{
		let (signal, exit) = ::exit_future::signal();

		// Create client
		let executor = NativeExecutor::new();

		let mut keystore = Keystore::open(config.keystore_path.as_str().into())?;

		// This is meant to be for testing only
		// FIXME: remove this - https://github.com/paritytech/substrate/issues/1063
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
		let import_queue = Arc::new(Components::build_import_queue(&mut config, client.clone())?);
		let best_header = client.best_block_header()?;

		let version = config.full_version();
		info!("Best block: #{}", best_header.number());
		telemetry!("node.start"; "height" => best_header.number().as_(), "best" => ?best_header.hash());

		let network_protocol = <Components::Factory>::build_network_protocol(&config)?;
		let transaction_pool = Arc::new(
			Components::build_transaction_pool(config.transaction_pool.clone(), client.clone())?
		);
		let transaction_pool_adapter = Arc::new(TransactionPoolAdapter::<Components> {
			imports_external_transactions: !(config.roles == Roles::LIGHT),
			pool: transaction_pool.clone(),
			client: client.clone(),
		 });

		let network_params = network::config::Params {
			config: network::config::ProtocolConfig { roles: config.roles },
			network_config: config.network.clone(),
			chain: client.clone(),
			on_demand: on_demand.as_ref().map(|d| d.clone() as _),
			transaction_pool: transaction_pool_adapter.clone() as _,
			specialization: network_protocol,
		};

		let protocol_id = {
			let protocol_id_full = config.chain_spec.protocol_id().unwrap_or(DEFAULT_PROTOCOL_ID).as_bytes();
			let mut protocol_id = network::ProtocolId::default();
			if protocol_id_full.len() > protocol_id.len() {
				warn!("Protocol ID truncated to {} chars", protocol_id.len());
			}
			let id_len = protocol_id_full.len().min(protocol_id.len());
			&mut protocol_id[0..id_len].copy_from_slice(&protocol_id_full[0..id_len]);
			protocol_id
		};

		let has_bootnodes = !network_params.network_config.boot_nodes.is_empty();
		let network = network::Service::new(
			network_params,
			protocol_id,
			import_queue
		)?;
		on_demand.map(|on_demand| on_demand.set_service_link(Arc::downgrade(&network)));

		{
			// block notifications
			let network = Arc::downgrade(&network);
			let txpool = Arc::downgrade(&transaction_pool);
			let wclient = Arc::downgrade(&client);

			let events = client.import_notification_stream()
				.for_each(move |notification| {
					if let Some(network) = network.upgrade() {
						network.on_block_imported(notification.hash, &notification.header);
					}
					if let (Some(txpool), Some(client)) = (txpool.upgrade(), wclient.upgrade()) {
						Components::TransactionPool::on_block_imported(
							&BlockId::hash(notification.hash),
							&*client,
							&*txpool,
						).map_err(|e| warn!("Pool error processing new block: {:?}", e))?;
					}
					Ok(())
				})
				.select(exit.clone())
				.then(|_| Ok(()));
			task_executor.spawn(events);
		}

		{
			// finality notifications
			let network = Arc::downgrade(&network);

			let events = client.finality_notification_stream()
				.for_each(move |notification| {
					if let Some(network) = network.upgrade() {
						network.on_block_finalized(notification.hash, &notification.header);
					}
					Ok(())
				})
				.select(exit.clone())
				.then(|_| Ok(()));

			task_executor.spawn(events);
		}

		{
			// extrinsic notifications
			let network = Arc::downgrade(&network);
			let events = transaction_pool.import_notification_stream()
				// TODO [ToDr] Consider throttling?
				.for_each(move |_| {
					if let Some(network) = network.upgrade() {
						network.trigger_repropagate();
					}
					Ok(())
				})
				.select(exit.clone())
				.then(|_| Ok(()));

			task_executor.spawn(events);
		}


		// RPC
		let system_info = rpc::apis::system::SystemInfo {
			chain_name: config.chain_spec.name().into(),
			impl_name: config.impl_name.into(),
			impl_version: config.impl_version.into(),
			properties: config.chain_spec.properties(),
		};
		let rpc = Components::RPC::start_rpc(
			client.clone(), network.clone(), has_bootnodes, system_info, config.rpc_http, config.rpc_ws, task_executor.clone(), transaction_pool.clone(),
		)?;

		// Telemetry
		let telemetry = config.telemetry_url.clone().map(|url| {
			let is_authority = config.roles == Roles::AUTHORITY;
			let pubkey = format!("{}", public_key);
			let name = config.name.clone();
			let impl_name = config.impl_name.to_owned();
			let version = version.clone();
			let chain_name = config.chain_spec.name().to_owned();
			Arc::new(tel::init_telemetry(tel::TelemetryConfig {
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
		});

		Ok(Service {
			client,
			network: Some(network),
			transaction_pool,
			signal: Some(signal),
			keystore,
			config,
			exit,
			_rpc: Box::new(rpc),
			_telemetry: telemetry,
		})
	}

	/// give the authority key, if we are an authority and have a key
	pub fn authority_key(&self) -> Option<primitives::ed25519::Pair> {
		if self.config.roles != Roles::AUTHORITY { return None }
		let keystore = &self.keystore;
		if let Ok(Some(Ok(key))) =  keystore.contents().map(|keys| keys.get(0)
				.map(|k| keystore.load(k, "")))
		{
			Some(key)
		} else {
			None
		}
	}

	pub fn telemetry(&self) -> Option<Arc<tel::Telemetry>> {
		self._telemetry.as_ref().map(|t| t.clone())
	}
}

impl<Components> Service<Components> where Components: components::Components {
	/// Get shared client instance.
	pub fn client(&self) -> Arc<ComponentClient<Components>> {
		self.client.clone()
	}

	/// Get shared network instance.
	pub fn network(&self) -> Arc<components::NetworkService<Components::Factory>> {
		self.network.as_ref().expect("self.network always Some").clone()
	}

	/// Get shared extrinsic pool instance.
	pub fn transaction_pool(&self) -> Arc<TransactionPool<Components::TransactionPoolApi>> {
		self.transaction_pool.clone()
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

/// Transaction pool adapter.
pub struct TransactionPoolAdapter<C: Components> {
	imports_external_transactions: bool,
	pool: Arc<TransactionPool<C::TransactionPoolApi>>,
	client: Arc<ComponentClient<C>>,
}

impl<C: Components> TransactionPoolAdapter<C> {
	fn best_block_id(&self) -> Option<BlockId<ComponentBlock<C>>> {
		self.client.info()
			.map(|info| BlockId::hash(info.chain.best_hash))
			.map_err(|e| {
				debug!("Error getting best block: {:?}", e);
			})
			.ok()
	}
}

impl<C: Components> network::TransactionPool<ComponentExHash<C>, ComponentBlock<C>> for TransactionPoolAdapter<C> where <C as components::Components>::RuntimeApi: Send + Sync{
	fn transactions(&self) -> Vec<(ComponentExHash<C>, ComponentExtrinsic<C>)> {
		self.pool.ready()
			.map(|t| {
				let hash = t.hash.clone();
				let ex: ComponentExtrinsic<C> = t.data.clone();
				(hash, ex)
			})
			.collect()
	}

	fn import(&self, transaction: &ComponentExtrinsic<C>) -> Option<ComponentExHash<C>> {
		if !self.imports_external_transactions {
			debug!("Transaction rejected");
			return None;
		}

		let encoded = transaction.encode();
		if let Some(uxt) = Decode::decode(&mut &encoded[..]) {
			let best_block_id = self.best_block_id()?;
			let hash = self.pool.hash_of(&uxt);
			match self.pool.submit_one(&best_block_id, uxt) {
				Ok(hash) => Some(hash),
				Err(e) => match e.into_pool_error() {
					Ok(e) => match e.kind() {
						txpool::error::ErrorKind::AlreadyImported => Some(hash),
						_ => {
							debug!("Error adding transaction to the pool: {:?}", e);
							None
						},
					},
					Err(e) => {
						debug!("Error converting pool error: {:?}", e);
						None
					},
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

/// Constructs a service factory with the given name that implements the `ServiceFactory` trait.
/// The required parameters are required to be given in the exact order. Some parameters are followed
/// by `{}` blocks. These blocks are required and used to initialize the given parameter.
/// In these block it is required to write a closure that takes the same number of arguments,
/// the corresponding function in the `ServiceFactory` trait provides.
///
/// # Example
///
/// ```nocompile
/// construct_service_factory! {
/// 	struct Factory {
///         // Declare the block type
/// 		Block = Block,
///         // Declare the network protocol and give an initializer.
/// 		NetworkProtocol = NodeProtocol { |config| Ok(NodeProtocol::new()) },
/// 		RuntimeDispatch = node_executor::Executor,
/// 		FullTransactionPoolApi = transaction_pool::ChainApi<FullBackend<Self>, FullExecutor<Self>, Block>
/// 			{ |config, client| Ok(TransactionPool::new(config, transaction_pool::ChainApi::new(client))) },
/// 		LightTransactionPoolApi = transaction_pool::ChainApi<LightBackend<Self>, LightExecutor<Self>, Block>
/// 			{ |config, client| Ok(TransactionPool::new(config, transaction_pool::ChainApi::new(client))) },
/// 		Genesis = GenesisConfig,
/// 		Configuration = (),
/// 		FullService = Service<FullComponents<Self>>
/// 			{ |config, executor| Service::<FullComponents<Factory>>::new(config, executor) },
///         // Setup as Consensus Authority (if the role and key are given)
/// 		AuthoritySetup = {
/// 			|service: Self::FullService, executor: TaskExecutor, key: Arc<Pair>| { Ok(service) }},
/// 		LightService = Service<LightComponents<Self>>
/// 			{ |config, executor| Service::<LightComponents<Factory>>::new(config, executor) },
///         // Declare the import queue. The import queue is special as it takes two initializers.
///         // The first one is for the initializing the full import queue and the second for the
///         // light import queue.
/// 		ImportQueue = BasicQueue<Block, NoneVerifier>
/// 			{ |_, client| Ok(BasicQueue::new(Arc::new(NoneVerifier {}, client))) }
/// 			{ |_, client| Ok(BasicQueue::new(Arc::new(NoneVerifier {}, client))) },
/// 	}
/// }
/// ```
#[macro_export]
macro_rules! construct_service_factory {
	(
		$(#[$attr:meta])*
		struct $name:ident {
			Block = $block:ty,
			RuntimeApi = $runtime_api:ty,
			NetworkProtocol = $protocol:ty { $( $protocol_init:tt )* },
			RuntimeDispatch = $dispatch:ty,
			FullTransactionPoolApi = $full_transaction:ty { $( $full_transaction_init:tt )* },
			LightTransactionPoolApi = $light_transaction:ty { $( $light_transaction_init:tt )* },
			Genesis = $genesis:ty,
			Configuration = $config:ty,
			FullService = $full_service:ty { $( $full_service_init:tt )* },
			AuthoritySetup = { $( $authority_setup:tt )* },
			LightService = $light_service:ty { $( $light_service_init:tt )* },
			FullImportQueue = $full_import_queue:ty
				{ $( $full_import_queue_init:tt )* },
			LightImportQueue = $light_import_queue:ty
				{ $( $light_import_queue_init:tt )* },
		}
	) => {
		$( #[$attr] )*
		pub struct $name {}

		#[allow(unused_variables)]
		impl $crate::ServiceFactory for $name {
			type Block = $block;
			type RuntimeApi = $runtime_api;
			type NetworkProtocol = $protocol;
			type RuntimeDispatch = $dispatch;
			type FullTransactionPoolApi = $full_transaction;
			type LightTransactionPoolApi = $light_transaction;
			type Genesis = $genesis;
			type Configuration = $config;
			type FullService = $full_service;
			type LightService = $light_service;
			type FullImportQueue = $full_import_queue;
			type LightImportQueue = $light_import_queue;

			fn build_full_transaction_pool(
				config: $crate::TransactionPoolOptions,
				client: $crate::Arc<$crate::FullClient<Self>>
			) -> $crate::Result<$crate::TransactionPool<Self::FullTransactionPoolApi>, $crate::Error>
			{
				( $( $full_transaction_init )* ) (config, client)
			}

			fn build_light_transaction_pool(
				config: $crate::TransactionPoolOptions,
				client: $crate::Arc<$crate::LightClient<Self>>
			) -> $crate::Result<$crate::TransactionPool<Self::LightTransactionPoolApi>, $crate::Error>
			{
				( $( $light_transaction_init )* ) (config, client)
			}

			fn build_network_protocol(config: &$crate::FactoryFullConfiguration<Self>)
				-> $crate::Result<Self::NetworkProtocol, $crate::Error>
			{
				( $( $protocol_init )* ) (config)
			}

			fn build_full_import_queue(
				config: &mut $crate::FactoryFullConfiguration<Self>,
				client: $crate::Arc<$crate::FullClient<Self>>,
			) -> $crate::Result<Self::FullImportQueue, $crate::Error> {
				( $( $full_import_queue_init )* ) (config, client)
			}

			fn build_light_import_queue(
				config: &mut FactoryFullConfiguration<Self>,
				client: Arc<$crate::LightClient<Self>>,
			) -> Result<Self::LightImportQueue, $crate::Error> {
				( $( $light_import_queue_init )* ) (config, client)
			}

			fn new_light(
				config: $crate::FactoryFullConfiguration<Self>,
				executor: $crate::TaskExecutor
			) -> $crate::Result<Self::LightService, $crate::Error>
			{
				( $( $light_service_init )* ) (config, executor)
			}

			fn new_full(
				config: $crate::FactoryFullConfiguration<Self>,
				executor: $crate::TaskExecutor,
			) -> Result<Self::FullService, $crate::Error>
			{
				( $( $full_service_init )* ) (config, executor.clone()).and_then(|service| {
					let key = (&service).authority_key().map(Arc::new);
					($( $authority_setup )*)(service, executor, key)
				})
			}
		}
	}
}
