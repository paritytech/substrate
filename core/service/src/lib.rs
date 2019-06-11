// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

#![warn(missing_docs)]

mod components;
mod chain_spec;
pub mod config;
pub mod chain_ops;
pub mod error;

use std::io;
use std::net::SocketAddr;
use std::collections::HashMap;
use futures::sync::mpsc;
use parking_lot::Mutex;

use client::BlockchainEvents;
use exit_future::Signal;
use futures::prelude::*;
use keystore::Store as Keystore;
use log::{info, warn, debug};
use parity_codec::{Encode, Decode};
use primitives::Pair;
use runtime_primitives::generic::BlockId;
use runtime_primitives::traits::{Header, SaturatedConversion};
use substrate_executor::NativeExecutor;
use tel::{telemetry, SUBSTRATE_INFO};

pub use self::error::Error;
pub use config::{Configuration, Roles, PruningMode};
pub use chain_spec::{ChainSpec, Properties};
pub use transaction_pool::txpool::{
	self, Pool as TransactionPool, Options as TransactionPoolOptions, ChainApi, IntoPoolError
};
use client::runtime_api::BlockT;
pub use client::FinalityNotifications;

pub use components::{ServiceFactory, FullBackend, FullExecutor, LightBackend,
	LightExecutor, Components, PoolApi, ComponentClient,
	ComponentBlock, FullClient, LightClient, FullComponents, LightComponents,
	CodeExecutor, NetworkService, FactoryChainSpec, FactoryBlock,
	FactoryFullConfiguration, RuntimeGenesis, FactoryGenesis,
	ComponentExHash, ComponentExtrinsic, FactoryExtrinsic
};
use components::{StartRPC, MaintainTransactionPool, OffchainWorker};
#[doc(hidden)]
pub use std::{ops::Deref, result::Result, sync::Arc};
#[doc(hidden)]
pub use network::{FinalityProofProvider, OnDemand};
#[doc(hidden)]
pub use tokio::runtime::TaskExecutor;

const DEFAULT_PROTOCOL_ID: &str = "sup";

/// Substrate service.
pub struct Service<Components: components::Components> {
	client: Arc<ComponentClient<Components>>,
	select_chain: Option<<Components as components::Components>::SelectChain>,
	network: Option<Arc<components::NetworkService<Components::Factory>>>,
	transaction_pool: Arc<TransactionPool<Components::TransactionPoolApi>>,
	keystore: Keystore,
	exit: ::exit_future::Exit,
	signal: Option<Signal>,
	/// Configuration of this Service
	pub config: FactoryFullConfiguration<Components::Factory>,
	_rpc: Box<dyn std::any::Any + Send + Sync>,
	_telemetry: Option<tel::Telemetry>,
	_offchain_workers: Option<Arc<offchain::OffchainWorkers<ComponentClient<Components>, ComponentBlock<Components>>>>,
	_telemetry_on_connect_sinks: Arc<Mutex<Vec<mpsc::UnboundedSender<()>>>>,
}

/// Creates bare client without any networking.
pub fn new_client<Factory: components::ServiceFactory>(config: &FactoryFullConfiguration<Factory>)
	-> Result<Arc<ComponentClient<components::FullComponents<Factory>>>, error::Error>
{
	let executor = NativeExecutor::new(config.default_heap_pages);
	let (client, _) = components::FullComponents::<Factory>::build_client(
		config,
		executor,
	)?;
	Ok(client)
}

/// Stream of events for connection established to a telemetry server.
pub type TelemetryOnConnectNotifications = mpsc::UnboundedReceiver<()>;

/// Used to hook on telemetry connection established events.
pub struct TelemetryOnConnect<'a> {
	/// Handle to a future that will resolve on exit.
	pub on_exit: Box<dyn Future<Item=(), Error=()> + Send + 'static>,
	/// Event stream.
	pub telemetry_connection_sinks: TelemetryOnConnectNotifications,
	/// Executor to which the hook is spawned.
	pub executor: &'a TaskExecutor,
}

impl<Components: components::Components> Service<Components> {
	/// Get event stream for telemetry connection established events.
	pub fn telemetry_on_connect_stream(&self) -> TelemetryOnConnectNotifications {
		let (sink, stream) = mpsc::unbounded();
		self._telemetry_on_connect_sinks.lock().push(sink);
		stream
	}

	/// Creates a new service.
	pub fn new(
		mut config: FactoryFullConfiguration<Components::Factory>,
		task_executor: TaskExecutor,
	) -> Result<Self, error::Error> {
		let (signal, exit) = ::exit_future::signal();

		// Create client
		let executor = NativeExecutor::new(config.default_heap_pages);

		let mut keystore = Keystore::open(config.keystore_path.as_str().into())?;

		// This is meant to be for testing only
		// FIXME #1063 remove this
		for seed in &config.keys {
			keystore.generate_from_seed(seed)?;
		}
		// Keep the public key for telemetry
		let public_key = match keystore.contents()?.get(0) {
			Some(public_key) => public_key.clone(),
			None => {
				let key = keystore.generate(&config.password)?;
				let public_key = key.public();
				info!("Generated a new keypair: {:?}", public_key);

				public_key
			}
		};

		let (client, on_demand) = Components::build_client(&config, executor)?;
		let select_chain = Components::build_select_chain(&mut config, client.clone())?;
		let import_queue = Box::new(Components::build_import_queue(
			&mut config,
			client.clone(),
			select_chain.clone(),
		)?);
		let finality_proof_provider = Components::build_finality_proof_provider(client.clone())?;
		let chain_info = client.info().chain;

		let version = config.full_version();
		info!("Highest known block at #{}", chain_info.best_number);
		telemetry!(SUBSTRATE_INFO; "node.start";
			"height" => chain_info.best_number.saturated_into::<u64>(),
			"best" => ?chain_info.best_hash
		);

		let network_protocol = <Components::Factory>::build_network_protocol(&config)?;
		let transaction_pool = Arc::new(
			Components::build_transaction_pool(config.transaction_pool.clone(), client.clone())?
		);
		let transaction_pool_adapter = Arc::new(TransactionPoolAdapter::<Components> {
			imports_external_transactions: !config.roles.is_light(),
			pool: transaction_pool.clone(),
			client: client.clone(),
		 });

		let protocol_id = {
			let protocol_id_full = match config.chain_spec.protocol_id() {
				Some(pid) => pid,
				None => {
					warn!("Using default protocol ID {:?} because none is configured in the \
						chain specs", DEFAULT_PROTOCOL_ID
					);
					DEFAULT_PROTOCOL_ID
				}
			}.as_bytes();
			network::ProtocolId::from(protocol_id_full)
		};

		let network_params = network::config::Params {
			roles: config.roles,
			network_config: config.network.clone(),
			chain: client.clone(),
			finality_proof_provider,
			on_demand,
			transaction_pool: transaction_pool_adapter.clone() as _,
			import_queue,
			protocol_id,
			specialization: network_protocol,
		};

		let has_bootnodes = !network_params.network_config.boot_nodes.is_empty();
		let network_mut = network::NetworkWorker::new(network_params)?;
		let network = network_mut.service().clone();

		task_executor.spawn(network_mut
			.map_err(|_| ())
			.select(exit.clone())
			.then(|_| Ok(())));

		let offchain_workers =  if config.offchain_worker {
			Some(Arc::new(offchain::OffchainWorkers::new(
				client.clone(),
				task_executor.clone(),
			)))
		} else {
			None
		};

		{
			// block notifications
			let network = Arc::downgrade(&network);
			let txpool = Arc::downgrade(&transaction_pool);
			let wclient = Arc::downgrade(&client);
			let offchain = offchain_workers.as_ref().map(Arc::downgrade);

			let events = client.import_notification_stream()
				.for_each(move |notification| {
					let number = *notification.header.number();

					if let Some(network) = network.upgrade() {
						network.on_block_imported(notification.hash, notification.header);
					}

					if let (Some(txpool), Some(client)) = (txpool.upgrade(), wclient.upgrade()) {
						Components::RuntimeServices::maintain_transaction_pool(
							&BlockId::hash(notification.hash),
							&*client,
							&*txpool,
						).map_err(|e| warn!("Pool error processing new block: {:?}", e))?;
					}

					if let (Some(txpool), Some(offchain)) = (txpool.upgrade(), offchain.as_ref().and_then(|o| o.upgrade())) {
						Components::RuntimeServices::offchain_workers(
							&number,
							&offchain,
							&txpool,
						).map_err(|e| warn!("Offchain workers error processing new block: {:?}", e))?;
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

			// A utility stream that drops all ready items and only returns the last one.
			// This is used to only keep the last finality notification and avoid
			// overloading the sync module with notifications.
			struct MostRecentNotification<B: BlockT>(futures::stream::Fuse<FinalityNotifications<B>>);

			impl<B: BlockT> Stream for MostRecentNotification<B> {
				type Item = <FinalityNotifications<B> as Stream>::Item;
				type Error = <FinalityNotifications<B> as Stream>::Error;

				fn poll(&mut self) -> Poll<Option<Self::Item>, Self::Error> {
					let mut last = None;
					let last = loop {
						match self.0.poll()? {
							Async::Ready(Some(item)) => { last = Some(item) }
							Async::Ready(None) => match last {
								None => return Ok(Async::Ready(None)),
								Some(last) => break last,
							},
							Async::NotReady => match last {
								None => return Ok(Async::NotReady),
								Some(last) => break last,
							},
						}
					};

					Ok(Async::Ready(Some(last)))
				}
			}

			let events = MostRecentNotification(client.finality_notification_stream().fuse())
				.for_each(move |notification| {
					if let Some(network) = network.upgrade() {
						network.on_block_finalized(notification.hash, notification.header);
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
		let rpc = Components::RuntimeServices::start_rpc(
			client.clone(),
			network.clone(),
			has_bootnodes,
			system_info,
			config.rpc_http,
			config.rpc_ws,
			config.rpc_ws_max_connections,
			config.rpc_cors.clone(),
			task_executor.clone(),
			transaction_pool.clone(),
		)?;

		let telemetry_connection_sinks: Arc<Mutex<Vec<mpsc::UnboundedSender<()>>>> = Default::default();

		// Telemetry
		let telemetry = config.telemetry_endpoints.clone().map(|endpoints| {
			let is_authority = config.roles == Roles::AUTHORITY;
			let network_id = network.local_peer_id().to_base58();
			let pubkey = format!("{}", public_key);
			let name = config.name.clone();
			let impl_name = config.impl_name.to_owned();
			let version = version.clone();
			let chain_name = config.chain_spec.name().to_owned();
			let telemetry_connection_sinks_ = telemetry_connection_sinks.clone();
			let telemetry = tel::init_telemetry(tel::TelemetryConfig {
				endpoints,
				wasm_external_transport: None,
				on_connect: Box::new(move || {
					telemetry!(SUBSTRATE_INFO; "system.connected";
						"name" => name.clone(),
						"implementation" => impl_name.clone(),
						"version" => version.clone(),
						"config" => "",
						"chain" => chain_name.clone(),
						"pubkey" => &pubkey,
						"authority" => is_authority,
						"network_id" => network_id.clone()
					);

					telemetry_connection_sinks_.lock().retain(|sink| {
						sink.unbounded_send(()).is_ok()
					});
				}),
			});
			task_executor.spawn(telemetry.clone()
				.select(exit.clone())
				.then(|_| Ok(())));
			telemetry
		});

		Ok(Service {
			client,
			network: Some(network),
			select_chain,
			transaction_pool,
			signal: Some(signal),
			keystore,
			config,
			exit,
			_rpc: Box::new(rpc),
			_telemetry: telemetry,
			_offchain_workers: offchain_workers,
			_telemetry_on_connect_sinks: telemetry_connection_sinks.clone(),
		})
	}

	/// give the authority key, if we are an authority and have a key
	pub fn authority_key(&self) -> Option<primitives::ed25519::Pair> {
		if self.config.roles != Roles::AUTHORITY { return None }
		let keystore = &self.keystore;
		if let Ok(Some(Ok(key))) =  keystore.contents().map(|keys| keys.get(0)
				.map(|k| keystore.load(k, &self.config.password)))
		{
			Some(key)
		} else {
			None
		}
	}

	/// return a shared instance of Telemetry (if enabled)
	pub fn telemetry(&self) -> Option<tel::Telemetry> {
		self._telemetry.as_ref().map(|t| t.clone())
	}
}

impl<Components> Service<Components> where Components: components::Components {
	/// Get shared client instance.
	pub fn client(&self) -> Arc<ComponentClient<Components>> {
		self.client.clone()
	}

	/// Get clone of select chain.
	pub fn select_chain(&self) -> Option<<Components as components::Components>::SelectChain> {
		self.select_chain.clone()
	}

	/// Get shared network instance.
	pub fn network(&self) -> Arc<components::NetworkService<Components::Factory>> {
		self.network.as_ref().expect("self.network always Some").clone()
	}

	/// Get shared transaction pool instance.
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

fn maybe_start_server<T, F>(address: Option<SocketAddr>, start: F) -> Result<Option<T>, io::Error>
	where F: Fn(&SocketAddr) -> Result<T, io::Error>,
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
		Some(BlockId::hash(self.client.info().chain.best_hash))
	}
}

/// Get transactions for propagation.
///
/// Function extracted to simplify the test and prevent creating `ServiceFactory`.
fn transactions_to_propagate<PoolApi, B, H, E>(pool: &TransactionPool<PoolApi>)
	-> Vec<(H, B::Extrinsic)>
where
	PoolApi: ChainApi<Block=B, Hash=H, Error=E>,
	B: BlockT,
	H: std::hash::Hash + Eq + runtime_primitives::traits::Member + serde::Serialize,
	E: txpool::error::IntoPoolError + From<txpool::error::Error>,
{
	pool.ready()
		.filter(|t| t.is_propagateable())
		.map(|t| {
			let hash = t.hash.clone();
			let ex: B::Extrinsic = t.data.clone();
			(hash, ex)
		})
		.collect()
}

impl<C: Components> network::TransactionPool<ComponentExHash<C>, ComponentBlock<C>> for
	TransactionPoolAdapter<C> where <C as components::Components>::RuntimeApi: Send + Sync
{
	fn transactions(&self) -> Vec<(ComponentExHash<C>, ComponentExtrinsic<C>)> {
		transactions_to_propagate(&self.pool)
	}

	fn import(&self, transaction: &ComponentExtrinsic<C>) -> Option<ComponentExHash<C>> {
		if !self.imports_external_transactions {
			debug!("Transaction rejected");
			return None;
		}

		let encoded = transaction.encode();
		if let Some(uxt) = Decode::decode(&mut &encoded[..]) {
			let best_block_id = self.best_block_id()?;
			match self.pool.submit_one(&best_block_id, uxt) {
				Ok(hash) => Some(hash),
				Err(e) => match e.into_pool_error() {
					Ok(txpool::error::Error::AlreadyImported(hash)) => {
						hash.downcast::<ComponentExHash<C>>().ok()
							.map(|x| x.as_ref().clone())
					},
					Ok(e) => {
						debug!("Error adding transaction to the pool: {:?}", e);
						None
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
/// ```
/// # use substrate_service::{
/// # 	construct_service_factory, Service, FullBackend, FullExecutor, LightBackend, LightExecutor,
/// # 	FullComponents, LightComponents, FactoryFullConfiguration, FullClient, TaskExecutor
/// # };
/// # use transaction_pool::{self, txpool::{Pool as TransactionPool}};
/// # use network::construct_simple_protocol;
/// # use client::{self, LongestChain};
/// # use primitives::{Pair as PairT, ed25519};
/// # use consensus_common::import_queue::{BasicQueue, Verifier};
/// # use consensus_common::{BlockOrigin, ImportBlock};
/// # use node_runtime::{GenesisConfig, RuntimeApi};
/// # use std::sync::Arc;
/// # use node_primitives::Block;
/// # use runtime_primitives::Justification;
/// # use runtime_primitives::traits::{AuthorityIdFor, Block as BlockT};
/// # use grandpa;
/// # construct_simple_protocol! {
/// # 	pub struct NodeProtocol where Block = Block { }
/// # }
/// # struct MyVerifier;
/// # impl<B: BlockT> Verifier<B> for MyVerifier {
/// # 	fn verify(
/// # 		&self,
/// # 		origin: BlockOrigin,
/// # 		header: B::Header,
/// # 		justification: Option<Justification>,
/// # 		body: Option<Vec<B::Extrinsic>>,
/// # 	) -> Result<(ImportBlock<B>, Option<Vec<AuthorityIdFor<B>>>), String> {
/// # 		unimplemented!();
/// # 	}
/// # }
/// type FullChainApi<T> = transaction_pool::ChainApi<
/// 	client::Client<FullBackend<T>, FullExecutor<T>, Block, RuntimeApi>, Block>;
/// type LightChainApi<T> = transaction_pool::ChainApi<
/// 	client::Client<LightBackend<T>, LightExecutor<T>, Block, RuntimeApi>, Block>;
///
/// construct_service_factory! {
/// 	struct Factory {
/// 		// Declare the block type
/// 		Block = Block,
/// 		RuntimeApi = RuntimeApi,
/// 		// Declare the network protocol and give an initializer.
/// 		NetworkProtocol = NodeProtocol { |config| Ok(NodeProtocol::new()) },
/// 		RuntimeDispatch = node_executor::Executor,
/// 		FullTransactionPoolApi = FullChainApi<Self>
/// 			{ |config, client| Ok(TransactionPool::new(config, transaction_pool::ChainApi::new(client))) },
/// 		LightTransactionPoolApi = LightChainApi<Self>
/// 			{ |config, client| Ok(TransactionPool::new(config, transaction_pool::ChainApi::new(client))) },
/// 		Genesis = GenesisConfig,
/// 		Configuration = (),
/// 		FullService = FullComponents<Self>
/// 			{ |config, executor| <FullComponents<Factory>>::new(config, executor) },
/// 		// Setup as Consensus Authority (if the role and key are given)
/// 		AuthoritySetup = {
/// 			|service: Self::FullService, executor: TaskExecutor, key: Option<Arc<ed25519::Pair>>| {
/// 				Ok(service)
/// 			}},
/// 		LightService = LightComponents<Self>
/// 			{ |config, executor| <LightComponents<Factory>>::new(config, executor) },
/// 		FullImportQueue = BasicQueue<Block>
/// 			{ |_, client, _| Ok(BasicQueue::new(Arc::new(MyVerifier), client, None, None, None)) },
/// 		LightImportQueue = BasicQueue<Block>
/// 			{ |_, client| Ok(BasicQueue::new(Arc::new(MyVerifier), client, None, None, None)) },
/// 		SelectChain = LongestChain<FullBackend<Self>, Self::Block>
/// 			{ |config: &FactoryFullConfiguration<Self>, client: Arc<FullClient<Self>>| {
/// 				#[allow(deprecated)]
/// 				Ok(LongestChain::new(client.backend().clone()))
/// 			}},
/// 		FinalityProofProvider = { |client: Arc<FullClient<Self>>| {
/// 				Ok(Some(Arc::new(grandpa::FinalityProofProvider::new(client.clone(), client)) as _))
/// 			}},
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
			SelectChain = $select_chain:ty
				{ $( $select_chain_init:tt )* },
			FinalityProofProvider = { $( $finality_proof_provider_init:tt )* },
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
			type SelectChain = $select_chain;

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

			fn build_select_chain(
				config: &mut $crate::FactoryFullConfiguration<Self>,
				client: Arc<$crate::FullClient<Self>>
			) -> $crate::Result<Self::SelectChain, $crate::Error> {
				( $( $select_chain_init )* ) (config, client)
			}

			fn build_full_import_queue(
				config: &mut $crate::FactoryFullConfiguration<Self>,
				client: $crate::Arc<$crate::FullClient<Self>>,
				select_chain: Self::SelectChain
			) -> $crate::Result<Self::FullImportQueue, $crate::Error> {
				( $( $full_import_queue_init )* ) (config, client, select_chain)
			}

			fn build_light_import_queue(
				config: &mut FactoryFullConfiguration<Self>,
				client: Arc<$crate::LightClient<Self>>,
			) -> Result<Self::LightImportQueue, $crate::Error> {
				( $( $light_import_queue_init )* ) (config, client)
			}

			fn build_finality_proof_provider(
				client: Arc<$crate::FullClient<Self>>
			) -> Result<Option<Arc<$crate::FinalityProofProvider<Self::Block>>>, $crate::Error> {
				( $( $finality_proof_provider_init )* ) (client)
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

#[cfg(test)]
mod tests {
	use super::*;
	use consensus_common::SelectChain;
	use runtime_primitives::traits::BlindCheckable;
	use substrate_test_client::{AccountKeyring, runtime::{Extrinsic, Transfer}, TestClientBuilder};

	#[test]
	fn should_not_propagate_transactions_that_are_marked_as_such() {
		// given
		let (client, longest_chain) = TestClientBuilder::new().build_with_longest_chain();
		let client = Arc::new(client);
		let pool = Arc::new(TransactionPool::new(
			Default::default(),
			transaction_pool::ChainApi::new(client.clone())
		));
		let best = longest_chain.best_chain().unwrap();
		let transaction = Transfer {
			amount: 5,
			nonce: 0,
			from: AccountKeyring::Alice.into(),
			to: Default::default(),
		}.into_signed_tx();
		pool.submit_one(&BlockId::hash(best.hash()), transaction.clone()).unwrap();
		pool.submit_one(&BlockId::hash(best.hash()), Extrinsic::IncludeData(vec![1])).unwrap();
		assert_eq!(pool.status().ready, 2);

		// when
		let transactions = transactions_to_propagate(&pool);

		// then
		assert_eq!(transactions.len(), 1);
		assert!(transactions[0].1.clone().check().is_ok());
		// this should not panic
		let _ = transactions[0].1.transfer();
	}
}
