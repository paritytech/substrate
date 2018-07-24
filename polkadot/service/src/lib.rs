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

#![warn(unused_extern_crates)]

//! Polkadot service. Specialized wrapper over substrate service.

extern crate ed25519;
extern crate polkadot_primitives;
extern crate polkadot_runtime;
extern crate polkadot_executor;
extern crate polkadot_api;
extern crate polkadot_consensus as consensus;
extern crate polkadot_transaction_pool as transaction_pool;
extern crate polkadot_network;
extern crate substrate_primitives as primitives;
extern crate substrate_network as network;
extern crate substrate_codec as codec;
extern crate substrate_client as client;
extern crate substrate_service as service;
extern crate tokio;

#[macro_use]
extern crate log;
#[macro_use]
extern crate hex_literal;

pub mod chain_spec;

use std::sync::Arc;
use std::collections::HashMap;

use codec::Encode;
use transaction_pool::TransactionPool;
use polkadot_api::{PolkadotApi, light::RemotePolkadotApiWrapper};
use polkadot_primitives::{parachain, AccountId, Block, BlockId, Hash};
use polkadot_runtime::GenesisConfig;
use client::Client;
use polkadot_network::{PolkadotProtocol, consensus::ConsensusNetwork};
use tokio::runtime::TaskExecutor;
use service::FactoryFullConfiguration;

pub use service::{Roles, PruningMode, ExtrinsicPoolOptions,
	ErrorKind, Error, ComponentBlock, LightComponents, FullComponents};
pub use client::ExecutionStrategy;

/// Specialised polkadot `ChainSpec`.
pub type ChainSpec = service::ChainSpec<GenesisConfig>;
/// Polkadot client type for specialised `Components`.
pub type ComponentClient<C> = Client<<C as Components>::Backend, <C as Components>::Executor, Block>;
pub type NetworkService = network::Service<Block, <Factory as service::ServiceFactory>::NetworkProtocol>;

/// A collection of type to generalise Polkadot specific components over full / light client.
pub trait Components: service::Components {
	/// Polkadot API.
	type Api: 'static + PolkadotApi + Send + Sync;
	/// Client backend.
	type Backend: 'static + client::backend::Backend<Block>;
	/// Client executor.
	type Executor: 'static + client::CallExecutor<Block> + Send + Sync;
}

impl Components for service::LightComponents<Factory> {
	type Api = RemotePolkadotApiWrapper<
		<service::LightComponents<Factory> as service::Components>::Backend,
		<service::LightComponents<Factory> as service::Components>::Executor,
	>;
	type Executor = service::LightExecutor<Factory>;
	type Backend = service::LightBackend<Factory>;
}

impl Components for service::FullComponents<Factory> {
	type Api = service::FullClient<Factory>;
	type Executor = service::FullExecutor<Factory>;
	type Backend = service::FullBackend<Factory>;
}

/// All configuration for the polkadot node.
pub type Configuration = FactoryFullConfiguration<Factory>;

/// Polkadot-specific configuration.
#[derive(Default)]
pub struct CustomConfiguration {
	/// Set to `Some` with a collator `AccountId` and desired parachain
	/// if the network protocol should be started in collator mode.
	pub collating_for: Option<(AccountId, parachain::Id)>,
}

/// Polkadot config for the substrate service.
pub struct Factory;

impl service::ServiceFactory for Factory {
	type Block = Block;
	type NetworkProtocol = PolkadotProtocol;
	type RuntimeDispatch = polkadot_executor::Executor;
	type FullExtrinsicPool = TransactionPoolAdapter<
		service::FullBackend<Self>,
		service::FullExecutor<Self>,
		service::FullClient<Self>
	>;
	type LightExtrinsicPool = TransactionPoolAdapter<
		service::LightBackend<Self>,
		service::LightExecutor<Self>,
		RemotePolkadotApiWrapper<service::LightBackend<Self>, service::LightExecutor<Self>>
	>;
	type Genesis = GenesisConfig;
	type Configuration = CustomConfiguration;

	const NETWORK_PROTOCOL_ID: network::ProtocolId = ::polkadot_network::DOT_PROTOCOL_ID;

	fn build_full_extrinsic_pool(config: ExtrinsicPoolOptions, client: Arc<service::FullClient<Self>>)
		-> Result<Self::FullExtrinsicPool, Error>
	{
		let api = client.clone();
		Ok(TransactionPoolAdapter {
			pool: Arc::new(TransactionPool::new(config, api)),
			client: client,
			imports_external_transactions: true,
		})
	}

	fn build_light_extrinsic_pool(config: ExtrinsicPoolOptions, client: Arc<service::LightClient<Self>>)
		-> Result<Self::LightExtrinsicPool, Error>
	{
		let api = Arc::new(RemotePolkadotApiWrapper(client.clone()));
		Ok(TransactionPoolAdapter {
			pool: Arc::new(TransactionPool::new(config, api)),
			client: client,
			imports_external_transactions: false,
		})
	}

	fn build_network_protocol(config: &Configuration)
		-> Result<PolkadotProtocol, Error>
	{
		if let Some((_, ref para_id)) = config.custom.collating_for {
			info!("Starting network in Collator mode for parachain {:?}", para_id);
		}
		Ok(PolkadotProtocol::new(config.custom.collating_for))
	}
}

/// Polkadot service.
pub struct Service<C: Components> {
	inner: service::Service<C>,
	client: Arc<ComponentClient<C>>,
	network: Arc<NetworkService>,
	api: Arc<<C as Components>::Api>,
	_consensus: Option<consensus::Service>,
}

impl <C: Components> Service<C> {
	pub fn client(&self) -> Arc<ComponentClient<C>> {
		self.client.clone()
	}

	pub fn network(&self) -> Arc<NetworkService> {
		self.network.clone()
	}

	pub fn api(&self) -> Arc<<C as Components>::Api> {
		self.api.clone()
	}
}

/// Creates light client and register protocol with the network service
pub fn new_light(config: Configuration, executor: TaskExecutor)
	-> Result<Service<LightComponents<Factory>>, Error>
{
	let service = service::Service::<LightComponents<Factory>>::new(config, executor)?;
	let api = Arc::new(RemotePolkadotApiWrapper(service.client()));
	Ok(Service {
		client: service.client(),
		network: service.network(),
		api: api,
		inner: service,
		_consensus: None,
	})
}

/// Creates full client and register protocol with the network service
pub fn new_full(config: Configuration, executor: TaskExecutor)
	-> Result<Service<FullComponents<Factory>>, Error>
{
	let is_validator = (config.roles & Roles::AUTHORITY) == Roles::AUTHORITY;
	let service = service::Service::<FullComponents<Factory>>::new(config, executor.clone())?;
	// Spin consensus service if configured
	let consensus = if is_validator {
		// Load the first available key
		let key = service.keystore().load(&service.keystore().contents()?[0], "")?;
		info!("Using authority key {}", key.public());

		let client = service.client();

		let consensus_net = ConsensusNetwork::new(service.network(), client.clone());
		Some(consensus::Service::new(
			client.clone(),
			client.clone(),
			consensus_net,
			service.extrinsic_pool(),
			executor,
			::std::time::Duration::from_secs(4), // TODO: dynamic
			key,
		))
	} else {
		None
	};

	Ok(Service {
		client: service.client(),
		network: service.network(),
		api: service.client(),
		inner: service,
		_consensus: consensus,
	})
}

/// Creates bare client without any networking.
pub fn new_client(config: Configuration)
-> Result<Arc<service::ComponentClient<FullComponents<Factory>>>, Error>
{
	service::new_client::<Factory>(config)
}

impl<C: Components> ::std::ops::Deref for Service<C> {
	type Target = service::Service<C>;

	fn deref(&self) -> &Self::Target {
		&self.inner
	}
}

/// Transaction pool adapter.
pub struct TransactionPoolAdapter<B, E, A> where A: Send + Sync, E: Send + Sync {
	imports_external_transactions: bool,
	pool: Arc<TransactionPool<A>>,
	client: Arc<Client<B, E, Block>>,
}

impl<B, E, A> TransactionPoolAdapter<B, E, A>
	where
		A: Send + Sync,
		B: client::backend::Backend<Block> + Send + Sync,
		E: client::CallExecutor<Block> + Send + Sync,
{
	fn best_block_id(&self) -> Option<BlockId> {
		self.client.info()
			.map(|info| BlockId::hash(info.chain.best_hash))
			.map_err(|e| {
				debug!("Error getting best block: {:?}", e);
			})
			.ok()
	}
}

impl<B, E, A> network::TransactionPool<Block> for TransactionPoolAdapter<B, E, A>
	where
		B: client::backend::Backend<Block> + Send + Sync,
		E: client::CallExecutor<Block> + Send + Sync,
		A: polkadot_api::PolkadotApi + Send + Sync,
{
	fn transactions(&self) -> Vec<(Hash, Vec<u8>)> {
		let best_block_id = match self.best_block_id() {
			Some(id) => id,
			None => return vec![],
		};
		self.pool.cull_and_get_pending(best_block_id, |pending| pending
			.map(|t| {
				let hash = t.hash().clone();
				(hash, t.primitive_extrinsic())
			})
			.collect()
		).unwrap_or_else(|e| {
			warn!("Error retrieving pending set: {}", e);
			vec![]
		})
	}

	fn import(&self, transaction: &Vec<u8>) -> Option<Hash> {
		if !self.imports_external_transactions {
			return None;
		}

		let encoded = transaction.encode();
		if let Some(uxt) = codec::Decode::decode(&mut &encoded[..]) {
			let best_block_id = self.best_block_id()?;
			match self.pool.import_unchecked_extrinsic(best_block_id, uxt) {
				Ok(xt) => Some(*xt.hash()),
				Err(e) => match *e.kind() {
					transaction_pool::ErrorKind::AlreadyImported(hash) => Some(hash[..].into()),
					_ => {
						debug!(target: "txpool", "Error adding transaction to the pool: {:?}", e);
						None
					},
				}
			}
		} else {
			debug!(target: "txpool", "Error decoding transaction");
			None
		}
	}

	fn on_broadcasted(&self, propagations: HashMap<Hash, Vec<String>>) {
		self.pool.on_broadcasted(propagations)
	}
}

impl<B, E, A> service::ExtrinsicPool<Block> for TransactionPoolAdapter<B, E, A>
	where
		B: client::backend::Backend<Block> + Send + Sync + 'static,
		E: client::CallExecutor<Block> + Send + Sync + 'static,
		A: polkadot_api::PolkadotApi + Send + Sync + 'static,
{
	type Api = TransactionPool<A>;

	fn prune_imported(&self, hash: &Hash) {
		let block = BlockId::hash(*hash);
		if let Err(e) = self.pool.cull(block) {
			warn!("Culling error: {:?}", e);
		}

		if let Err(e) = self.pool.retry_verification(block) {
			warn!("Re-verifying error: {:?}", e);
		}
	}

	fn api(&self) -> Arc<Self::Api> {
		self.pool.clone()
	}
}

