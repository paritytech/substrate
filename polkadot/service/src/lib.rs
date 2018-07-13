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
extern crate substrate_keystore as keystore;
extern crate substrate_primitives as primitives;
extern crate substrate_runtime_primitives as runtime_primitives;
extern crate substrate_network as network;
extern crate substrate_codec as codec;
extern crate substrate_client as client;
extern crate substrate_client_db as client_db;
extern crate substrate_service as service;
extern crate tokio;

#[macro_use]
extern crate log;
#[macro_use]
extern crate hex_literal;

pub mod chain_spec;

use std::sync::Arc;
use std::collections::HashMap;

use codec::Slicable;
use transaction_pool::TransactionPool;
use keystore::Store as Keystore;
use polkadot_api::light::RemotePolkadotApiWrapper;
use polkadot_primitives::{Block, BlockId, Hash};
use runtime_primitives::traits::Block as BlockT;
use polkadot_runtime::GenesisConfig;
use client::Client;
use polkadot_network::PolkadotProtocol;
use tokio::runtime::TaskExecutor;
use network::OnDemand;

pub use service::{Configuration, Role, PruningMode, ExtrinsicPoolOptions,
	ErrorKind, Error, ComponentBlock};

pub type ChainSpec = service::ChainSpec<GenesisConfig>;

struct FullComponents;
struct LightComponents;

/*
pub trait PolkadotComponents: service::Components<Factory=Factory>
where
	<Self as service::Components>::Executor: client::CallExecutor<Block>,
	<Self as service::Components>::Backend: client::backend::Backend<Block>,
	<Self as service::Components>::ExtrinsicPool: service::ExtrinsicPool<Block>,
	<<Self as service::Components>::ExtrinsicPool as service::ExtrinsicPool<Block>>::Api:
		service::ExtrinsicPoolApi<<Block as BlockT>::Extrinsic, BlockId, <Block as BlockT>::Hash>
{

}

impl PolkadotComponents for service::FullComponents<Factory>
where
	<Self as service::Components>::Executor: client::CallExecutor<Block>,
	<Self as service::Components>::Backend: client::backend::Backend<Block>,
	<Self as service::Components>::ExtrinsicPool: service::ExtrinsicPool<Block>,
	<<Self as service::Components>::ExtrinsicPool as service::ExtrinsicPool<Block>>::Api:
		service::ExtrinsicPoolApi<<Block as BlockT>::Extrinsic, BlockId, <Block as BlockT>::Hash>
{

}

impl PolkadotComponents for service::LightComponents<Factory>
where
	<Self as service::Components>::Executor: client::CallExecutor<Block>,
	<Self as service::Components>::Backend: client::backend::Backend<Block>,
	<Self as service::Components>::ExtrinsicPool: service::ExtrinsicPool<Block>,
	<<Self as service::Components>::ExtrinsicPool as service::ExtrinsicPool<Block>>::Api:
		service::ExtrinsicPoolApi<<Block as BlockT>::Extrinsic, BlockId, <Block as BlockT>::Hash>
{

}
*/
/*
impl PolkadotComponents for service::Components<Factory=Factory> {
}
*/


pub type ComponentClient<C> = Client<<C as Components>::Backend, <C as Components>::Executor, Block>;

pub trait Components: service::Components {
	type Backend: 'static + client::backend::Backend<Block>;
	type Executor: 'static + client::CallExecutor<Block> + Send + Sync;
	type ExtrinsicPool: service::ExtrinsicPool<Block>;

	/// Create client.
	fn build_client(settings: client_db::DatabaseSettings, executor: service::CodeExecutor<Factory>, chain_spec: &ChainSpec)
		-> Result<(Arc<ComponentClient<Self>>, Option<Arc<OnDemand<Block, service::NetworkService<Factory>>>>), Error>;

	fn build_extrinsic_pool(config: ExtrinsicPoolOptions, client: Arc<ComponentClient<Self>>) -> Result<<Self as Components>::ExtrinsicPool, Error>;
}

impl Components for FullComponents {
	type Executor = <service::FullComponents<Factory> as service::Components>::Executor;
	type Backend = <service::FullComponents<Factory> as service::Components>::Backend;
	type ExtrinsicPool = <service::FullComponents<Factory> as service::Components>::ExtrinsicPool;

	fn build_client(settings: client_db::DatabaseSettings, executor: service::CodeExecutor<Factory>, chain_spec: &ChainSpec)
		-> Result<(Arc<ComponentClient<Self>>, Option<Arc<OnDemand<Block, service::NetworkService<Factory>>>>), Error> {
			service::FullComponents::<Factory>::build_client()
		}

	fn build_extrinsic_pool(config: ExtrinsicPoolOptions, client: Arc<ComponentClient<Self>>) -> Result<<Self as Components>::ExtrinsicPool, Error> {
		service::FullComponents::<Factory>::build_extrinsic_pool(config, client)
	}
}

impl Components for LightComponents {
	type Executor = <service::LightComponents<Factory> as service::Components>::Executor;
	type Backend = <service::LightComponents<Factory> as service::Components>::Backend;
	type ExtrinsicPool = <service::LightComponents<Factory> as service::Components>::ExtrinsicPool;

	fn build_client(settings: client_db::DatabaseSettings, executor: service::CodeExecutor<Factory>, chain_spec: &ChainSpec)
		-> Result<(Arc<ComponentClient<Self>>, Option<Arc<OnDemand<Block, service::NetworkService<Factory>>>>), Error> {
			service::LightComponents::<Factory>::build_client()
		}

	fn build_extrinsic_pool(config: ExtrinsicPoolOptions, client: Arc<ComponentClient<Self>>) -> Result<<Self as Components>::ExtrinsicPool, Error> {
		service::LightComponents::<Factory>::build_extrinsic_pool(config, client)
	}
}

impl service::Components for LightComponents {
	type Executor = <service::LightComponents<Factory> as service::Components>::Executor;
	type Backend = <service::LightComponents<Factory> as service::Components>::Backend;
	type ExtrinsicPool = <service::LightComponents<Factory> as service::Components>::ExtrinsicPool;

	fn build_client(settings: client_db::DatabaseSettings, executor: service::CodeExecutor<Factory>, chain_spec: &ChainSpec)
		-> Result<(Arc<ComponentClient<Self>>, Option<Arc<OnDemand<Block, service::NetworkService<Factory>>>>), Error> {
			service::LightComponents::<Factory>::build_client()
		}

	fn build_extrinsic_pool(config: ExtrinsicPoolOptions, client: Arc<ComponentClient<Self>>) -> Result<Self::ExtrinsicPool, Error> {
		service::LightComponents::<Factory>::build_extrinsic_pool(config, client)
	}
}

impl service::Components for FullComponents {
	type Executor = <service::FullComponents<Factory> as service::Components>::Executor;
	type Backend = <service::FullComponents<Factory> as service::Components>::Backend;
	type ExtrinsicPool = <service::FullComponents<Factory> as service::Components>::ExtrinsicPool;

	fn build_client(settings: client_db::DatabaseSettings, executor: service::CodeExecutor<Factory>, chain_spec: &ChainSpec)
		-> Result<(Arc<ComponentClient<Self>>, Option<Arc<OnDemand<Block, service::NetworkService<Factory>>>>), Error> {
			service::FullComponents::<Factory>::build_client()
		}

	fn build_extrinsic_pool(config: ExtrinsicPoolOptions, client: Arc<ComponentClient<Self>>) -> Result<Self::ExtrinsicPool, Error> {
		service::FullComponents::<Factory>::build_extrinsic_pool(config, client)
	}
}

/*
impl<T:Components> service::Components for T {
	type Factory = Factory;
	type Executor = T::Executor;
	type Backend = T::Backend;
	type ExtrinsicPool = T::ExtrinsicPool;

	fn build_client(db_settings: client_db::DatabaseSettings, executor: service::CodeExecutor<Factory>, chain_spec: &ChainSpec)
		-> Result<(Arc<service::ComponentClient<Self>>, Option<Arc<OnDemand<service::FactoryBlock<Self::Factory>, service::NetworkService<Factory>>>>), Error> {
			<Self as Components>::build_client(db_settings, executor, chain_spec)
		}

	fn build_extrinsic_pool(config: ExtrinsicPoolOptions, client: Arc<service::ComponentClient<Self>>) -> Result<Self::ExtrinsicPool, Error> {
		<Self as Components>::build_extrinsic_pool(config, client)
	}
}
*/

/// Polkadot config for substrate service.
pub struct Factory;

impl service::ServiceFactory for Factory {
	type Block = Block;
	type NetworkProtocol = PolkadotProtocol;
	type RuntimeDispatch = polkadot_executor::Executor;
	type FullExtrinsicPool = TransactionPoolAdapter<service::FullBackend<Self>, service::FullExecutor<Self>, service::FullClient<Self>>;
	type LightExtrinsicPool = TransactionPoolAdapter<service::LightBackend<Self>, service::LightExecutor<Self>, RemotePolkadotApiWrapper<service::LightBackend<Self>, service::LightExecutor<Self>>>;
	type Genesis = GenesisConfig;

	const NETWORK_PROTOCOL_ID: network::ProtocolId = ::polkadot_network::DOT_PROTOCOL_ID;

	fn build_full_extrinsic_pool(config: ExtrinsicPoolOptions, client: Arc<service::FullClient<Self>>) -> Result<Self::FullExtrinsicPool, Error> {
		let api = client.clone();
		Ok(TransactionPoolAdapter {
			pool: Arc::new(TransactionPool::new(config, api)),
			client: client,
			imports_external_transactions: true,
		})
	}

	fn build_light_extrinsic_pool(config: ExtrinsicPoolOptions, client: Arc<service::LightClient<Self>>) -> Result<Self::LightExtrinsicPool, Error> {
		let api = Arc::new(RemotePolkadotApiWrapper(client.clone()));
		Ok(TransactionPoolAdapter {
			pool: Arc::new(TransactionPool::new(config, api)),
			client: client,
			imports_external_transactions: false,
		})
	}
}

/// Polkadot service.
pub struct Service<C: Components> {
	inner: service::Service<C>,
	_consensus: Option<consensus::Service>,
}

/// Creates light client and register protocol with the network service
pub fn new_light(config: Configuration<GenesisConfig>, executor: TaskExecutor) -> Result<Service<LightComponents>, Error> {
	let service = service::Service::<LightComponents>::new(config, executor)?;
	Ok(Service {
		inner: service,
		_consensus: None,
	})
}

/// Creates full client and register protocol with the network service
pub fn new_full(config: Configuration<GenesisConfig>, executor: TaskExecutor) -> Result<Service<FullComponents>, Error> {
	let keystore_path = config.keystore_path.clone();
	let is_validator = (config.roles & Role::AUTHORITY) == Role::AUTHORITY;
	let service = service::Service::<FullComponents>::new(config, executor.clone())?;
	let consensus = if is_validator {
		// Spin consensus service if configured
		let keystore = Keystore::open(keystore_path.into())?;
		// Load the first available key
		let key = keystore.load(&keystore.contents()?[0], "")?;
		info!("Using authority key {}", key.public());

		let client = service.client();

		let consensus_net = ::polkadot_network::consensus::ConsensusNetwork::new(service.network(), client.clone());
		Some(consensus::Service::new(
			client.clone(),
			client.clone(),
			consensus_net,
			service.extrinsic_pool(),
			executor,
			::std::time::Duration::from_millis(4000), // TODO: dynamic
			key,
		))
	} else {
		None
	};

	Ok(Service {
		inner: service,
		_consensus: consensus,
	})
}

/// Creates bare client without any networking.
pub fn new_client(config: Configuration<GenesisConfig>)
-> Result<Arc<ComponentClient<FullComponents>>, Error>
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
		if let Some(uxt) = codec::Slicable::decode(&mut &encoded[..]) {
			let best_block_id = self.best_block_id()?;
			match self.pool.import_unchecked_extrinsic(best_block_id, uxt) {
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

