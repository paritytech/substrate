// Copyright 2018 Parity Technologies (UK) Ltd.
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

#![warn(unused_extern_crates)]

//! Substrate service. Specialized wrapper over substrate service.

extern crate node_api;
extern crate node_primitives;
extern crate node_runtime;
extern crate node_executor;
extern crate node_network;
extern crate node_transaction_pool as transaction_pool;
extern crate node_consensus as consensus;
extern crate substrate_primitives as primitives;
extern crate substrate_network as network;
extern crate substrate_client as client;
extern crate substrate_service as service;
extern crate parity_codec as codec;
extern crate tokio;
#[cfg(test)]
extern crate substrate_service_test as service_test;

#[macro_use]
extern crate log;
#[macro_use]
extern crate hex_literal;
#[cfg(test)]
extern crate parking_lot;
#[cfg(test)]
extern crate substrate_bft as bft;
#[cfg(test)]
extern crate substrate_test_client;

pub mod chain_spec;

use std::sync::Arc;
use codec::Decode;
use transaction_pool::TransactionPool;
use node_api::Api;
use node_primitives::{Block, Hash, Timestamp};
use node_runtime::{GenesisConfig, BlockPeriod, StorageValue, Runtime};
use client::Client;
use node_network::{Protocol as DemoProtocol, consensus::ConsensusNetwork};
use tokio::runtime::TaskExecutor;
use service::FactoryFullConfiguration;
use primitives::{Blake2Hasher, storage::StorageKey, twox_128};

pub use service::{Roles, PruningMode, TransactionPoolOptions, ServiceFactory,
	ErrorKind, Error, ComponentBlock, LightComponents, FullComponents};
pub use client::ExecutionStrategy;

/// Specialised `ChainSpec`.
pub type ChainSpec = service::ChainSpec<GenesisConfig>;
/// Client type for specialised `Components`.
pub type ComponentClient<C> = Client<<C as Components>::Backend, <C as Components>::Executor, Block>;
pub type NetworkService = network::Service<Block, <Factory as service::ServiceFactory>::NetworkProtocol, Hash>;

/// A collection of type to generalise specific components over full / light client.
pub trait Components: service::Components {
	/// Demo API.
	type Api: 'static + Api + Send + Sync;
	/// Client backend.
	type Backend: 'static + client::backend::Backend<Block, Blake2Hasher>;
	/// Client executor.
	type Executor: 'static + client::CallExecutor<Block, Blake2Hasher> + Send + Sync;
}

impl Components for service::LightComponents<Factory> {
	type Api = service::LightClient<Factory>;
	type Executor = service::LightExecutor<Factory>;
	type Backend = service::LightBackend<Factory>;
}

impl Components for service::FullComponents<Factory> {
	type Api = service::FullClient<Factory>;
	type Executor = service::FullExecutor<Factory>;
	type Backend = service::FullBackend<Factory>;
}

/// All configuration for the node.
pub type Configuration = FactoryFullConfiguration<Factory>;

/// Demo-specific configuration.
#[derive(Default)]
pub struct CustomConfiguration;

/// Config for the substrate service.
pub struct Factory;

impl service::ServiceFactory for Factory {
	type Block = Block;
	type ExtrinsicHash = Hash;
	type NetworkProtocol = DemoProtocol;
	type RuntimeDispatch = node_executor::Executor;
	type FullTransactionPoolApi = transaction_pool::ChainApi<service::FullClient<Self>>;
	type LightTransactionPoolApi = transaction_pool::ChainApi<service::LightClient<Self>>;
	type Genesis = GenesisConfig;
	type Configuration = CustomConfiguration;
	type FullService = Service<service::FullComponents<Self>>;
	type LightService = Service<service::LightComponents<Self>>;

	const NETWORK_PROTOCOL_ID: network::ProtocolId = ::node_network::PROTOCOL_ID;

	fn build_full_transaction_pool(config: TransactionPoolOptions, client: Arc<service::FullClient<Self>>)
		-> Result<TransactionPool<service::FullClient<Self>>, Error>
	{
		Ok(TransactionPool::new(config, transaction_pool::ChainApi::new(client)))
	}

	fn build_light_transaction_pool(config: TransactionPoolOptions, client: Arc<service::LightClient<Self>>)
		-> Result<TransactionPool<service::LightClient<Self>>, Error>
	{
		Ok(TransactionPool::new(config, transaction_pool::ChainApi::new(client)))
	}

	fn build_network_protocol(_config: &Configuration)
		-> Result<DemoProtocol, Error>
	{
		Ok(DemoProtocol::new())
	}

	fn new_light(config: Configuration, executor: TaskExecutor)
		-> Result<Service<LightComponents<Factory>>, Error>
	{
		let service = service::Service::<LightComponents<Factory>>::new(config, executor.clone())?;
		Ok(Service {
			inner: service,
			_consensus: None,
		})
	}

	fn new_full(config: Configuration, executor: TaskExecutor)
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
			let block_delay = client.storage(&client.best_block_id()?, &StorageKey(twox_128(BlockPeriod::<Runtime>::key()).to_vec()))?
				.and_then(|data| Timestamp::decode(&mut data.0.as_slice()))
				.unwrap_or_else(|| {
					warn!("Block period is missing in the storage.");
					5
				});
			Some(consensus::Service::new(
					client.clone(),
					client.clone(),
					consensus_net,
					service.transaction_pool(),
					executor,
					key,
					block_delay,
					))
		} else {
			None
		};

		Ok(Service {
			inner: service,
			_consensus: consensus,
		})
	}
}

/// Demo service.
pub struct Service<C: Components> {
	inner: service::Service<C>,
	_consensus: Option<consensus::Service>,
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

#[cfg(test)]
mod tests {
	use std::sync::Arc;
	use parking_lot::RwLock;
	use {service, service_test, Factory, chain_spec};
	use consensus::{self, OfflineTracker};
	use primitives::ed25519;
	use node_primitives::Block;
	use bft::{Proposer, Environment};
	use node_network::consensus::ConsensusNetwork;
	use substrate_test_client::fake_justify;

	#[test]
	fn test_connectivity() {
		service_test::connectivity::<Factory>(chain_spec::integration_test_config());
	}

	#[test]
	fn test_sync() {
		let alice = Arc::new(ed25519::Pair::from_seed(b"Alice                           "));
		let bob = Arc::new(ed25519::Pair::from_seed(b"Bob                             "));
		let validators = vec![alice.public().0.into(), bob.public().0.into()];
		let keys: Vec<&ed25519::Pair> = vec![&*alice, &*bob];
		let offline = Arc::new(RwLock::new(OfflineTracker::new()));
		let dummy_runtime = ::tokio::runtime::Runtime::new().unwrap();
		let block_factory = |service: &<Factory as service::ServiceFactory>::FullService| {
			let parent_header = service.client().header(&service.client().best_block_id().unwrap()).unwrap().unwrap();
			let consensus_net = ConsensusNetwork::new(service.network(), service.client().clone());
			let proposer_factory = consensus::ProposerFactory {
				client: service.client().clone(),
				transaction_pool: service.transaction_pool().clone(),
				network: consensus_net,
				offline: offline.clone(),
				force_delay: 0,
				handle: dummy_runtime.executor(),
			};
			let (proposer, _, _) = proposer_factory.init(&parent_header, &validators, alice.clone()).unwrap();
			let block = proposer.propose().expect("Error making test block");
			let justification = fake_justify::<Block>(&block.header, &keys);
			let justification = service.client().check_justification(block.header, justification).unwrap();
			(justification, Some(block.extrinsics))
		};
		service_test::sync::<Factory, _>(chain_spec::integration_test_config(), block_factory);
	}

	#[test]
	fn test_consensus() {
		service_test::consensus::<Factory>(chain_spec::integration_test_config(), vec!["Alice".into(), "Bob".into()]);
	}

}
