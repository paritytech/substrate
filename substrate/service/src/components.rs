// Copyright 2017 Parity Technologies (UK) Ltd.
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

//! Polkadot service components.

use std::sync::Arc;
use std::marker::PhantomData;
use serde::{Serialize, de::DeserializeOwned};
use chain_spec::ChainSpec;
use client_db;
use client::{self, Client};
use error;
use network::{self, OnDemand};
use substrate_executor::{NativeExecutor, NativeExecutionDispatch};
use extrinsic_pool::{txpool::Options as ExtrinsicPoolOptions, api::ExtrinsicPool as ExtrinsicPoolApi};
use runtime_primitives::{traits::Block as BlockT, traits::Header as HeaderT, generic::BlockId, BuildStorage};
use config::Configuration;

// Type aliases.
// These exist mainly to avoid typing `<F as Factory>::Foo` all over the code.
/// Network service type for a factory.
pub type NetworkService<F> = network::Service<
	<F as ServiceFactory>::Block,
	<F as ServiceFactory>::NetworkProtocol
>;

/// Code executor type for a factory.
pub type CodeExecutor<F> =  NativeExecutor<<F as ServiceFactory>::RuntimeDispatch>;

/// Full client backend type for a factory.
pub type FullBackend<F> = client_db::Backend<<F as ServiceFactory>::Block>;

/// Full client executor type for a factory.
pub type FullExecutor<F> = client::LocalCallExecutor<
	client_db::Backend<<F as ServiceFactory>::Block>,
	CodeExecutor<F>
>;

/// Light client backend type for a factory.
pub type LightBackend<F> = client::light::backend::Backend<
	client_db::light::LightStorage<<F as ServiceFactory>::Block>,
	network::OnDemand<<F as ServiceFactory>::Block,
	NetworkService<F>>
>;

/// Light client executor type for a factory.
pub type LightExecutor<F> = client::light::call_executor::RemoteCallExecutor<
	client::light::blockchain::Blockchain<
		client_db::light::LightStorage<<F as ServiceFactory>::Block>,
		network::OnDemand<<F as ServiceFactory>::Block, NetworkService<F>>
	>,
	network::OnDemand<<F as ServiceFactory>::Block, NetworkService<F>>
>;

/// Full client type for a factory.
pub type FullClient<F> = Client<FullBackend<F>, FullExecutor<F>, <F as ServiceFactory>::Block>;

/// Light client type for a factory.
pub type LightClient<F> = Client<LightBackend<F>, LightExecutor<F>, <F as ServiceFactory>::Block>;

/// `ChainSpec` specialization for a factory.
pub type FactoryChainSpec<F> = ChainSpec<<F as ServiceFactory>::Genesis>;

/// `Genesis` specialization for a factory.
pub type FactoryGenesis<F> = <F as ServiceFactory>::Genesis;

/// `Block` type for a factory.
pub type FactoryBlock<F> = <F as ServiceFactory>::Block;

/// `Number` type for a factory.
pub type FactoryBlockNumber<F> = <<FactoryBlock<F> as BlockT>::Header as HeaderT>::Number;

/// Full `Configuration` type for a factory.
pub type FactoryFullConfiguration<F> = Configuration<<F as ServiceFactory>::Configuration, FactoryGenesis<F>>;

/// Client type for `Components`.
pub type ComponentClient<C> = Client<
	<C as Components>::Backend,
	<C as Components>::Executor,
	FactoryBlock<<C as Components>::Factory>
>;

/// Block type for `Components`
pub type ComponentBlock<C> = <<C as Components>::Factory as ServiceFactory>::Block;

/// Extrinsic pool API type for `Components`.
pub type PoolApi<C> = <<C as Components>::ExtrinsicPool as ExtrinsicPool<ComponentBlock<C>>>::Api;

/// A set of traits for the runtime genesis config.
pub trait RuntimeGenesis: Serialize + DeserializeOwned + BuildStorage {}
impl<T: Serialize + DeserializeOwned + BuildStorage> RuntimeGenesis for T {}

/// A collection of types and methods to build a service on top of the substrate service.
pub trait ServiceFactory {
	/// Block type.
	type Block: BlockT;
	/// Network protocol extensions.
	type NetworkProtocol: network::specialization::Specialization<Self::Block>;
	/// Chain runtime.
	type RuntimeDispatch: NativeExecutionDispatch + Send + Sync + 'static;
	/// Extrinsic pool type for the full client.
	type FullExtrinsicPool: ExtrinsicPool<Self::Block>;
	/// Extrinsic pool type for the light client.
	type LightExtrinsicPool: ExtrinsicPool<Self::Block>;
	/// Genesis configuration for the runtime.
	type Genesis: RuntimeGenesis;
	/// Other configuration for service members.
	type Configuration: Default;

	/// Network protocol id.
	const NETWORK_PROTOCOL_ID: network::ProtocolId;

	//TODO: replace these with a constructor trait. that ExtrinsicPool implements.
	/// Extrinsic pool constructor for the full client.
	fn build_full_extrinsic_pool(config: ExtrinsicPoolOptions, client: Arc<FullClient<Self>>)
		-> Result<Self::FullExtrinsicPool, error::Error>;
	/// Extrinsic pool constructor for the light client.
	fn build_light_extrinsic_pool(config: ExtrinsicPoolOptions, client: Arc<LightClient<Self>>)
		-> Result<Self::LightExtrinsicPool, error::Error>;

	/// Build network protocol.
	fn build_network_protocol(config: &FactoryFullConfiguration<Self>)
		-> Result<Self::NetworkProtocol, error::Error>;
}

// TODO: move this to substrate-extrinsic-pool
/// Extrinsic pool bridge.
pub trait ExtrinsicPool<Block: BlockT>: network::TransactionPool<Block> + Send + Sync + 'static {
	type Api: ExtrinsicPoolApi<Block::Extrinsic, BlockId<Block>, Block::Hash>;

	/// Update the pool after a new block has been imported.
	fn prune_imported(&self, hash: &Block::Hash);
	/// Returns underlying API.
	fn api(&self) -> Arc<Self::Api>;
}

/// A collection of types and function to generalise over full / light client type.
pub trait Components {
	/// Associated service factory.
	type Factory: ServiceFactory;
	/// Client backend.
	type Backend: 'static + client::backend::Backend<FactoryBlock<Self::Factory>>;
	/// Client executor.
	type Executor: 'static + client::CallExecutor<FactoryBlock<Self::Factory>> + Send + Sync;
	/// Extrinsic pool type.
	type ExtrinsicPool: ExtrinsicPool<FactoryBlock<Self::Factory>>;

	/// Create client.
	fn build_client(
		config: &FactoryFullConfiguration<Self::Factory>,
		executor: CodeExecutor<Self::Factory>,
	)
		-> Result<(
			Arc<ComponentClient<Self>>,
			Option<Arc<OnDemand<FactoryBlock<Self::Factory>, NetworkService<Self::Factory>>>>
		), error::Error>;

	/// Create extrinsic pool.
	fn build_extrinsic_pool(config: ExtrinsicPoolOptions, client: Arc<ComponentClient<Self>>)
		-> Result<Self::ExtrinsicPool, error::Error>;
}

/// A struct that implement `Components` for the full client.
pub struct FullComponents<Factory: ServiceFactory> {
	_factory: PhantomData<Factory>,
}

impl<Factory: ServiceFactory> Components for FullComponents<Factory> {
	type Factory = Factory;
	type Executor = FullExecutor<Factory>;
	type Backend = FullBackend<Factory>;
	type ExtrinsicPool = <Factory as ServiceFactory>::FullExtrinsicPool;

	fn build_client(
		config: &FactoryFullConfiguration<Factory>,
		executor: CodeExecutor<Self::Factory>,
	)
		-> Result<(
			Arc<ComponentClient<Self>>,
			Option<Arc<OnDemand<FactoryBlock<Self::Factory>, NetworkService<Self::Factory>>>>
		), error::Error>
	{
		let db_settings = client_db::DatabaseSettings {
			cache_size: None,
			path: config.database_path.as_str().into(),
			pruning: config.pruning.clone(),
		};
		Ok((Arc::new(client_db::new_client(db_settings, executor, &config.chain_spec, config.execution_strategy)?), None))
	}

	fn build_extrinsic_pool(config: ExtrinsicPoolOptions, client: Arc<ComponentClient<Self>>)
		-> Result<Self::ExtrinsicPool, error::Error>
	{
		Factory::build_full_extrinsic_pool(config, client)
	}
}

/// A struct that implement `Components` for the light client.
pub struct LightComponents<Factory: ServiceFactory> {
	_factory: PhantomData<Factory>,
}

impl<Factory: ServiceFactory> Components for LightComponents<Factory> {
	type Factory = Factory;
	type Executor = LightExecutor<Factory>;
	type Backend = LightBackend<Factory>;
	type ExtrinsicPool = <Factory as ServiceFactory>::LightExtrinsicPool;

	fn build_client(
		config: &FactoryFullConfiguration<Factory>,
		executor: CodeExecutor<Self::Factory>,
	)
		-> Result<(
			Arc<ComponentClient<Self>>,
			Option<Arc<OnDemand<FactoryBlock<Self::Factory>,
			NetworkService<Self::Factory>>>>
		), error::Error>
	{
		let db_settings = client_db::DatabaseSettings {
			cache_size: None,
			path: config.database_path.as_str().into(),
			pruning: config.pruning.clone(),
		};
		let db_storage = client_db::light::LightStorage::new(db_settings)?;
		let light_blockchain = client::light::new_light_blockchain(db_storage);
		let fetch_checker = Arc::new(client::light::new_fetch_checker(light_blockchain.clone(), executor));
		let fetcher = Arc::new(network::OnDemand::new(fetch_checker));
		let client_backend = client::light::new_light_backend(light_blockchain, fetcher.clone());
		let client = client::light::new_light(client_backend, fetcher.clone(), &config.chain_spec)?;
		Ok((Arc::new(client), Some(fetcher)))
	}

	fn build_extrinsic_pool(config: ExtrinsicPoolOptions, client: Arc<ComponentClient<Self>>)
		-> Result<Self::ExtrinsicPool, error::Error>
	{
		Factory::build_light_extrinsic_pool(config, client)
	}
}
