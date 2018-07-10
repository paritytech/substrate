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
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.?

//! Polkadot service components.

use std::sync::Arc;
use std::marker::PhantomData;
use chain_spec::ChainSpec;
use client_db;
use client::{self, Client};
use error;
use network::{self, OnDemand};
use substrate_executor::{NativeExecutor, NativeExecutionDispatch};
use extrinsic_pool::txpool::{Options as ExtrinsicPoolOptions};
use runtime_primitives::traits::Block as BlockT;
use futures::sync::mpsc;
use RuntimeGenesis;

/// Code executor.

pub trait ExtrinsicPool<Block: BlockT>: Send + Sync + Clone + 'static {
	type Pool;

	fn prune_imported(&self, hash: &Block::Hash);
	fn as_network_pool(&self) -> Arc<network::TransactionPool<Block>>;
	fn as_pool(&self) -> Arc<Self::Pool>;
	fn import_notification_stream(&self) -> mpsc::UnboundedReceiver<()>;
}

// Type aliases
pub type NetworkService<F> = network::Service<<F as ServiceFactory>::Block, <F as ServiceFactory>::NetworkProtocol>;
pub type CodeExecutor<F> =  NativeExecutor<<F as ServiceFactory>::RuntimeDispatch>;
pub type FullBackend<F> = client_db::Backend<<F as ServiceFactory>::Block>;
pub type FullExecutor<F> = client::LocalCallExecutor<client_db::Backend<<F as ServiceFactory>::Block>, CodeExecutor<F>>;
pub type LightBackend<F> = client::light::backend::Backend<client_db::light::LightStorage<<F as ServiceFactory>::Block>, network::OnDemand<<F as ServiceFactory>::Block, NetworkService<F>>>;
pub type LightExecutor<F> = client::light::call_executor::RemoteCallExecutor<
	client::light::blockchain::Blockchain<client_db::light::LightStorage<<F as ServiceFactory>::Block>, network::OnDemand<<F as ServiceFactory>::Block, NetworkService<F>>>,
	network::OnDemand<<F as ServiceFactory>::Block, NetworkService<F>>>;
pub type FullClient<F> = Client<FullBackend<F>, FullExecutor<F>, <F as ServiceFactory>::Block>;
pub type LightClient<F> = Client<LightBackend<F>, LightExecutor<F>, <F as ServiceFactory>::Block>;
pub type FactoryChainSpec<F> = ChainSpec<<F as ServiceFactory>::Genesis>;
pub type FactoryExtrinsicPool<F> = <F as ServiceFactory>::ExtrinsicPool;
pub type FactoryBlock<F> = <F as ServiceFactory>::Block;
pub type SharedPool<F> = <<F as ServiceFactory>::ExtrinsicPool as ExtrinsicPool<<F as ServiceFactory>::Block>>::Pool;
pub type ComponentClient<C> = Client<<C as Components>::Backend, <C as Components>::Executor, FactoryBlock<<C as Components>::Factory>>;
pub type ComponentBlock<C> = <<C as Components>::Factory as ServiceFactory>::Block;

pub trait ServiceFactory {
	type Block: BlockT;
	type NetworkProtocol: network::specialization::Specialization<Self::Block> + Default;
	type RuntimeDispatch: NativeExecutionDispatch + Send + Sync + 'static;
	type ExtrinsicPool: ExtrinsicPool<Self::Block>;
	type Genesis: RuntimeGenesis;

	const NETWORK_PROTOCOL_ID: network::ProtocolId;

	fn build_full_extrinsic_pool(config: &ExtrinsicPoolOptions, client: Arc<FullClient<Self>>) -> Result<Self::ExtrinsicPool, error::Error>;
	fn build_light_extrinsic_pool(config: &ExtrinsicPoolOptions, client: Arc<LightClient<Self>>) -> Result<Self::ExtrinsicPool, error::Error>;
}

pub trait Components {
	type Factory: ServiceFactory;
	type Backend: 'static + client::backend::Backend<FactoryBlock<Self::Factory>>;
	type Executor: 'static + client::CallExecutor<FactoryBlock<Self::Factory>> + Send + Sync;

	/// Create client.
	fn build_client(settings: client_db::DatabaseSettings, executor: CodeExecutor<Self::Factory>, chain_spec: &FactoryChainSpec<Self::Factory>)
		-> Result<(Arc<ComponentClient<Self>>, Option<Arc<OnDemand<FactoryBlock<Self::Factory>, NetworkService<Self::Factory>>>>), error::Error>;

	fn build_extrinsic_pool(config: &ExtrinsicPoolOptions, client: Arc<ComponentClient<Self>>) -> Result<FactoryExtrinsicPool<Self::Factory>, error::Error>;
}

pub struct FullComponents<Factory: ServiceFactory> {
	_factory: PhantomData<Factory>,
}

impl<Factory: ServiceFactory> Components for FullComponents<Factory> {
	type Factory = Factory;
	type Executor = FullExecutor<Factory>;
	type Backend = FullBackend<Factory>;

	fn build_client(db_settings: client_db::DatabaseSettings, executor: CodeExecutor<Self::Factory>, chain_spec: &FactoryChainSpec<Self::Factory>)
		-> Result<(Arc<ComponentClient<Self>>, Option<Arc<OnDemand<FactoryBlock<Self::Factory>, NetworkService<Self::Factory>>>>), error::Error> {
		Ok((Arc::new(client_db::new_client(db_settings, executor, chain_spec)?), None))
	}

	fn build_extrinsic_pool(config: &ExtrinsicPoolOptions, client: Arc<ComponentClient<Self>>) -> Result<FactoryExtrinsicPool<Self::Factory>, error::Error> {
		Factory::build_full_extrinsic_pool(config, client)
	}
}

pub struct LightComponents<Factory: ServiceFactory> {
	_factory: PhantomData<Factory>,
}

impl<Factory: ServiceFactory> Components for LightComponents<Factory> {
	type Factory = Factory;
	type Executor = LightExecutor<Factory>;
	type Backend = LightBackend<Factory>;

	fn build_client(db_settings: client_db::DatabaseSettings, executor: CodeExecutor<Self::Factory>, spec: &FactoryChainSpec<Self::Factory>)
		-> Result<(Arc<ComponentClient<Self>>, Option<Arc<OnDemand<FactoryBlock<Self::Factory>, NetworkService<Self::Factory>>>>), error::Error> {
		let db_storage = client_db::light::LightStorage::new(db_settings)?;
		let light_blockchain = client::light::new_light_blockchain(db_storage);
		let fetch_checker = Arc::new(client::light::new_fetch_checker(light_blockchain.clone(), executor));
		let fetcher = Arc::new(network::OnDemand::new(fetch_checker));
		let client_backend = client::light::new_light_backend(light_blockchain, fetcher.clone());
		let client = client::light::new_light(client_backend, fetcher.clone(), spec)?;
		Ok((Arc::new(client), Some(fetcher)))
	}

	fn build_extrinsic_pool(config: &ExtrinsicPoolOptions, client: Arc<ComponentClient<Self>>) -> Result<FactoryExtrinsicPool<Self::Factory>, error::Error> {
		Factory::build_light_extrinsic_pool(config, client)
	}
}

