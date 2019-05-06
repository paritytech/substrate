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

//! Substrate service components.

use std::{sync::Arc, net::SocketAddr, ops::Deref, ops::DerefMut};
use serde::{Serialize, de::DeserializeOwned};
use tokio::runtime::TaskExecutor;
use crate::chain_spec::ChainSpec;
use client_db;
use client::{self, Client, runtime_api};
use crate::{error, Service, maybe_start_server};
use consensus_common::{import_queue::ImportQueue, SelectChain};
use network::{self, OnDemand};
use substrate_executor::{NativeExecutor, NativeExecutionDispatch};
use transaction_pool::txpool::{self, Options as TransactionPoolOptions, Pool as TransactionPool};
use runtime_primitives::{
	BuildStorage, traits::{Block as BlockT, Header as HeaderT, ProvideRuntimeApi}, generic::BlockId
};
use crate::config::Configuration;
use primitives::{Blake2Hasher, H256};
use rpc::{self, apis::system::SystemInfo};
use parking_lot::Mutex;

// Type aliases.
// These exist mainly to avoid typing `<F as Factory>::Foo` all over the code.
/// Network service type for a factory.
pub type NetworkService<F> = network::Service<<F as ServiceFactory>::Block, <F as ServiceFactory>::NetworkProtocol>;

/// Code executor type for a factory.
pub type CodeExecutor<F> = NativeExecutor<<F as ServiceFactory>::RuntimeDispatch>;

/// Full client backend type for a factory.
pub type FullBackend<F> = client_db::Backend<<F as ServiceFactory>::Block>;

/// Full client executor type for a factory.
pub type FullExecutor<F> = client::LocalCallExecutor<
	client_db::Backend<<F as ServiceFactory>::Block>,
	CodeExecutor<F>,
>;

/// Light client backend type for a factory.
pub type LightBackend<F> = client::light::backend::Backend<
	client_db::light::LightStorage<<F as ServiceFactory>::Block>,
	network::OnDemand<<F as ServiceFactory>::Block>,
	Blake2Hasher,
>;

/// Light client executor type for a factory.
pub type LightExecutor<F> = client::light::call_executor::RemoteOrLocalCallExecutor<
	<F as ServiceFactory>::Block,
	client::light::backend::Backend<
		client_db::light::LightStorage<<F as ServiceFactory>::Block>,
		network::OnDemand<<F as ServiceFactory>::Block>,
		Blake2Hasher
	>,
	client::light::call_executor::RemoteCallExecutor<
		client::light::blockchain::Blockchain<
			client_db::light::LightStorage<<F as ServiceFactory>::Block>,
			network::OnDemand<<F as ServiceFactory>::Block>
		>,
		network::OnDemand<<F as ServiceFactory>::Block>
	>,
	client::LocalCallExecutor<
		client::light::backend::Backend<
			client_db::light::LightStorage<<F as ServiceFactory>::Block>,
			network::OnDemand<<F as ServiceFactory>::Block>,
			Blake2Hasher
		>,
		CodeExecutor<F>
	>
>;

/// Full client type for a factory.
pub type FullClient<F> = Client<FullBackend<F>, FullExecutor<F>, <F as ServiceFactory>::Block, <F as ServiceFactory>::RuntimeApi>;

/// Light client type for a factory.
pub type LightClient<F> = Client<LightBackend<F>, LightExecutor<F>, <F as ServiceFactory>::Block, <F as ServiceFactory>::RuntimeApi>;

/// `ChainSpec` specialization for a factory.
pub type FactoryChainSpec<F> = ChainSpec<<F as ServiceFactory>::Genesis>;

/// `Genesis` specialization for a factory.
pub type FactoryGenesis<F> = <F as ServiceFactory>::Genesis;

/// `Block` type for a factory.
pub type FactoryBlock<F> = <F as ServiceFactory>::Block;

/// `Extrinsic` type for a factory.
pub type FactoryExtrinsic<F> = <<F as ServiceFactory>::Block as BlockT>::Extrinsic;

/// `Number` type for a factory.
pub type FactoryBlockNumber<F> = <<FactoryBlock<F> as BlockT>::Header as HeaderT>::Number;

/// Full `Configuration` type for a factory.
pub type FactoryFullConfiguration<F> = Configuration<<F as ServiceFactory>::Configuration, FactoryGenesis<F>>;

/// Client type for `Components`.
pub type ComponentClient<C> = Client<
	<C as Components>::Backend,
	<C as Components>::Executor,
	FactoryBlock<<C as Components>::Factory>,
	<C as Components>::RuntimeApi,
>;

/// Block type for `Components`
pub type ComponentBlock<C> = <<C as Components>::Factory as ServiceFactory>::Block;

/// Extrinsic hash type for `Components`
pub type ComponentExHash<C> = <<C as Components>::TransactionPoolApi as txpool::ChainApi>::Hash;

/// Extrinsic type.
pub type ComponentExtrinsic<C> = <ComponentBlock<C> as BlockT>::Extrinsic;

/// Extrinsic pool API type for `Components`.
pub type PoolApi<C> = <C as Components>::TransactionPoolApi;

/// A set of traits for the runtime genesis config.
pub trait RuntimeGenesis: Serialize + DeserializeOwned + BuildStorage {}
impl<T: Serialize + DeserializeOwned + BuildStorage> RuntimeGenesis for T {}

/// Something that can start the RPC service.
pub trait StartRPC<C: Components> {
	type ServersHandle: Send + Sync;

	fn start_rpc(
		client: Arc<ComponentClient<C>>,
		network: Arc<network::SyncProvider<ComponentBlock<C>>>,
		should_have_peers: bool,
		system_info: SystemInfo,
		rpc_http: Option<SocketAddr>,
		rpc_ws: Option<SocketAddr>,
		rpc_cors: Option<Vec<String>>,
		task_executor: TaskExecutor,
		transaction_pool: Arc<TransactionPool<C::TransactionPoolApi>>,
	) -> error::Result<Self::ServersHandle>;
}

impl<C: Components> StartRPC<Self> for C where
	ComponentClient<C>: ProvideRuntimeApi,
	<ComponentClient<C> as ProvideRuntimeApi>::Api: runtime_api::Metadata<ComponentBlock<C>>,
{
	type ServersHandle = (Option<rpc::HttpServer>, Option<Mutex<rpc::WsServer>>);

	fn start_rpc(
		client: Arc<ComponentClient<C>>,
		network: Arc<network::SyncProvider<ComponentBlock<C>>>,
		should_have_peers: bool,
		rpc_system_info: SystemInfo,
		rpc_http: Option<SocketAddr>,
		rpc_ws: Option<SocketAddr>,
		rpc_cors: Option<Vec<String>>,
		task_executor: TaskExecutor,
		transaction_pool: Arc<TransactionPool<C::TransactionPoolApi>>,
	) -> error::Result<Self::ServersHandle> {
		let handler = || {
			let client = client.clone();
			let subscriptions = rpc::apis::Subscriptions::new(task_executor.clone());
			let chain = rpc::apis::chain::Chain::new(client.clone(), subscriptions.clone());
			let state = rpc::apis::state::State::new(client.clone(), subscriptions.clone());
			let author = rpc::apis::author::Author::new(
				client.clone(), transaction_pool.clone(), subscriptions
			);
			let system = rpc::apis::system::System::new(
				rpc_system_info.clone(), network.clone(), should_have_peers
			);
			rpc::rpc_handler::<ComponentBlock<C>, ComponentExHash<C>, _, _, _, _>(
				state,
				chain,
				author,
				system,
			)
		};

		Ok((
			maybe_start_server(rpc_http, |address| rpc::start_http(address, rpc_cors.as_ref(), handler()))?,
			maybe_start_server(rpc_ws, |address| rpc::start_ws(address, rpc_cors.as_ref(), handler()))?.map(Mutex::new),
		))
	}
}

/// Something that can maintain transaction pool on every imported block.
pub trait MaintainTransactionPool<C: Components> {
	fn maintain_transaction_pool(
		id: &BlockId<ComponentBlock<C>>,
		client: &ComponentClient<C>,
		transaction_pool: &TransactionPool<C::TransactionPoolApi>,
	) -> error::Result<()>;
}

fn maintain_transaction_pool<Api, Backend, Block, Executor, PoolApi>(
	id: &BlockId<Block>,
	client: &Client<Backend, Executor, Block, Api>,
	transaction_pool: &TransactionPool<PoolApi>,
) -> error::Result<()> where
	Block: BlockT<Hash = <Blake2Hasher as ::primitives::Hasher>::Out>,
	Backend: client::backend::Backend<Block, Blake2Hasher>,
	Client<Backend, Executor, Block, Api>: ProvideRuntimeApi,
	<Client<Backend, Executor, Block, Api> as ProvideRuntimeApi>::Api: runtime_api::TaggedTransactionQueue<Block>,
	Executor: client::CallExecutor<Block, Blake2Hasher>,
	PoolApi: txpool::ChainApi<Hash = Block::Hash, Block = Block>,
{
	// Avoid calling into runtime if there is nothing to prune from the pool anyway.
	if transaction_pool.status().is_empty() {
		return Ok(())
	}

	if let Some(block) = client.block(id)? {
		let parent_id = BlockId::hash(*block.block.header().parent_hash());
		let extrinsics = block.block.extrinsics();
		transaction_pool.prune(id, &parent_id, extrinsics).map_err(|e| format!("{:?}", e))?;
	}

	Ok(())
}

impl<C: Components> MaintainTransactionPool<Self> for C where
	ComponentClient<C>: ProvideRuntimeApi,
	<ComponentClient<C> as ProvideRuntimeApi>::Api: runtime_api::TaggedTransactionQueue<ComponentBlock<C>>,
{
	fn maintain_transaction_pool(
		id: &BlockId<ComponentBlock<C>>,
		client: &ComponentClient<C>,
		transaction_pool: &TransactionPool<C::TransactionPoolApi>,
	) -> error::Result<()> {
		maintain_transaction_pool(id, client, transaction_pool)
	}
}

pub trait OffchainWorker<C: Components> {
	fn offchain_workers(
		number: &FactoryBlockNumber<C::Factory>,
		offchain: &offchain::OffchainWorkers<ComponentClient<C>, ComponentBlock<C>>,
		pool: &Arc<TransactionPool<C::TransactionPoolApi>>,
	) -> error::Result<()>;
}

impl<C: Components> OffchainWorker<Self> for C where
	ComponentClient<C>: ProvideRuntimeApi,
	<ComponentClient<C> as ProvideRuntimeApi>::Api: offchain::OffchainWorkerApi<ComponentBlock<C>>,
{
	fn offchain_workers(
		number: &FactoryBlockNumber<C::Factory>,
		offchain: &offchain::OffchainWorkers<ComponentClient<C>, ComponentBlock<C>>,
		pool: &Arc<TransactionPool<C::TransactionPoolApi>>,
	) -> error::Result<()> {
		Ok(offchain.on_block_imported(number, pool))
	}
}

/// The super trait that combines all required traits a `Service` needs to implement.
pub trait ServiceTrait<C: Components>:
	Deref<Target = Service<C>>
	+ Send
	+ Sync
	+ 'static
	+ StartRPC<C>
	+ MaintainTransactionPool<C>
	+ OffchainWorker<C>
{}
impl<C: Components, T> ServiceTrait<C> for T where
	T: Deref<Target = Service<C>>
	+ Send
	+ Sync
	+ 'static
	+ StartRPC<C>
	+ MaintainTransactionPool<C>
	+ OffchainWorker<C>
{}

/// A collection of types and methods to build a service on top of the substrate service.
pub trait ServiceFactory: 'static + Sized {
	/// Block type.
	type Block: BlockT<Hash=H256>;
	/// The type that implements the runtime API.
	type RuntimeApi: Send + Sync;
	/// Network protocol extensions.
	type NetworkProtocol: network::specialization::NetworkSpecialization<Self::Block>;
	/// Chain runtime.
	type RuntimeDispatch: NativeExecutionDispatch + Send + Sync + 'static;
	/// Extrinsic pool backend type for the full client.
	type FullTransactionPoolApi: txpool::ChainApi<Hash = <Self::Block as BlockT>::Hash, Block = Self::Block> + Send + 'static;
	/// Extrinsic pool backend type for the light client.
	type LightTransactionPoolApi: txpool::ChainApi<Hash = <Self::Block as BlockT>::Hash, Block = Self::Block> + 'static;
	/// Genesis configuration for the runtime.
	type Genesis: RuntimeGenesis;
	/// Other configuration for service members.
	type Configuration: Default;
	/// Extended full service type.
	type FullService: ServiceTrait<FullComponents<Self>>;
	/// Extended light service type.
	type LightService: ServiceTrait<LightComponents<Self>>;
	/// ImportQueue for full client
	type FullImportQueue: ImportQueue<Self::Block> + 'static;
	/// ImportQueue for light clients
	type LightImportQueue: ImportQueue<Self::Block> + 'static;
	/// The Fork Choice Strategy for the chain
	type SelectChain: SelectChain<Self::Block> + 'static;

	//TODO: replace these with a constructor trait. that TransactionPool implements. (#1242)
	/// Extrinsic pool constructor for the full client.
	fn build_full_transaction_pool(config: TransactionPoolOptions, client: Arc<FullClient<Self>>)
		-> Result<TransactionPool<Self::FullTransactionPoolApi>, error::Error>;
	/// Extrinsic pool constructor for the light client.
	fn build_light_transaction_pool(config: TransactionPoolOptions, client: Arc<LightClient<Self>>)
		-> Result<TransactionPool<Self::LightTransactionPoolApi>, error::Error>;

	/// Build network protocol.
	fn build_network_protocol(config: &FactoryFullConfiguration<Self>)
		-> Result<Self::NetworkProtocol, error::Error>;

	/// Build the Fork Choice algorithm for full client
	fn build_select_chain(
		config: &mut FactoryFullConfiguration<Self>,
		client: Arc<FullClient<Self>>, 
	) -> Result<Self::SelectChain, error::Error>;

	/// Build full service.
	fn new_full(config: FactoryFullConfiguration<Self>, executor: TaskExecutor)
		-> Result<Self::FullService, error::Error>;
	/// Build light service.
	fn new_light(config: FactoryFullConfiguration<Self>, executor: TaskExecutor)
		-> Result<Self::LightService, error::Error>;

	/// ImportQueue for a full client
	fn build_full_import_queue(
		config: &mut FactoryFullConfiguration<Self>,
		_client: Arc<FullClient<Self>>,
		_select_chain: Self::SelectChain
	) -> Result<Self::FullImportQueue, error::Error> {
		if let Some(name) = config.chain_spec.consensus_engine() {
			match name {
				_ => Err(format!("Chain Specification defines unknown consensus engine '{}'", name).into())
			}

		} else {
			Err("Chain Specification doesn't contain any consensus_engine name".into())
		}
	}

	/// ImportQueue for a light client
	fn build_light_import_queue(
		config: &mut FactoryFullConfiguration<Self>,
		_client: Arc<LightClient<Self>>
	) -> Result<Self::LightImportQueue, error::Error> {
		if let Some(name) = config.chain_spec.consensus_engine() {
			match name {
				_ => Err(format!("Chain Specification defines unknown consensus engine '{}'", name).into())
			}

		} else {
			Err("Chain Specification doesn't contain any consensus_engine name".into())
		}
	}
}

/// A collection of types and function to generalize over full / light client type.
pub trait Components: Sized + 'static {
	/// Associated service factory.
	type Factory: ServiceFactory;
	/// Client backend.
	type Backend: 'static + client::backend::Backend<FactoryBlock<Self::Factory>, Blake2Hasher>;
	/// Client executor.
	type Executor: 'static + client::CallExecutor<FactoryBlock<Self::Factory>, Blake2Hasher> + Send + Sync + Clone;
	/// The type that implements the runtime API.
	type RuntimeApi: Send + Sync;
	/// A type that can start all runtime-dependent services.
	type RuntimeServices: ServiceTrait<Self>;
	// TODO: Traitify transaction pool and allow people to implement their own. (#1242)
	/// Extrinsic pool type.
	type TransactionPoolApi: 'static + txpool::ChainApi<
		Hash = <FactoryBlock<Self::Factory> as BlockT>::Hash,
		Block = FactoryBlock<Self::Factory>
	>;
	/// Our Import Queue
	type ImportQueue: ImportQueue<FactoryBlock<Self::Factory>> + 'static;
	/// The Fork Choice Strategy for the chain
	type SelectChain: SelectChain<FactoryBlock<Self::Factory>>;

	/// Create client.
	fn build_client(
		config: &FactoryFullConfiguration<Self::Factory>,
		executor: CodeExecutor<Self::Factory>,
	) -> Result<
		(
			Arc<ComponentClient<Self>>,
			Option<Arc<OnDemand<FactoryBlock<Self::Factory>>>>
		),
		error::Error
	>;

	/// Create extrinsic pool.
	fn build_transaction_pool(config: TransactionPoolOptions, client: Arc<ComponentClient<Self>>)
		-> Result<TransactionPool<Self::TransactionPoolApi>, error::Error>;

	/// instance of import queue for clients
	fn build_import_queue(
		config: &mut FactoryFullConfiguration<Self::Factory>,
		client: Arc<ComponentClient<Self>>,
		select_chain: Self::SelectChain,
	) -> Result<Self::ImportQueue, error::Error>;

	/// Build fork choice selector
	fn build_select_chain(
		config: &mut FactoryFullConfiguration<Self::Factory>,
		client: Arc<ComponentClient<Self>>
	) -> Result<Self::SelectChain, error::Error>;

}

/// A struct that implement `Components` for the full client.
pub struct FullComponents<Factory: ServiceFactory> {
	service: Service<FullComponents<Factory>>,
}

impl<Factory: ServiceFactory> FullComponents<Factory> {
	/// Create new `FullComponents`
	pub fn new(
		config: FactoryFullConfiguration<Factory>,
		task_executor: TaskExecutor
	) -> Result<Self, error::Error> {
		Ok(
			Self {
				service: Service::new(config, task_executor)?,
			}
		)
	}
}

impl<Factory: ServiceFactory> Deref for FullComponents<Factory> {
	type Target = Service<Self>;

	fn deref(&self) -> &Self::Target {
		&self.service
	}
}

impl<Factory: ServiceFactory> DerefMut for FullComponents<Factory> {
	fn deref_mut(&mut self) -> &mut Service<Self> {
		&mut self.service
	}
}

impl<Factory: ServiceFactory> Components for FullComponents<Factory> {
	type Factory = Factory;
	type Executor = FullExecutor<Factory>;
	type Backend = FullBackend<Factory>;
	type TransactionPoolApi = <Factory as ServiceFactory>::FullTransactionPoolApi;
	type ImportQueue = Factory::FullImportQueue;
	type RuntimeApi = Factory::RuntimeApi;
	type RuntimeServices = Factory::FullService;
	type SelectChain = Factory::SelectChain;

	fn build_client(
		config: &FactoryFullConfiguration<Factory>,
		executor: CodeExecutor<Self::Factory>,
	)
		-> Result<(
			Arc<ComponentClient<Self>>,
			Option<Arc<OnDemand<FactoryBlock<Self::Factory>>>>
		), error::Error>
	{
		let db_settings = client_db::DatabaseSettings {
			cache_size: config.database_cache_size.map(|u| u as usize),
			state_cache_size: config.state_cache_size,
			path: config.database_path.as_str().into(),
			pruning: config.pruning.clone(),
		};
		Ok((Arc::new(client_db::new_client(
			db_settings,
			executor,
			&config.chain_spec,
			config.execution_strategies.clone(),
		)?), None))
	}

	fn build_transaction_pool(
		config: TransactionPoolOptions, 
		client: Arc<ComponentClient<Self>>
	) -> Result<TransactionPool<Self::TransactionPoolApi>, error::Error> {
		Factory::build_full_transaction_pool(config, client)
	}

	fn build_import_queue(
		config: &mut FactoryFullConfiguration<Self::Factory>,
		client: Arc<ComponentClient<Self>>,
		select_chain: Self::SelectChain,
	) -> Result<Self::ImportQueue, error::Error> {
		Factory::build_full_import_queue(config, client, select_chain)
	}

	fn build_select_chain(
		config: &mut FactoryFullConfiguration<Self::Factory>,
		client: Arc<ComponentClient<Self>>
	) -> Result<Self::SelectChain, error::Error> {
		Self::Factory::build_select_chain(config, client)
	}
	
}

/// A struct that implement `Components` for the light client.
pub struct LightComponents<Factory: ServiceFactory> {
	service: Service<LightComponents<Factory>>,
}

impl<Factory: ServiceFactory> LightComponents<Factory> {
	/// Create new `LightComponents`
	pub fn new(
		config: FactoryFullConfiguration<Factory>,
		task_executor: TaskExecutor
	) -> Result<Self, error::Error> {
		Ok(
			Self {
				service: Service::new(config, task_executor)?,
			}
		)
	}
}

impl<Factory: ServiceFactory> Deref for LightComponents<Factory> {
	type Target = Service<Self>;

	fn deref(&self) -> &Self::Target {
		&self.service
	}
}

impl<Factory: ServiceFactory> Components for LightComponents<Factory> {
	type Factory = Factory;
	type Executor = LightExecutor<Factory>;
	type Backend = LightBackend<Factory>;
	type TransactionPoolApi = <Factory as ServiceFactory>::LightTransactionPoolApi;
	type ImportQueue = <Factory as ServiceFactory>::LightImportQueue;
	type RuntimeApi = Factory::RuntimeApi;
	type RuntimeServices = Factory::LightService;
	type SelectChain = Factory::SelectChain;

	fn build_client(
		config: &FactoryFullConfiguration<Factory>,
		executor: CodeExecutor<Self::Factory>,
	)
		-> Result<
			(
				Arc<ComponentClient<Self>>,
				Option<Arc<OnDemand<FactoryBlock<Self::Factory>>>>
			), error::Error>
	{
		let db_settings = client_db::DatabaseSettings {
			cache_size: None,
			state_cache_size: config.state_cache_size,
			path: config.database_path.as_str().into(),
			pruning: config.pruning.clone(),
		};
		let db_storage = client_db::light::LightStorage::new(db_settings)?;
		let light_blockchain = client::light::new_light_blockchain(db_storage);
		let fetch_checker = Arc::new(client::light::new_fetch_checker(light_blockchain.clone(), executor.clone()));
		let fetcher = Arc::new(network::OnDemand::new(fetch_checker));
		let client_backend = client::light::new_light_backend(light_blockchain, fetcher.clone());
		let client = client::light::new_light(client_backend, fetcher.clone(), &config.chain_spec, executor)?;
		Ok((Arc::new(client), Some(fetcher)))
	}

	fn build_transaction_pool(config: TransactionPoolOptions, client: Arc<ComponentClient<Self>>)
		-> Result<TransactionPool<Self::TransactionPoolApi>, error::Error>
	{
		Factory::build_light_transaction_pool(config, client)
	}

	fn build_import_queue(
		config: &mut FactoryFullConfiguration<Self::Factory>,
		client: Arc<ComponentClient<Self>>,
		_select_chain: Self::SelectChain,
	) -> Result<Self::ImportQueue, error::Error> {
		Factory::build_light_import_queue(config, client)
	}

	/// Build fork choice selector
	fn build_select_chain(
		_config: &mut FactoryFullConfiguration<Self::Factory>,
		_client: Arc<ComponentClient<Self>>
	) -> Result<Self::SelectChain, error::Error> {
		Err("Fork choice doesn't happen on light clients.".into())
	}

}

#[cfg(test)]
mod tests {
	use super::*;
	use consensus_common::BlockOrigin;
	use client::LongestChain;
	use substrate_test_client::{self, TestClient, AccountKeyring, runtime::Transfer};

	#[test]
	fn should_remove_transactions_from_the_pool() {
		let client = Arc::new(substrate_test_client::new());
		let pool = TransactionPool::new(Default::default(), ::transaction_pool::ChainApi::new(client.clone()));
		let transaction = Transfer {
			amount: 5,
			nonce: 0,
			from: AccountKeyring::Alice.into(),
			to: Default::default(),
		}.into_signed_tx();
		let best = LongestChain::new(client.backend().clone(), client.import_lock())
			.best_chain().unwrap();

		// store the transaction in the pool
		pool.submit_one(&BlockId::hash(best.hash()), transaction.clone()).unwrap();

		// import the block
		let mut builder = client.new_block().unwrap();
		builder.push(transaction.clone()).unwrap();
		let block = builder.bake().unwrap();
		let id = BlockId::hash(block.header().hash());
		client.import(BlockOrigin::Own, block).unwrap();

		// fire notification - this should clean up the queue
		assert_eq!(pool.status().ready, 1);
		maintain_transaction_pool(
			&id,
			&client,
			&pool,
		).unwrap();

		// then
		assert_eq!(pool.status().ready, 0);
		assert_eq!(pool.status().future, 0);
	}
}
