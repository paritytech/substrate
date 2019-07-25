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

use std::{sync::Arc, ops::Deref, ops::DerefMut};
use serde::{Serialize, de::DeserializeOwned};
use crate::chain_spec::ChainSpec;
use std::time::{Duration, Instant};
use log::{log, warn, Level};
use std::collections::HashSet;
use libp2p::Multiaddr;
use parking_lot::Mutex;
use client::{BlockchainEvents};
use futures03::stream::{StreamExt as _, TryStreamExt as _};
use consensus_aura_primitives::AuraApi;
use offchain::AuthorityKeyProvider as _;
use consensus_common_primitives::ConsensusApi;

use network::{Event, DhtEvent};
use client_db;
use client::{self, Client, runtime_api};
use crate::{error, Service, AuthorityKeyProvider, NetworkStatus};
use consensus_common::{import_queue::ImportQueue, SelectChain};
use network::{self, OnDemand, FinalityProofProvider, NetworkStateInfo, config::BoxFinalityProofRequestBuilder};
use substrate_executor::{NativeExecutor, NativeExecutionDispatch};
use transaction_pool::txpool::{self, Options as TransactionPoolOptions, Pool as TransactionPool};
use sr_primitives::{
	BuildStorage, traits::{Block as BlockT, Header as HeaderT, ProvideRuntimeApi}, generic::BlockId
};

use network::NetworkState;
use crate::config::Configuration;
use primitives::{Blake2Hasher, H256, Pair};
use rpc::{self, apis::system::SystemInfo};
use futures::{prelude::*, future::Executor, sync::mpsc};

// Type aliases.
// These exist mainly to avoid typing `<F as Factory>::Foo` all over the code.

/// Network service type for `Components`.
pub type NetworkService<C> = network::NetworkService<
	ComponentBlock<C>,
	<<C as Components>::Factory as ServiceFactory>::NetworkProtocol,
	ComponentExHash<C>
>;

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
		network::OnDemand<<F as ServiceFactory>::Block>,
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

/// A offchain workers storage backend type.
pub type ComponentOffchainStorage<C> = <
	<C as Components>::Backend as client::backend::Backend<ComponentBlock<C>, Blake2Hasher>
>::OffchainStorage;

/// Block type for `Components`
pub type ComponentBlock<C> = <<C as Components>::Factory as ServiceFactory>::Block;

/// ConsensusPair type for `Components`
pub type ComponentConsensusPair<C> = <<C as Components>::Factory as ServiceFactory>::ConsensusPair;

/// FinalityPair type for `Components`
pub type ComponentFinalityPair<C> = <<C as Components>::Factory as ServiceFactory>::FinalityPair;

/// AuthorityKeyProvider type for `Components`
pub type ComponentAuthorityKeyProvider<C> =
	AuthorityKeyProvider<ComponentBlock<C>, ComponentConsensusPair<C>, ComponentFinalityPair<C>>;

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
	fn start_rpc(
		client: Arc<ComponentClient<C>>,
		system_send_back: mpsc::UnboundedSender<rpc::apis::system::Request<ComponentBlock<C>>>,
		system_info: SystemInfo,
		task_executor: TaskExecutor,
		transaction_pool: Arc<TransactionPool<C::TransactionPoolApi>>,
	) -> rpc::RpcHandler;
}

impl<C: Components> StartRPC<Self> for C where
	ComponentClient<C>: ProvideRuntimeApi,
	<ComponentClient<C> as ProvideRuntimeApi>::Api: runtime_api::Metadata<ComponentBlock<C>>,
{
	fn start_rpc(
		client: Arc<ComponentClient<C>>,
		system_send_back: mpsc::UnboundedSender<rpc::apis::system::Request<ComponentBlock<C>>>,
		rpc_system_info: SystemInfo,
		task_executor: TaskExecutor,
		transaction_pool: Arc<TransactionPool<C::TransactionPoolApi>>,
	) -> rpc::RpcHandler {
		let subscriptions = rpc::apis::Subscriptions::new(task_executor.clone());
		let chain = rpc::apis::chain::Chain::new(client.clone(), subscriptions.clone());
		let state = rpc::apis::state::State::new(client.clone(), subscriptions.clone());
		let author = rpc::apis::author::Author::new(client, transaction_pool, subscriptions);
		let system = rpc::apis::system::System::new(rpc_system_info, system_send_back);
		rpc::rpc_handler::<ComponentBlock<C>, ComponentExHash<C>, _, _, _, _>(
			state,
			chain,
			author,
			system,
		)
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
	Block: BlockT<Hash = <Blake2Hasher as primitives::Hasher>::Out>,
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
		offchain: &offchain::OffchainWorkers<
			ComponentClient<C>,
			ComponentOffchainStorage<C>,
			ComponentAuthorityKeyProvider<C>,
			ComponentBlock<C>
		>,
		pool: &Arc<TransactionPool<C::TransactionPoolApi>>,
		network_state: &Arc<dyn NetworkStateInfo + Send + Sync>,
	) -> error::Result<Box<dyn Future<Item = (), Error = ()> + Send>>;
}

impl<C: Components> OffchainWorker<Self> for C where
	ComponentClient<C>: ProvideRuntimeApi,
	<ComponentClient<C> as ProvideRuntimeApi>::Api: offchain::OffchainWorkerApi<ComponentBlock<C>>,
{
	fn offchain_workers(
		number: &FactoryBlockNumber<C::Factory>,
		offchain: &offchain::OffchainWorkers<
			ComponentClient<C>,
			ComponentOffchainStorage<C>,
			ComponentAuthorityKeyProvider<C>,
			ComponentBlock<C>
		>,
		pool: &Arc<TransactionPool<C::TransactionPoolApi>>,
		network_state: &Arc<dyn NetworkStateInfo + Send + Sync>,
	) -> error::Result<Box<dyn Future<Item = (), Error = ()> + Send>> {
		Ok(Box::new(offchain.on_block_imported(number, pool, network_state.clone())))
	}
}

pub trait NetworkFutureBuilder<C: Components> {
	fn build_network_future<
			H: network::ExHashT,
		S:network::specialization::NetworkSpecialization<ComponentBlock<C>> ,
		>(
		network: network::NetworkWorker<ComponentBlock<C>, S, H >,
		client: Arc<ComponentClient<C>>,
		status_sinks: Arc<Mutex<Vec<mpsc::UnboundedSender<(NetworkStatus<ComponentBlock<C>>, NetworkState)>>>>,
		rpc_rx: mpsc::UnboundedReceiver<rpc::apis::system::Request<ComponentBlock<C>>>,
		should_have_peers: bool,
		// TODO: still needed?
		keystore: ComponentAuthorityKeyProvider<C>,
	)-> Box<dyn Future<Item = (), Error = ()>+ Send>  ;
}

impl<C: Components> NetworkFutureBuilder<Self> for C where
	ComponentClient<C>: ProvideRuntimeApi,
	<ComponentClient<C> as ProvideRuntimeApi>::Api: runtime_api::Metadata<ComponentBlock<C>>,
    // <ComponentClient<C> as ProvideRuntimeApi>::Api: runtime_api::KeyTypeGetter<ComponentBlock<C>>,
	<ComponentClient<C> as ProvideRuntimeApi>::Api: consensus_common_primitives::ConsensusApi<ComponentBlock<C>, <C::Factory as ServiceFactory>::AuthorityId>,
// <ComponentClient<C> as ProvideRuntimeApi>::Api: consensus_babe_primitives::BabeApi<ComponentBlock<C>>,
<<<C as Components>::Factory as ServiceFactory>::ConsensusPair as primitives::crypto::Pair>::Public : std::string::ToString
{
	fn build_network_future<
			H: network::ExHashT,
		S:network::specialization::NetworkSpecialization<ComponentBlock<C>> ,
		>(
		mut network: network::NetworkWorker<ComponentBlock<C>,  S, H>,
		client: Arc<ComponentClient<C>>,
		status_sinks: Arc<Mutex<Vec<mpsc::UnboundedSender<(NetworkStatus<ComponentBlock<C>>, NetworkState)>>>>,
		mut rpc_rx: mpsc::UnboundedReceiver<rpc::apis::system::Request<ComponentBlock<C>>>,
		should_have_peers: bool,
		keystore: ComponentAuthorityKeyProvider<C>,
	)-> Box<dyn Future<Item = (), Error = ()> + Send>  {
		// Interval at which we send status updates on the status stream.
		const STATUS_INTERVAL: Duration = Duration::from_millis(5000);

		let mut status_interval = tokio_timer::Interval::new_interval(STATUS_INTERVAL);

		let mut report_ext_addresses_interval = tokio_timer::Interval::new_interval(Duration::from_secs(5));

		let mut imported_blocks_stream = client.import_notification_stream().fuse()
			.map(|v| Ok::<_, ()>(v)).compat();
		let mut finality_notification_stream = client.finality_notification_stream().fuse()
			.map(|v| Ok::<_, ()>(v)).compat();

		Box::new(futures::future::poll_fn(move || {
		    let before_polling = Instant::now();

			// We poll `imported_blocks_stream`.
			while let Ok(Async::Ready(Some(notification))) = imported_blocks_stream.poll() {
				network.on_block_imported(notification.hash, notification.header);
			}

			while let Ok(Async::Ready(_)) = report_ext_addresses_interval.poll() {
				println!("==== We are connected to {} nodes", network.service().num_connected());
				let id = BlockId::hash( client.info().chain.best_hash);

				// TODO: remove unwrap().
				match keystore.authority_key( &id).map(|k| k.public().to_string()) {
					Some(public_key) => {
						println!("=== authority key: {}", public_key);
						let hashed_public_key = libp2p::multihash::encode(
							libp2p::multihash::Hash::SHA2256,
							&public_key.as_bytes(),
						).unwrap();

						let external_addresses = network.external_addresses();
						println!("==== external addresses: {:?}", external_addresses);

						let enriched_addresses: Vec<Multiaddr> = external_addresses.iter().map(|a| {
							let mut a = a.clone();
							// TODO: Don't get peer id on each iteration.
							a.push(libp2p::core::multiaddr::Protocol::P2p(network.service().peer_id().into()));
							a
						}).collect();

						// TODO: Remove unwrap.
						let serialized_addresses = serde_json::to_string(&enriched_addresses).unwrap();

						// TODO: Sign the payload before putting it on the DHT.
						network.service().put_value(hashed_public_key.clone(), serialized_addresses.as_bytes().to_vec());
					},
					None => {
						println!("==== Got no authority key");
					}
				}

				match client.runtime_api().authorities(&id) {
					Ok(authorities) => {
						for authority in authorities.iter() {
							println!("==== querying dht for authority: {}", authority.to_string());
							// TODO: Remove unwrap.
							let hashed_public_key = libp2p::multihash::encode(
								libp2p::multihash::Hash::SHA2256,
								authority.to_string().as_bytes(),
							).unwrap();

							network.service().get_value(&hashed_public_key.clone());
						}
					},
					Err(e) => {
						println!("==== Got no authorities, but an error: {:?}", e);
					}
				}
			}



			// We poll `finality_notification_stream`, but we only take the last event.
			let mut last = None;
			while let Ok(Async::Ready(Some(item))) = finality_notification_stream.poll() {
				last = Some(item);
			}
			if let Some(notification) = last {
				network.on_block_finalized(notification.hash, notification.header);
			}

			// Poll the RPC requests and answer them.
			while let Ok(Async::Ready(Some(request))) = rpc_rx.poll() {
				match request {
					rpc::apis::system::Request::Health(sender) => {
						let _ = sender.send(rpc::apis::system::Health {
							peers: network.peers_debug_info().len(),
							is_syncing: network.service().is_major_syncing(),
							should_have_peers,
						});
					},
					rpc::apis::system::Request::Peers(sender) => {
						let _ = sender.send(network.peers_debug_info().into_iter().map(|(peer_id, p)|
																					   rpc::apis::system::PeerInfo {
																						   peer_id: peer_id.to_base58(),
																						   roles: format!("{:?}", p.roles),
																						   protocol_version: p.protocol_version,
																						   best_hash: p.best_hash,
																						   best_number: p.best_number,
																					   }
						).collect());
					}
					rpc::apis::system::Request::NetworkState(sender) => {
						let _ = sender.send(network.network_state());
					}
				};
			}

			// Interval report for the external API.
			while let Ok(Async::Ready(_)) = status_interval.poll() {
				let status = NetworkStatus {
					sync_state: network.sync_state(),
					best_seen_block: network.best_seen_block(),
					num_sync_peers: network.num_sync_peers(),
					num_connected_peers: network.num_connected_peers(),
					num_active_peers: network.num_active_peers(),
					average_download_per_sec: network.average_download_per_sec(),
					average_upload_per_sec: network.average_upload_per_sec(),
				};
				let state = network.network_state();

				status_sinks.lock().retain(|sink| sink.unbounded_send((status.clone(), state.clone())).is_ok());
			}

			// Main network polling.
			while let Ok(Async::Ready(Some(Event::Dht(DhtEvent::ValueFound(values))))) = network.poll().map_err(|err| {
				warn!(target: "service", "Error in network: {:?}", err);
			}) {
				for (key, value) in values.iter() {
					let id = BlockId::hash( client.info().chain.best_hash);

					match client.runtime_api().authorities(&id) {
						Ok(authorities) => {
							for authority in authorities.iter() {
								// TODO: Remove unwrap.
								let hashed_public_key = libp2p::multihash::encode(
									libp2p::multihash::Hash::SHA2256,
									authority.to_string().as_bytes(),
								).unwrap();

								if *key == hashed_public_key {
									let value = std::str::from_utf8(value).unwrap();

									let external_addresses: HashSet<libp2p::Multiaddr> = serde_json::from_str(value).unwrap();
									println!("==== Got key {:?} value {:?} from DHT", authority.to_string(), external_addresses);

									for address in external_addresses.iter() {
										// TODO: Why does add_reserved_peer take a string?
										network.service().add_reserved_peer(address.to_string());
									}
								}
							}
						},
						Err(e) => {
							println!("==== Got no authorities, but an error: {:?}", e);
						}
					}
				}
			}

			// Now some diagnostic for performances.
			let polling_dur = before_polling.elapsed();
			log!(
				target: "service",
				if polling_dur >= Duration::from_millis(50) { Level::Warn } else { Level::Trace },
				"Polling the network future took {:?}",
				polling_dur
			);

			Ok(Async::NotReady)

		}))
	}

}

/// The super trait that combines all required traits a `Service` needs to implement.
pub trait ServiceTrait<C: Components>:
	Deref<Target = Service<C>>
	+ Send
	+ 'static
	+ StartRPC<C>
	+ NetworkFutureBuilder<C>
	+ MaintainTransactionPool<C>
	+ OffchainWorker<C>
{}
impl<C: Components, T> ServiceTrait<C> for T where
	T: Deref<Target = Service<C>>
	+ Send
	+ 'static
	+ StartRPC<C>
	+ NetworkFutureBuilder<C>
	+ MaintainTransactionPool<C>
	+ OffchainWorker<C>
{}

/// Alias for a an implementation of `futures::future::Executor`.
pub type TaskExecutor = Arc<dyn Executor<Box<dyn Future<Item = (), Error = ()> + Send>> + Send + Sync>;

/// A collection of types and methods to build a service on top of the substrate service.
pub trait ServiceFactory: 'static + Sized {
	/// Block type.
	type Block: BlockT<Hash=H256>;
	/// Consensus crypto type.
	type ConsensusPair: Pair;
	/// Finality crypto type.
	type FinalityPair: Pair;
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
	///
	type AuthorityId: parity_codec::Codec + std::fmt::Debug + std::string::ToString;

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

	/// Build finality proof provider for serving network requests on full node.
	fn build_finality_proof_provider(
		client: Arc<FullClient<Self>>
	) -> Result<Option<Arc<dyn FinalityProofProvider<Self::Block>>>, error::Error>;

	/// Build the Fork Choice algorithm for full client
	fn build_select_chain(
		config: &mut FactoryFullConfiguration<Self>,
		client: Arc<FullClient<Self>>,
	) -> Result<Self::SelectChain, error::Error>;

	/// Build full service.
	fn new_full(config: FactoryFullConfiguration<Self>)
		-> Result<Self::FullService, error::Error>;
	/// Build light service.
	fn new_light(config: FactoryFullConfiguration<Self>)
		-> Result<Self::LightService, error::Error>;

	/// ImportQueue for a full client
	fn build_full_import_queue(
		config: &mut FactoryFullConfiguration<Self>,
		_client: Arc<FullClient<Self>>,
		_select_chain: Self::SelectChain,
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
	) -> Result<(Self::LightImportQueue, BoxFinalityProofRequestBuilder<Self::Block>), error::Error> {
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

	/// Build the queue that imports blocks from the network, and optionally a way for the network
	/// to build requests for proofs of finality.
	fn build_import_queue(
		config: &mut FactoryFullConfiguration<Self::Factory>,
		client: Arc<ComponentClient<Self>>,
		select_chain: Option<Self::SelectChain>,
	) -> Result<(Self::ImportQueue, Option<BoxFinalityProofRequestBuilder<FactoryBlock<Self::Factory>>>), error::Error>;

	/// Finality proof provider for serving network requests.
	fn build_finality_proof_provider(
		client: Arc<ComponentClient<Self>>
	) -> Result<Option<Arc<dyn FinalityProofProvider<<Self::Factory as ServiceFactory>::Block>>>, error::Error>;

	/// Build fork choice selector
	fn build_select_chain(
		config: &mut FactoryFullConfiguration<Self::Factory>,
		client: Arc<ComponentClient<Self>>
	) -> Result<Option<Self::SelectChain>, error::Error>;
}

/// A struct that implement `Components` for the full client.
pub struct FullComponents<Factory: ServiceFactory> {
	service: Service<FullComponents<Factory>>,
}

impl<Factory: ServiceFactory> FullComponents<Factory> {
	/// Create new `FullComponents`
	pub fn new(
		config: FactoryFullConfiguration<Factory>
	) -> Result<Self, error::Error> {
		Ok(
			Self {
				service: Service::new(config)?,
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

impl<Factory: ServiceFactory> Future for FullComponents<Factory> {
	type Item = ();
	type Error = ();

	fn poll(&mut self) -> Poll<Self::Item, Self::Error> {
		self.service.poll()
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
			state_cache_child_ratio:
				config.state_cache_child_ratio.map(|v| (v, 100)),
			path: config.database_path.clone(),
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
		select_chain: Option<Self::SelectChain>,
	) -> Result<(Self::ImportQueue, Option<BoxFinalityProofRequestBuilder<FactoryBlock<Self::Factory>>>), error::Error> {
		let select_chain = select_chain
			.ok_or(error::Error::SelectChainRequired)?;
		Factory::build_full_import_queue(config, client, select_chain)
			.map(|queue| (queue, None))
	}

	fn build_select_chain(
		config: &mut FactoryFullConfiguration<Self::Factory>,
		client: Arc<ComponentClient<Self>>
	) -> Result<Option<Self::SelectChain>, error::Error> {
		Self::Factory::build_select_chain(config, client).map(Some)
	}

	fn build_finality_proof_provider(
		client: Arc<ComponentClient<Self>>
	) -> Result<Option<Arc<dyn FinalityProofProvider<<Self::Factory as ServiceFactory>::Block>>>, error::Error> {
		Factory::build_finality_proof_provider(client)
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
	) -> Result<Self, error::Error> {
		Ok(
			Self {
				service: Service::new(config)?,
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

impl<Factory: ServiceFactory> Future for LightComponents<Factory> {
	type Item = ();
	type Error = ();

	fn poll(&mut self) -> Poll<Self::Item, Self::Error> {
		self.service.poll()
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
			state_cache_child_ratio:
				config.state_cache_child_ratio.map(|v| (v, 100)),
			path: config.database_path.clone(),
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
		_select_chain: Option<Self::SelectChain>,
	) -> Result<(Self::ImportQueue, Option<BoxFinalityProofRequestBuilder<FactoryBlock<Self::Factory>>>), error::Error> {
		Factory::build_light_import_queue(config, client)
			.map(|(queue, builder)| (queue, Some(builder)))
	}

	fn build_finality_proof_provider(
		_client: Arc<ComponentClient<Self>>
	) -> Result<Option<Arc<dyn FinalityProofProvider<<Self::Factory as ServiceFactory>::Block>>>, error::Error> {
		Ok(None)
	}
	fn build_select_chain(
		_config: &mut FactoryFullConfiguration<Self::Factory>,
		_client: Arc<ComponentClient<Self>>
	) -> Result<Option<Self::SelectChain>, error::Error> {
		Ok(None)
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use consensus_common::BlockOrigin;
	use substrate_test_runtime_client::{prelude::*, runtime::Transfer};

	#[test]
	fn should_remove_transactions_from_the_pool() {
		let (client, longest_chain) = TestClientBuilder::new().build_with_longest_chain();
		let client = Arc::new(client);
		let pool = TransactionPool::new(Default::default(), ::transaction_pool::ChainApi::new(client.clone()));
		let transaction = Transfer {
			amount: 5,
			nonce: 0,
			from: AccountKeyring::Alice.into(),
			to: Default::default(),
		}.into_signed_tx();
		let best = longest_chain.best_chain().unwrap();

		// store the transaction in the pool
		pool.submit_one(&BlockId::hash(best.hash()), transaction.clone()).unwrap();

		// import the block
		let mut builder = client.new_block(Default::default()).unwrap();
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
