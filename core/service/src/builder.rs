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

use crate::{NewService, NetworkStatus, NetworkState, error::{self, Error}, DEFAULT_PROTOCOL_ID};
use crate::{SpawnTaskHandle, start_rpc_servers, build_network_future, TransactionPoolAdapter};
use crate::TaskExecutor;
use crate::config::Configuration;
use client::{
	BlockchainEvents, Client, runtime_api,
	backend::RemoteBackend, light::blockchain::RemoteBlockchain,
};
use chain_spec::{RuntimeGenesis, Extension};
use codec::{Decode, Encode, IoReader};
use consensus_common::import_queue::ImportQueue;
use futures::{prelude::*, sync::mpsc};
use futures03::{
	compat::Compat,
	future::ready,
	FutureExt as _, TryFutureExt as _,
	StreamExt as _, TryStreamExt as _,
};
use keystore::{Store as Keystore, KeyStorePtr};
use log::{info, warn};
use network::{FinalityProofProvider, OnDemand, NetworkService, NetworkStateInfo, DhtEvent};
use network::{config::BoxFinalityProofRequestBuilder, specialization::NetworkSpecialization};
use parking_lot::{Mutex, RwLock};
use primitives::{Blake2Hasher, H256, Hasher};
use rpc::{self, system::SystemInfo};
use sr_primitives::generic::BlockId;
use sr_primitives::traits::{
	Block as BlockT, Extrinsic, ProvideRuntimeApi, NumberFor, One, Zero, Header, SaturatedConversion
};
use substrate_executor::{NativeExecutor, NativeExecutionDispatch};
use std::{io::{Read, Write, Seek}, marker::PhantomData, sync::Arc, sync::atomic::AtomicBool};
use sysinfo::{get_current_pid, ProcessExt, System, SystemExt};
use tel::{telemetry, SUBSTRATE_INFO};
use transaction_pool::txpool::{self, ChainApi, Pool as TransactionPool};

/// Aggregator for the components required to build a service.
///
/// # Usage
///
/// Call [`ServiceBuilder::new_full`] or [`ServiceBuilder::new_light`], then call the various
/// `with_` methods to add the required components that you built yourself:
///
/// - [`with_select_chain`](ServiceBuilder::with_select_chain)
/// - [`with_import_queue`](ServiceBuilder::with_import_queue)
/// - [`with_network_protocol`](ServiceBuilder::with_network_protocol)
/// - [`with_finality_proof_provider`](ServiceBuilder::with_finality_proof_provider)
/// - [`with_transaction_pool`](ServiceBuilder::with_transaction_pool)
///
/// After this is done, call [`build`](ServiceBuilder::build) to construct the service.
///
/// The order in which the `with_*` methods are called doesn't matter, as the correct binding of
/// generics is done when you call `build`.
///
pub struct ServiceBuilder<TBl, TRtApi, TCfg, TGen, TCSExt, TCl, TFchr, TSc, TImpQu, TFprb, TFpp,
	TNetP, TExPool, TRpc, TRpcB, Backend>
{
	config: Configuration<TCfg, TGen, TCSExt>,
	client: Arc<TCl>,
	backend: Arc<Backend>,
	keystore: Arc<RwLock<Keystore>>,
	fetcher: Option<TFchr>,
	select_chain: Option<TSc>,
	import_queue: TImpQu,
	finality_proof_request_builder: Option<TFprb>,
	finality_proof_provider: Option<TFpp>,
	network_protocol: TNetP,
	transaction_pool: Arc<TExPool>,
	rpc_extensions: TRpc,
	rpc_builder: TRpcB,
	dht_event_tx: Option<mpsc::Sender<DhtEvent>>,
	marker: PhantomData<(TBl, TRtApi)>,
}

/// Full client type.
type TFullClient<TBl, TRtApi, TExecDisp> = Client<
	TFullBackend<TBl>,
	TFullCallExecutor<TBl, TExecDisp>,
	TBl,
	TRtApi,
>;

/// Full client backend type.
type TFullBackend<TBl> = client_db::Backend<TBl>;

/// Full client call executor type.
type TFullCallExecutor<TBl, TExecDisp> = client::LocalCallExecutor<
	client_db::Backend<TBl>,
	NativeExecutor<TExecDisp>,
>;

/// Light client type.
type TLightClient<TBl, TRtApi, TExecDisp> = Client<
	TLightBackend<TBl>,
	TLightCallExecutor<TBl, TExecDisp>,
	TBl,
	TRtApi,
>;

/// Light client backend type.
type TLightBackend<TBl> = client::light::backend::Backend<
	client_db::light::LightStorage<TBl>,
	Blake2Hasher,
>;

/// Light call executor type.
type TLightCallExecutor<TBl, TExecDisp> = client::light::call_executor::GenesisCallExecutor<
	client::light::backend::Backend<
		client_db::light::LightStorage<TBl>,
		Blake2Hasher
	>,
	client::LocalCallExecutor<
		client::light::backend::Backend<
			client_db::light::LightStorage<TBl>,
			Blake2Hasher
		>,
		NativeExecutor<TExecDisp>
	>,
>;

impl<TCfg, TGen, TCSExt> ServiceBuilder<(), (), TCfg, TGen, TCSExt, (), (), (), (), (), (), (), (), (), (), ()>
where TGen: RuntimeGenesis, TCSExt: Extension {
	/// Start the service builder with a configuration.
	pub fn new_full<TBl: BlockT<Hash=H256>, TRtApi, TExecDisp: NativeExecutionDispatch>(
		config: Configuration<TCfg, TGen, TCSExt>
	) -> Result<ServiceBuilder<
		TBl,
		TRtApi,
		TCfg,
		TGen,
		TCSExt,
		TFullClient<TBl, TRtApi, TExecDisp>,
		Arc<OnDemand<TBl>>,
		(),
		(),
		BoxFinalityProofRequestBuilder<TBl>,
		(),
		(),
		(),
		(),
		FullRpcBuilder<TBl, TRtApi, TExecDisp>,
		TFullBackend<TBl>,
	>, Error> {
		let keystore = Keystore::open(config.keystore_path.clone(), config.keystore_password.clone())?;

		let db_settings = client_db::DatabaseSettings {
			cache_size: None,
			state_cache_size: config.state_cache_size,
			state_cache_child_ratio:
				config.state_cache_child_ratio.map(|v| (v, 100)),
			path: config.database_path.clone(),
			pruning: config.pruning.clone(),
		};

		let executor = NativeExecutor::<TExecDisp>::new(config.default_heap_pages);

		let fork_blocks = config.chain_spec
			.extensions()
			.get::<client::ForkBlocks<TBl>>()
			.cloned()
			.unwrap_or_default();

		let (client, backend) = client_db::new_client(
			db_settings,
			executor,
			&config.chain_spec,
			fork_blocks,
			config.execution_strategies.clone(),
			Some(keystore.clone()),
		)?;

		let client = Arc::new(client);

		let rpc_builder = FullRpcBuilder { client: client.clone() };

		Ok(ServiceBuilder {
			config,
			client,
			backend,
			keystore,
			fetcher: None,
			select_chain: None,
			import_queue: (),
			finality_proof_request_builder: None,
			finality_proof_provider: None,
			network_protocol: (),
			transaction_pool: Arc::new(()),
			rpc_extensions: Default::default(),
			rpc_builder,
			dht_event_tx: None,
			marker: PhantomData,
		})
	}

	/// Start the service builder with a configuration.
	pub fn new_light<TBl: BlockT<Hash=H256>, TRtApi, TExecDisp: NativeExecutionDispatch + 'static>(
		config: Configuration<TCfg, TGen, TCSExt>
	) -> Result<ServiceBuilder<
		TBl,
		TRtApi,
		TCfg,
		TGen,
		TCSExt,
		TLightClient<TBl, TRtApi, TExecDisp>,
		Arc<OnDemand<TBl>>,
		(),
		(),
		BoxFinalityProofRequestBuilder<TBl>,
		(),
		(),
		(),
		(),
		LightRpcBuilder<TBl, TRtApi, TExecDisp>,
		TLightBackend<TBl>,
	>, Error> {
		let keystore = Keystore::open(config.keystore_path.clone(), config.keystore_password.clone())?;

		let db_settings = client_db::DatabaseSettings {
			cache_size: config.database_cache_size.map(|u| u as usize),
			state_cache_size: config.state_cache_size,
			state_cache_child_ratio:
				config.state_cache_child_ratio.map(|v| (v, 100)),
			path: config.database_path.clone(),
			pruning: config.pruning.clone(),
		};

		let executor = NativeExecutor::<TExecDisp>::new(config.default_heap_pages);

		let db_storage = client_db::light::LightStorage::new(db_settings)?;
		let light_blockchain = client::light::new_light_blockchain(db_storage);
		let fetch_checker = Arc::new(client::light::new_fetch_checker(light_blockchain.clone(), executor.clone()));
		let fetcher = Arc::new(network::OnDemand::new(fetch_checker));
		let backend = client::light::new_light_backend(light_blockchain);
		let remote_blockchain = backend.remote_blockchain();
		let client = Arc::new(client::light::new_light(
			backend.clone(),
			&config.chain_spec,
			executor,
		)?);
		let rpc_builder = LightRpcBuilder {
			client: client.clone(),
			remote_blockchain,
			fetcher: fetcher.clone(),
		};

		Ok(ServiceBuilder {
			config,
			client,
			backend,
			keystore,
			fetcher: Some(fetcher),
			select_chain: None,
			import_queue: (),
			finality_proof_request_builder: None,
			finality_proof_provider: None,
			network_protocol: (),
			transaction_pool: Arc::new(()),
			rpc_extensions: Default::default(),
			rpc_builder,
			dht_event_tx: None,
			marker: PhantomData,
		})
	}
}

impl<TBl, TRtApi, TCfg, TGen, TCSExt, TCl, TFchr, TSc, TImpQu, TFprb, TFpp, TNetP, TExPool, TRpc, TRpcB, Backend>
	ServiceBuilder<TBl, TRtApi, TCfg, TGen, TCSExt, TCl, TFchr, TSc, TImpQu, TFprb, TFpp,
		TNetP, TExPool, TRpc, TRpcB, Backend> {

	/// Returns a reference to the client that was stored in this builder.
	pub fn client(&self) -> &Arc<TCl> {
		&self.client
	}

	/// Returns a reference to the backend that was used in this builder.
	pub fn backend(&self) -> &Arc<Backend> {
		&self.backend
	}

	/// Returns a reference to the select-chain that was stored in this builder.
	pub fn select_chain(&self) -> Option<&TSc> {
		self.select_chain.as_ref()
	}

	/// Defines which head-of-chain strategy to use.
	pub fn with_opt_select_chain<USc>(
		self,
		select_chain_builder: impl FnOnce(
			&Configuration<TCfg, TGen, TCSExt>, &Arc<Backend>
		) -> Result<Option<USc>, Error>
	) -> Result<ServiceBuilder<TBl, TRtApi, TCfg, TGen, TCSExt, TCl, TFchr, USc, TImpQu, TFprb, TFpp,
		TNetP, TExPool, TRpc, TRpcB, Backend>, Error> {
		let select_chain = select_chain_builder(&self.config, &self.backend)?;

		Ok(ServiceBuilder {
			config: self.config,
			client: self.client,
			backend: self.backend,
			keystore: self.keystore,
			fetcher: self.fetcher,
			select_chain,
			import_queue: self.import_queue,
			finality_proof_request_builder: self.finality_proof_request_builder,
			finality_proof_provider: self.finality_proof_provider,
			network_protocol: self.network_protocol,
			transaction_pool: self.transaction_pool,
			rpc_extensions: self.rpc_extensions,
			rpc_builder: self.rpc_builder,
			dht_event_tx: self.dht_event_tx,
			marker: self.marker,
		})
	}

	/// Defines which head-of-chain strategy to use.
	pub fn with_select_chain<USc>(
		self,
		builder: impl FnOnce(&Configuration<TCfg, TGen, TCSExt>, &Arc<Backend>) -> Result<USc, Error>
	) -> Result<ServiceBuilder<TBl, TRtApi, TCfg, TGen, TCSExt, TCl, TFchr, USc, TImpQu, TFprb, TFpp,
		TNetP, TExPool, TRpc, TRpcB, Backend>, Error> {
		self.with_opt_select_chain(|cfg, b| builder(cfg, b).map(Option::Some))
	}

	/// Defines which import queue to use.
	pub fn with_import_queue<UImpQu>(
		self,
		builder: impl FnOnce(&Configuration<TCfg, TGen, TCSExt>, Arc<TCl>, Option<TSc>, Arc<TExPool>)
			-> Result<UImpQu, Error>
	) -> Result<ServiceBuilder<TBl, TRtApi, TCfg, TGen, TCSExt, TCl, TFchr, TSc, UImpQu, TFprb, TFpp,
			TNetP, TExPool, TRpc, TRpcB, Backend>, Error>
	where TSc: Clone {
		let import_queue = builder(
			&self.config,
			self.client.clone(),
			self.select_chain.clone(),
			self.transaction_pool.clone()
		)?;

		Ok(ServiceBuilder {
			config: self.config,
			client: self.client,
			backend: self.backend,
			keystore: self.keystore,
			fetcher: self.fetcher,
			select_chain: self.select_chain,
			import_queue,
			finality_proof_request_builder: self.finality_proof_request_builder,
			finality_proof_provider: self.finality_proof_provider,
			network_protocol: self.network_protocol,
			transaction_pool: self.transaction_pool,
			rpc_extensions: self.rpc_extensions,
			rpc_builder: self.rpc_builder,
			dht_event_tx: self.dht_event_tx,
			marker: self.marker,
		})
	}

	/// Defines which network specialization protocol to use.
	pub fn with_network_protocol<UNetP>(
		self,
		network_protocol_builder: impl FnOnce(&Configuration<TCfg, TGen, TCSExt>) -> Result<UNetP, Error>
	) -> Result<ServiceBuilder<TBl, TRtApi, TCfg, TGen, TCSExt, TCl, TFchr, TSc, TImpQu, TFprb, TFpp,
		UNetP, TExPool, TRpc, TRpcB, Backend>, Error> {
		let network_protocol = network_protocol_builder(&self.config)?;

		Ok(ServiceBuilder {
			config: self.config,
			client: self.client,
			backend: self.backend,
			keystore: self.keystore,
			fetcher: self.fetcher,
			select_chain: self.select_chain,
			import_queue: self.import_queue,
			finality_proof_request_builder: self.finality_proof_request_builder,
			finality_proof_provider: self.finality_proof_provider,
			network_protocol,
			transaction_pool: self.transaction_pool,
			rpc_extensions: self.rpc_extensions,
			rpc_builder: self.rpc_builder,
			dht_event_tx: self.dht_event_tx,
			marker: self.marker,
		})
	}

	/// Defines which strategy to use for providing finality proofs.
	pub fn with_opt_finality_proof_provider(
		self,
		builder: impl FnOnce(Arc<TCl>, Arc<Backend>) -> Result<Option<Arc<dyn FinalityProofProvider<TBl>>>, Error>
	) -> Result<ServiceBuilder<
		TBl,
		TRtApi,
		TCfg,
		TGen,
		TCSExt,
		TCl,
		TFchr,
		TSc,
		TImpQu,
		TFprb,
		Arc<dyn FinalityProofProvider<TBl>>,
		TNetP,
		TExPool,
		TRpc,
		TRpcB,
		Backend,
	>, Error> {
		let finality_proof_provider = builder(self.client.clone(), self.backend.clone())?;

		Ok(ServiceBuilder {
			config: self.config,
			client: self.client,
			backend: self.backend,
			keystore: self.keystore,
			fetcher: self.fetcher,
			select_chain: self.select_chain,
			import_queue: self.import_queue,
			finality_proof_request_builder: self.finality_proof_request_builder,
			finality_proof_provider,
			network_protocol: self.network_protocol,
			transaction_pool: self.transaction_pool,
			rpc_extensions: self.rpc_extensions,
			rpc_builder: self.rpc_builder,
			dht_event_tx: self.dht_event_tx,
			marker: self.marker,
		})
	}

	/// Defines which strategy to use for providing finality proofs.
	pub fn with_finality_proof_provider(
		self,
		build: impl FnOnce(Arc<TCl>, Arc<Backend>) -> Result<Arc<dyn FinalityProofProvider<TBl>>, Error>
	) -> Result<ServiceBuilder<
		TBl,
		TRtApi,
		TCfg,
		TGen,
		TCSExt,
		TCl,
		TFchr,
		TSc,
		TImpQu,
		TFprb,
		Arc<dyn FinalityProofProvider<TBl>>,
		TNetP,
		TExPool,
		TRpc,
		TRpcB,
		Backend,
	>, Error> {
		self.with_opt_finality_proof_provider(|client, backend| build(client, backend).map(Option::Some))
	}

	/// Defines which import queue to use.
	pub fn with_import_queue_and_opt_fprb<UImpQu, UFprb>(
		self,
		builder: impl FnOnce(
			&Configuration<TCfg, TGen, TCSExt>,
			Arc<TCl>,
			Arc<Backend>,
			Option<TFchr>,
			Option<TSc>,
			Arc<TExPool>,
		) -> Result<(UImpQu, Option<UFprb>), Error>
	) -> Result<ServiceBuilder<TBl, TRtApi, TCfg, TGen, TCSExt, TCl, TFchr, TSc, UImpQu, UFprb, TFpp,
		TNetP, TExPool, TRpc, TRpcB, Backend>, Error>
	where TSc: Clone, TFchr: Clone {
		let (import_queue, fprb) = builder(
			&self.config,
			self.client.clone(),
			self.backend.clone(),
			self.fetcher.clone(),
			self.select_chain.clone(),
			self.transaction_pool.clone()
		)?;

		Ok(ServiceBuilder {
			config: self.config,
			client: self.client,
			backend: self.backend,
			keystore: self.keystore,
			fetcher: self.fetcher,
			select_chain: self.select_chain,
			import_queue,
			finality_proof_request_builder: fprb,
			finality_proof_provider: self.finality_proof_provider,
			network_protocol: self.network_protocol,
			transaction_pool: self.transaction_pool,
			rpc_extensions: self.rpc_extensions,
			rpc_builder: self.rpc_builder,
			dht_event_tx: self.dht_event_tx,
			marker: self.marker,
		})
	}

	/// Defines which import queue to use.
	pub fn with_import_queue_and_fprb<UImpQu, UFprb>(
		self,
		builder: impl FnOnce(
			&Configuration<TCfg, TGen, TCSExt>,
			Arc<TCl>,
			Arc<Backend>,
			Option<TFchr>,
			Option<TSc>,
			Arc<TExPool>,
		) -> Result<(UImpQu, UFprb), Error>
	) -> Result<ServiceBuilder<TBl, TRtApi, TCfg, TGen, TCSExt, TCl, TFchr, TSc, UImpQu, UFprb, TFpp,
			TNetP, TExPool, TRpc, TRpcB, Backend>, Error>
	where TSc: Clone, TFchr: Clone {
		self.with_import_queue_and_opt_fprb(|cfg, cl, b, f, sc, tx|
			builder(cfg, cl, b, f, sc, tx)
				.map(|(q, f)| (q, Some(f)))
		)
	}

	/// Defines which transaction pool to use.
	pub fn with_transaction_pool<UExPool>(
		self,
		transaction_pool_builder: impl FnOnce(transaction_pool::txpool::Options, Arc<TCl>) -> Result<UExPool, Error>
	) -> Result<ServiceBuilder<TBl, TRtApi, TCfg, TGen, TCSExt, TCl, TFchr, TSc, TImpQu, TFprb, TFpp,
		TNetP, UExPool, TRpc, TRpcB, Backend>, Error> {
		let transaction_pool = transaction_pool_builder(self.config.transaction_pool.clone(), self.client.clone())?;

		Ok(ServiceBuilder {
			config: self.config,
			client: self.client,
			backend: self.backend,
			keystore: self.keystore,
			fetcher: self.fetcher,
			select_chain: self.select_chain,
			import_queue: self.import_queue,
			finality_proof_request_builder: self.finality_proof_request_builder,
			finality_proof_provider: self.finality_proof_provider,
			network_protocol: self.network_protocol,
			transaction_pool: Arc::new(transaction_pool),
			rpc_extensions: self.rpc_extensions,
			rpc_builder: self.rpc_builder,
			dht_event_tx: self.dht_event_tx,
			marker: self.marker,
		})
	}

	/// Defines the RPC extensions to use.
	pub fn with_rpc_extensions<URpc>(
		self,
		rpc_ext_builder: impl FnOnce(Arc<TCl>, Arc<TExPool>) -> URpc
	) -> Result<ServiceBuilder<TBl, TRtApi, TCfg, TGen, TCSExt, TCl, TFchr, TSc, TImpQu, TFprb, TFpp,
		TNetP, TExPool, URpc, TRpcB, Backend>, Error> {
		let rpc_extensions = rpc_ext_builder(self.client.clone(), self.transaction_pool.clone());

		Ok(ServiceBuilder {
			config: self.config,
			client: self.client,
			backend: self.backend,
			keystore: self.keystore,
			fetcher: self.fetcher,
			select_chain: self.select_chain,
			import_queue: self.import_queue,
			finality_proof_request_builder: self.finality_proof_request_builder,
			finality_proof_provider: self.finality_proof_provider,
			network_protocol: self.network_protocol,
			transaction_pool: self.transaction_pool,
			rpc_extensions,
			rpc_builder: self.rpc_builder,
			dht_event_tx: self.dht_event_tx,
			marker: self.marker,
		})
	}

		/// Adds a dht event sender to builder to be used by the network to send dht events to the authority discovery
		/// module.
		pub fn with_dht_event_tx(
			self,
			dht_event_tx: mpsc::Sender<DhtEvent>,
		) -> Result<ServiceBuilder<TBl, TRtApi, TCfg, TGen, TCSExt, TCl, TFchr, TSc, TImpQu, TFprb, TFpp,
								   TNetP, TExPool, TRpc, TRpcB, Backend>, Error> {
			Ok(ServiceBuilder {
				config: self.config,
				client: self.client,
				backend: self.backend,
				keystore: self.keystore,
				fetcher: self.fetcher,
				select_chain: self.select_chain,
				import_queue: self.import_queue,
				finality_proof_request_builder: self.finality_proof_request_builder,
				finality_proof_provider: self.finality_proof_provider,
				network_protocol: self.network_protocol,
				transaction_pool: self.transaction_pool,
				rpc_extensions: self.rpc_extensions,
				rpc_builder: self.rpc_builder,
				dht_event_tx: Some(dht_event_tx),
				marker: self.marker,
			})
		}
}

/// RPC handlers builder.
pub trait RpcBuilder<TBl: BlockT, TBackend, TExec, TRtApi> {
	/// Build chain RPC handler.
	fn build_chain(&self, subscriptions: rpc::Subscriptions) -> rpc::chain::Chain<TBackend, TExec, TBl, TRtApi>;
	/// Build state RPC handler.
	fn build_state(&self, subscriptions: rpc::Subscriptions) -> rpc::state::State<TBackend, TExec, TBl, TRtApi>;
}

/// RPC handlers builder for full nodes.
pub struct FullRpcBuilder<TBl: BlockT, TRtApi, TExecDisp> {
	client: Arc<TFullClient<TBl, TRtApi, TExecDisp>>,
}

impl<TBl, TRtApi, TExecDisp> RpcBuilder<TBl, TFullBackend<TBl>, TFullCallExecutor<TBl, TExecDisp>, TRtApi>
	for
		FullRpcBuilder<TBl, TRtApi, TExecDisp>
	where
		TBl: BlockT<Hash=H256>,
		TRtApi: 'static + Send + Sync,
		TExecDisp: 'static + NativeExecutionDispatch,
		TFullClient<TBl, TRtApi, TExecDisp>: ProvideRuntimeApi,
		<TFullClient<TBl, TRtApi, TExecDisp> as ProvideRuntimeApi>::Api: runtime_api::Metadata<TBl>,
{
	fn build_chain(
		&self,
		subscriptions: rpc::Subscriptions,
	) -> rpc::chain::Chain<TFullBackend<TBl>, TFullCallExecutor<TBl, TExecDisp>, TBl, TRtApi> {
		rpc::chain::new_full(self.client.clone(), subscriptions)
	}

	fn build_state(
		&self,
		subscriptions: rpc::Subscriptions,
	) -> rpc::state::State<TFullBackend<TBl>, TFullCallExecutor<TBl, TExecDisp>, TBl, TRtApi> {
		rpc::state::new_full(self.client.clone(), subscriptions)
	}
}

/// RPC handlers builder for light nodes.
pub struct LightRpcBuilder<TBl: BlockT<Hash=H256>, TRtApi, TExecDisp> {
	client: Arc<TLightClient<TBl, TRtApi, TExecDisp>>,
	remote_blockchain: Arc<dyn RemoteBlockchain<TBl>>,
	fetcher: Arc<network::OnDemand<TBl>>,
}

impl<TBl, TRtApi, TExecDisp> RpcBuilder<TBl, TLightBackend<TBl>, TLightCallExecutor<TBl, TExecDisp>, TRtApi>
	for
		LightRpcBuilder<TBl, TRtApi, TExecDisp>
	where
		TBl: BlockT<Hash=H256>,
		TRtApi: 'static + Send + Sync,
		TExecDisp: 'static + NativeExecutionDispatch,
{
	fn build_chain(
		&self,
		subscriptions: rpc::Subscriptions,
	) -> rpc::chain::Chain<TLightBackend<TBl>, TLightCallExecutor<TBl, TExecDisp>, TBl, TRtApi> {
		rpc::chain::new_light(
			self.client.clone(),
			subscriptions,
			self.remote_blockchain.clone(),
			self.fetcher.clone(),
		)
	}

	fn build_state(
		&self,
		subscriptions: rpc::Subscriptions,
	) -> rpc::state::State<TLightBackend<TBl>, TLightCallExecutor<TBl, TExecDisp>, TBl, TRtApi> {
		rpc::state::new_light(
			self.client.clone(),
			subscriptions,
			self.remote_blockchain.clone(),
			self.fetcher.clone(),
		)
	}
}

/// Implemented on `ServiceBuilder`. Allows importing blocks once you have given all the required
/// components to the builder.
pub trait ServiceBuilderImport {
	/// Starts the process of importing blocks.
	fn import_blocks(
		self,
		exit: impl Future<Item=(),Error=()> + Send + 'static,
		input: impl Read + Seek,
	) -> Result<Box<dyn Future<Item = (), Error = ()> + Send>, Error>;
}

/// Implemented on `ServiceBuilder`. Allows exporting blocks once you have given all the required
/// components to the builder.
pub trait ServiceBuilderExport {
	/// Type of block of the builder.
	type Block: BlockT;

	/// Performs the blocks export.
	fn export_blocks(
		&self,
		exit: impl Future<Item=(),Error=()> + Send + 'static,
		output: impl Write,
		from: NumberFor<Self::Block>,
		to: Option<NumberFor<Self::Block>>,
		json: bool
	) -> Result<(), Error>;
}

/// Implemented on `ServiceBuilder`. Allows reverting the chain once you have given all the
/// required components to the builder.
pub trait ServiceBuilderRevert {
	/// Type of block of the builder.
	type Block: BlockT;

	/// Performs a revert of `blocks` bocks.
	fn revert_chain(
		&self,
		blocks: NumberFor<Self::Block>
	) -> Result<(), Error>;
}

impl<
	TBl, TRtApi, TCfg, TGen, TCSExt, TBackend,
	TExec, TFchr, TSc, TImpQu, TFprb, TFpp, TNetP,
	TExPool, TRpc, TRpcB, Backend
> ServiceBuilderImport for ServiceBuilder<
	TBl, TRtApi, TCfg, TGen, TCSExt, Client<TBackend, TExec, TBl, TRtApi>,
	TFchr, TSc, TImpQu, TFprb, TFpp, TNetP, TExPool, TRpc, TRpcB, Backend
> where
	TBl: BlockT<Hash = <Blake2Hasher as Hasher>::Out>,
	TBackend: 'static + client::backend::Backend<TBl, Blake2Hasher> + Send,
	TExec: 'static + client::CallExecutor<TBl, Blake2Hasher> + Send + Sync + Clone,
	TImpQu: 'static + ImportQueue<TBl>,
	TRtApi: 'static + Send + Sync,
{
	fn import_blocks(
		self,
		exit: impl Future<Item=(),Error=()> + Send + 'static,
		input: impl Read + Seek,
	) -> Result<Box<dyn Future<Item = (), Error = ()> + Send>, Error> {
		let client = self.client;
		let mut queue = self.import_queue;
		import_blocks!(TBl, client, queue, exit, input)
			.map(|f| Box::new(f) as Box<_>)
	}
}

impl<TBl, TRtApi, TCfg, TGen, TCSExt, TBackend, TExec, TFchr, TSc, TImpQu, TFprb, TFpp, TNetP, TExPool, TRpc, TRpcB>
	ServiceBuilderExport for ServiceBuilder<TBl, TRtApi, TCfg, TGen, TCSExt, Client<TBackend, TExec, TBl, TRtApi>,
		TFchr, TSc, TImpQu, TFprb, TFpp, TNetP, TExPool, TRpc, TRpcB, TBackend>
where
	TBl: BlockT<Hash = <Blake2Hasher as Hasher>::Out>,
	TBackend: 'static + client::backend::Backend<TBl, Blake2Hasher> + Send,
	TExec: 'static + client::CallExecutor<TBl, Blake2Hasher> + Send + Sync + Clone
{
	type Block = TBl;

	fn export_blocks(
		&self,
		exit: impl Future<Item=(),Error=()> + Send + 'static,
		mut output: impl Write,
		from: NumberFor<TBl>,
		to: Option<NumberFor<TBl>>,
		json: bool
	) -> Result<(), Error> {
		let client = &self.client;
		export_blocks!(client, exit, output, from, to, json)
	}
}

impl<TBl, TRtApi, TCfg, TGen, TCSExt, TBackend, TExec, TFchr, TSc, TImpQu, TFprb, TFpp, TNetP, TExPool, TRpc, TRpcB>
	ServiceBuilderRevert for ServiceBuilder<TBl, TRtApi, TCfg, TGen, TCSExt, Client<TBackend, TExec, TBl, TRtApi>,
		TFchr, TSc, TImpQu, TFprb, TFpp, TNetP, TExPool, TRpc, TRpcB, TBackend>
where
	TBl: BlockT<Hash = <Blake2Hasher as Hasher>::Out>,
	TBackend: 'static + client::backend::Backend<TBl, Blake2Hasher> + Send,
	TExec: 'static + client::CallExecutor<TBl, Blake2Hasher> + Send + Sync + Clone
{
	type Block = TBl;

	fn revert_chain(
		&self,
		blocks: NumberFor<TBl>
	) -> Result<(), Error> {
		let client = &self.client;
		revert_chain!(client, blocks)
	}
}

impl<TBl, TRtApi, TCfg, TGen, TCSExt, TBackend, TExec, TSc, TImpQu, TNetP, TExPoolApi, TRpc, TRpcB>
ServiceBuilder<
	TBl,
	TRtApi,
	TCfg,
	TGen,
	TCSExt,
	Client<TBackend, TExec, TBl, TRtApi>,
	Arc<OnDemand<TBl>>,
	TSc,
	TImpQu,
	BoxFinalityProofRequestBuilder<TBl>,
	Arc<dyn FinalityProofProvider<TBl>>,
	TNetP,
	TransactionPool<TExPoolApi>,
	TRpc,
	TRpcB,
	TBackend,
> where
	Client<TBackend, TExec, TBl, TRtApi>: ProvideRuntimeApi,
	<Client<TBackend, TExec, TBl, TRtApi> as ProvideRuntimeApi>::Api:
		runtime_api::Metadata<TBl> +
		offchain::OffchainWorkerApi<TBl> +
		runtime_api::TaggedTransactionQueue<TBl> +
		session::SessionKeys<TBl>,
	TBl: BlockT<Hash = <Blake2Hasher as Hasher>::Out>,
	TRtApi: 'static + Send + Sync,
	TCfg: Default,
	TGen: RuntimeGenesis,
	TCSExt: Extension,
	TBackend: 'static + client::backend::Backend<TBl, Blake2Hasher> + Send,
	TExec: 'static + client::CallExecutor<TBl, Blake2Hasher> + Send + Sync + Clone,
	TSc: Clone,
	TImpQu: 'static + ImportQueue<TBl>,
	TNetP: NetworkSpecialization<TBl>,
	TExPoolApi: 'static + ChainApi<Block = TBl, Hash = <TBl as BlockT>::Hash>,
	TRpc: rpc::RpcExtension<rpc::Metadata> + Clone,
	TRpcB: RpcBuilder<TBl, TBackend, TExec, TRtApi>,
{
	/// Builds the service.
	pub fn build(self) -> Result<NewService<
		TBl,
		Client<TBackend, TExec, TBl, TRtApi>,
		TSc,
		NetworkStatus<TBl>,
		NetworkService<TBl, TNetP, <TBl as BlockT>::Hash>,
		TransactionPool<TExPoolApi>,
		offchain::OffchainWorkers<
			Client<TBackend, TExec, TBl, TRtApi>,
			TBackend::OffchainStorage,
			TBl
		>,
	>, Error> {
		let ServiceBuilder {
			marker: _,
			mut config,
			client,
			fetcher,
			backend,
			keystore,
			select_chain,
			import_queue,
			finality_proof_request_builder,
			finality_proof_provider,
			network_protocol,
			transaction_pool,
			rpc_extensions,
			dht_event_tx,
			rpc_builder,
		} = self;

		session::generate_initial_session_keys(
			client.clone(),
			config.dev_key_seed.clone().map(|s| vec![s]).unwrap_or_default()
		)?;

		new_impl!(
			TBl,
			config,
			move |_| -> Result<_, Error> {
				Ok((
					client,
					fetcher,
					backend,
					keystore,
					select_chain,
					import_queue,
					finality_proof_request_builder,
					finality_proof_provider,
					network_protocol,
					transaction_pool,
					rpc_extensions,
					dht_event_tx,
				))
			},
			|h, c, tx, r| maintain_transaction_pool(h, c, tx, r),
			|n, o, p, ns, v| offchain_workers(n, o, p, ns, v),
			|c, ssb, si, te, tp, ext, ks| start_rpc(&rpc_builder, c, ssb, si, te, tp, ext, ks),
		)
	}
}

pub(crate) fn start_rpc<Api, Backend, Block, Executor, PoolApi, RpcB>(
	rpc_builder: &RpcB,
	client: Arc<Client<Backend, Executor, Block, Api>>,
	system_send_back: futures03::channel::mpsc::UnboundedSender<rpc::system::Request<Block>>,
	rpc_system_info: SystemInfo,
	task_executor: TaskExecutor,
	transaction_pool: Arc<TransactionPool<PoolApi>>,
	rpc_extensions: impl rpc::RpcExtension<rpc::Metadata>,
	keystore: KeyStorePtr,
) -> rpc_servers::RpcHandler<rpc::Metadata>
where
	Block: BlockT<Hash = <Blake2Hasher as primitives::Hasher>::Out>,
	Backend: client::backend::Backend<Block, Blake2Hasher> + 'static,
	Client<Backend, Executor, Block, Api>: ProvideRuntimeApi,
	<Client<Backend, Executor, Block, Api> as ProvideRuntimeApi>::Api:
		runtime_api::Metadata<Block> + session::SessionKeys<Block>,
	Api: Send + Sync + 'static,
	Executor: client::CallExecutor<Block, Blake2Hasher> + Send + Sync + Clone + 'static,
	PoolApi: txpool::ChainApi<Hash = Block::Hash, Block = Block> + 'static,
	RpcB: RpcBuilder<Block, Backend, Executor, Api>,
{
	use rpc::{chain, state, author, system};
	let subscriptions = rpc::Subscriptions::new(task_executor);
	let chain = rpc_builder.build_chain(subscriptions.clone());
	let state = rpc_builder.build_state(subscriptions.clone());
	let author = rpc::author::Author::new(
		client,
		transaction_pool,
		subscriptions,
		keystore,
	);
	let system = system::System::new(rpc_system_info, system_send_back);

	rpc_servers::rpc_handler((
		state::StateApi::to_delegate(state),
		chain::ChainApi::to_delegate(chain),
		author::AuthorApi::to_delegate(author),
		system::SystemApi::to_delegate(system),
		rpc_extensions,
	))
}

pub(crate) fn maintain_transaction_pool<Api, Backend, Block, Executor, PoolApi>(
	id: &BlockId<Block>,
	client: &Arc<Client<Backend, Executor, Block, Api>>,
	transaction_pool: &TransactionPool<PoolApi>,
	retracted: &[Block::Hash],
) -> error::Result<Box<dyn Future<Item = (), Error = ()> + Send>> where
	Block: BlockT<Hash = <Blake2Hasher as primitives::Hasher>::Out>,
	Backend: 'static + client::backend::Backend<Block, Blake2Hasher>,
	Client<Backend, Executor, Block, Api>: ProvideRuntimeApi,
	<Client<Backend, Executor, Block, Api> as ProvideRuntimeApi>::Api: runtime_api::TaggedTransactionQueue<Block>,
	Executor: 'static + client::CallExecutor<Block, Blake2Hasher>,
	PoolApi: 'static + txpool::ChainApi<Hash = Block::Hash, Block = Block>,
	Api: 'static,
{
	// Put transactions from retracted blocks back into the pool.
	let client_copy = client.clone();
	let retracted_transactions = retracted.to_vec().into_iter()
		.filter_map(move |hash| client_copy.block(&BlockId::hash(hash)).ok().unwrap_or(None))
		.flat_map(|block| block.block.deconstruct().1.into_iter())
		.filter(|tx| tx.is_signed().unwrap_or(false));
	let resubmit_future = transaction_pool
		.submit_at(id, retracted_transactions, true)
		.then(|resubmit_result| ready(match resubmit_result {
			Ok(_) => Ok(()),
			Err(e) => {
				warn!("Error re-submitting transactions: {:?}", e);
				Ok(())
			}
		}))
		.compat();

	// Avoid calling into runtime if there is nothing to prune from the pool anyway.
	if transaction_pool.status().is_empty() {
		return Ok(Box::new(resubmit_future))
	}

	let block = client.block(id)?;
	Ok(match block {
		Some(block) => {
			let parent_id = BlockId::hash(*block.block.header().parent_hash());
			let prune_future = transaction_pool
				.prune(id, &parent_id, block.block.extrinsics())
				.boxed()
				.compat()
				.map_err(|e| { format!("{:?}", e); });

			Box::new(resubmit_future.and_then(|_| prune_future))
		},
		None => Box::new(resubmit_future),
	})
}

pub(crate) fn offchain_workers<Api, Backend, Block, Executor, PoolApi>(
	number: &NumberFor<Block>,
	offchain: &offchain::OffchainWorkers<
		Client<Backend, Executor, Block, Api>,
		<Backend as client::backend::Backend<Block, Blake2Hasher>>::OffchainStorage,
		Block
	>,
	pool: &Arc<TransactionPool<PoolApi>>,
	network_state: &Arc<dyn NetworkStateInfo + Send + Sync>,
	is_validator: bool,
) -> error::Result<Box<dyn Future<Item = (), Error = ()> + Send>>
where
	Block: BlockT<Hash = <Blake2Hasher as primitives::Hasher>::Out>,
	Backend: client::backend::Backend<Block, Blake2Hasher> + 'static,
	Api: 'static,
	<Backend as client::backend::Backend<Block, Blake2Hasher>>::OffchainStorage: 'static,
	Client<Backend, Executor, Block, Api>: ProvideRuntimeApi + Send + Sync,
	<Client<Backend, Executor, Block, Api> as ProvideRuntimeApi>::Api: offchain::OffchainWorkerApi<Block>,
	Executor: client::CallExecutor<Block, Blake2Hasher> + 'static,
	PoolApi: txpool::ChainApi<Hash = Block::Hash, Block = Block> + 'static,
{
	let future = offchain.on_block_imported(number, pool, network_state.clone(), is_validator)
		.map(|()| Ok(()));
	Ok(Box::new(Compat::new(future)))
}

#[cfg(test)]
mod tests {
	use super::*;
	use futures03::executor::block_on;
	use consensus_common::{BlockOrigin, SelectChain};
	use substrate_test_runtime_client::{prelude::*, runtime::Transfer};

	#[test]
	fn should_remove_transactions_from_the_pool() {
		let (client, longest_chain) = TestClientBuilder::new().build_with_longest_chain();
		let client = Arc::new(client);
		let pool = TransactionPool::new(Default::default(), ::transaction_pool::FullChainApi::new(client.clone()));
		let transaction = Transfer {
			amount: 5,
			nonce: 0,
			from: AccountKeyring::Alice.into(),
			to: Default::default(),
		}.into_signed_tx();
		let best = longest_chain.best_chain().unwrap();

		// store the transaction in the pool
		block_on(pool.submit_one(&BlockId::hash(best.hash()), transaction.clone())).unwrap();

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
			&[]
		).unwrap().wait().unwrap();

		// then
		assert_eq!(pool.status().ready, 0);
		assert_eq!(pool.status().future, 0);
	}

	#[test]
	fn should_add_reverted_transactions_to_the_pool() {
		let (client, longest_chain) = TestClientBuilder::new().build_with_longest_chain();
		let client = Arc::new(client);
		let pool = TransactionPool::new(Default::default(), ::transaction_pool::FullChainApi::new(client.clone()));
		let transaction = Transfer {
			amount: 5,
			nonce: 0,
			from: AccountKeyring::Alice.into(),
			to: Default::default(),
		}.into_signed_tx();
		let best = longest_chain.best_chain().unwrap();

		// store the transaction in the pool
		block_on(pool.submit_one(&BlockId::hash(best.hash()), transaction.clone())).unwrap();

		// import the block
		let mut builder = client.new_block(Default::default()).unwrap();
		builder.push(transaction.clone()).unwrap();
		let block = builder.bake().unwrap();
		let block1_hash = block.header().hash();
		let id = BlockId::hash(block1_hash.clone());
		client.import(BlockOrigin::Own, block).unwrap();

		// fire notification - this should clean up the queue
		assert_eq!(pool.status().ready, 1);
		maintain_transaction_pool(
			&id,
			&client,
			&pool,
			&[]
		).unwrap().wait().unwrap();

		// then
		assert_eq!(pool.status().ready, 0);
		assert_eq!(pool.status().future, 0);

		// import second block
		let builder = client.new_block_at(&BlockId::hash(best.hash()), Default::default()).unwrap();
		let block = builder.bake().unwrap();
		let id = BlockId::hash(block.header().hash());
		client.import(BlockOrigin::Own, block).unwrap();

		// fire notification - this should add the transaction back to the pool.
		maintain_transaction_pool(
			&id,
			&client,
			&pool,
			&[block1_hash]
		).unwrap().wait().unwrap();

		// then
		assert_eq!(pool.status().ready, 1);
		assert_eq!(pool.status().future, 0);
	}
}
