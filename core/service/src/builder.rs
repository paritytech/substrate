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

use crate::{Service, NetworkStatus, NetworkState, error::{self, Error}, DEFAULT_PROTOCOL_ID};
use crate::{SpawnTaskHandle, start_rpc_servers, build_network_future, TransactionPoolAdapter};
use crate::status_sinks;
use crate::config::{Configuration, DatabaseConfig};
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
use keystore::{Store as Keystore};
use log::{info, warn};
use network::{FinalityProofProvider, OnDemand, NetworkService, NetworkStateInfo, DhtEvent};
use network::{config::BoxFinalityProofRequestBuilder, specialization::NetworkSpecialization};
use parking_lot::{Mutex, RwLock};
use primitives::{Blake2Hasher, H256, Hasher};
use rpc;
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
	TNetP, TExPool, TRpc, Backend>
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
	remote_backend: Option<Arc<dyn RemoteBlockchain<TBl>>>,
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

impl<TCfg, TGen, TCSExt> ServiceBuilder<(), (), TCfg, TGen, TCSExt, (), (), (), (), (), (), (), (), (), ()>
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
		Arc<dyn FinalityProofProvider<TBl>>,
		(),
		(),
		(),
		TFullBackend<TBl>,
	>, Error> {
		let keystore = Keystore::open(config.keystore_path.clone(), config.keystore_password.clone())?;

		let executor = NativeExecutor::<TExecDisp>::new(
			config.wasm_method,
			config.default_heap_pages,
		);

		let fork_blocks = config.chain_spec
			.extensions()
			.get::<client::ForkBlocks<TBl>>()
			.cloned()
			.unwrap_or_default();

		let (client, backend) = {
			let db_config = client_db::DatabaseSettings {
				state_cache_size: config.state_cache_size,
				state_cache_child_ratio:
					config.state_cache_child_ratio.map(|v| (v, 100)),
				pruning: config.pruning.clone(),
				source: match &config.database {
					DatabaseConfig::Path { path, cache_size } =>
						client_db::DatabaseSettingsSrc::Path {
							path: path.clone(),
							cache_size: cache_size.clone().map(|u| u as usize),
						},
					DatabaseConfig::Custom(db) =>
						client_db::DatabaseSettingsSrc::Custom(db.clone()),
				},
			};
			
			client_db::new_client(
				db_config,
				executor,
				&config.chain_spec,
				fork_blocks,
				config.execution_strategies.clone(),
				Some(keystore.clone()),
			)?
		};

		let client = Arc::new(client);

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
			remote_backend: None,
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
		Arc<dyn FinalityProofProvider<TBl>>,
		(),
		(),
		(),
		TLightBackend<TBl>,
	>, Error> {
		let keystore = Keystore::open(config.keystore_path.clone(), config.keystore_password.clone())?;

		let executor = NativeExecutor::<TExecDisp>::new(
			config.wasm_method,
			config.default_heap_pages,
		);

		let db_storage = {
			let db_settings = client_db::DatabaseSettings {
				state_cache_size: config.state_cache_size,
				state_cache_child_ratio:
					config.state_cache_child_ratio.map(|v| (v, 100)),
				pruning: config.pruning.clone(),
				source: match &config.database {
					DatabaseConfig::Path { path, cache_size } =>
						client_db::DatabaseSettingsSrc::Path {
							path: path.clone(),
							cache_size: cache_size.clone().map(|u| u as usize),
						},
					DatabaseConfig::Custom(db) =>
						client_db::DatabaseSettingsSrc::Custom(db.clone()),
				},
			};
			client_db::light::LightStorage::new(db_settings)?
		};
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
			remote_backend: Some(remote_blockchain),
			dht_event_tx: None,
			marker: PhantomData,
		})
	}
}

impl<TBl, TRtApi, TCfg, TGen, TCSExt, TCl, TFchr, TSc, TImpQu, TFprb, TFpp, TNetP, TExPool, TRpc, Backend>
	ServiceBuilder<TBl, TRtApi, TCfg, TGen, TCSExt, TCl, TFchr, TSc, TImpQu, TFprb, TFpp,
		TNetP, TExPool, TRpc, Backend> {

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
		TNetP, TExPool, TRpc, Backend>, Error> {
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
			remote_backend: self.remote_backend,
			dht_event_tx: self.dht_event_tx,
			marker: self.marker,
		})
	}

	/// Defines which head-of-chain strategy to use.
	pub fn with_select_chain<USc>(
		self,
		builder: impl FnOnce(&Configuration<TCfg, TGen, TCSExt>, &Arc<Backend>) -> Result<USc, Error>
	) -> Result<ServiceBuilder<TBl, TRtApi, TCfg, TGen, TCSExt, TCl, TFchr, USc, TImpQu, TFprb, TFpp,
		TNetP, TExPool, TRpc, Backend>, Error> {
		self.with_opt_select_chain(|cfg, b| builder(cfg, b).map(Option::Some))
	}

	/// Defines which import queue to use.
	pub fn with_import_queue<UImpQu>(
		self,
		builder: impl FnOnce(&Configuration<TCfg, TGen, TCSExt>, Arc<TCl>, Option<TSc>, Arc<TExPool>)
			-> Result<UImpQu, Error>
	) -> Result<ServiceBuilder<TBl, TRtApi, TCfg, TGen, TCSExt, TCl, TFchr, TSc, UImpQu, TFprb, TFpp,
			TNetP, TExPool, TRpc, Backend>, Error>
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
			remote_backend: self.remote_backend,
			dht_event_tx: self.dht_event_tx,
			marker: self.marker,
		})
	}

	/// Defines which network specialization protocol to use.
	pub fn with_network_protocol<UNetP>(
		self,
		network_protocol_builder: impl FnOnce(&Configuration<TCfg, TGen, TCSExt>) -> Result<UNetP, Error>
	) -> Result<ServiceBuilder<TBl, TRtApi, TCfg, TGen, TCSExt, TCl, TFchr, TSc, TImpQu, TFprb, TFpp,
		UNetP, TExPool, TRpc, Backend>, Error> {
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
			remote_backend: self.remote_backend,
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
			remote_backend: self.remote_backend,
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
		TNetP, TExPool, TRpc, Backend>, Error>
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
			remote_backend: self.remote_backend,
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
			TNetP, TExPool, TRpc, Backend>, Error>
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
		TNetP, UExPool, TRpc, Backend>, Error> {
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
			remote_backend: self.remote_backend,
			dht_event_tx: self.dht_event_tx,
			marker: self.marker,
		})
	}

	/// Defines the RPC extensions to use.
	pub fn with_rpc_extensions<URpc>(
		self,
		rpc_ext_builder: impl FnOnce(Arc<TCl>, Arc<TExPool>) -> URpc
	) -> Result<ServiceBuilder<TBl, TRtApi, TCfg, TGen, TCSExt, TCl, TFchr, TSc, TImpQu, TFprb, TFpp,
		TNetP, TExPool, URpc, Backend>, Error> {
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
			remote_backend: self.remote_backend,
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
								TNetP, TExPool, TRpc, Backend>, Error> {
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
			remote_backend: self.remote_backend,
			dht_event_tx: Some(dht_event_tx),
			marker: self.marker,
		})
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
	TExPool, TRpc, Backend
> ServiceBuilderImport for ServiceBuilder<
	TBl, TRtApi, TCfg, TGen, TCSExt, Client<TBackend, TExec, TBl, TRtApi>,
	TFchr, TSc, TImpQu, TFprb, TFpp, TNetP, TExPool, TRpc, Backend
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

impl<TBl, TRtApi, TCfg, TGen, TCSExt, TBackend, TExec, TFchr, TSc, TImpQu, TFprb, TFpp, TNetP, TExPool, TRpc>
	ServiceBuilderExport for ServiceBuilder<TBl, TRtApi, TCfg, TGen, TCSExt, Client<TBackend, TExec, TBl, TRtApi>,
		TFchr, TSc, TImpQu, TFprb, TFpp, TNetP, TExPool, TRpc, TBackend>
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

impl<TBl, TRtApi, TCfg, TGen, TCSExt, TBackend, TExec, TFchr, TSc, TImpQu, TFprb, TFpp, TNetP, TExPool, TRpc>
	ServiceBuilderRevert for ServiceBuilder<TBl, TRtApi, TCfg, TGen, TCSExt, Client<TBackend, TExec, TBl, TRtApi>,
		TFchr, TSc, TImpQu, TFprb, TFpp, TNetP, TExPool, TRpc, TBackend>
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

impl<TBl, TRtApi, TCfg, TGen, TCSExt, TBackend, TExec, TSc, TImpQu, TNetP, TExPoolApi, TRpc>
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
{
	/// Builds the service.
	pub fn build(self) -> Result<Service<
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
			fetcher: on_demand,
			backend,
			keystore,
			select_chain,
			import_queue,
			finality_proof_request_builder,
			finality_proof_provider,
			network_protocol,
			transaction_pool,
			rpc_extensions,
			remote_backend,
			dht_event_tx,
		} = self;

		session::generate_initial_session_keys(
			client.clone(),
			config.dev_key_seed.clone().map(|s| vec![s]).unwrap_or_default()
		)?;

		let (signal, exit) = exit_future::signal();

		// List of asynchronous tasks to spawn. We collect them, then spawn them all at once.
		let (to_spawn_tx, to_spawn_rx) =
			mpsc::unbounded::<Box<dyn Future<Item = (), Error = ()> + Send>>();

		let import_queue = Box::new(import_queue);
		let chain_info = client.info().chain;

		let version = config.full_version();
		info!("Highest known block at #{}", chain_info.best_number);
		telemetry!(
			SUBSTRATE_INFO;
			"node.start";
			"height" => chain_info.best_number.saturated_into::<u64>(),
			"best" => ?chain_info.best_hash
		);

		let transaction_pool_adapter = Arc::new(TransactionPoolAdapter {
			imports_external_transactions: !config.roles.is_light(),
			pool: transaction_pool.clone(),
			client: client.clone(),
			executor: Arc::new(SpawnTaskHandle { sender: to_spawn_tx.clone(), on_exit: exit.clone() }),
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
			network::config::ProtocolId::from(protocol_id_full)
		};

		let block_announce_validator =
			Box::new(consensus_common::block_validation::DefaultBlockAnnounceValidator::new(client.clone()));

		let network_params = network::config::Params {
			roles: config.roles,
			network_config: config.network.clone(),
			chain: client.clone(),
			finality_proof_provider,
			finality_proof_request_builder,
			on_demand: on_demand.clone(),
			transaction_pool: transaction_pool_adapter.clone() as _,
			import_queue,
			protocol_id,
			specialization: network_protocol,
			block_announce_validator,
		};

		let has_bootnodes = !network_params.network_config.boot_nodes.is_empty();
		let network_mut = network::NetworkWorker::new(network_params)?;
		let network = network_mut.service().clone();
		let network_status_sinks = Arc::new(Mutex::new(status_sinks::StatusSinks::new()));

		let offchain_storage = backend.offchain_storage();
		let offchain_workers = match (config.offchain_worker, offchain_storage) {
			(true, Some(db)) => {
				Some(Arc::new(offchain::OffchainWorkers::new(client.clone(), db)))
			},
			(true, None) => {
				log::warn!("Offchain workers disabled, due to lack of offchain storage support in backend.");
				None
			},
			_ => None,
		};

		{
			// block notifications
			let txpool = Arc::downgrade(&transaction_pool);
			let wclient = Arc::downgrade(&client);
			let offchain = offchain_workers.as_ref().map(Arc::downgrade);
			let to_spawn_tx_ = to_spawn_tx.clone();
			let network_state_info: Arc<dyn NetworkStateInfo + Send + Sync> = network.clone();
			let is_validator = config.roles.is_authority();

			let events = client.import_notification_stream()
				.map(|v| Ok::<_, ()>(v)).compat()
				.for_each(move |notification| {
					let number = *notification.header.number();
					let txpool = txpool.upgrade();

					if let (Some(txpool), Some(client)) = (txpool.as_ref(), wclient.upgrade()) {
						let future = maintain_transaction_pool(
							&BlockId::hash(notification.hash),
							&client,
							&*txpool,
							&notification.retracted,
						).map_err(|e| warn!("Pool error processing new block: {:?}", e))?;
						let _ = to_spawn_tx_.unbounded_send(future);
					}

					let offchain = offchain.as_ref().and_then(|o| o.upgrade());
					if let (Some(txpool), Some(offchain)) = (txpool, offchain) {
						let future = offchain.on_block_imported(&number, &txpool, network_state_info.clone(), is_validator)
							.map(|()| Ok(()));
						let _ = to_spawn_tx_.unbounded_send(Box::new(Compat::new(future)));
					}

					Ok(())
				})
				.select(exit.clone())
				.then(|_| Ok(()));
			let _ = to_spawn_tx.unbounded_send(Box::new(events));
		}

		{
			// extrinsic notifications
			let network = Arc::downgrade(&network);
			let transaction_pool_ = transaction_pool.clone();
			let events = transaction_pool.import_notification_stream()
				.map(|v| Ok::<_, ()>(v)).compat()
				.for_each(move |_| {
					if let Some(network) = network.upgrade() {
						network.trigger_repropagate();
					}
					let status = transaction_pool_.status();
					telemetry!(SUBSTRATE_INFO; "txpool.import";
						"ready" => status.ready,
						"future" => status.future
					);
					Ok(())
				})
				.select(exit.clone())
				.then(|_| Ok(()));

			let _ = to_spawn_tx.unbounded_send(Box::new(events));
		}

		// Periodically notify the telemetry.
		let transaction_pool_ = transaction_pool.clone();
		let client_ = client.clone();
		let mut sys = System::new();
		let self_pid = get_current_pid().ok();
		let (state_tx, state_rx) = mpsc::unbounded::<(NetworkStatus<_>, NetworkState)>();
		network_status_sinks.lock().push(std::time::Duration::from_millis(5000), state_tx);
		let tel_task = state_rx.for_each(move |(net_status, _)| {
			let info = client_.info();
			let best_number = info.chain.best_number.saturated_into::<u64>();
			let best_hash = info.chain.best_hash;
			let num_peers = net_status.num_connected_peers;
			let txpool_status = transaction_pool_.status();
			let finalized_number: u64 = info.chain.finalized_number.saturated_into::<u64>();
			let bandwidth_download = net_status.average_download_per_sec;
			let bandwidth_upload = net_status.average_upload_per_sec;

			let used_state_cache_size = match info.used_state_cache_size {
				Some(size) => size,
				None => 0,
			};

			// get cpu usage and memory usage of this process
			let (cpu_usage, memory) = if let Some(self_pid) = self_pid {
				if sys.refresh_process(self_pid) {
					let proc = sys.get_process(self_pid)
						.expect("Above refresh_process succeeds, this should be Some(), qed");
					(proc.cpu_usage(), proc.memory())
				} else { (0.0, 0) }
			} else { (0.0, 0) };

			telemetry!(
				SUBSTRATE_INFO;
				"system.interval";
				"peers" => num_peers,
				"height" => best_number,
				"best" => ?best_hash,
				"txcount" => txpool_status.ready,
				"cpu" => cpu_usage,
				"memory" => memory,
				"finalized_height" => finalized_number,
				"finalized_hash" => ?info.chain.finalized_hash,
				"bandwidth_download" => bandwidth_download,
				"bandwidth_upload" => bandwidth_upload,
				"used_state_cache_size" => used_state_cache_size,
			);

			Ok(())
		}).select(exit.clone()).then(|_| Ok(()));
		let _ = to_spawn_tx.unbounded_send(Box::new(tel_task));

		// Periodically send the network state to the telemetry.
		let (netstat_tx, netstat_rx) = mpsc::unbounded::<(NetworkStatus<_>, NetworkState)>();
		network_status_sinks.lock().push(std::time::Duration::from_secs(30), netstat_tx);
		let tel_task_2 = netstat_rx.for_each(move |(_, network_state)| {
			telemetry!(
				SUBSTRATE_INFO;
				"system.network_state";
				"state" => network_state,
			);
			Ok(())
		}).select(exit.clone()).then(|_| Ok(()));
		let _ = to_spawn_tx.unbounded_send(Box::new(tel_task_2));

		// RPC
		let (system_rpc_tx, system_rpc_rx) = futures03::channel::mpsc::unbounded();
		let gen_handler = || {
			use rpc::{chain, state, author, system};

			let system_info = rpc::system::SystemInfo {
				chain_name: config.chain_spec.name().into(),
				impl_name: config.impl_name.into(),
				impl_version: config.impl_version.into(),
				properties: config.chain_spec.properties().clone(),
			};

			let subscriptions = rpc::Subscriptions::new(Arc::new(SpawnTaskHandle {
				sender: to_spawn_tx.clone(),
				on_exit: exit.clone()
			}));

			let (chain, state) = if let (Some(remote_backend), Some(on_demand)) =
				(remote_backend.as_ref(), on_demand.as_ref()) {
				// Light clients
				let chain = rpc::chain::new_light(
					client.clone(),
					subscriptions.clone(),
					remote_backend.clone(),
					on_demand.clone()
				);
				let state = rpc::state::new_light(
					client.clone(),
					subscriptions.clone(),
					remote_backend.clone(),
					on_demand.clone()
				);
				(chain, state)

			} else {
				// Full nodes
				let chain = rpc::chain::new_full(client.clone(), subscriptions.clone());
				let state = rpc::state::new_full(client.clone(), subscriptions.clone());
				(chain, state)
			};

			let author = rpc::author::Author::new(
				client.clone(),
				transaction_pool.clone(),
				subscriptions,
				keystore.clone(),
			);
			let system = system::System::new(system_info, system_rpc_tx.clone());

			rpc_servers::rpc_handler((
				state::StateApi::to_delegate(state),
				chain::ChainApi::to_delegate(chain),
				author::AuthorApi::to_delegate(author),
				system::SystemApi::to_delegate(system),
				rpc_extensions.clone(),
			))
		};
		let rpc_handlers = gen_handler();
		let rpc = start_rpc_servers(&config, gen_handler)?;


		let _ = to_spawn_tx.unbounded_send(Box::new(build_network_future(
			config.roles,
			network_mut,
			client.clone(),
			network_status_sinks.clone(),
			system_rpc_rx,
			has_bootnodes,
			dht_event_tx,
		)
			.map_err(|_| ())
			.select(exit.clone())
			.then(|_| Ok(()))));

		let telemetry_connection_sinks: Arc<Mutex<Vec<mpsc::UnboundedSender<()>>>> = Default::default();

		// Telemetry
		let telemetry = config.telemetry_endpoints.clone().map(|endpoints| {
			let is_authority = config.roles.is_authority();
			let network_id = network.local_peer_id().to_base58();
			let name = config.name.clone();
			let impl_name = config.impl_name.to_owned();
			let version = version.clone();
			let chain_name = config.chain_spec.name().to_owned();
			let telemetry_connection_sinks_ = telemetry_connection_sinks.clone();
			let telemetry = tel::init_telemetry(tel::TelemetryConfig {
				endpoints,
				wasm_external_transport: config.telemetry_external_transport.take(),
			});
			let future = telemetry.clone()
				.map(|ev| Ok::<_, ()>(ev))
				.compat()
				.for_each(move |event| {
					// Safe-guard in case we add more events in the future.
					let tel::TelemetryEvent::Connected = event;

					telemetry!(SUBSTRATE_INFO; "system.connected";
						"name" => name.clone(),
						"implementation" => impl_name.clone(),
						"version" => version.clone(),
						"config" => "",
						"chain" => chain_name.clone(),
						"authority" => is_authority,
						"network_id" => network_id.clone()
					);

					telemetry_connection_sinks_.lock().retain(|sink| {
						sink.unbounded_send(()).is_ok()
					});
					Ok(())
				});
			let _ = to_spawn_tx.unbounded_send(Box::new(future
				.select(exit.clone())
				.then(|_| Ok(()))));
			telemetry
		});

		Ok(Service {
			client,
			network,
			network_status_sinks,
			select_chain,
			transaction_pool,
			exit,
			signal: Some(signal),
			essential_failed: Arc::new(AtomicBool::new(false)),
			to_spawn_tx,
			to_spawn_rx,
			to_poll: Vec::new(),
			rpc_handlers,
			_rpc: rpc,
			_telemetry: telemetry,
			_offchain_workers: offchain_workers,
			_telemetry_on_connect_sinks: telemetry_connection_sinks.clone(),
			keystore,
			marker: PhantomData::<TBl>,
		})
	}
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
