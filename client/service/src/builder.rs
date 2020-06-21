// This file is part of Substrate.

// Copyright (C) 2017-2020 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

use crate::{
	Service, NetworkStatus, NetworkState, error::Error, DEFAULT_PROTOCOL_ID, MallocSizeOfWasm,
	start_rpc_servers, build_network_future, TransactionPoolAdapter, TaskManager, SpawnTaskHandle,
	status_sinks, metrics::MetricsService,
	client::{light, Client, ClientConfig},
	config::{Configuration, KeystoreConfig, PrometheusConfig, OffchainWorkerConfig},
};
use sc_client_api::{
	self, light::RemoteBlockchain, execution_extensions::ExtensionsFactory,
	ExecutorProvider, CallExecutor, ForkBlocks, BadBlocks, CloneableSpawn, UsageProvider,
	backend::RemoteBackend,
};
use sp_utils::mpsc::{tracing_unbounded, TracingUnboundedSender, TracingUnboundedReceiver};
use sc_chain_spec::get_extension;
use sp_consensus::{
	block_validation::{BlockAnnounceValidator, DefaultBlockAnnounceValidator},
	import_queue::ImportQueue,
};
use futures::{
	Future, FutureExt, StreamExt,
	future::ready,
};
use jsonrpc_pubsub::manager::SubscriptionManager;
use sc_keystore::Store as Keystore;
use log::{info, warn, error};
use sc_network::config::{Role, FinalityProofProvider, OnDemand, BoxFinalityProofRequestBuilder};
use sc_network::NetworkService;
use parking_lot::{Mutex, RwLock};
use sp_runtime::generic::BlockId;
use sp_runtime::traits::{
	Block as BlockT, NumberFor, SaturatedConversion, HashFor,
};
use sp_api::ProvideRuntimeApi;
use sc_executor::{NativeExecutor, NativeExecutionDispatch, RuntimeInfo};
use std::{
	collections::HashMap,
	io::{Read, Write, Seek},
	marker::PhantomData, sync::Arc, pin::Pin
};
use wasm_timer::SystemTime;
use sc_telemetry::{telemetry, SUBSTRATE_INFO};
use sp_transaction_pool::{LocalTransactionPool, MaintainedTransactionPool};
use prometheus_endpoint::Registry;
use sc_client_db::{Backend, DatabaseSettings};
use sp_core::traits::CodeExecutor;
use sp_runtime::BuildStorage;
use sc_client_api::execution_extensions::ExecutionExtensions;
use sp_core::storage::Storage;

pub type BackgroundTask = Pin<Box<dyn Future<Output=()> + Send>>;

/// Aggregator for the components required to build a service.
///
/// # Usage
///
/// Call [`ServiceBuilder::new_full`] or [`ServiceBuilder::new_light`], then call the various
/// `with_` methods to add the required components that you built yourself:
///
/// - [`with_select_chain`](ServiceBuilder::with_select_chain)
/// - [`with_import_queue`](ServiceBuilder::with_import_queue)
/// - [`with_finality_proof_provider`](ServiceBuilder::with_finality_proof_provider)
/// - [`with_transaction_pool`](ServiceBuilder::with_transaction_pool)
///
/// After this is done, call [`build`](ServiceBuilder::build) to construct the service.
///
/// The order in which the `with_*` methods are called doesn't matter, as the correct binding of
/// generics is done when you call `build`.
///
pub struct ServiceBuilder<TBl, TRtApi, TCl, TFchr, TSc, TImpQu, TFprb, TFpp,
	TExPool, TRpc, Backend>
{
	config: Configuration,
	pub (crate) client: Arc<TCl>,
	backend: Arc<Backend>,
	task_manager: TaskManager,
	keystore: Arc<RwLock<Keystore>>,
	fetcher: Option<TFchr>,
	select_chain: Option<TSc>,
	pub (crate) import_queue: TImpQu,
	finality_proof_request_builder: Option<TFprb>,
	finality_proof_provider: Option<TFpp>,
	transaction_pool: Arc<TExPool>,
	rpc_extensions_builder: Box<dyn RpcExtensionBuilder<Output = TRpc> + Send>,
	remote_backend: Option<Arc<dyn RemoteBlockchain<TBl>>>,
	marker: PhantomData<(TBl, TRtApi)>,
	block_announce_validator_builder: Option<Box<dyn FnOnce(Arc<TCl>) -> Box<dyn BlockAnnounceValidator<TBl> + Send> + Send>>,
	informant_prefix: String,
}

/// A utility trait for building an RPC extension given a `DenyUnsafe` instance.
/// This is useful since at service definition time we don't know whether the
/// specific interface where the RPC extension will be exposed is safe or not.
/// This trait allows us to lazily build the RPC extension whenever we bind the
/// service to an interface.
pub trait RpcExtensionBuilder {
	/// The type of the RPC extension that will be built.
	type Output: sc_rpc::RpcExtension<sc_rpc::Metadata>;

	/// Returns an instance of the RPC extension for a particular `DenyUnsafe`
	/// value, e.g. the RPC extension might not expose some unsafe methods.
	fn build(&self, deny: sc_rpc::DenyUnsafe) -> Self::Output;
}

impl<F, R> RpcExtensionBuilder for F where
	F: Fn(sc_rpc::DenyUnsafe) -> R,
	R: sc_rpc::RpcExtension<sc_rpc::Metadata>,
{
	type Output = R;

	fn build(&self, deny: sc_rpc::DenyUnsafe) -> Self::Output {
		(*self)(deny)
	}
}

/// A utility struct for implementing an `RpcExtensionBuilder` given a cloneable
/// `RpcExtension`, the resulting builder will simply ignore the provided
/// `DenyUnsafe` instance and return a static `RpcExtension` instance.
struct NoopRpcExtensionBuilder<R>(R);

impl<R> RpcExtensionBuilder for NoopRpcExtensionBuilder<R> where
	R: Clone + sc_rpc::RpcExtension<sc_rpc::Metadata>,
{
	type Output = R;

	fn build(&self, _deny: sc_rpc::DenyUnsafe) -> Self::Output {
		self.0.clone()
	}
}

impl<R> From<R> for NoopRpcExtensionBuilder<R> where
	R: sc_rpc::RpcExtension<sc_rpc::Metadata>,
{
	fn from(e: R) -> NoopRpcExtensionBuilder<R> {
		NoopRpcExtensionBuilder(e)
	}
}


/// Full client type.
pub type TFullClient<TBl, TRtApi, TExecDisp> = Client<
	TFullBackend<TBl>,
	TFullCallExecutor<TBl, TExecDisp>,
	TBl,
	TRtApi,
>;

/// Full client backend type.
pub type TFullBackend<TBl> = sc_client_db::Backend<TBl>;

/// Full client call executor type.
pub type TFullCallExecutor<TBl, TExecDisp> = crate::client::LocalCallExecutor<
	sc_client_db::Backend<TBl>,
	NativeExecutor<TExecDisp>,
>;

/// Light client type.
pub type TLightClient<TBl, TRtApi, TExecDisp> = Client<
	TLightBackend<TBl>,
	TLightCallExecutor<TBl, TExecDisp>,
	TBl,
	TRtApi,
>;

/// Light client backend type.
pub type TLightBackend<TBl> = sc_light::Backend<
	sc_client_db::light::LightStorage<TBl>,
	HashFor<TBl>,
>;

/// Light call executor type.
pub type TLightCallExecutor<TBl, TExecDisp> = sc_light::GenesisCallExecutor<
	sc_light::Backend<
		sc_client_db::light::LightStorage<TBl>,
		HashFor<TBl>
	>,
	crate::client::LocalCallExecutor<
		sc_light::Backend<
			sc_client_db::light::LightStorage<TBl>,
			HashFor<TBl>
		>,
		NativeExecutor<TExecDisp>
	>,
>;

type TFullParts<TBl, TRtApi, TExecDisp> = (
	TFullClient<TBl, TRtApi, TExecDisp>,
	Arc<TFullBackend<TBl>>,
	Arc<RwLock<sc_keystore::Store>>,
	TaskManager,
);

/// Creates a new full client for the given config.
pub fn new_full_client<TBl, TRtApi, TExecDisp>(
	config: &Configuration,
) -> Result<TFullClient<TBl, TRtApi, TExecDisp>, Error> where
	TBl: BlockT,
	TExecDisp: NativeExecutionDispatch + 'static,
{
	new_full_parts(config).map(|parts| parts.0)
}

fn new_full_parts<TBl, TRtApi, TExecDisp>(
	config: &Configuration,
) -> Result<TFullParts<TBl, TRtApi, TExecDisp>,	Error> where
	TBl: BlockT,
	TExecDisp: NativeExecutionDispatch + 'static,
{
	let keystore = match &config.keystore {
		KeystoreConfig::Path { path, password } => Keystore::open(
			path.clone(),
			password.clone()
		)?,
		KeystoreConfig::InMemory => Keystore::new_in_memory(),
	};

	let task_manager = {
		let registry = config.prometheus_config.as_ref().map(|cfg| &cfg.registry);
		TaskManager::new(config.task_executor.clone(), registry)?
	};

	let executor = NativeExecutor::<TExecDisp>::new(
		config.wasm_method,
		config.default_heap_pages,
		config.max_runtime_instances,
	);

	let chain_spec = &config.chain_spec;
	let fork_blocks = get_extension::<ForkBlocks<TBl>>(chain_spec.extensions())
		.cloned()
		.unwrap_or_default();

	let bad_blocks = get_extension::<BadBlocks<TBl>>(chain_spec.extensions())
		.cloned()
		.unwrap_or_default();

	let (client, backend) = {
		let db_config = sc_client_db::DatabaseSettings {
			state_cache_size: config.state_cache_size,
			state_cache_child_ratio:
			config.state_cache_child_ratio.map(|v| (v, 100)),
			pruning: config.pruning.clone(),
			source: config.database.clone(),
		};

		let extensions = sc_client_api::execution_extensions::ExecutionExtensions::new(
			config.execution_strategies.clone(),
			Some(keystore.clone()),
		);

		new_client(
			db_config,
			executor,
			chain_spec.as_storage_builder(),
			fork_blocks,
			bad_blocks,
			extensions,
			Box::new(task_manager.spawn_handle()),
			config.prometheus_config.as_ref().map(|config| config.registry.clone()),
			ClientConfig {
				offchain_worker_enabled : config.offchain_worker.enabled ,
				offchain_indexing_api: config.offchain_worker.indexing_enabled,
			},
		)?
	};

	Ok((client, backend, keystore, task_manager))
}


/// Create an instance of db-backed client.
pub fn new_client<E, Block, RA>(
	settings: DatabaseSettings,
	executor: E,
	genesis_storage: &dyn BuildStorage,
	fork_blocks: ForkBlocks<Block>,
	bad_blocks: BadBlocks<Block>,
	execution_extensions: ExecutionExtensions<Block>,
	spawn_handle: Box<dyn CloneableSpawn>,
	prometheus_registry: Option<Registry>,
	config: ClientConfig,
) -> Result<(
	crate::client::Client<
		Backend<Block>,
		crate::client::LocalCallExecutor<Backend<Block>, E>,
		Block,
		RA,
	>,
	Arc<Backend<Block>>,
),
	sp_blockchain::Error,
>
	where
		Block: BlockT,
		E: CodeExecutor + RuntimeInfo,
{
	const CANONICALIZATION_DELAY: u64 = 4096;

	let backend = Arc::new(Backend::new(settings, CANONICALIZATION_DELAY)?);
	let executor = crate::client::LocalCallExecutor::new(backend.clone(), executor, spawn_handle, config.clone());
	Ok((
		crate::client::Client::new(
			backend.clone(),
			executor,
			genesis_storage,
			fork_blocks,
			bad_blocks,
			execution_extensions,
			prometheus_registry,
			config,
		)?,
		backend,
	))
}

impl ServiceBuilder<(), (), (), (), (), (), (), (), (), (), ()> {
	/// Start the service builder with a configuration.
	pub fn new_full<TBl: BlockT, TRtApi, TExecDisp: NativeExecutionDispatch + 'static>(
		config: Configuration,
	) -> Result<ServiceBuilder<
		TBl,
		TRtApi,
		TFullClient<TBl, TRtApi, TExecDisp>,
		Arc<OnDemand<TBl>>,
		(),
		(),
		BoxFinalityProofRequestBuilder<TBl>,
		Arc<dyn FinalityProofProvider<TBl>>,
		(),
		(),
		TFullBackend<TBl>,
	>, Error> {
		let (client, backend, keystore, task_manager) = new_full_parts(&config)?;

		let client = Arc::new(client);

		Ok(ServiceBuilder {
			config,
			client,
			backend,
			keystore,
			task_manager,
			fetcher: None,
			select_chain: None,
			import_queue: (),
			finality_proof_request_builder: None,
			finality_proof_provider: None,
			transaction_pool: Arc::new(()),
			rpc_extensions_builder: Box::new(|_| ()),
			remote_backend: None,
			block_announce_validator_builder: None,
			informant_prefix: Default::default(),
			marker: PhantomData,
		})
	}

	/// Start the service builder with a configuration.
	pub fn new_light<TBl: BlockT, TRtApi, TExecDisp: NativeExecutionDispatch + 'static>(
		config: Configuration,
	) -> Result<ServiceBuilder<
		TBl,
		TRtApi,
		TLightClient<TBl, TRtApi, TExecDisp>,
		Arc<OnDemand<TBl>>,
		(),
		(),
		BoxFinalityProofRequestBuilder<TBl>,
		Arc<dyn FinalityProofProvider<TBl>>,
		(),
		(),
		TLightBackend<TBl>,
	>, Error> {
		let task_manager = {
			let registry = config.prometheus_config.as_ref().map(|cfg| &cfg.registry);
			TaskManager::new(config.task_executor.clone(), registry)?
		};

		let keystore = match &config.keystore {
			KeystoreConfig::Path { path, password } => Keystore::open(
				path.clone(),
				password.clone()
			)?,
			KeystoreConfig::InMemory => Keystore::new_in_memory(),
		};

		let executor = NativeExecutor::<TExecDisp>::new(
			config.wasm_method,
			config.default_heap_pages,
			config.max_runtime_instances,
		);

		let db_storage = {
			let db_settings = sc_client_db::DatabaseSettings {
				state_cache_size: config.state_cache_size,
				state_cache_child_ratio:
					config.state_cache_child_ratio.map(|v| (v, 100)),
				pruning: config.pruning.clone(),
				source: config.database.clone(),
			};
			sc_client_db::light::LightStorage::new(db_settings)?
		};
		let light_blockchain = sc_light::new_light_blockchain(db_storage);
		let fetch_checker = Arc::new(
			sc_light::new_fetch_checker::<_, TBl, _>(
				light_blockchain.clone(),
				executor.clone(),
				Box::new(task_manager.spawn_handle()),
			),
		);
		let fetcher = Arc::new(sc_network::config::OnDemand::new(fetch_checker));
		let backend = sc_light::new_light_backend(light_blockchain);
		let remote_blockchain = backend.remote_blockchain();
		let client = Arc::new(light::new_light(
			backend.clone(),
			config.chain_spec.as_storage_builder(),
			executor,
			Box::new(task_manager.spawn_handle()),
			config.prometheus_config.as_ref().map(|config| config.registry.clone()),
		)?);

		Ok(ServiceBuilder {
			config,
			client,
			backend,
			task_manager,
			keystore,
			fetcher: Some(fetcher.clone()),
			select_chain: None,
			import_queue: (),
			finality_proof_request_builder: None,
			finality_proof_provider: None,
			transaction_pool: Arc::new(()),
			rpc_extensions_builder: Box::new(|_| ()),
			remote_backend: Some(remote_blockchain),
			block_announce_validator_builder: None,
			informant_prefix: Default::default(),
			marker: PhantomData,
		})
	}
}

impl<TBl, TRtApi, TCl, TFchr, TSc, TImpQu, TFprb, TFpp, TExPool, TRpc, Backend>
	ServiceBuilder<
		TBl,
		TRtApi,
		TCl,
		TFchr,
		TSc,
		TImpQu,
		TFprb,
		TFpp,
		TExPool,
		TRpc,
		Backend
	>
{
	/// Returns a reference to the configuration that was stored in this builder.
	pub fn config(&self) -> &Configuration {
		&self.config
	}

	/// Returns a reference to the optional prometheus registry that was stored in this builder.
	pub fn prometheus_registry(&self) -> Option<&Registry> {
		self.config.prometheus_config.as_ref().map(|config| &config.registry)
	}

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

	/// Returns a reference to the keystore
	pub fn keystore(&self) -> Arc<RwLock<Keystore>> {
		self.keystore.clone()
	}

	/// Returns a reference to the transaction pool stored in this builder
	pub fn pool(&self) -> Arc<TExPool> {
		self.transaction_pool.clone()
	}

	/// Returns a reference to the fetcher, only available if builder
	/// was created with `new_light`.
	pub fn fetcher(&self) -> Option<TFchr>
		where TFchr: Clone
	{
		self.fetcher.clone()
	}

	/// Returns a reference to the remote_backend, only available if builder
	/// was created with `new_light`.
	pub fn remote_backend(&self) -> Option<Arc<dyn RemoteBlockchain<TBl>>> {
		self.remote_backend.clone()
	}

	/// Defines which head-of-chain strategy to use.
	pub fn with_opt_select_chain<USc>(
		self,
		select_chain_builder: impl FnOnce(
			&Configuration, &Arc<Backend>,
		) -> Result<Option<USc>, Error>
	) -> Result<ServiceBuilder<TBl, TRtApi, TCl, TFchr, USc, TImpQu, TFprb, TFpp,
		TExPool, TRpc, Backend>, Error> {
		let select_chain = select_chain_builder(&self.config, &self.backend)?;

		Ok(ServiceBuilder {
			config: self.config,
			client: self.client,
			backend: self.backend,
			task_manager: self.task_manager,
			keystore: self.keystore,
			fetcher: self.fetcher,
			select_chain,
			import_queue: self.import_queue,
			finality_proof_request_builder: self.finality_proof_request_builder,
			finality_proof_provider: self.finality_proof_provider,
			transaction_pool: self.transaction_pool,
			rpc_extensions_builder: self.rpc_extensions_builder,
			remote_backend: self.remote_backend,
			block_announce_validator_builder: self.block_announce_validator_builder,
			informant_prefix: self.informant_prefix,
			marker: self.marker,
		})
	}

	/// Defines which head-of-chain strategy to use.
	pub fn with_select_chain<USc>(
		self,
		builder: impl FnOnce(&Configuration, &Arc<Backend>) -> Result<USc, Error>,
	) -> Result<ServiceBuilder<TBl, TRtApi, TCl, TFchr, USc, TImpQu, TFprb, TFpp,
		TExPool, TRpc, Backend>, Error> {
		self.with_opt_select_chain(|cfg, b| builder(cfg, b).map(Option::Some))
	}

	/// Defines which import queue to use.
	pub fn with_import_queue<UImpQu>(
		self,
		builder: impl FnOnce(&Configuration, Arc<TCl>, Option<TSc>, Arc<TExPool>, &SpawnTaskHandle, Option<&Registry>)
			-> Result<UImpQu, Error>
	) -> Result<ServiceBuilder<TBl, TRtApi, TCl, TFchr, TSc, UImpQu, TFprb, TFpp,
			TExPool, TRpc, Backend>, Error>
	where TSc: Clone {
		let import_queue = builder(
			&self.config,
			self.client.clone(),
			self.select_chain.clone(),
			self.transaction_pool.clone(),
			&self.task_manager.spawn_handle(),
			self.config.prometheus_config.as_ref().map(|config| &config.registry),
		)?;

		Ok(ServiceBuilder {
			config: self.config,
			client: self.client,
			backend: self.backend,
			task_manager: self.task_manager,
			keystore: self.keystore,
			fetcher: self.fetcher,
			select_chain: self.select_chain,
			import_queue,
			finality_proof_request_builder: self.finality_proof_request_builder,
			finality_proof_provider: self.finality_proof_provider,
			transaction_pool: self.transaction_pool,
			rpc_extensions_builder: self.rpc_extensions_builder,
			remote_backend: self.remote_backend,
			block_announce_validator_builder: self.block_announce_validator_builder,
			informant_prefix: self.informant_prefix,
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
		TCl,
		TFchr,
		TSc,
		TImpQu,
		TFprb,
		Arc<dyn FinalityProofProvider<TBl>>,
		TExPool,
		TRpc,
		Backend,
	>, Error> {
		let finality_proof_provider = builder(self.client.clone(), self.backend.clone())?;

		Ok(ServiceBuilder {
			config: self.config,
			client: self.client,
			backend: self.backend,
			task_manager: self.task_manager,
			keystore: self.keystore,
			fetcher: self.fetcher,
			select_chain: self.select_chain,
			import_queue: self.import_queue,
			finality_proof_request_builder: self.finality_proof_request_builder,
			finality_proof_provider,
			transaction_pool: self.transaction_pool,
			rpc_extensions_builder: self.rpc_extensions_builder,
			remote_backend: self.remote_backend,
			block_announce_validator_builder: self.block_announce_validator_builder,
			informant_prefix: self.informant_prefix,
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
		TCl,
		TFchr,
		TSc,
		TImpQu,
		TFprb,
		Arc<dyn FinalityProofProvider<TBl>>,
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
			&Configuration,
			Arc<TCl>,
			Arc<Backend>,
			Option<TFchr>,
			Option<TSc>,
			Arc<TExPool>,
			&SpawnTaskHandle,
			Option<&Registry>,
		) -> Result<(UImpQu, Option<UFprb>), Error>
	) -> Result<ServiceBuilder<TBl, TRtApi, TCl, TFchr, TSc, UImpQu, UFprb, TFpp,
		TExPool, TRpc, Backend>, Error>
	where TSc: Clone, TFchr: Clone {
		let (import_queue, fprb) = builder(
			&self.config,
			self.client.clone(),
			self.backend.clone(),
			self.fetcher.clone(),
			self.select_chain.clone(),
			self.transaction_pool.clone(),
			&self.task_manager.spawn_handle(),
			self.config.prometheus_config.as_ref().map(|config| &config.registry),
		)?;

		Ok(ServiceBuilder {
			config: self.config,
			client: self.client,
			backend: self.backend,
			task_manager: self.task_manager,
			keystore: self.keystore,
			fetcher: self.fetcher,
			select_chain: self.select_chain,
			import_queue,
			finality_proof_request_builder: fprb,
			finality_proof_provider: self.finality_proof_provider,
			transaction_pool: self.transaction_pool,
			rpc_extensions_builder: self.rpc_extensions_builder,
			remote_backend: self.remote_backend,
			block_announce_validator_builder: self.block_announce_validator_builder,
			informant_prefix: self.informant_prefix,
			marker: self.marker,
		})
	}

	/// Defines which import queue to use.
	pub fn with_import_queue_and_fprb<UImpQu, UFprb>(
		self,
		builder: impl FnOnce(
			&Configuration,
			Arc<TCl>,
			Arc<Backend>,
			Option<TFchr>,
			Option<TSc>,
			Arc<TExPool>,
			&SpawnTaskHandle,
			Option<&Registry>,
		) -> Result<(UImpQu, UFprb), Error>
	) -> Result<ServiceBuilder<TBl, TRtApi, TCl, TFchr, TSc, UImpQu, UFprb, TFpp,
			TExPool, TRpc, Backend>, Error>
	where TSc: Clone, TFchr: Clone {
		self.with_import_queue_and_opt_fprb(|cfg, cl, b, f, sc, tx, tb, pr|
			builder(cfg, cl, b, f, sc, tx, tb, pr)
				.map(|(q, f)| (q, Some(f)))
		)
	}

	/// Defines which transaction pool to use.
	pub fn with_transaction_pool<UExPool>(
		self,
		transaction_pool_builder: impl FnOnce(
			&Self,
		) -> Result<(UExPool, Option<BackgroundTask>), Error>,
	) -> Result<ServiceBuilder<TBl, TRtApi, TCl, TFchr, TSc, TImpQu, TFprb, TFpp,
		UExPool, TRpc, Backend>, Error>
	where TSc: Clone, TFchr: Clone {
		let (transaction_pool, background_task) = transaction_pool_builder(&self)?;

		if let Some(background_task) = background_task{
			self.task_manager.spawn_handle().spawn("txpool-background", background_task);
		}

		Ok(ServiceBuilder {
			config: self.config,
			client: self.client,
			task_manager: self.task_manager,
			backend: self.backend,
			keystore: self.keystore,
			fetcher: self.fetcher,
			select_chain: self.select_chain,
			import_queue: self.import_queue,
			finality_proof_request_builder: self.finality_proof_request_builder,
			finality_proof_provider: self.finality_proof_provider,
			transaction_pool: Arc::new(transaction_pool),
			rpc_extensions_builder: self.rpc_extensions_builder,
			remote_backend: self.remote_backend,
			block_announce_validator_builder: self.block_announce_validator_builder,
			informant_prefix: self.informant_prefix,
			marker: self.marker,
		})
	}

	/// Defines the RPC extension builder to use. Unlike `with_rpc_extensions`,
	/// this method is useful in situations where the RPC extensions need to
	/// access to a `DenyUnsafe` instance to avoid exposing sensitive methods.
	pub fn with_rpc_extensions_builder<URpcBuilder, URpc>(
		self,
		rpc_extensions_builder: impl FnOnce(&Self) -> Result<URpcBuilder, Error>,
	) -> Result<
		ServiceBuilder<TBl, TRtApi, TCl, TFchr, TSc, TImpQu, TFprb, TFpp, TExPool, URpc, Backend>,
		Error,
	>
	where
		TSc: Clone,
		TFchr: Clone,
		URpcBuilder: RpcExtensionBuilder<Output = URpc> + Send + 'static,
		URpc: sc_rpc::RpcExtension<sc_rpc::Metadata>,
	{
		let rpc_extensions_builder = rpc_extensions_builder(&self)?;

		Ok(ServiceBuilder {
			config: self.config,
			client: self.client,
			backend: self.backend,
			task_manager: self.task_manager,
			keystore: self.keystore,
			fetcher: self.fetcher,
			select_chain: self.select_chain,
			import_queue: self.import_queue,
			finality_proof_request_builder: self.finality_proof_request_builder,
			finality_proof_provider: self.finality_proof_provider,
			transaction_pool: self.transaction_pool,
			rpc_extensions_builder: Box::new(rpc_extensions_builder),
			remote_backend: self.remote_backend,
			block_announce_validator_builder: self.block_announce_validator_builder,
			informant_prefix: self.informant_prefix,
			marker: self.marker,
		})
	}

	/// Defines the RPC extensions to use.
	pub fn with_rpc_extensions<URpc>(
		self,
		rpc_extensions: impl FnOnce(&Self) -> Result<URpc, Error>,
	) -> Result<
		ServiceBuilder<TBl, TRtApi, TCl, TFchr, TSc, TImpQu, TFprb, TFpp, TExPool, URpc, Backend>,
		Error,
	>
	where
		TSc: Clone,
		TFchr: Clone,
		URpc: Clone + sc_rpc::RpcExtension<sc_rpc::Metadata> + Send + 'static,
	{
		let rpc_extensions = rpc_extensions(&self)?;
		self.with_rpc_extensions_builder(|_| Ok(NoopRpcExtensionBuilder::from(rpc_extensions)))
	}

	/// Defines the `BlockAnnounceValidator` to use. `DefaultBlockAnnounceValidator` will be used by
	/// default.
	pub fn with_block_announce_validator(
		self,
		block_announce_validator_builder:
			impl FnOnce(Arc<TCl>) -> Box<dyn BlockAnnounceValidator<TBl> + Send> + Send + 'static,
	) -> Result<ServiceBuilder<TBl, TRtApi, TCl, TFchr, TSc, TImpQu, TFprb, TFpp,
		TExPool, TRpc, Backend>, Error>
	where TSc: Clone, TFchr: Clone {
		Ok(ServiceBuilder {
			config: self.config,
			client: self.client,
			backend: self.backend,
			task_manager: self.task_manager,
			keystore: self.keystore,
			fetcher: self.fetcher,
			select_chain: self.select_chain,
			import_queue: self.import_queue,
			finality_proof_request_builder: self.finality_proof_request_builder,
			finality_proof_provider: self.finality_proof_provider,
			transaction_pool: self.transaction_pool,
			rpc_extensions_builder: self.rpc_extensions_builder,
			remote_backend: self.remote_backend,
			block_announce_validator_builder: Some(Box::new(block_announce_validator_builder)),
			informant_prefix: self.informant_prefix,
			marker: self.marker,
		})
	}

	/// Defines the informant's prefix for the logs. An empty string by default.
	///
	/// By default substrate will show logs without a prefix. Example:
	///
	/// ```text
	/// 2020-05-28 15:11:06 ✨ Imported #2 (0xc21c…2ca8)
	/// 2020-05-28 15:11:07 💤 Idle (0 peers), best: #2 (0xc21c…2ca8), finalized #0 (0x7299…e6df), ⬇ 0 ⬆ 0
	/// ```
	///
	/// But you can define a prefix by using this function. Example:
	///
	/// ```rust,ignore
	/// service.with_informant_prefix("[Prefix] ".to_string());
	/// ```
	///
	/// This will output:
	///
	/// ```text
	/// 2020-05-28 15:11:06 ✨ [Prefix] Imported #2 (0xc21c…2ca8)
	/// 2020-05-28 15:11:07 💤 [Prefix] Idle (0 peers), best: #2 (0xc21c…2ca8), finalized #0 (0x7299…e6df), ⬇ 0 ⬆ 0
	/// ```
	pub fn with_informant_prefix(
		self,
		informant_prefix: String,
	) -> Result<ServiceBuilder<TBl, TRtApi, TCl, TFchr, TSc, TImpQu, TFprb, TFpp,
		TExPool, TRpc, Backend>, Error>
	where TSc: Clone, TFchr: Clone {
		Ok(ServiceBuilder {
			informant_prefix: informant_prefix,
			..self
		})
	}
}

/// Implemented on `ServiceBuilder`. Allows running block commands, such as import/export/validate
/// components to the builder.
pub trait ServiceBuilderCommand {
	/// Block type this API operates on.
	type Block: BlockT;
	/// Native execution dispatch required by some commands.
	type NativeDispatch: NativeExecutionDispatch + 'static;
	/// Starts the process of importing blocks.
	fn import_blocks(
		self,
		input: impl Read + Seek + Send + 'static,
		force: bool,
		binary: bool,
	) -> Pin<Box<dyn Future<Output = Result<(), Error>> + Send>>;

	/// Performs the blocks export.
	fn export_blocks(
		self,
		output: impl Write + 'static,
		from: NumberFor<Self::Block>,
		to: Option<NumberFor<Self::Block>>,
		binary: bool
	) -> Pin<Box<dyn Future<Output = Result<(), Error>>>>;

	/// Performs a revert of `blocks` blocks.
	fn revert_chain(
		&self,
		blocks: NumberFor<Self::Block>
	) -> Result<(), Error>;

	/// Re-validate known block.
	fn check_block(
		self,
		block: BlockId<Self::Block>
	) -> Pin<Box<dyn Future<Output = Result<(), Error>> + Send>>;

	/// Export the raw state at the given `block`. If `block` is `None`, the
	/// best block will be used.
	fn export_raw_state(
		&self,
		block: Option<BlockId<Self::Block>>,
	) -> Result<Storage, Error>;
}

impl<TBl, TRtApi, TBackend, TExec, TSc, TImpQu, TExPool, TRpc>
ServiceBuilder<
	TBl,
	TRtApi,
	Client<TBackend, TExec, TBl, TRtApi>,
	Arc<OnDemand<TBl>>,
	TSc,
	TImpQu,
	BoxFinalityProofRequestBuilder<TBl>,
	Arc<dyn FinalityProofProvider<TBl>>,
	TExPool,
	TRpc,
	TBackend,
> where
	Client<TBackend, TExec, TBl, TRtApi>: ProvideRuntimeApi<TBl>,
	<Client<TBackend, TExec, TBl, TRtApi> as ProvideRuntimeApi<TBl>>::Api:
		sp_api::Metadata<TBl> +
		sc_offchain::OffchainWorkerApi<TBl> +
		sp_transaction_pool::runtime_api::TaggedTransactionQueue<TBl> +
		sp_session::SessionKeys<TBl> +
		sp_api::ApiErrorExt<Error = sp_blockchain::Error> +
		sp_api::ApiExt<TBl, StateBackend = TBackend::State>,
	TBl: BlockT,
	TRtApi: 'static + Send + Sync,
	TBackend: 'static + sc_client_api::backend::Backend<TBl> + Send,
	TExec: 'static + CallExecutor<TBl> + Send + Sync + Clone,
	TSc: Clone,
	TImpQu: 'static + ImportQueue<TBl>,
	TExPool: MaintainedTransactionPool<Block=TBl, Hash = <TBl as BlockT>::Hash> + MallocSizeOfWasm + 'static,
	TRpc: sc_rpc::RpcExtension<sc_rpc::Metadata>,
{

	/// Set an ExecutionExtensionsFactory
	pub fn with_execution_extensions_factory(self, execution_extensions_factory: Box<dyn ExtensionsFactory>) -> Result<Self, Error> {
		self.client.execution_extensions().set_extensions_factory(execution_extensions_factory);
		Ok(self)
	}

	fn build_common(self) -> Result<Service<
		TBl,
		Client<TBackend, TExec, TBl, TRtApi>,
		TSc,
		NetworkStatus<TBl>,
		NetworkService<TBl, <TBl as BlockT>::Hash>,
		TExPool,
		sc_offchain::OffchainWorkers<
			Client<TBackend, TExec, TBl, TRtApi>,
			TBackend::OffchainStorage,
			TBl
		>,
	>, Error>
		where TExec: CallExecutor<TBl, Backend = TBackend>,
	{
		let ServiceBuilder {
			marker: _,
			mut config,
			client,
			task_manager,
			fetcher: on_demand,
			backend,
			keystore,
			select_chain,
			import_queue,
			finality_proof_request_builder,
			finality_proof_provider,
			transaction_pool,
			rpc_extensions_builder,
			remote_backend,
			block_announce_validator_builder,
			informant_prefix,
		} = self;

		sp_session::generate_initial_session_keys(
			client.clone(),
			&BlockId::Hash(client.chain_info().best_hash),
			config.dev_key_seed.clone().map(|s| vec![s]).unwrap_or_default(),
		)?;

		// A side-channel for essential tasks to communicate shutdown.
		let (essential_failed_tx, essential_failed_rx) = tracing_unbounded("mpsc_essential_tasks");

		let chain_info = client.chain_info();

		info!("📦 Highest known block at #{}", chain_info.best_number);
		telemetry!(
			SUBSTRATE_INFO;
			"node.start";
			"height" => chain_info.best_number.saturated_into::<u64>(),
			"best" => ?chain_info.best_hash
		);

		let spawn_handle = task_manager.spawn_handle();
		let (system_rpc_tx, system_rpc_rx) = tracing_unbounded("mpsc_system_rpc");

		let (network, network_status_sinks, network_future) = build_network(
			&config, client.clone(), transaction_pool.clone(), Clone::clone(&spawn_handle), on_demand.clone(),
			block_announce_validator_builder, finality_proof_request_builder, finality_proof_provider,
			system_rpc_rx, import_queue
		)?;

		// The network worker is responsible for gathering all network messages and processing
		// them. This is quite a heavy task, and at the time of the writing of this comment it
		// frequently happens that this future takes several seconds or in some situations
		// even more than a minute until it has processed its entire queue. This is clearly an
		// issue, and ideally we would like to fix the network future to take as little time as
		// possible, but we also take the extra harm-prevention measure to execute the networking
		// future using `spawn_blocking`.
		spawn_handle.spawn_blocking(
			"network-worker",
			network_future
		);

		let offchain_storage = backend.offchain_storage();
		let offchain_workers = match (config.offchain_worker.clone(), offchain_storage.clone()) {
			(OffchainWorkerConfig {enabled: true, .. }, Some(db)) => {
				Some(Arc::new(sc_offchain::OffchainWorkers::new(client.clone(), db)))
			},
			(OffchainWorkerConfig {enabled: true, .. }, None) => {
				warn!("Offchain workers disabled, due to lack of offchain storage support in backend.");
				None
			},
			_ => None,
		};

		// Inform the tx pool about imported and finalized blocks.
		spawn_handle.spawn(
			"txpool-notifications",
			sc_transaction_pool::notification_future(client.clone(), transaction_pool.clone()),
		);

		// Inform the offchain worker about new imported blocks
		if let Some(offchain) = offchain_workers.clone() {
			spawn_handle.spawn(
				"offchain-notifications",
				sc_offchain::notification_future(
					config.role.is_authority(),
					client.clone(),
					offchain,
					task_manager.spawn_handle(),
					network.clone()
				)
			);
		}

		spawn_handle.spawn(
			"on-transaction-imported",
			transaction_notifications(transaction_pool.clone(), network.clone()),
		);

		// Prometheus metrics.
		let metrics_service = if let Some(PrometheusConfig { port, registry }) = config.prometheus_config.clone() {
			// Set static metrics.
			let metrics = MetricsService::with_prometheus(
				&registry,
				&config.network.node_name,
				&config.impl_version,
				&config.role,
			)?;
			spawn_handle.spawn(
				"prometheus-endpoint",
				prometheus_endpoint::init_prometheus(port, registry).map(drop)
			);

			metrics
		} else {
			MetricsService::new()
		};

		// Periodically notify the telemetry.
		spawn_handle.spawn("telemetry-periodic-send", telemetry_periodic_send(
			client.clone(), transaction_pool.clone(), metrics_service, network_status_sinks.clone()
		));

		// Periodically send the network state to the telemetry.
		spawn_handle.spawn(
			"telemetry-periodic-network-state",
			telemetry_periodic_network_state(network_status_sinks.clone()),
		);

		// RPC
		let gen_handler = |deny_unsafe: sc_rpc::DenyUnsafe| gen_handler(
			deny_unsafe, &config, &task_manager, client.clone(), transaction_pool.clone(),
			keystore.clone(), on_demand.clone(), remote_backend.clone(), &*rpc_extensions_builder,
			offchain_storage.clone(), system_rpc_tx.clone()
		);
		let rpc = start_rpc_servers(&config, gen_handler)?;
		// This is used internally, so don't restrict access to unsafe RPC
		let rpc_handlers = gen_handler(sc_rpc::DenyUnsafe::No);

		let telemetry_connection_sinks: Arc<Mutex<Vec<TracingUnboundedSender<()>>>> = Default::default();

		// Telemetry
		let telemetry = config.telemetry_endpoints.clone().map(|endpoints| {
			let (telemetry, future) = build_telemetry(
				&mut config, endpoints, telemetry_connection_sinks.clone(), network.clone()
			);

			spawn_handle.spawn(
				"telemetry-worker",
				future,
			);

			telemetry
		});

		// Instrumentation
		if let Some(tracing_targets) = config.tracing_targets.as_ref() {
			let subscriber = sc_tracing::ProfilingSubscriber::new(
				config.tracing_receiver, tracing_targets
			);
			match tracing::subscriber::set_global_default(subscriber) {
				Ok(_) => (),
				Err(e) => error!(target: "tracing", "Unable to set global default subscriber {}", e),
			}
		}

		// Spawn informant task
		spawn_handle.spawn("informant", sc_informant::build(
			client.clone(),
			network_status_sinks.clone(),
			transaction_pool.clone(),
			sc_informant::OutputFormat { enable_color: true, prefix: informant_prefix },
		));

		Ok(Service {
			client,
			task_manager,
			network,
			network_status_sinks,
			select_chain,
			transaction_pool,
			essential_failed_tx,
			essential_failed_rx,
			rpc_handlers,
			_rpc: rpc,
			_telemetry: telemetry,
			_offchain_workers: offchain_workers,
			_telemetry_on_connect_sinks: telemetry_connection_sinks.clone(),
			keystore,
			marker: PhantomData::<TBl>,
			prometheus_registry: config.prometheus_config.map(|config| config.registry),
			_base_path: config.base_path.map(Arc::new),
		})
	}

	/// Builds the light service.
	pub fn build_light(self) -> Result<Service<
		TBl,
		Client<TBackend, TExec, TBl, TRtApi>,
		TSc,
		NetworkStatus<TBl>,
		NetworkService<TBl, <TBl as BlockT>::Hash>,
		TExPool,
		sc_offchain::OffchainWorkers<
			Client<TBackend, TExec, TBl, TRtApi>,
			TBackend::OffchainStorage,
			TBl
		>,
	>, Error>
		where TExec: CallExecutor<TBl, Backend = TBackend>,
	{
		self.build_common()
	}
}

impl<TBl, TRtApi, TBackend, TExec, TSc, TImpQu, TExPool, TRpc>
ServiceBuilder<
	TBl,
	TRtApi,
	Client<TBackend, TExec, TBl, TRtApi>,
	Arc<OnDemand<TBl>>,
	TSc,
	TImpQu,
	BoxFinalityProofRequestBuilder<TBl>,
	Arc<dyn FinalityProofProvider<TBl>>,
	TExPool,
	TRpc,
	TBackend,
> where
	Client<TBackend, TExec, TBl, TRtApi>: ProvideRuntimeApi<TBl>,
	<Client<TBackend, TExec, TBl, TRtApi> as ProvideRuntimeApi<TBl>>::Api:
		sp_api::Metadata<TBl> +
		sc_offchain::OffchainWorkerApi<TBl> +
		sp_transaction_pool::runtime_api::TaggedTransactionQueue<TBl> +
		sp_session::SessionKeys<TBl> +
		sp_api::ApiErrorExt<Error = sp_blockchain::Error> +
		sp_api::ApiExt<TBl, StateBackend = TBackend::State>,
	TBl: BlockT,
	TRtApi: 'static + Send + Sync,
	TBackend: 'static + sc_client_api::backend::Backend<TBl> + Send,
	TExec: 'static + CallExecutor<TBl> + Send + Sync + Clone,
	TSc: Clone,
	TImpQu: 'static + ImportQueue<TBl>,
	TExPool: MaintainedTransactionPool<Block = TBl, Hash = <TBl as BlockT>::Hash> +
		LocalTransactionPool<Block = TBl, Hash = <TBl as BlockT>::Hash> +
		MallocSizeOfWasm +
		'static,
	TRpc: sc_rpc::RpcExtension<sc_rpc::Metadata>,
{

	/// Builds the full service.
	pub fn build_full(self) -> Result<Service<
		TBl,
		Client<TBackend, TExec, TBl, TRtApi>,
		TSc,
		NetworkStatus<TBl>,
		NetworkService<TBl, <TBl as BlockT>::Hash>,
		TExPool,
		sc_offchain::OffchainWorkers<
			Client<TBackend, TExec, TBl, TRtApi>,
			TBackend::OffchainStorage,
			TBl
		>,
	>, Error>
		where TExec: CallExecutor<TBl, Backend = TBackend>,
	{
		// make transaction pool available for off-chain runtime calls.
		self.client.execution_extensions()
			.register_transaction_pool(Arc::downgrade(&self.transaction_pool) as _);

		self.build_common()
	}
}

async fn transaction_notifications<TBl, TExPool>(
	transaction_pool: Arc<TExPool>,
	network: Arc<NetworkService<TBl, <TBl as BlockT>::Hash>>
)
	where
		TBl: BlockT,
		TExPool: MaintainedTransactionPool<Block=TBl, Hash = <TBl as BlockT>::Hash>,
{
	// transaction notifications
	transaction_pool.import_notification_stream()
		.for_each(move |hash| {
			network.propagate_transaction(hash);
			let status = transaction_pool.status();
			telemetry!(SUBSTRATE_INFO; "txpool.import";
				"ready" => status.ready,
				"future" => status.future
			);
			ready(())
		})
		.await;
}

// Periodically notify the telemetry.
async fn telemetry_periodic_send<TBl, TBackend, TExec, TRtApi, TExPool>(
	client: Arc<Client<TBackend, TExec, TBl, TRtApi>>,
	transaction_pool: Arc<TExPool>,
	mut metrics_service: MetricsService,
	network_status_sinks: Arc<Mutex<status_sinks::StatusSinks<(NetworkStatus<TBl>, NetworkState)>>>
)
	where
		TBl: BlockT,
		TExec: CallExecutor<TBl>,
		Client<TBackend, TExec, TBl, TRtApi>: ProvideRuntimeApi<TBl>,
		TExPool: MaintainedTransactionPool<Block=TBl, Hash = <TBl as BlockT>::Hash>,
		TBackend: sc_client_api::backend::Backend<TBl>,
{
	let (state_tx, state_rx) = tracing_unbounded::<(NetworkStatus<_>, NetworkState)>("mpsc_netstat1");
	network_status_sinks.lock().push(std::time::Duration::from_millis(5000), state_tx);
	state_rx.for_each(move |(net_status, _)| {
		let info = client.usage_info();
		metrics_service.tick(
			&info,
			&transaction_pool.status(),
			&net_status,
		);
		ready(())
	}).await;
}

async fn telemetry_periodic_network_state<TBl: BlockT>(
	network_status_sinks: Arc<Mutex<status_sinks::StatusSinks<(NetworkStatus<TBl>, NetworkState)>>>
) {
	// Periodically send the network state to the telemetry.
	let (netstat_tx, netstat_rx) = tracing_unbounded::<(NetworkStatus<_>, NetworkState)>("mpsc_netstat2");
	network_status_sinks.lock().push(std::time::Duration::from_secs(30), netstat_tx);
	netstat_rx.for_each(move |(_, network_state)| {
		telemetry!(
			SUBSTRATE_INFO;
			"system.network_state";
			"state" => network_state,
		);
		ready(())
	}).await;
}

fn build_telemetry<TBl: BlockT>(
	config: &mut Configuration,
	endpoints: sc_telemetry::TelemetryEndpoints,
	telemetry_connection_sinks: Arc<Mutex<Vec<TracingUnboundedSender<()>>>>,
	network: Arc<NetworkService<TBl, <TBl as BlockT>::Hash>>
) -> (sc_telemetry::Telemetry, Pin<Box<dyn Future<Output = ()> + Send>>) {
	let is_authority = config.role.is_authority();
	let network_id = network.local_peer_id().to_base58();
	let name = config.network.node_name.clone();
	let impl_name = config.impl_name.to_owned();
	let version = config.impl_version;
	let chain_name = config.chain_spec.name().to_owned();
	let telemetry = sc_telemetry::init_telemetry(sc_telemetry::TelemetryConfig {
		endpoints,
		wasm_external_transport: config.telemetry_external_transport.take(),
	});
	let startup_time = SystemTime::UNIX_EPOCH.elapsed()
		.map(|dur| dur.as_millis())
		.unwrap_or(0);
	let future = telemetry.clone()
		.for_each(move |event| {
			// Safe-guard in case we add more events in the future.
			let sc_telemetry::TelemetryEvent::Connected = event;

			telemetry!(SUBSTRATE_INFO; "system.connected";
				"name" => name.clone(),
				"implementation" => impl_name.clone(),
				"version" => version,
				"config" => "",
				"chain" => chain_name.clone(),
				"authority" => is_authority,
				"startup_time" => startup_time,
				"network_id" => network_id.clone()
			);

			telemetry_connection_sinks.lock().retain(|sink| {
				sink.unbounded_send(()).is_ok()
			});
			ready(())
		})
		.boxed();

	(telemetry, future)
}

fn gen_handler<TBl, TBackend, TExec, TRtApi, TExPool, TRpc>(
	deny_unsafe: sc_rpc::DenyUnsafe,
	config: &Configuration,
	task_manager: &TaskManager,
	client: Arc<Client<TBackend, TExec, TBl, TRtApi>>,
	transaction_pool: Arc<TExPool>,
	keystore: Arc<RwLock<Keystore>>,
	on_demand: Option<Arc<OnDemand<TBl>>>,
	remote_backend: Option<Arc<dyn RemoteBlockchain<TBl>>>,
	rpc_extensions_builder: &(dyn RpcExtensionBuilder<Output = TRpc> + Send),
	offchain_storage: Option<<TBackend as sc_client_api::backend::Backend<TBl>>::OffchainStorage>,
	system_rpc_tx: TracingUnboundedSender<sc_rpc::system::Request<TBl>>
) -> jsonrpc_pubsub::PubSubHandler<sc_rpc::Metadata>
	where
		TBl: BlockT,
		TExec: CallExecutor<TBl, Backend = TBackend> + Send + Sync + 'static,
		TRtApi: Send + Sync + 'static,
		Client<TBackend, TExec, TBl, TRtApi>: ProvideRuntimeApi<TBl>,
		TExPool: MaintainedTransactionPool<Block=TBl, Hash = <TBl as BlockT>::Hash> + 'static,
		TBackend: sc_client_api::backend::Backend<TBl> + 'static,
		TRpc: sc_rpc::RpcExtension<sc_rpc::Metadata>,
		<Client<TBackend, TExec, TBl, TRtApi> as ProvideRuntimeApi<TBl>>::Api:
			sp_session::SessionKeys<TBl> +
			sp_api::Metadata<TBl, Error = sp_blockchain::Error>,
{
	use sc_rpc::{chain, state, author, system, offchain};

	let system_info = sc_rpc::system::SystemInfo {
		chain_name: config.chain_spec.name().into(),
		impl_name: config.impl_name.into(),
		impl_version: config.impl_version.into(),
		properties: config.chain_spec.properties(),
		chain_type: config.chain_spec.chain_type(),
	};

	let subscriptions = SubscriptionManager::new(Arc::new(task_manager.spawn_handle()));

	let (chain, state, child_state) = if let (Some(remote_backend), Some(on_demand)) =
		(remote_backend, on_demand) {
		// Light clients
		let chain = sc_rpc::chain::new_light(
			client.clone(),
			subscriptions.clone(),
			remote_backend.clone(),
			on_demand.clone()
		);
		let (state, child_state) = sc_rpc::state::new_light(
			client.clone(),
			subscriptions.clone(),
			remote_backend.clone(),
			on_demand.clone()
		);
		(chain, state, child_state)

	} else {
		// Full nodes
		let chain = sc_rpc::chain::new_full(client.clone(), subscriptions.clone());
		let (state, child_state) = sc_rpc::state::new_full(client.clone(), subscriptions.clone());
		(chain, state, child_state)
	};

	let author = sc_rpc::author::Author::new(
		client.clone(),
		transaction_pool.clone(),
		subscriptions,
		keystore.clone(),
		deny_unsafe,
	);
	let system = system::System::new(system_info, system_rpc_tx.clone(), deny_unsafe);

	let maybe_offchain_rpc = offchain_storage.clone()
	.map(|storage| {
		let offchain = sc_rpc::offchain::Offchain::new(storage, deny_unsafe);
		// FIXME: Use plain Option (don't collect into HashMap) when we upgrade to jsonrpc 14.1
		// https://github.com/paritytech/jsonrpc/commit/20485387ed06a48f1a70bf4d609a7cde6cf0accf
		let delegate = offchain::OffchainApi::to_delegate(offchain);
			delegate.into_iter().collect::<HashMap<_, _>>()
	}).unwrap_or_default();

	sc_rpc_server::rpc_handler((
		state::StateApi::to_delegate(state),
		state::ChildStateApi::to_delegate(child_state),
		chain::ChainApi::to_delegate(chain),
		maybe_offchain_rpc,
		author::AuthorApi::to_delegate(author),
		system::SystemApi::to_delegate(system),
		rpc_extensions_builder.build(deny_unsafe),
	))
}

fn build_network<TBl, TBackend, TExec, TRtApi, TExPool, TImpQu>(
	config: &Configuration,
	client: Arc<Client<TBackend, TExec, TBl, TRtApi>>,
	transaction_pool: Arc<TExPool>,
	spawn_handle: SpawnTaskHandle,
	on_demand: Option<Arc<OnDemand<TBl>>>,
	block_announce_validator_builder: Option<Box<
		dyn FnOnce(Arc<Client<TBackend, TExec, TBl, TRtApi>>) ->
			Box<dyn BlockAnnounceValidator<TBl> + Send> + Send
	>>,
	finality_proof_request_builder: Option<BoxFinalityProofRequestBuilder<TBl>>,
	finality_proof_provider: Option<Arc<dyn FinalityProofProvider<TBl>>>,
	system_rpc_rx: TracingUnboundedReceiver<sc_rpc::system::Request<TBl>>,
	import_queue: TImpQu
) -> Result<
	(
		Arc<NetworkService<TBl, <TBl as BlockT>::Hash>>,
		Arc<Mutex<status_sinks::StatusSinks<(NetworkStatus<TBl>, NetworkState)>>>,
		Pin<Box<dyn Future<Output = ()> + Send>>
	),
	Error
>
	where
		TBl: BlockT,
		TExec: CallExecutor<TBl> + Send + Sync + 'static,
		TRtApi: Send + Sync + 'static,
		Client<TBackend, TExec, TBl, TRtApi>: ProvideRuntimeApi<TBl>,
		TExPool: MaintainedTransactionPool<Block=TBl, Hash = <TBl as BlockT>::Hash> + 'static,
		TBackend: sc_client_api::backend::Backend<TBl> + 'static,
		TImpQu: ImportQueue<TBl> + 'static,
{
	let transaction_pool_adapter = Arc::new(TransactionPoolAdapter {
		imports_external_transactions: !matches!(config.role, Role::Light),
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
		sc_network::config::ProtocolId::from(protocol_id_full)
	};

	let block_announce_validator = if let Some(f) = block_announce_validator_builder {
		f(client.clone())
	} else {
		Box::new(DefaultBlockAnnounceValidator::new(client.clone()))
	};

	let network_params = sc_network::config::Params {
		role: config.role.clone(),
		executor: {
			Some(Box::new(move |fut| {
				spawn_handle.spawn("libp2p-node", fut);
			}))
		},
		network_config: config.network.clone(),
		chain: client.clone(),
		finality_proof_provider,
		finality_proof_request_builder,
		on_demand: on_demand.clone(),
		transaction_pool: transaction_pool_adapter.clone() as _,
		import_queue: Box::new(import_queue),
		protocol_id,
		block_announce_validator,
		metrics_registry: config.prometheus_config.as_ref().map(|config| config.registry.clone())
	};

	let has_bootnodes = !network_params.network_config.boot_nodes.is_empty();
	let network_mut = sc_network::NetworkWorker::new(network_params)?;
	let network = network_mut.service().clone();
	let network_status_sinks = Arc::new(Mutex::new(status_sinks::StatusSinks::new()));

	let future = build_network_future(
		config.role.clone(),
		network_mut,
		client.clone(),
		network_status_sinks.clone(),
		system_rpc_rx,
		has_bootnodes,
		config.announce_block,
	).boxed();

	Ok((network, network_status_sinks, future))
}
