//! Service and ServiceFactory implementation. Specialized wrapper over substrate service.

use std::sync::Arc;
use std::time::Duration;
use sc_client_api::ExecutorProvider;
use sc_consensus::LongestChain;
use node_template_runtime::{self, opaque::Block, RuntimeApi};
use sc_service::{error::{Error as ServiceError}, AbstractService, Configuration, ServiceBuilder};
use sp_inherents::InherentDataProviders;
use sc_executor::native_executor_instance;
pub use sc_executor::NativeExecutor;
use sp_consensus_aura::sr25519::{AuthorityPair as AuraPair};
use sc_finality_grandpa::{
	FinalityProofProvider as GrandpaFinalityProofProvider, StorageAndProofProvider, SharedVoterState,
};

// Our native executor instance.
native_executor_instance!(
	pub Executor,
	node_template_runtime::api::dispatch,
	node_template_runtime::native_version,
);

/// Starts a `ServiceBuilder` for a full service.
///
/// Use this macro if you don't actually need the full service, but just the builder in order to
/// be able to perform chain operations.
macro_rules! new_full_start {
	($config:expr) => {{
		use std::sync::Arc;
		use sp_consensus_aura::sr25519::AuthorityPair as AuraPair;

		let mut import_setup = None;
		let inherent_data_providers = sp_inherents::InherentDataProviders::new();

		let builder = sc_service::ServiceBuilder::new_full::<
			node_template_runtime::opaque::Block,
			node_template_runtime::RuntimeApi,
			crate::service::Executor
		>($config)?
			.with_select_chain(|_config, backend| {
				Ok(sc_consensus::LongestChain::new(backend.clone()))
			})?
			.with_transaction_pool(|builder| {
				let pool_api = sc_transaction_pool::FullChainApi::new(
					builder.client().clone(),
				);
				Ok(sc_transaction_pool::BasicPool::new(
					builder.config().transaction_pool.clone(),
					std::sync::Arc::new(pool_api),
					builder.prometheus_registry(),
				))
			})?
			.with_import_queue(|
				_config,
				client,
				mut select_chain,
				_transaction_pool,
				spawn_task_handle,
				registry,
			| {
				let select_chain = select_chain.take()
					.ok_or_else(|| sc_service::Error::SelectChainRequired)?;

				let (grandpa_block_import, grandpa_link) = sc_finality_grandpa::block_import(
					client.clone(),
					&(client.clone() as Arc<_>),
					select_chain,
				)?;

				let aura_block_import = sc_consensus_aura::AuraBlockImport::<_, _, _, AuraPair>::new(
					grandpa_block_import.clone(), client.clone(),
				);

				let import_queue = sc_consensus_aura::import_queue::<_, _, _, AuraPair, _>(
					sc_consensus_aura::slot_duration(&*client)?,
					aura_block_import,
					Some(Box::new(grandpa_block_import.clone())),
					None,
					client,
					inherent_data_providers.clone(),
					spawn_task_handle,
					registry,
				)?;

				import_setup = Some((grandpa_block_import, grandpa_link));

				Ok(import_queue)
			})?;

		(builder, import_setup, inherent_data_providers)
	}}
}

/// Builds a new service for a full client.
pub fn new_full(config: Configuration) -> Result<impl AbstractService, ServiceError> {
	let role = config.role.clone();
	let force_authoring = config.force_authoring;
	let name = config.network.node_name.clone();
	let disable_grandpa = config.disable_grandpa;

	let (builder, mut import_setup, inherent_data_providers) = new_full_start!(config);

	let (block_import, grandpa_link) =
		import_setup.take()
			.expect("Link Half and Block Import are present for Full Services or setup failed before. qed");

	let service = builder
		.with_finality_proof_provider(|client, backend| {
			// GenesisAuthoritySetProvider is implemented for StorageAndProofProvider
			let provider = client as Arc<dyn StorageAndProofProvider<_, _>>;
			Ok(Arc::new(GrandpaFinalityProofProvider::new(backend, provider)) as _)
		})?
		.build_full()?;

	if role.is_authority() {
		let proposer = sc_basic_authorship::ProposerFactory::new(
			service.client(),
			service.transaction_pool(),
			service.prometheus_registry().as_ref(),
		);

		let client = service.client();
		let select_chain = service.select_chain()
			.ok_or(ServiceError::SelectChainRequired)?;

		let can_author_with =
			sp_consensus::CanAuthorWithNativeVersion::new(client.executor().clone());

		let aura = sc_consensus_aura::start_aura::<_, _, _, _, _, AuraPair, _, _, _>(
			sc_consensus_aura::slot_duration(&*client)?,
			client,
			select_chain,
			block_import,
			proposer,
			service.network(),
			inherent_data_providers.clone(),
			force_authoring,
			service.keystore(),
			can_author_with,
		)?;

		// the AURA authoring task is considered essential, i.e. if it
		// fails we take down the service with it.
		service.spawn_essential_task_handle().spawn_blocking("aura", aura);
	}

	// if the node isn't actively participating in consensus then it doesn't
	// need a keystore, regardless of which protocol we use below.
	let keystore = if role.is_authority() {
		Some(service.keystore() as sp_core::traits::BareCryptoStorePtr)
	} else {
		None
	};

	let grandpa_config = sc_finality_grandpa::Config {
		// FIXME #1578 make this available through chainspec
		gossip_duration: Duration::from_millis(333),
		justification_period: 512,
		name: Some(name),
		observer_enabled: false,
		keystore,
		is_authority: role.is_network_authority(),
	};

	let enable_grandpa = !disable_grandpa;
	if enable_grandpa {
		// start the full GRANDPA voter
		// NOTE: non-authorities could run the GRANDPA observer protocol, but at
		// this point the full voter should provide better guarantees of block
		// and vote data availability than the observer. The observer has not
		// been tested extensively yet and having most nodes in a network run it
		// could lead to finality stalls.
		let grandpa_config = sc_finality_grandpa::GrandpaParams {
			config: grandpa_config,
			link: grandpa_link,
			network: service.network(),
			inherent_data_providers: inherent_data_providers.clone(),
			telemetry_on_connect: Some(service.telemetry_on_connect_stream()),
			voting_rule: sc_finality_grandpa::VotingRulesBuilder::default().build(),
			prometheus_registry: service.prometheus_registry(),
			shared_voter_state: SharedVoterState::empty(),
		};

		// the GRANDPA voter task is considered infallible, i.e.
		// if it fails we take down the service with it.
		service.spawn_essential_task_handle().spawn_blocking(
			"grandpa-voter",
			sc_finality_grandpa::run_grandpa_voter(grandpa_config)?
		);
	} else {
		sc_finality_grandpa::setup_disabled_grandpa(
			service.client(),
			&inherent_data_providers,
			service.network(),
		)?;
	}

	Ok(service)
}

/// Builds a new service for a light client.
pub fn new_light(config: Configuration) -> Result<impl AbstractService, ServiceError> {
	let inherent_data_providers = InherentDataProviders::new();

	ServiceBuilder::new_light::<Block, RuntimeApi, Executor>(config)?
		.with_select_chain(|_config, backend| {
			Ok(LongestChain::new(backend.clone()))
		})?
		.with_transaction_pool(|builder| {
			let fetcher = builder.fetcher()
				.ok_or_else(|| "Trying to start light transaction pool without active fetcher")?;

			let pool_api = sc_transaction_pool::LightChainApi::new(
				builder.client().clone(),
				fetcher.clone(),
			);
			let pool = sc_transaction_pool::BasicPool::with_revalidation_type(
				builder.config().transaction_pool.clone(),
				Arc::new(pool_api),
				builder.prometheus_registry(),
				sc_transaction_pool::RevalidationType::Light,
			);
			Ok(pool)
		})?
		.with_import_queue_and_fprb(|
			_config,
			client,
			backend,
			fetcher,
			_select_chain,
			_tx_pool,
			spawn_task_handle,
			prometheus_registry,
		| {
			let fetch_checker = fetcher
				.map(|fetcher| fetcher.checker().clone())
				.ok_or_else(|| "Trying to start light import queue without active fetch checker")?;
			let grandpa_block_import = sc_finality_grandpa::light_block_import(
				client.clone(),
				backend,
				&(client.clone() as Arc<_>),
				Arc::new(fetch_checker),
			)?;
			let finality_proof_import = grandpa_block_import.clone();
			let finality_proof_request_builder =
				finality_proof_import.create_finality_proof_request_builder();

			let import_queue = sc_consensus_aura::import_queue::<_, _, _, AuraPair, _>(
				sc_consensus_aura::slot_duration(&*client)?,
				grandpa_block_import,
				None,
				Some(Box::new(finality_proof_import)),
				client,
				inherent_data_providers.clone(),
				spawn_task_handle,
				prometheus_registry,
			)?;

			Ok((import_queue, finality_proof_request_builder))
		})?
		.with_finality_proof_provider(|client, backend| {
			// GenesisAuthoritySetProvider is implemented for StorageAndProofProvider
			let provider = client as Arc<dyn StorageAndProofProvider<_, _>>;
			Ok(Arc::new(GrandpaFinalityProofProvider::new(backend, provider)) as _)
		})?
		.build_light()
}
