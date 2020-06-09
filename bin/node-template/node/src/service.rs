//! Service and ServiceFactory implementation. Specialized wrapper over substrate service.

use std::sync::Arc;
use std::time::Duration;
use sc_client_api::ExecutorProvider;
use sc_consensus::LongestChain;
use node_template_runtime::{self, opaque::Block, RuntimeApi};
use sc_service::{error::{Error as ServiceError}, AbstractService, Configuration};
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
		let inherent_data_providers = sp_inherents::InherentDataProviders::new();

		let (client, backend, keystore, task_manager) = sc_service::new_full_parts::<
			node_template_runtime::opaque::Block, node_template_runtime::RuntimeApi, crate::service::Executor
		>(&$config)?;
		let client = Arc::new(client);
		let select_chain = sc_consensus::LongestChain::new(backend.clone());
		let pool_api = sc_transaction_pool::FullChainApi::new(Arc::clone(&client));
		let registry = $config.prometheus_config.as_ref().map(|cfg| cfg.registry.clone());
		let (transaction_pool, background_task_one) = sc_transaction_pool::BasicPool::new($config.transaction_pool.clone(), std::sync::Arc::new(pool_api), registry.as_ref());
		let transaction_pool = Arc::new(transaction_pool);
		let mut background_tasks = Vec::new();

		if let Some(bg_t) = background_task_one {
			background_tasks.push(("txpool-background", bg_t));
		}

		let (import_queue, import_setup) = {
			let (grandpa_block_import, grandpa_link) =
				sc_finality_grandpa::block_import(Arc::clone(&client), &(Arc::clone(&client) as Arc<_>), select_chain.clone())?;

			let aura_block_import = sc_consensus_aura::AuraBlockImport::<_, _, _, AuraPair>::new(
				grandpa_block_import.clone(), Arc::clone(&client),
			);

			let spawn_task_handle = task_manager.spawn_handle();
			let import_queue = sc_consensus_aura::import_queue::<_, _, _, AuraPair, _>(
				sc_consensus_aura::slot_duration(&*client)?,
				aura_block_import,
				Some(Box::new(grandpa_block_import.clone())),
				None,
				client.clone(),
				inherent_data_providers.clone(),
				&spawn_task_handle,
				registry.as_ref(),
			)?;

			let import_setup = Some((grandpa_block_import, grandpa_link));

			(import_queue, import_setup)
		};

		(
			client, import_setup, inherent_data_providers, backend, task_manager, keystore,
			import_queue, select_chain, transaction_pool, background_tasks,
		)
	}}
}

/// Builds a new service for a full client.
pub fn new_full(config: Configuration) -> Result<impl AbstractService, ServiceError> {
	let role = config.role.clone();
	let force_authoring = config.force_authoring;
	let name = config.network.node_name.clone();
	let disable_grandpa = config.disable_grandpa;

	let (
		client, mut import_setup, inherent_data_providers, backend, task_manager, keystore,
		import_queue, select_chain, transaction_pool, background_tasks,
	) = new_full_start!(config);

	let (block_import, grandpa_link) =
		import_setup.take()
			.expect("Link Half and Block Import are present for Full Services or setup failed before. qed");

	let provider = client.clone() as Arc<dyn StorageAndProofProvider<_, _>>;
	let finality_proof_provider = Arc::new(GrandpaFinalityProofProvider::new(backend.clone(), provider));
	let service = sc_service::build(
		config,
		client,
		backend,
		task_manager,
		keystore,
		None,
		Some(select_chain),
		import_queue,
		None,
		Some(finality_proof_provider),
		transaction_pool,
		(),
		None,
		background_tasks,
		None,
		Box::new(|_| ()),
		String::new()
	)?;

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
		service.spawn_essential_task("aura", aura);
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
		service.spawn_essential_task(
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

	let ((client, backend, keystore, task_manager), fetcher, remote_blockchain) = sc_service::new_light_parts::<
		Block, RuntimeApi, Executor
	>(&config)?;
	let select_chain = LongestChain::new(backend.clone());
	let pool_api = sc_transaction_pool::LightChainApi::new(client.clone(), fetcher.clone());
	let registry = config.prometheus_config.as_ref().map(|cfg| cfg.registry.clone());
	let (transaction_pool, background_task_one) = sc_transaction_pool::BasicPool::new(config.transaction_pool.clone(), std::sync::Arc::new(pool_api), registry.as_ref());
	let transaction_pool = Arc::new(transaction_pool);
	let mut background_tasks = Vec::new();

	if let Some(bg_t) = background_task_one {
		background_tasks.push(("txpool-background", bg_t));
	}
	let fetch_checker = fetcher.checker().clone();
	let grandpa_block_import = sc_finality_grandpa::light_block_import(
		client.clone(),
		backend.clone(),
		&(client.clone() as Arc<_>),
		Arc::new(fetch_checker),
	)?;
	let finality_proof_import = grandpa_block_import.clone();
	let finality_proof_request_builder =
		finality_proof_import.create_finality_proof_request_builder();

	let spawn_task_handle = task_manager.spawn_handle();
	let import_queue = sc_consensus_aura::import_queue::<_, _, _, AuraPair, _>(
		sc_consensus_aura::slot_duration(&*client)?,
		grandpa_block_import,
		None,
		Some(Box::new(finality_proof_import)),
		client.clone(),
		inherent_data_providers.clone(),
		&spawn_task_handle,
		registry.as_ref()
	)?;
	// GenesisAuthoritySetProvider is implemented for StorageAndProofProvider
	let provider = client.clone() as Arc<dyn StorageAndProofProvider<_, _>>;
	let finality_proof_provider = Arc::new(GrandpaFinalityProofProvider::new(backend.clone(), provider));
	sc_service::build(
		config,
		client,
		backend,
		task_manager,
		keystore,
		None,
		Some(select_chain),
		import_queue,
		Some(finality_proof_request_builder),
		Some(finality_proof_provider),
		transaction_pool,
		(),
		Some(remote_blockchain),
		background_tasks,
		None,
		Box::new(|_| ()),
		String::new()
	)
}
