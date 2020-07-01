//! Service and ServiceFactory implementation. Specialized wrapper over substrate service.

use std::sync::Arc;
use std::time::Duration;
use sc_client_api::{ExecutorProvider, RemoteBackend};
use node_template_runtime::{self, opaque::Block, RuntimeApi};
use sc_service::{error::Error as ServiceError, Configuration, ServiceComponents, TaskManager};
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

macro_rules! new_full_up_to_import_queue {
	($config:expr) => {{
		use std::sync::Arc;
		use node_template_runtime::{Block, RuntimeApi};
		use crate::service::Executor;
		use sp_consensus_aura::sr25519::AuthorityPair as AuraPair;

		let inherent_data_providers = sp_inherents::InherentDataProviders::new();

		let (client, backend, keystore, task_manager) = sc_service::new_full_parts::<Block, RuntimeApi, Executor>(&$config)?;
		let client = Arc::new(client);

		let select_chain = sc_consensus::LongestChain::new(backend.clone());

		let pool_api = sc_transaction_pool::FullChainApi::new(client.clone());
		let transaction_pool = sc_transaction_pool::BasicPool::new_full(
			$config.transaction_pool.clone(),
			std::sync::Arc::new(pool_api),
			$config.prometheus_registry().as_ref(),
			task_manager.spawn_handle(),
			client.clone(),
		);

		let (grandpa_block_import, grandpa_link) = sc_finality_grandpa::block_import(
			client.clone(), select_chain.clone(),
		)?;

		let aura_block_import = sc_consensus_aura::AuraBlockImport::<_, _, _, AuraPair>::new(
			grandpa_block_import.clone(), client.clone(),
		);

		let import_queue = sc_consensus_aura::import_queue::<_, _, _, AuraPair, _>(
			sc_consensus_aura::slot_duration(&*client)?,
			aura_block_import,
			Some(Box::new(grandpa_block_import.clone())),
			None,
			client.clone(),
			inherent_data_providers.clone(),
			&task_manager.spawn_handle(),
			$config.prometheus_registry().as_ref(),
		)?;

		(
			client, backend, keystore, task_manager, inherent_data_providers, select_chain,
			transaction_pool, grandpa_block_import, grandpa_link, import_queue
		)
	}}
}

/// Builds a new service for a full client.
pub fn new_full(config: Configuration) -> Result<TaskManager, ServiceError> {	
	let (
		client, backend, keystore, mut task_manager, inherent_data_providers, select_chain,
		transaction_pool, block_import, grandpa_link, import_queue
	) = new_full_up_to_import_queue!(&config);

	let provider = client.clone() as Arc<dyn StorageAndProofProvider<_, _>>;
	let finality_proof_provider = Arc::new(GrandpaFinalityProofProvider::new(backend.clone(), provider));
	
	let prometheus_registry = config.prometheus_registry();

	let role = config.role.clone();
	let force_authoring = config.force_authoring;
	let name = config.network.node_name.clone();
	let enable_grandpa = !config.disable_grandpa;

	let ServiceComponents {
		network,
		telemetry_on_connect_sinks, ..
	 } = sc_service::build_common(sc_service::ServiceParams {
		config: config,
		backend: backend.clone(),
		client: client.clone(),
		block_announce_validator_builder: None,
		finality_proof_request_builder: None,
		finality_proof_provider: Some(finality_proof_provider),
		on_demand: None,
		import_queue: import_queue,
		keystore: keystore.clone(),
		task_manager: &mut task_manager,
		remote_backend: None,
		rpc_extensions_builder: Box::new(|_| ()),
		transaction_pool: transaction_pool.clone(),
	 })?;

	if role.is_authority() {
		let proposer = sc_basic_authorship::ProposerFactory::new(
			client.clone(),
			transaction_pool,
			prometheus_registry.as_ref(),
		);

		let can_author_with =
			sp_consensus::CanAuthorWithNativeVersion::new(client.executor().clone());

		let aura = sc_consensus_aura::start_aura::<_, _, _, _, _, AuraPair, _, _, _>(
			sc_consensus_aura::slot_duration(&*client)?,
			client.clone(),
			select_chain,
			block_import,
			proposer,
			network.clone(),
			inherent_data_providers.clone(),
			force_authoring,
			keystore.clone(),
			can_author_with,
		)?;

		// the AURA authoring task is considered essential, i.e. if it
		// fails we take down the service with it.
		task_manager.spawn_essential_handle().spawn_blocking("aura", aura);
	}

	// if the node isn't actively participating in consensus then it doesn't
	// need a keystore, regardless of which protocol we use below.
	let keystore = if role.is_authority() {
		Some(keystore.clone() as sp_core::traits::BareCryptoStorePtr)
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
			network: network.clone(),
			inherent_data_providers: inherent_data_providers.clone(),
			telemetry_on_connect: Some(telemetry_on_connect_sinks.on_connect_stream()),
			voting_rule: sc_finality_grandpa::VotingRulesBuilder::default().build(),
			prometheus_registry: prometheus_registry.clone(),
			shared_voter_state: SharedVoterState::empty(),
		};

		// the GRANDPA voter task is considered infallible, i.e.
		// if it fails we take down the service with it.
		task_manager.spawn_essential_handle().spawn_blocking(
			"grandpa-voter",
			sc_finality_grandpa::run_grandpa_voter(grandpa_config)?
		);
	} else {
		sc_finality_grandpa::setup_disabled_grandpa(
			client,
			&inherent_data_providers,
			network.clone(),
		)?;
	}

	Ok(task_manager)
}

/// Builds a new service for a light client.
pub fn new_light(config: Configuration) -> Result<TaskManager, ServiceError> {
	let (client, backend, keystore, mut task_manager, on_demand) =
		sc_service::new_light_parts::<Block, RuntimeApi, Executor>(&config)?;
	
	let transaction_pool_api = Arc::new(sc_transaction_pool::LightChainApi::new(
		client.clone(), on_demand.clone(),
	));
	let transaction_pool = sc_transaction_pool::BasicPool::new_light(
		config.transaction_pool.clone(),
		transaction_pool_api,
		config.prometheus_registry().as_ref(),
		task_manager.spawn_handle(),
	);

	let grandpa_block_import = sc_finality_grandpa::light_block_import(
		client.clone(), backend.clone(),
		Arc::new(on_demand.checker().clone()) as Arc<_>,
	)?;
	let finality_proof_import = grandpa_block_import.clone();
	let finality_proof_request_builder =
		finality_proof_import.create_finality_proof_request_builder();

	let import_queue = sc_consensus_aura::import_queue::<_, _, _, AuraPair, _>(
		sc_consensus_aura::slot_duration(&*client)?,
		grandpa_block_import,
		None,
		Some(Box::new(finality_proof_import)),
		client.clone(),
		InherentDataProviders::new(),
		&task_manager.spawn_handle(),
		config.prometheus_registry().as_ref(),
	)?;

	let finality_proof_provider = Arc::new(GrandpaFinalityProofProvider::new(
		backend.clone(), client.clone() as Arc<_>
	));

	sc_service::build_common(sc_service::ServiceParams {	
		block_announce_validator_builder: None,
		finality_proof_request_builder: Some(finality_proof_request_builder),
		finality_proof_provider: Some(finality_proof_provider),
		on_demand: Some(on_demand),
		task_manager: &mut task_manager,
		remote_backend: Some(backend.remote_blockchain()),
		rpc_extensions_builder: Box::new(|_| ()),
		transaction_pool: Arc::new(transaction_pool),
		config, client, import_queue, keystore, backend,
	 })?;

	Ok(task_manager)
}
