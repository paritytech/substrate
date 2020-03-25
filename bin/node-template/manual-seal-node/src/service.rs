//! Service and ServiceFactory implementation. Specialized wrapper over substrate service.

use std::sync::Arc;
use std::time::Duration;
use sc_client::LongestChain;
use sc_client_api::ExecutorProvider;
use node_template_runtime::{self, opaque::Block, RuntimeApi};
use sc_service::{error::{Error as ServiceError}, AbstractService, Configuration, ServiceBuilder};
use sp_inherents::InherentDataProviders;
use sc_executor::native_executor_instance;
pub use sc_executor::NativeExecutor;
use sc_basic_authorship::ProposerFactory;
use sc_consensus_manual_seal as manual_seal;

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
		sc_service::ServiceBuilder::new_full::<
			node_template_runtime::opaque::Block,
			node_template_runtime::RuntimeApi,
			crate::service::Executor,
		 >($config)?
			.with_select_chain(|_, backend| {
				Ok(sc_client::LongestChain::new(backend.clone()))
			})?
			.with_transaction_pool(|config, client, _fetcher| {
				let pool_api = sc_transaction_pool::FullChainApi::new(client.clone());
				Ok(sc_transaction_pool::BasicPool::new(config, std::sync::Arc::new(pool_api)))
			})?
			.with_import_queue(|_config, client, _select_chain, _transaction_pool| {
				Ok(manual_seal::import_queue(Box::new(client)))
			})?
	}}
}

/// Builds a new service for a full client.
pub fn new_full(config: Configuration)
	-> Result<impl AbstractService, ServiceError>
{
	let service = new_full_start!(config).build()?;
	let inherent_data_providers = sp_inherents::InherentDataProviders::new();
	// this is a hack for runtime modules that expect a timestamp inherent data provider.
	inherent_data_providers.register_provider(sp_timestamp::InherentDataProvider)?;
	
	let future = manual_seal::run_instant_seal(
		Box::new(service.client()),
		ProposerFactory::new(
			service.client().clone(),
			service.transaction_pool(),
		),
		service.client().clone(),
		service.transaction_pool().pool().clone(),
		service.select_chain().unwrap(),
		inherent_data_providers,
	);
	service.spawn_essential_task("manual-seal", future);

	Ok(service)
}

/// Builds a new service for a light client.
pub fn new_light(_: Configuration) -> Result<impl AbstractService, ServiceError> {
	// manual seal can't run as a light client.
	unimplemented!()
}
