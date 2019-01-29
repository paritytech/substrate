//! Service and ServiceFactory implementation. Specialized wrapper over Substrate service.

#![warn(unused_extern_crates)]

use std::sync::Arc;
use transaction_pool::{self, txpool::{Pool as TransactionPool}};
use template_node_runtime::{self, GenesisConfig, opaque::Block, RuntimeApi};
use substrate_service::{
	FactoryFullConfiguration, LightComponents, FullComponents, FullBackend,
	FullClient, LightClient, LightBackend, FullExecutor, LightExecutor,
	TaskExecutor,
};
use basic_authorship::ProposerFactory;
use node_executor;
use consensus::{import_queue, start_aura, AuraImportQueue, SlotDuration, NothingExtra};
use client;
use primitives::ed25519::Pair;
use inherents::InherentDataProviders;

pub use substrate_executor::NativeExecutor;
// Our native executor instance.
native_executor_instance!(
	pub Executor,
	template_node_runtime::api::dispatch,
	template_node_runtime::native_version,
	include_bytes!("../runtime/wasm/target/wasm32-unknown-unknown/release/template_node_runtime.compact.wasm")
);

#[derive(Default)]
pub struct NodeConfig {
	inherent_data_providers: InherentDataProviders,
}

construct_simple_protocol! {
	/// Demo protocol attachment for substrate.
	pub struct NodeProtocol where Block = Block { }
}

construct_service_factory! {
	struct Factory {
		Block = Block,
		RuntimeApi = RuntimeApi,
		NetworkProtocol = NodeProtocol { |config| Ok(NodeProtocol::new()) },
		RuntimeDispatch = node_executor::Executor,
		FullTransactionPoolApi = transaction_pool::ChainApi<client::Client<FullBackend<Self>, FullExecutor<Self>, Block, RuntimeApi>, Block>
			{ |config, client| Ok(TransactionPool::new(config, transaction_pool::ChainApi::new(client))) },
		LightTransactionPoolApi = transaction_pool::ChainApi<client::Client<LightBackend<Self>, LightExecutor<Self>, Block, RuntimeApi>, Block>
			{ |config, client| Ok(TransactionPool::new(config, transaction_pool::ChainApi::new(client))) },
		Genesis = GenesisConfig,
		Configuration = NodeConfig,
		FullService = FullComponents<Self>
			{ |config: FactoryFullConfiguration<Self>, executor: TaskExecutor|
				FullComponents::<Factory>::new(config, executor)
			},
		AuthoritySetup = {
			|service: Self::FullService, executor: TaskExecutor, key: Option<Arc<Pair>>| {
				if let Some(key) = key {
					info!("Using authority key {}", key.public());
					let proposer = Arc::new(ProposerFactory {
						client: service.client(),
						transaction_pool: service.transaction_pool(),
					});
					let client = service.client();
					executor.spawn(start_aura(
						SlotDuration::get_or_compute(&*client)?,
						key.clone(),
						client.clone(),
						client,
						proposer,
						service.network(),
						service.on_exit(),
						service.config.custom.inherent_data_providers.clone(),
					)?);
				}

				Ok(service)
			}
		},
		LightService = LightComponents<Self>
			{ |config, executor| <LightComponents<Factory>>::new(config, executor) },
		FullImportQueue = AuraImportQueue<
			Self::Block,
			FullClient<Self>,
			NothingExtra,
		>
			{ |config: &mut FactoryFullConfiguration<Self> , client: Arc<FullClient<Self>>|
				import_queue(
					SlotDuration::get_or_compute(&*client)?,
					client.clone(),
					None,
					client,
					NothingExtra,
					config.custom.inherent_data_providers.clone(),
				).map_err(Into::into)
			},
		LightImportQueue = AuraImportQueue<
			Self::Block,
			LightClient<Self>,
			NothingExtra,
		>
			{ |config: &mut FactoryFullConfiguration<Self>, client: Arc<LightClient<Self>>|
				import_queue(
					SlotDuration::get_or_compute(&*client)?,
					client.clone(),
					None,
					client,
					NothingExtra,
					config.custom.inherent_data_providers.clone(),
				).map_err(Into::into)
			},
	}
}
