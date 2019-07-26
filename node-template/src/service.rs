//! Service and ServiceFactory implementation. Specialized wrapper over Substrate service.

#![warn(unused_extern_crates)]

use std::sync::Arc;
use log::info;
use transaction_pool::{self, txpool::{Pool as TransactionPool}};
use node_template_runtime::{self, GenesisConfig, opaque::Block, RuntimeApi, WASM_BINARY};
use substrate_service::{
	FactoryFullConfiguration, LightComponents, FullComponents, FullBackend,
	FullClient, LightClient, LightBackend, FullExecutor, LightExecutor,
	error::{Error as ServiceError}, FullComponentsSetupState, LightComponentsSetupState
};
use basic_authorship::ProposerFactory;
use consensus::{import_queue, start_aura, AuraImportQueue, SlotDuration};
use futures::prelude::*;
use substrate_client::{self as client, LongestChain};
use primitives::{ed25519::Pair, Pair as PairT};
use inherents::InherentDataProviders;
use network::{config::DummyFinalityProofRequestBuilder, construct_simple_protocol};
use substrate_executor::native_executor_instance;
use substrate_service::construct_service_factory;

pub use substrate_executor::NativeExecutor;
// Our native executor instance.
native_executor_instance!(
	pub Executor,
	node_template_runtime::api::dispatch,
	node_template_runtime::native_version,
	WASM_BINARY
);

#[derive(Default)]
pub struct SetupState {
	inherent_data_providers: InherentDataProviders,
}

construct_simple_protocol! {
	/// Demo protocol attachment for substrate.
	pub struct NodeProtocol where Block = Block { }
}

construct_service_factory! {
	struct Factory {
		Block = Block,
		ConsensusPair = Pair,
		FinalityPair = Pair,
		RuntimeApi = RuntimeApi,
		NetworkProtocol = NodeProtocol { |config| Ok(NodeProtocol::new()) },
		RuntimeDispatch = Executor,
		FullTransactionPoolApi = transaction_pool::ChainApi<
			client::Client<FullBackend<Self>, FullExecutor<Self>, Block, RuntimeApi>,
			Block
		> {
			|config, client| Ok(TransactionPool::new(config, transaction_pool::ChainApi::new(client)))
		},
		LightTransactionPoolApi = transaction_pool::ChainApi<
			client::Client<LightBackend<Self>, LightExecutor<Self>, Block, RuntimeApi>,
			Block
		> {
			|config, client| Ok(TransactionPool::new(config, transaction_pool::ChainApi::new(client)))
		},
		Genesis = GenesisConfig,
		SetupState = SetupState,
		Configuration = (),
		FullService = FullComponents<Self>
			{ |config: FactoryFullConfiguration<Self>|
				FullComponents::<Factory>::new(config)
			},
		AuthoritySetup = {
			|service: Self::FullService, state: FullComponentsSetupState<Self>| {
				if let Some(key) = service.authority_key() {
					info!("Using authority key {}", key.public());
					let proposer = Arc::new(ProposerFactory {
						client: service.client(),
						transaction_pool: service.transaction_pool(),
					});
					let client = service.client();
					let select_chain = service.select_chain()
						.ok_or_else(|| ServiceError::SelectChainRequired)?;
					let aura = start_aura(
						SlotDuration::get_or_compute(&*client)?,
						Arc::new(key),
						client.clone(),
						select_chain,
						client,
						proposer,
						service.network(),
						state.custom.inherent_data_providers.clone(),
						state.config.force_authoring,
					)?;
					service.spawn_task(Box::new(aura.select(service.on_exit()).then(|_| Ok(()))));
				}

				Ok(service)
			}
		},
		LightService = LightComponents<Self>
			{ |config| <LightComponents<Factory>>::new(config) },
		FullImportQueue = AuraImportQueue<
			Self::Block,
		>
			{ |state: &mut FullComponentsSetupState<Self>, client: Arc<FullClient<Self>>, _select_chain: Self::SelectChain| {
					import_queue::<_, _, Pair>(
						SlotDuration::get_or_compute(&*client)?,
						Box::new(client.clone()),
						None,
						None,
						client,
						state.custom.inherent_data_providers.clone(),
					).map_err(Into::into)
				}
			},
		LightImportQueue = AuraImportQueue<
			Self::Block,
		>
			{ |state: &mut LightComponentsSetupState<Self>, client: Arc<LightClient<Self>>| {
					let fprb = Box::new(DummyFinalityProofRequestBuilder::default()) as Box<_>;
					import_queue::<_, _, Pair>(
						SlotDuration::get_or_compute(&*client)?,
						Box::new(client.clone()),
						None,
						None,
						client,
						state.custom.inherent_data_providers.clone(),
					).map(|q| (q, fprb)).map_err(Into::into)
				}
			},
		SelectChain = LongestChain<FullBackend<Self>, Self::Block>
			{ |state: &mut FullComponentsSetupState<Self>, client: Arc<FullClient<Self>>| {
				Ok(LongestChain::new(state.backend.clone()))
			}
		},
		FinalityProofProvider =  { |state: &mut FullComponentsSetupState<Self>, client: Arc<FullClient<Self>>| {
			Ok(None)
		}},
	}
}
