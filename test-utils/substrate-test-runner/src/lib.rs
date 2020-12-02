use manual_seal::consensus::ConsensusDataProvider;
use sc_executor::NativeExecutionDispatch;
use sc_service::{ChainSpec, Configuration, TFullBackend, TFullClient, TaskManager};
use sp_api::{ConstructRuntimeApi, TransactionFor};
use sp_consensus::{BlockImport, SelectChain};
use sp_inherents::InherentDataProviders;
use sp_keystore::SyncCryptoStorePtr;
use sp_runtime::traits::{Block as BlockT, SignedExtension};
use std::sync::Arc;

mod node;
mod utils;
mod host_functions;

pub use host_functions::*;
pub use node::*;

/// Wrapper trait for concrete type required by this testing framework.
pub trait ChainInfo: Sized {
	/// Opaque block type
	type Block: BlockT;

	/// Executor type
	type Executor: NativeExecutionDispatch + 'static;

	/// Runtime
	type Runtime: frame_system::Config;

	/// RuntimeApi
	type RuntimeApi: Send
		+ Sync
		+ 'static
		+ ConstructRuntimeApi<Self::Block, TFullClient<Self::Block, Self::RuntimeApi, Self::Executor>>;

	/// select chain type.
	type SelectChain: SelectChain<Self::Block> + 'static;

	/// Block import type.
	type BlockImport: Send
		+ Sync
		+ Clone
		+ BlockImport<
			Self::Block,
			Error = sp_consensus::Error,
			Transaction = TransactionFor<TFullClient<Self::Block, Self::RuntimeApi, Self::Executor>, Self::Block>,
		> + 'static;

	type SignedExtras: SignedExtension;

	/// chain spec factory
	fn load_spec() -> Result<Box<dyn ChainSpec>, String>;

	/// Get polkadot base path from env.
	fn base_path() -> Option<String> {
		std::env::var("POLKADOT_BASE_PATH").ok()
	}

	/// Signed extras, this function is caled in an externalities provided environment.
	fn signed_extras(from: <Self::Runtime as frame_system::Config>::AccountId) -> Self::SignedExtras;

	/// Attempt to create client parts, including block import,
	/// select chain strategy and consensus data provider.
	fn create_client_parts(
		config: &Configuration,
	) -> Result<
		(
			Arc<TFullClient<Self::Block, Self::RuntimeApi, Self::Executor>>,
			Arc<TFullBackend<Self::Block>>,
			SyncCryptoStorePtr,
			TaskManager,
			InherentDataProviders,
			Option<
				Box<
					dyn ConsensusDataProvider<
						Self::Block,
						Transaction = TransactionFor<
							TFullClient<Self::Block, Self::RuntimeApi, Self::Executor>,
							Self::Block,
						>,
					>,
				>,
			>,
			Self::SelectChain,
			Self::BlockImport,
		),
		sc_service::Error,
	>;
}
