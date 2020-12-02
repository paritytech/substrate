use substrate_test_runner::{Node, ChainInfo, SignatureVerificationOverride};
use grandpa::GrandpaBlockImport;
use sc_service::{TFullBackend, TFullClient, Configuration, TaskManager, new_full_parts};
use node_runtime::{SignedExtra, Runtime, Call, Event};
use sp_runtime::generic::Era;
use std::{sync::Arc, str::FromStr};
use sp_inherents::InherentDataProviders;
use sc_consensus_babe::BabeBlockImport;
use sp_keystore::SyncCryptoStorePtr;
use sp_keyring::sr25519::Keyring::Alice;
use node_cli::chain_spec::development_config;
use sp_consensus_babe::AuthorityId;
use sc_consensus_manual_seal::{ConsensusDataProvider, consensus::babe::BabeConsensusDataProvider};
use sp_runtime::AccountId32;

type BlockImport<B, BE, C, SC> = BabeBlockImport<B, C, GrandpaBlockImport<BE, B, C, SC>>;

sc_executor::native_executor_instance!(
	pub Executor,
	node_runtime::api::dispatch,
	node_runtime::native_version,
	SignatureVerificationOverride,
);

pub struct NodeTemplateChainInfo;

impl ChainInfo for NodeTemplateChainInfo {
    type Block = node_primitives::Block;
    type Executor = Executor;
    type Runtime = node_runtime::Runtime;
    type RuntimeApi = node_runtime::RuntimeApi;
    type SelectChain = sc_consensus::LongestChain<TFullBackend<Self::Block>, Self::Block>;
    type BlockImport = BlockImport<
        Self::Block,
        TFullBackend<Self::Block>,
        TFullClient<Self::Block, Self::RuntimeApi, Self::Executor>,
        Self::SelectChain,
    >;
    type SignedExtras = SignedExtra;

    fn load_spec() -> Result<Box<dyn sc_service::ChainSpec>, String> {
        Ok(Box::new(development_config()))
    }

    fn signed_extras(from: <Self::Runtime as frame_system::Config>::AccountId) -> Self::SignedExtras {
        (
            frame_system::CheckSpecVersion::<Self::Runtime>::new(),
            frame_system::CheckTxVersion::<Self::Runtime>::new(),
            frame_system::CheckGenesis::<Self::Runtime>::new(),
            frame_system::CheckMortality::<Self::Runtime>::from(Era::Immortal),
            frame_system::CheckNonce::<Self::Runtime>::from(frame_system::Module::<Self::Runtime>::account_nonce(from)),
            frame_system::CheckWeight::<Self::Runtime>::new(),
            pallet_transaction_payment::ChargeTransactionPayment::<Self::Runtime>::from(0),
        )
    }

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
                        Transaction = sp_api::TransactionFor<
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
    > {
        let (client, backend, keystore, task_manager) =
            new_full_parts::<Self::Block, Self::RuntimeApi, Self::Executor>(config)?;
        let client = Arc::new(client);

        let inherent_providers = InherentDataProviders::new();
        let select_chain = sc_consensus::LongestChain::new(backend.clone());

        let (grandpa_block_import, ..) =
            grandpa::block_import(client.clone(), &(client.clone() as Arc<_>), select_chain.clone())?;

        let (block_import, babe_link) = sc_consensus_babe::block_import(
            sc_consensus_babe::Config::get_or_compute(&*client)?,
            grandpa_block_import,
            client.clone(),
        )?;

        let consensus_data_provider = BabeConsensusDataProvider::new(
            client.clone(),
            keystore.sync_keystore(),
            &inherent_providers,
            babe_link.epoch_changes().clone(),
            vec![(AuthorityId::from(Alice.public()), 1000)],
        )
            .expect("failed to create ConsensusDataProvider");

        Ok((
            client,
            backend,
            keystore.sync_keystore(),
            task_manager,
            inherent_providers,
            Some(Box::new(consensus_data_provider)),
            select_chain,
            block_import,
        ))
    }
}

/// performs a runtime upgrade given wasm blob and a handle to a node.
pub fn perform_runtime_upgrade(node: &Node<NodeTemplateChainInfo>) {
    type SystemCall = frame_system::Call<Runtime>;
    type SudoCall = pallet_sudo::Call<Runtime>;

    let whales = vec![
        "5GrwvaEF5zXb26Fz9rcQpDWS57CtERHpNehXCPcNoHGKutQY", //Alice
        "5FHneW46xGXgs5mUiveU4sbTyGBzmstUspZC92UhjJM694ty", //Bob
    ]
        .into_iter()
        .map(|account| AccountId32::from_str(account).unwrap())
        .collect::<Vec<_>>();

    let wasm = include_bytes!("./runtime.wasm");

    let call = Call::Sudo(SudoCall::sudo(Box::new(Call::System(SystemCall::set_code(wasm.to_vec())))));
    node.submit_extrinsic(call, whales[0].clone());
    node.seal_blocks(1);

    // assert that the runtime is upgraded by looking at events
    let events = node.with_state(|| frame_system::Module::<Runtime>::events())
        .into_iter()
        .filter(|event| {
            match event.event {
                Event::frame_system(frame_system::RawEvent::CodeUpdated) => true,
                _ => false,
            }
        })
        .collect::<Vec<_>>();

    // make sure event is in state
    assert_eq!(events.len(), 1);
}

#[cfg(test)]
mod tests {
    use super::*;
    use pallet_balances_e2e_tests::*;

    #[test]
    fn runtime_upgrade() {
        let node = Node::<NodeTemplateChainInfo>::new().unwrap();

        // first perform runtime upgrade
        perform_runtime_upgrade(&node);
        // pallet balances assertions
        transfer_keep_alive(&node);
        set_balance(&node);
        force_transfer(&node);

    }
}