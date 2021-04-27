use codec::Decode;

use frame_support::{
    assert_err_ignore_postinfo, assert_ok,
    dispatch::DispatchErrorWithPostInfo,
    impl_outer_dispatch, impl_outer_event, impl_outer_origin, parameter_types,
    traits::{Currency, OffchainWorker},
};
use frame_system::Trait as FST;
use pallet_contracts::{self as contracts, ContractAddressFor, Trait as CT};
use pallet_contracts::Gas;
use sp_core::{
    offchain::{OffchainExt, testing, TransactionPoolExt},
    testing::KeyStore,
    traits::KeystoreExt,
};
use sp_runtime::{RuntimeAppPublic, traits::Hash};
use sp_std::str::FromStr;
use test_runtime::{
    AccountId, Balances, Contracts, CURRENT_METRICS_CONTRACT_ID, ExampleOffchainWorker, Extrinsic, Origin, System, Test,
};

use crate::{METRICS_CONTRACT_ADDR, METRICS_CONTRACT_ID};

mod test_runtime;

type T = Test;

#[test]
fn decode_contract_address() {
    let account_decoded = AccountId::from_str(METRICS_CONTRACT_ADDR).unwrap();
    let account_from_bytes = AccountId::from_raw(METRICS_CONTRACT_ID);

    assert_eq!(account_decoded.0, account_from_bytes.0);
}

fn build_ext() -> sp_io::TestExternalities {
    build_ext_for_contracts()
}

// Taken from pallet_contracts::tests::ExtBuilder
fn build_ext_for_contracts() -> sp_io::TestExternalities {
    let mut t = frame_system::GenesisConfig::default()
        .build_storage::<Test>()
        .unwrap();
    pallet_balances::GenesisConfig::<Test> { balances: vec![] }
        .assimilate_storage(&mut t)
        .unwrap();
    contracts::GenesisConfig {
        current_schedule: contracts::Schedule {
            enable_println: true,
            ..Default::default()
        },
    }
        .assimilate_storage(&mut t)
        .unwrap();
    let mut ext = sp_io::TestExternalities::new(t);
    ext.execute_with(|| System::set_block_number(1));
    ext
}

#[test]
fn should_submit_signed_transaction_on_chain() {
    let mut t = build_ext();

    let (pool, pool_state) = testing::TestTransactionPoolExt::new();
    t.register_extension(TransactionPoolExt::new(pool));

    const PHRASE: &str =
        "news slush supreme milk chapter athlete soap sausage put clutch what kitten";
    let keystore = KeyStore::new();
    keystore
        .write()
        .sr25519_generate_new(
            crate::crypto::Public::ID,
            Some(&format!("{}/hunter1", PHRASE)),
        )
        .unwrap();
    t.register_extension(KeystoreExt(keystore));

    let (offchain, offchain_state) = testing::TestOffchainExt::new();
    t.register_extension(OffchainExt::new(offchain));

    {
        let mut state = offchain_state.write();
        state.expect_request(testing::PendingRequest {
            method: "GET".into(),
            uri: "https://node-0.ddc.stage.cere.network/api/rest/nodes".into(),
            response: Some(include_bytes!("./test_data/ddc_nodes.json").to_vec()),
            sent: true,
            ..Default::default()
        });
        state.expect_request(testing::PendingRequest {
            method: "GET".into(),
            uri: "https://node-0.ddc.stage.cere.network/api/rest/metrics".into(),
            response: Some(include_bytes!("./test_data/ddc_metrics.json").to_vec()),
            sent: true,
            ..Default::default()
        });
    }

    t.execute_with(|| {
        deploy_contract();

        // Trigger the worker.
        ExampleOffchainWorker::offchain_worker(0);

        let events = System::events();
        eprintln!("Events: {:?}\n", events);

        // Get the transaction from the worker.
        let transactions = pool_state.read().transactions.clone();
        eprintln!("Transactions: {:?}\n", transactions);
        assert_eq!(transactions.len(), 1);

        // TODO: recognize smart contract call.
    });
}

fn deploy_contract() {
    // Admin account who deploys the contract.
    let alice = AccountId::default();
    let _ = Balances::deposit_creating(&alice, 10_000_000_000);

    // Load the contract code.
    let wasm = &include_bytes!("./test_data/ddc.wasm")[..];
    let wasm_hash = <T as FST>::Hashing::hash(wasm);
    let contract_args = vec![];

    // Deploy the contract.
    let endowment = contracts::Config::<T>::subsistence_threshold_uncached();
    const GAS_LIMIT: Gas = 10_000_000_000;
    Contracts::put_code(Origin::signed(alice), wasm.to_vec()).unwrap();
    Contracts::instantiate(
        Origin::signed(alice),
        endowment,
        GAS_LIMIT,
        wasm_hash.into(),
        contract_args.clone(),
    ).unwrap();

    // Configure worker with the contract address.
    let contract_id = <T as CT>::DetermineContractAddress::contract_address_for(
        &wasm_hash,
        &contract_args,
        &alice,
    );
    CURRENT_METRICS_CONTRACT_ID.with(|v| *v.borrow_mut() = contract_id);
    //eprintln!("Test contract address: {}\n", <T as crate::Trait>::ContractId::get());
}
