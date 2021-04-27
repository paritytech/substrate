use codec::Decode;
use frame_support::{
    assert_err_ignore_postinfo, assert_ok,
    dispatch::DispatchErrorWithPostInfo,
    impl_outer_dispatch, impl_outer_event, impl_outer_origin, parameter_types,
    traits::{Currency, Get, ReservableCurrency, OffchainWorker},
    weights::{PostDispatchInfo, Weight},
    StorageMap, StorageValue,
};
use frame_system::Trait as FST;
use pallet_contracts::Gas;
use pallet_contracts::{self as contracts, ContractAddressFor, Trait as CT};
use sp_core::{
    offchain::{testing, OffchainExt, TransactionPoolExt},
    testing::KeyStore,
    traits::KeystoreExt,
};
use sp_runtime::{traits::Hash, RuntimeAppPublic};
use sp_std::str::FromStr;

use crate::{METRICS_CONTRACT_ADDR, METRICS_CONTRACT_ID};

mod test_runtime;

use test_runtime::{
    AccountId, Balances, Contracts, ExampleOffchainWorker, Extrinsic, Origin, System, Test, CURRENT_METRICS_CONTRACT_ID,
};

type T = Test;
type ContractCall = pallet_contracts::Call<<Test as crate::Trait>::CT>;

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
    const PHRASE: &str =
        "news slush supreme milk chapter athlete soap sausage put clutch what kitten";

    let mut t = build_ext();

    let (pool, pool_state) = testing::TestTransactionPoolExt::new();
    t.register_extension(TransactionPoolExt::new(pool));

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
        // Admin account who deploys the contract.
        let alice = AccountId::default();
        let _ = Balances::deposit_creating(&alice, 10_000_000_000);

        // Deploy the contract.
        let wasm = &include_bytes!("./test_data/ddc.wasm")[..];
        let wasm_hash = <T as FST>::Hashing::hash(wasm);
        let contract_args = vec![];
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
        eprintln!("Test contract address: {}", <T as crate::Trait>::ContractId::get());

        let events = System::events();
        eprintln!("Events: {:?}", events);

        // Trigger the worker.
        ExampleOffchainWorker::offchain_worker(0);

        // Get the transaction from the worker.
        let tx = pool_state.write().transactions.pop().unwrap();
        assert!(pool_state.read().transactions.is_empty());
        let tx = Extrinsic::decode(&mut &*tx).unwrap();
        assert_eq!(tx.signature.unwrap().0, 0);

        // TODO: recognize smart contract call.
        println!("{:?}", tx.call);
    });
}
