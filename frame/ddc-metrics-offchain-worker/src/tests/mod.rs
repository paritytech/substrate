use frame_support::traits::{Currency, OffchainWorker};
use frame_system::Trait as FST;
use pallet_contracts::Gas;
use pallet_contracts::{self as contracts, ContractAddressFor, Trait as CT};
use sp_core::{
    offchain::{testing, OffchainExt, Timestamp as OCWTimestamp, TransactionPoolExt},
    testing::KeyStore,
    traits::KeystoreExt,
};
use sp_runtime::{traits::Hash, AccountId32, RuntimeAppPublic};
use test_runtime::{
    AccountId, Balances, Contracts, DdcMetricsOffchainWorker, Origin, System, Test, Timestamp,
};

use crate::{CURRENT_PERIOD_MS, FINALIZE_METRIC_PERIOD, REPORT_METRICS_SELECTOR};
use hex_literal::hex;
use sp_core::bytes::from_hex;

mod test_runtime;

type T = Test;

#[test]
fn test_contract_api() {
    // Parse the contract spec.
    let contract_meta = include_str!("./test_data/metadata.json");
    let contract_meta: serde_json::Value = serde_json::from_str(contract_meta).unwrap();
    let messages = contract_meta
        .pointer("/spec/messages")
        .unwrap()
        .as_array()
        .unwrap();

    // Find the report_metrics function.
    let report_metrics = messages
        .iter()
        .find(|msg| msg.pointer("/name/0").unwrap().as_str().unwrap() == "report_metrics")
        .unwrap();

    // Check the selector.
    let selector = from_hex(report_metrics.get("selector").unwrap().as_str().unwrap()).unwrap();
    assert_eq!(REPORT_METRICS_SELECTOR.to_vec(), selector);

    // Find the get_current_period_ms function.
    let get_current_period_ms = messages
        .iter()
        .find(|msg| msg.pointer("/name/0").unwrap().as_str().unwrap() == "get_current_period_ms")
        .unwrap();

    // Check the selector for get_current_period_ms
    let selector_get_current_period_ms = from_hex(
        get_current_period_ms
            .get("selector")
            .unwrap()
            .as_str()
            .unwrap(),
    )
    .unwrap();
    assert_eq!(CURRENT_PERIOD_MS.to_vec(), selector_get_current_period_ms);

    // Find the finalize_metric_period function.
    let finalize_metric_period = messages
        .iter()
        .find(|msg| msg.pointer("/name/0").unwrap().as_str().unwrap() == "finalize_metric_period")
        .unwrap();

    // Check the selector for finalize_metric_period
    let selector_finalize_metric_period = from_hex(
        finalize_metric_period
            .get("selector")
            .unwrap()
            .as_str()
            .unwrap(),
    )
    .unwrap();
    assert_eq!(
        FINALIZE_METRIC_PERIOD.to_vec(),
        selector_finalize_metric_period
    );
}

#[test]
fn test_encode_report_metrics() {
    let call_data = DdcMetricsOffchainWorker::encode_report_metrics(
        &AccountId32::from([2; 32]),
        3 + (4 << 8),
        5 + (6 << 16),
        7 + (8 << 24),
    );
    assert_eq!(
        call_data,
        vec![
            53, 50, 11, 190, // Selector
            2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
            2, 2, 2, // 32 bytes, app_id
            3, 4, 0, 0, 0, 0, 0, 0, // 8 bytes, day_start_ms
            5, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, // 16 bytes, stored_bytes
            7, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, // 16 bytes, requests
        ]
    );
}

#[test]
fn test_encode_get_current_period_ms() {
    let call_data = DdcMetricsOffchainWorker::encode_get_current_period_ms();
    assert_eq!(
        call_data,
        vec![
        172, 228, 236, 179, // Selector
    ]
    );
}

#[test]
fn test_encode_finalize_metric_period() {
    let call_data = DdcMetricsOffchainWorker::encode_finalize_metric_period(INIT_TIME_MS);
    assert_eq!(
        call_data,
        vec![
            178, 105, 213, 87, // Selector
            80, 152, 94, 120, 118, 1, 0, 0, // 8 bytes, in_day_start_ms
        ]
    );
}

fn build_ext() -> sp_io::TestExternalities {
    build_ext_for_contracts()
}

// Some day, and some time during that day.
const INIT_DAY_MS: u64 = 51 * 365 * 24 * 3_600 * 1_000;
const INIT_TIME_MS: u64 = INIT_DAY_MS + 1234 * 1000;

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
    ext.execute_with(|| {
        System::set_block_number(1);
        Timestamp::set_timestamp(INIT_TIME_MS);
    });
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

        state.timestamp = OCWTimestamp::from_unix_millis(INIT_TIME_MS);

        let mut expect_request = |url: &str, response: &[u8]| {
            state.expect_request(testing::PendingRequest {
                method: "GET".into(),
                uri: url.to_string(),
                response: Some(response.to_vec()),
                sent: true,
                ..Default::default()
            });
        };

        // List nodes from a boot node.
        expect_request(
            "https://TEST_DDC/api/rest/nodes",
            include_bytes!("./test_data/ddc_nodes.json"),
        );

        // List partitions from a boot node.
        expect_request("https://node-0.ddc.stage.cere.network/api/rest/metrics?isMaster=true&active=true&from=1608336000&to=1608337114",
                       include_bytes!("test_data/ddc_metrics_node-0.json"));

        // List partitions from a boot node.
        expect_request("https://node-3.ddc.stage.cere.network/api/rest/metrics?isMaster=true&active=true&from=1608336000&to=1608337114",
                       include_bytes!("test_data/ddc_metrics_node-3.json"));
    }

    t.execute_with(|| {
        let contract_id = deploy_contract();

        let kind = sp_core::offchain::StorageKind::PERSISTENT;
        sp_io::offchain::local_storage_set(
            kind,
            b"ddc-metrics-offchain-worker::sc_address",
            contract_id.as_ref(),
        );
        sp_io::offchain::local_storage_set(
            kind,
            b"ddc-metrics-offchain-worker::ddc_url",
            b"https://TEST_DDC",
        );

        // Trigger the worker.
        DdcMetricsOffchainWorker::offchain_worker(0);

        let events = System::events();
        eprintln!("Events: {:?}\n", events);

        // Get the transaction from the worker.
        let transactions = pool_state.read().transactions.clone();
        eprintln!("Transactions: {:?}\n", transactions);
        assert_eq!(transactions.len(), 2);

        // Check metrics of an app based on ddc_metrics_node-0.json and ddc_metrics_node-3.json.
        let app_id = AccountId32::from(hex!(
            "00a2e826451b78afb99241b1331e7594526329225ff8937dbc62f43ec20d1830"
        ));
        let expected_call =
            DdcMetricsOffchainWorker::encode_report_metrics(&app_id, INIT_DAY_MS, 1 + 10, 2 + 20);
        assert!(
            transactions[0].ends_with(&expected_call),
            "Expected a specific call to the report_metrics function"
        );

        // Check metrics of the second app.
        let app_id = AccountId32::from(hex!(
            "100ad4097b6e60700a5d5c5294cb6d663090ef5f547e84cc20ec6bcc7a552f13"
        ));
        let expected_call =
            DdcMetricsOffchainWorker::encode_report_metrics(&app_id, INIT_DAY_MS, 100, 200);
        assert!(
            transactions[1].ends_with(&expected_call),
            "Expected a specific call to the report_metrics function"
        );
    });
}

fn deploy_contract() -> AccountId {
    // Admin account who deploys the contract.
    let alice = AccountId::default();
    let _ = Balances::deposit_creating(&alice, 10_000_000_000);

    // Load the contract code.
    let wasm = &include_bytes!("./test_data/cere02.wasm")[..];
    let wasm_hash = <T as FST>::Hashing::hash(wasm);
    let contract_args = vec![];

    // Deploy the contract.
    let endowment = contracts::Config::<T>::subsistence_threshold_uncached();
    const GAS_LIMIT: Gas = 10_000_000_000;
    Contracts::put_code(Origin::signed(alice.clone()), wasm.to_vec()).unwrap();
    Contracts::instantiate(
        Origin::signed(alice.clone()),
        endowment,
        GAS_LIMIT,
        wasm_hash.into(),
        contract_args.clone(),
    )
    .unwrap();

    // Configure worker with the contract address.
    let contract_id = <T as CT>::DetermineContractAddress::contract_address_for(
        &wasm_hash,
        &contract_args,
        &alice,
    );

    contract_id
}
