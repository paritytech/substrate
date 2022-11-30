use frame_support::traits::{Currency, OffchainWorker};
use frame_system::Config as FSC;
use pallet_contracts::Gas;
use pallet_contracts::{self as contracts, Config as CC};
use sp_core::{
    offchain::{testing, OffchainExt, Timestamp as OCWTimestamp, TransactionPoolExt}
};
use sp_runtime::{traits::Hash, AccountId32, RuntimeAppPublic};
use test_runtime::{
    AccountId, Balance, Balances, Contracts, DdcMetricsOffchainWorker, Origin, System, Test,
    Timestamp,
};

use sp_keystore::{KeystoreExt, testing::KeyStore};
use sp_keystore::SyncCryptoStore;
use std::sync::Arc;

use crate::{
    CURRENT_PERIOD_MS, FINALIZE_METRIC_PERIOD, REPORT_DDN_STATUS_SELECTOR, REPORT_METRICS_SELECTOR,
};
use codec::Encode;
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

    // Find the report_ddn_status function.
    let report_ddn_status = messages
        .iter()
        .find(|msg| msg.pointer("/name/0").unwrap().as_str().unwrap() == "report_ddn_status")
        .unwrap();

    // Check the selector for report_ddn_status
    let selector_report_ddn_status =
        from_hex(report_ddn_status.get("selector").unwrap().as_str().unwrap()).unwrap();
    assert_eq!(
        REPORT_DDN_STATUS_SELECTOR.to_vec(),
        selector_report_ddn_status
    );
}

#[test]
fn test_encode_report_metrics() {
    let call_data = DdcMetricsOffchainWorker::encode_report_metrics(
        &AccountId32::from([2; 32]),
        3 + (4 << 8),
        5 + (6 << 16),
        7 + (8 << 24),
        9 + (16 << 24),
    );
    assert_eq!(
        call_data,
        vec![
            53, 50, 11, 190, // Selector
            2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
            2, 2, 2, // 32 bytes, app_id
            3, 4, 0, 0, 0, 0, 0, 0, // 8 bytes, day_start_ms
            5, 0, 6, 0, 0, 0, 0, 0, // 8 bytes, storage_bytes
            7, 0, 0, 8, 0, 0, 0, 0, // 8 bytes, wcu_used
            9, 0, 0, 16, 0, 0, 0, 0 // 8 bytes, rcu_used
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

#[test]
fn test_encode_report_ddn_status() {
    let call_data = DdcMetricsOffchainWorker::encode_report_ddn_status(
        &String::from_utf8(vec![0, 1, 2, 3]).unwrap(),
        true,
    );
    assert_eq!(
        call_data,
        [
            REPORT_DDN_STATUS_SELECTOR.to_vec(), // Selector
            vec![
                16, // size of p2p_id
                0, 1, 2, 3, // p2p_id
                1  // is_online
            ],
        ]
        .concat()
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
    contracts::GenesisConfig::<Test> {
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
        .sr25519_generate_new(
            crate::crypto::Public::ID,
            Some(&format!("{}/hunter1", PHRASE)),
        )
        .unwrap();
    t.register_extension(KeystoreExt(Arc::new(keystore)));

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

        // Trigger the worker.
        DdcMetricsOffchainWorker::offchain_worker(0);

        let events = System::events();
        eprintln!("Events: {:?}\n", events);

        // Get the transaction from the worker.
        let transactions = pool_state.read().transactions.clone();
        eprintln!("Transactions: {:?}\n", transactions);
        assert_eq!(transactions.len(), 4); // (2 x send_metrics_to_sc) + (2 x send_metrics_ddn_to_sc)

        // Check metrics of an app based on ddc_metrics_node-0.json and ddc_metrics_node-3.json.
        let app_id = AccountId32::from(hex!(
            "00a2e826451b78afb99241b1331e7594526329225ff8937dbc62f43ec20d1830"
        ));
        let expected_call =
            DdcMetricsOffchainWorker::encode_report_metrics(&app_id, INIT_DAY_MS, 2 + 20, 0, 0);
        assert!(
            transactions[0].ends_with(&expected_call),
            "Expected a specific call to the report_metrics function"
        );

        // Check metrics of the second app.
        let app_id = AccountId32::from(hex!(
            "100ad4097b6e60700a5d5c5294cb6d663090ef5f547e84cc20ec6bcc7a552f13"
        ));
        let expected_call =
            DdcMetricsOffchainWorker::encode_report_metrics(&app_id, INIT_DAY_MS, 200, 0, 0);
        assert!(
            transactions[1].ends_with(&expected_call),
            "Expected a specific call to the report_metrics function"
        );

        let expected_call = DdcMetricsOffchainWorker::encode_report_metrics_ddn(
            "12D3KooWB4SMhKK12ASU4qH1ZYh3pN9vsW9QbFTwkjZxUhTqmYaS".to_string(),
            INIT_DAY_MS,
            2 + 200,
            0,
            0,
        );
        assert!(
            transactions[2].ends_with(&expected_call),
            "Expected a specific call to the report_metrics_ddn function"
        );

        let expected_call = DdcMetricsOffchainWorker::encode_report_metrics_ddn(
            "12D3KooWJLuJEmtYf3bakUwe2q1uMcnbCBKRg7GkpG6Ws74Aq6NC".to_string(),
            INIT_DAY_MS,
            20,
            0,
            0,
        );
        assert!(
            transactions[3].ends_with(&expected_call),
            "Expected a specific call to the report_metrics_ddn function"
        );
    });
}

#[test]
fn should_run_contract() {
    let mut t = build_ext();

    t.execute_with(|| {
        let alice = AccountId::from([1; 32]);
        let contract_id = deploy_contract();
        let call_data = DdcMetricsOffchainWorker::encode_get_current_period_ms();

        pallet_contracts::Module::<T>::call(
            Origin::signed(alice.clone()),
            contract_id.clone(),
            0,
            100_000_000_000,
            call_data.clone(),
        )
        .unwrap();

        let contract_exec_result = pallet_contracts::Module::<T>::bare_call(
            alice.clone(),
            contract_id,
            0,
            100_000_000_000,
            call_data,
        );
        match &contract_exec_result.exec_result {
            Ok(res) => {
                //println!("XXX Contract returned {:?}", res.data);
                assert_eq!(res.data.len(), 8); // size of u64
            }
            Err(_) => panic!("error in contract call"),
        };
    });
}

pub const CTOR_SELECTOR: [u8; 4] = hex!("9bae9d5e");

fn encode_constructor() -> Vec<u8> {
    let mut call_data = CTOR_SELECTOR.to_vec();
    let x = 0 as u128;
    for _ in 0..9 {
        x.encode_to(&mut call_data);
    }
    call_data
}

fn deploy_contract() -> AccountId {
    // Admin account who deploys the contract.
    let alice = AccountId::from([1; 32]);
    let _ = Balances::deposit_creating(&alice, 1_000_000_000_000);

    // Load the contract code.
    let wasm = &include_bytes!("./test_data/ddc.wasm")[..];
    let wasm_hash = <T as FSC>::Hashing::hash(wasm);
    let contract_args = encode_constructor();

    // Deploy the contract.
    //let endowment = contracts::Config::<T>::subsistence_threshold_uncached();
    const GAS_LIMIT: Gas = 100_000_000_000;
    const ENDOWMENT: Balance = 100_000_000_000;
    Contracts::put_code(Origin::signed(alice.clone()), wasm.to_vec()).unwrap();
    Contracts::instantiate(
        Origin::signed(alice.clone()),
        ENDOWMENT,
        GAS_LIMIT,
        wasm_hash.into(),
        contract_args.clone(),
        vec![]
    )
    .unwrap();

    // Configure worker with the contract address.
    let contract_id = Contracts::contract_address(
        &alice,
        &wasm_hash,
        &vec![],
    );

    pub const ADD_DDC_NODE_SELECTOR: [u8; 4] = hex!("11a9e1b9");

    let call_data_items = vec![
        ["12D3KooWB4SMhKK12ASU4qH1ZYh3pN9vsW9QbFTwkjZxUhTqmYaS", "/dns4/node-0.ddc.dev.cere.network/tcp/5000/p2p/12D3KooWB4SMhKK12ASU4qH1ZYh3pN9vsW9QbFTwkjZxUhTqmYaS", "https://node-0.ddc.stage.cere.network"],
        ["12D3KooWJLuJEmtYf3bakUwe2q1uMcnbCBKRg7GkpG6Ws74Aq6NC", "/dns4/node-3.ddc.dev.cere.network/tcp/5000/p2p/12D3KooWJLuJEmtYf3bakUwe2q1uMcnbCBKRg7GkpG6Ws74Aq6NC", "https://node-3.ddc.stage.cere.network"],
    ];
    let permissions: u64 = 1;

    for call_data_item in call_data_items {
        let mut call_data = ADD_DDC_NODE_SELECTOR.to_vec();
        call_data_item[0].encode_to(&mut call_data);
        call_data_item[1].encode_to(&mut call_data);
        call_data_item[2].encode_to(&mut call_data);
        permissions.encode_to(&mut call_data);

        let results = Contracts::call(
            Origin::signed(alice.clone()),
            contract_id.clone(),
            0,
            1_000_000_000_000,
            call_data,
        );
        results.unwrap();
    }

    contract_id
}
