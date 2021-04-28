use codec::Decode;
use sp_core::{
	offchain::{testing, OffchainExt, TransactionPoolExt},
	testing::KeyStore,
	traits::KeystoreExt,
};
use sp_runtime::RuntimeAppPublic;
use sp_std::str::FromStr;

use crate::{METRICS_CONTRACT_ADDR, METRICS_CONTRACT_ID};

mod test_runtime;
use test_runtime::{AccountId, ExampleOffchainWorker, Extrinsic};

#[test]
fn decode_contract_address() {
	let account_decoded = AccountId::from_str(METRICS_CONTRACT_ADDR).unwrap();
	let account_from_bytes = AccountId::from_raw(METRICS_CONTRACT_ID);

	assert_eq!(account_decoded.0, account_from_bytes.0);
}

#[test]
fn should_submit_signed_transaction_on_chain() {
	const PHRASE: &str =
		"news slush supreme milk chapter athlete soap sausage put clutch what kitten";

	let (offchain, offchain_state) = testing::TestOffchainExt::new();
	let (pool, pool_state) = testing::TestTransactionPoolExt::new();
	let keystore = KeyStore::new();
	keystore
		.write()
		.sr25519_generate_new(
			crate::crypto::Public::ID,
			Some(&format!("{}/hunter1", PHRASE)),
		)
		.unwrap();

	let mut t = sp_io::TestExternalities::default();
	t.register_extension(OffchainExt::new(offchain));
	t.register_extension(TransactionPoolExt::new(pool));
	t.register_extension(KeystoreExt(keystore));

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
		state.expect_request(testing::PendingRequest {
			method: "GET".into(),
			uri: "https://node-0.ddc.stage.cere.network/api/rest/partitions".into(),
			response: Some(include_bytes!("./test_data/ddc_partitions.json").to_vec()),
			sent: true,
			..Default::default()
		});
	}

	t.execute_with(|| {
		// Trigger the worker.
		ExampleOffchainWorker::fetch_ddc_data_and_send_to_sc(0).unwrap();

		// Get the transaction from the worker.
		let tx = pool_state.write().transactions.pop().unwrap();
		assert!(pool_state.read().transactions.is_empty());
		let tx = Extrinsic::decode(&mut &*tx).unwrap();
		assert_eq!(tx.signature.unwrap().0, 0);

		// TODO: recognize smart contract call.
		println!("{:?}", tx.call);
	});
}
