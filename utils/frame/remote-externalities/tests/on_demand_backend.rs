#![cfg(test)]

use assert_cmd::cargo::cargo_bin;
use frame_remote_externalities::on_demand_backend::{OnDemandBackend, RawIter};
use regex::Regex;
use sp_core::Blake2Hasher;
use sp_keyring::AccountKeyring;
use sp_state_machine::StorageIterator;
use substrate_cli_test_utils as common;
use subxt::{
	config::substrate::{Era, SubstrateExtrinsicParamsBuilder},
	tx::PairSigner,
	OnlineClient, SubstrateConfig,
};
use tokio::process::{Child, Command};

#[subxt::subxt(runtime_metadata_path = "tests/artifacts/substrate.scale")]
pub mod node_runtime {}

type SystemCall = node_runtime::runtime_types::frame_system::pallet::Call;
type RuntimeCall = node_runtime::runtime_types::kitchensink_runtime::RuntimeCall;

async fn setup_remote_node(port: u32) -> Result<Child, subxt::Error> {
	// Spawn node
	let mut child = Command::new(cargo_bin("substrate"))
		.args(&["--dev", "--no-hardware-benchmarks", format!("--rpc-port={}", port).as_str()])
		.stderr(std::process::Stdio::piped())
		.stdout(std::process::Stdio::piped())
		.kill_on_drop(true)
		.spawn()
		.unwrap();

	// Wait for node to start importing blocks
	let stderr = child.stderr.take().unwrap();
	let re = Regex::new(r"^.*Imported\s#.*$").unwrap();
	// wait 10 seconds
	// tokio::sleep(tokio::time::Duration::from_secs(10)).await;

	match common::wait_for_stream_pattern_match(stderr, re).await {
		Ok(()) => {},
		Err(e) => println!("Error: {}", e),
	}

	// Connect to node
	let api = OnlineClient::<SubstrateConfig>::from_url(format!("ws://localhost:{}", port)).await?;

	// Create storage items
	let items = vec![
		(b"key1".to_vec(), b"value1".to_vec()),
		(b"key2".to_vec(), b"value2".to_vec()),
		(b"key3".to_vec(), b"value3".to_vec()),
	];
	let tx_params = SubstrateExtrinsicParamsBuilder::new().era(Era::Immortal, api.genesis_hash());
	let call = RuntimeCall::System(SystemCall::set_storage { items });
	let tx = node_runtime::tx().sudo().sudo(call);
	let from = PairSigner::new(AccountKeyring::Alice.pair());
	api.tx()
		.sign_and_submit_then_watch(&tx, &from, tx_params)
		.await?
		.wait_for_in_block()
		.await?
		.wait_for_success()
		.await?;

	println!("\nSent sudo transaction to set storage items");

	Ok(child)
}

#[tokio::test]
async fn test_next_key() {
	let port = 9989;

	let _node_child = match setup_remote_node(port).await {
		Ok(child) => child,
		Err(e) => return println!("Error: {}", e),
	};

	let backend =
		OnDemandBackend::<Blake2Hasher>::new("ws://localhost:9989".to_owned(), None, false)
			.await
			.unwrap();

	let mut iter = RawIter::new(None, None, None, true);

	while let Some(key) = iter.next_key(&backend) {
		dbg!(key.unwrap());
	}
	dbg!("done");

	// // Test with a backend containing a few keys
	// let mut iter = new_raw_iter(None, None);
	// assert_eq!(iter.next_key(&backend), Some(Ok(b"key1".to_vec())));
	// assert_eq!(iter.next_key(&backend), Some(Ok(b"key2".to_vec())));
	// assert_eq!(iter.next_key(&backend), Some(Ok(b"key3".to_vec())));
	// assert_eq!(iter.next_key(&backend), None);

	// // Test with a different prefix
	// let mut iter = new_raw_iter(Some(b"key"), None);
	// assert_eq!(iter.next_key(&backend), Some(Ok(b"key1".to_vec())));
	// assert_eq!(iter.next_key(&backend), Some(Ok(b"key2".to_vec())));
	// assert_eq!(iter.next_key(&backend), Some(Ok(b"key3".to_vec())));
	// assert_eq!(iter.next_key(&backend), None);
}
