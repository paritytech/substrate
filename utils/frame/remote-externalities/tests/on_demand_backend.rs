#![cfg(test)]

use assert_cmd::cargo::cargo_bin;
use frame_remote_externalities::on_demand_backend::{OnDemandBackend, RawIter};
use regex::Regex;
use sp_core::Blake2Hasher;
use sp_keyring::AccountKeyring;
use sp_state_machine::{Backend, StorageIterator};
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

fn build_key_value_vec() -> Vec<(Vec<u8>, Vec<u8>)> {
	// Make sure we have enough items to fetch a few pages from the node over the course
	// of the tests
	let n_items = RawIter::<Blake2Hasher>::NEXT_KEYS_CACHE_PAGE_SIZE * 3 + 10;
	let mut v = (0..n_items)
		.map(|i| {
			let key = format!("test__key{}", i).into_bytes();
			let value = format!("test__value{}", i).into_bytes();
			(key, value)
		})
		.collect::<Vec<_>>();
	v.sort();
	v
}

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
	let items = build_key_value_vec();
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
async fn test_raw_iter() {
	let port = 9989;
	let _node_child = match setup_remote_node(port).await {
		Ok(child) => child,
		Err(e) => return println!("Error: {}", e),
	};

	let backend = OnDemandBackend::<Blake2Hasher>::new(
		format!("ws://localhost:{}", port).to_owned(),
		None,
		false,
	)
	.await
	.unwrap();

	// Test iter with prefix works, and values come back OK
	let mut iter = RawIter::new(Some(b"test__key"), None, None, true);
	let items = build_key_value_vec();
	for (expected_key, expected_value) in items.clone() {
		assert_eq!(iter.next_key(&backend), Some(Ok(expected_key.clone())));
		assert_eq!(backend.storage(&expected_key).unwrap(), Some(expected_value));
	}
	assert_eq!(iter.was_complete(), true);
	assert_eq!(iter.next_key(&backend), None);
	assert_eq!(iter.was_complete(), true);

	// Test iter with start_key works, and values come back OK
	let mut iter = RawIter::new(None, None, Some(b"test__key"), true);
	for (expected_key, expected_value) in items.clone() {
		assert_eq!(iter.next_key(&backend), Some(Ok(expected_key.clone())));
		assert_eq!(backend.storage(&expected_key).unwrap(), Some(expected_value));
	}
	assert_eq!(iter.was_complete(), false);

	// Test iter next_pair works
	let mut iter = RawIter::new(Some(b"test__key"), None, None, true);
	for (expected_key, expected_value) in items.clone() {
		assert_eq!(iter.next_pair(&backend), Some(Ok((expected_key, expected_value))));
	}
	assert_eq!(iter.was_complete(), true);
	assert_eq!(iter.next_pair(&backend), None);
	assert_eq!(iter.was_complete(), true);

	// Test using next_key and next_pair together on the same iter works
	let mut iter = RawIter::new(Some(b"test__key"), None, None, true);
	for (i, (expected_key, expected_value)) in items.clone().iter().enumerate() {
		// Every 5th iteration use next_pair
		if i % 5 == 0 {
			assert_eq!(
				iter.next_pair(&backend),
				Some(Ok((expected_key.clone(), expected_value.clone())))
			);
		} else {
			assert_eq!(iter.next_key(&backend), Some(Ok(expected_key.clone())));
			assert_eq!(
				backend.storage(&expected_key.clone()).unwrap(),
				Some(expected_value.clone())
			);
		}
	}
	assert_eq!(iter.was_complete(), true);
	assert_eq!(iter.next_pair(&backend), None);
	assert_eq!(iter.next_key(&backend), None);
	assert_eq!(iter.was_complete(), true);
}
