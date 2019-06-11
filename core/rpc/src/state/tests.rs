// Copyright 2017-2019 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

use super::*;
use self::error::Error;

use assert_matches::assert_matches;
use consensus::BlockOrigin;
use primitives::storage::well_known_keys;
use sr_io::blake2_256;
use test_client::{self, runtime, AccountKeyring, TestClient, BlockBuilderExt, LocalExecutor, TestClientBuilder};
use substrate_executor::NativeExecutionDispatch;

#[test]
fn should_return_storage() {
	let core = tokio::runtime::Runtime::new().unwrap();
	let client = Arc::new(test_client::new());
	let genesis_hash = client.genesis_hash();
	let client = State::new(client, Subscriptions::new(core.executor()));
	let key = StorageKey(b":code".to_vec());

	assert_eq!(
		client.storage(key.clone(), Some(genesis_hash).into())
			.map(|x| x.map(|x| x.0.len())).unwrap().unwrap() as usize,
		LocalExecutor::native_equivalent().len(),
	);
	assert_matches!(
		client.storage_hash(key.clone(), Some(genesis_hash).into()).map(|x| x.is_some()),
		Ok(true)
	);
	assert_eq!(
		client.storage_size(key.clone(), None).unwrap().unwrap() as usize,
		LocalExecutor::native_equivalent().len(),
	);
}

#[test]
fn should_return_child_storage() {
	let core = tokio::runtime::Runtime::new().unwrap();
	let client = Arc::new(test_client::new());
	let genesis_hash = client.genesis_hash();
	let client = State::new(client, Subscriptions::new(core.executor()));
	let child_key = StorageKey(well_known_keys::CHILD_STORAGE_KEY_PREFIX.iter().chain(b"test").cloned().collect());
	let key = StorageKey(b"key".to_vec());


	assert_matches!(
		client.child_storage(child_key.clone(), key.clone(), Some(genesis_hash).into()),
		Ok(Some(StorageData(ref d))) if d[0] == 42 && d.len() == 1
	);
	assert_matches!(
		client.child_storage_hash(child_key.clone(), key.clone(), Some(genesis_hash).into())
			.map(|x| x.is_some()),
		Ok(true)
	);
	assert_matches!(
		client.child_storage_size(child_key.clone(), key.clone(), None),
		Ok(Some(1))
	);
}

#[test]
fn should_call_contract() {
	let core = tokio::runtime::Runtime::new().unwrap();
	let client = Arc::new(test_client::new());
	let genesis_hash = client.genesis_hash();
	let client = State::new(client, Subscriptions::new(core.executor()));

	assert_matches!(
		client.call("balanceOf".into(), Bytes(vec![1,2,3]), Some(genesis_hash).into()),
		Err(Error::Client(client::error::Error::Execution(_)))
	)
}

#[test]
fn should_notify_about_storage_changes() {
	let mut core = tokio::runtime::Runtime::new().unwrap();
	let remote = core.executor();
	let (subscriber, id, transport) = Subscriber::new_test("test");

	{
		let api = State::new(Arc::new(test_client::new()), Subscriptions::new(remote));

		api.subscribe_storage(Default::default(), subscriber, None.into());

		// assert id assigned
		assert_eq!(core.block_on(id), Ok(Ok(SubscriptionId::Number(1))));

		let mut builder = api.client.new_block(Default::default()).unwrap();
		builder.push_transfer(runtime::Transfer {
			from: AccountKeyring::Alice.into(),
			to: AccountKeyring::Ferdie.into(),
			amount: 42,
			nonce: 0,
		}).unwrap();
		api.client.import(BlockOrigin::Own, builder.bake().unwrap()).unwrap();
	}

	// assert notification sent to transport
	let (notification, next) = core.block_on(transport.into_future()).unwrap();
	assert!(notification.is_some());
	// no more notifications on this channel
	assert_eq!(core.block_on(next.into_future()).unwrap().0, None);
}

#[test]
fn should_send_initial_storage_changes_and_notifications() {
	let mut core = tokio::runtime::Runtime::new().unwrap();
	let remote = core.executor();
	let (subscriber, id, transport) = Subscriber::new_test("test");

	{
		let api = State::new(Arc::new(test_client::new()), Subscriptions::new(remote));

		let alice_balance_key = blake2_256(&test_runtime::system::balance_of_key(AccountKeyring::Alice.into()));

		api.subscribe_storage(Default::default(), subscriber, Some(vec![
			StorageKey(alice_balance_key.to_vec()),
		]).into());

		// assert id assigned
		assert_eq!(core.block_on(id), Ok(Ok(SubscriptionId::Number(1))));

		let mut builder = api.client.new_block(Default::default()).unwrap();
		builder.push_transfer(runtime::Transfer {
			from: AccountKeyring::Alice.into(),
			to: AccountKeyring::Ferdie.into(),
			amount: 42,
			nonce: 0,
		}).unwrap();
		api.client.import(BlockOrigin::Own, builder.bake().unwrap()).unwrap();
	}

	// assert initial values sent to transport
	let (notification, next) = core.block_on(transport.into_future()).unwrap();
	assert!(notification.is_some());
	// assert notification sent to transport
	let (notification, next) = core.block_on(next.into_future()).unwrap();
	assert!(notification.is_some());
	// no more notifications on this channel
	assert_eq!(core.block_on(next.into_future()).unwrap().0, None);
}

#[test]
fn should_query_storage() {
	type TestClient = test_client::client::Client<
		test_client::Backend,
		test_client::Executor,
		runtime::Block,
		runtime::RuntimeApi
	>;

	fn run_tests(client: Arc<TestClient>) {
		let core = tokio::runtime::Runtime::new().unwrap();
		let api = State::new(client.clone(), Subscriptions::new(core.executor()));

		let add_block = |nonce| {
			let mut builder = client.new_block(Default::default()).unwrap();
			builder.push_transfer(runtime::Transfer {
				from: AccountKeyring::Alice.into(),
				to: AccountKeyring::Ferdie.into(),
				amount: 42,
				nonce,
			}).unwrap();
			let block = builder.bake().unwrap();
			let hash = block.header.hash();
			client.import(BlockOrigin::Own, block).unwrap();
			hash
		};
		let block1_hash = add_block(0);
		let block2_hash = add_block(1);
		let genesis_hash = client.genesis_hash();

		let alice_balance_key = blake2_256(&test_runtime::system::balance_of_key(AccountKeyring::Alice.into()));

		let mut expected = vec![
			StorageChangeSet {
				block: genesis_hash,
				changes: vec![
					(
						StorageKey(alice_balance_key.to_vec()),
						Some(StorageData(vec![232, 3, 0, 0, 0, 0, 0, 0]))
					),
				],
			},
			StorageChangeSet {
				block: block1_hash,
				changes: vec![
					(
						StorageKey(alice_balance_key.to_vec()),
						Some(StorageData(vec![190, 3, 0, 0, 0, 0, 0, 0]))
					),
				],
			},
		];

		// Query changes only up to block1
		let result = api.query_storage(
			vec![StorageKey(alice_balance_key.to_vec())],
			genesis_hash,
			Some(block1_hash).into(),
		);

		assert_eq!(result.unwrap(), expected);

		// Query all changes
		let result = api.query_storage(
			vec![StorageKey(alice_balance_key.to_vec())],
			genesis_hash,
			None.into(),
		);

		expected.push(StorageChangeSet {
			block: block2_hash,
			changes: vec![
				(
					StorageKey(alice_balance_key.to_vec()),
					Some(StorageData(vec![148, 3, 0, 0, 0, 0, 0, 0]))
				),
			],
		});
		assert_eq!(result.unwrap(), expected);
	}

	run_tests(Arc::new(test_client::new()));
	run_tests(Arc::new(TestClientBuilder::new().set_support_changes_trie(true).build()));
}

#[test]
fn should_split_ranges() {
	assert_eq!(split_range(1, None), (0..1, None));
	assert_eq!(split_range(100, None), (0..100, None));
	assert_eq!(split_range(1, Some(0)), (0..1, None));
	assert_eq!(split_range(100, Some(50)), (0..50, Some(50..100)));
	assert_eq!(split_range(100, Some(99)), (0..99, Some(99..100)));
}


#[test]
fn should_return_runtime_version() {
	let core = tokio::runtime::Runtime::new().unwrap();

	let client = Arc::new(test_client::new());
	let api = State::new(client.clone(), Subscriptions::new(core.executor()));

	assert_eq!(
		serde_json::to_string(&api.runtime_version(None.into()).unwrap()).unwrap(),
		r#"{"specName":"test","implName":"parity-test","authoringVersion":1,"specVersion":1,"implVersion":1,"apis":[["0xdf6acb689907609b",2],["0x37e397fc7c91f5e4",1],["0xd2bc9897eed08f15",1],["0x40fe3ad401f8959a",3],["0xc6e9a76309f39b09",1],["0xdd718d5cc53262d4",1],["0xcbca25e39f142387",1],["0xf78b278be53f454c",1],["0x7801759919ee83e5",1]]}"#
	);
}

#[test]
fn should_notify_on_runtime_version_initially() {
	let mut core = tokio::runtime::Runtime::new().unwrap();
	let (subscriber, id, transport) = Subscriber::new_test("test");

	{
		let client = Arc::new(test_client::new());
		let api = State::new(client.clone(), Subscriptions::new(core.executor()));

		api.subscribe_runtime_version(Default::default(), subscriber);

		// assert id assigned
		assert_eq!(core.block_on(id), Ok(Ok(SubscriptionId::Number(1))));
	}

	// assert initial version sent.
	let (notification, next) = core.block_on(transport.into_future()).unwrap();
	assert!(notification.is_some());
		// no more notifications on this channel
	assert_eq!(core.block_on(next.into_future()).unwrap().0, None);
}

