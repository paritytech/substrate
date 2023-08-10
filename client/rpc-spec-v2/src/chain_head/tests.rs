use crate::chain_head::{
	event::{MethodResponse, StorageQuery, StorageQueryType, StorageResultType},
	test_utils::ChainHeadMockClient,
};

use super::*;
use assert_matches::assert_matches;
use codec::{Decode, Encode};
use futures::Future;
use jsonrpsee::{
	core::{error::Error, server::rpc_module::Subscription as RpcSubscription},
	rpc_params,
	types::{error::CallError, EmptyServerParams as EmptyParams},
	RpcModule,
};
use sc_block_builder::BlockBuilderProvider;
use sc_client_api::ChildInfo;
use sc_service::client::new_in_mem;
use sp_api::BlockT;
use sp_blockchain::HeaderBackend;
use sp_consensus::BlockOrigin;
use sp_core::{
	storage::well_known_keys::{self, CODE},
	testing::TaskExecutor,
	Blake2Hasher, Hasher,
};
use sp_version::RuntimeVersion;
use std::{collections::HashSet, sync::Arc, time::Duration};
use substrate_test_runtime::Transfer;
use substrate_test_runtime_client::{
	prelude::*, runtime, runtime::RuntimeApi, Backend, BlockBuilderExt, Client,
	ClientBlockImportExt, GenesisInit,
};

type Header = substrate_test_runtime_client::runtime::Header;
type Block = substrate_test_runtime_client::runtime::Block;
const MAX_PINNED_BLOCKS: usize = 32;
const MAX_PINNED_SECS: u64 = 60;
const CHAIN_GENESIS: [u8; 32] = [0; 32];
const INVALID_HASH: [u8; 32] = [1; 32];
const KEY: &[u8] = b":mock";
const VALUE: &[u8] = b"hello world";
const CHILD_STORAGE_KEY: &[u8] = b"child";
const CHILD_VALUE: &[u8] = b"child value";

async fn get_next_event<T: serde::de::DeserializeOwned>(sub: &mut RpcSubscription) -> T {
	let (event, _sub_id) = tokio::time::timeout(std::time::Duration::from_secs(60), sub.next())
		.await
		.unwrap()
		.unwrap()
		.unwrap();
	event
}

async fn run_with_timeout<F: Future>(future: F) -> <F as Future>::Output {
	tokio::time::timeout(std::time::Duration::from_secs(60 * 10), future)
		.await
		.unwrap()
}

async fn setup_api() -> (
	Arc<Client<Backend>>,
	RpcModule<ChainHead<Backend, Block, Client<Backend>>>,
	RpcSubscription,
	String,
	Block,
) {
	let child_info = ChildInfo::new_default(CHILD_STORAGE_KEY);
	let builder = TestClientBuilder::new().add_extra_child_storage(
		&child_info,
		KEY.to_vec(),
		CHILD_VALUE.to_vec(),
	);
	let backend = builder.backend();
	let mut client = Arc::new(builder.build());

	let api = ChainHead::new(
		client.clone(),
		backend,
		Arc::new(TaskExecutor::default()),
		CHAIN_GENESIS,
		MAX_PINNED_BLOCKS,
		Duration::from_secs(MAX_PINNED_SECS),
	)
	.into_rpc();

	let mut sub = api.subscribe("chainHead_unstable_follow", [true]).await.unwrap();
	let sub_id = sub.subscription_id();
	let sub_id = serde_json::to_string(&sub_id).unwrap();

	let block = client.new_block(Default::default()).unwrap().build().unwrap().block;
	client.import(BlockOrigin::Own, block.clone()).await.unwrap();

	// Ensure the imported block is propagated and pinned for this subscription.
	assert_matches!(
		get_next_event::<FollowEvent<String>>(&mut sub).await,
		FollowEvent::Initialized(_)
	);
	assert_matches!(
		get_next_event::<FollowEvent<String>>(&mut sub).await,
		FollowEvent::NewBlock(_)
	);
	assert_matches!(
		get_next_event::<FollowEvent<String>>(&mut sub).await,
		FollowEvent::BestBlockChanged(_)
	);

	(client, api, sub, sub_id, block)
}

#[tokio::test]
async fn follow_subscription_produces_blocks() {
	let builder = TestClientBuilder::new();
	let backend = builder.backend();
	let mut client = Arc::new(builder.build());

	let api = ChainHead::new(
		client.clone(),
		backend,
		Arc::new(TaskExecutor::default()),
		CHAIN_GENESIS,
		MAX_PINNED_BLOCKS,
		Duration::from_secs(MAX_PINNED_SECS),
	)
	.into_rpc();

	let finalized_hash = client.info().finalized_hash;
	let mut sub = api.subscribe("chainHead_unstable_follow", [false]).await.unwrap();

	// Initialized must always be reported first.
	let event: FollowEvent<String> = get_next_event(&mut sub).await;
	let expected = FollowEvent::Initialized(Initialized {
		finalized_block_hash: format!("{:?}", finalized_hash),
		finalized_block_runtime: None,
		with_runtime: false,
	});
	assert_eq!(event, expected);

	let block = client.new_block(Default::default()).unwrap().build().unwrap().block;

	let best_hash = block.header.hash();
	client.import(BlockOrigin::Own, block.clone()).await.unwrap();

	let event: FollowEvent<String> = get_next_event(&mut sub).await;
	let expected = FollowEvent::NewBlock(NewBlock {
		block_hash: format!("{:?}", best_hash),
		parent_block_hash: format!("{:?}", finalized_hash),
		new_runtime: None,
		with_runtime: false,
	});
	assert_eq!(event, expected);

	let event: FollowEvent<String> = get_next_event(&mut sub).await;
	let expected = FollowEvent::BestBlockChanged(BestBlockChanged {
		best_block_hash: format!("{:?}", best_hash),
	});
	assert_eq!(event, expected);

	client.finalize_block(best_hash, None).unwrap();

	let event: FollowEvent<String> = get_next_event(&mut sub).await;
	let expected = FollowEvent::Finalized(Finalized {
		finalized_block_hashes: vec![format!("{:?}", best_hash)],
		pruned_block_hashes: vec![],
	});
	assert_eq!(event, expected);
}

#[tokio::test]
async fn follow_with_runtime() {
	let builder = TestClientBuilder::new();
	let backend = builder.backend();
	let mut client = Arc::new(builder.build());

	let api = ChainHead::new(
		client.clone(),
		backend,
		Arc::new(TaskExecutor::default()),
		CHAIN_GENESIS,
		MAX_PINNED_BLOCKS,
		Duration::from_secs(MAX_PINNED_SECS),
	)
	.into_rpc();

	let finalized_hash = client.info().finalized_hash;
	let mut sub = api.subscribe("chainHead_unstable_follow", [true]).await.unwrap();

	// Initialized must always be reported first.
	let event: FollowEvent<String> = get_next_event(&mut sub).await;

	// it is basically json-encoded substrate_test_runtime_client::runtime::VERSION
	let runtime_str = "{\"specName\":\"test\",\"implName\":\"parity-test\",\"authoringVersion\":1,\
		\"specVersion\":2,\"implVersion\":2,\"apis\":[[\"0xdf6acb689907609b\",4],\
		[\"0x37e397fc7c91f5e4\",2],[\"0xd2bc9897eed08f15\",3],[\"0x40fe3ad401f8959a\",6],\
		[\"0xbc9d89904f5b923f\",1],[\"0xc6e9a76309f39b09\",2],[\"0xdd718d5cc53262d4\",1],\
		[\"0xcbca25e39f142387\",2],[\"0xf78b278be53f454c\",2],[\"0xab3c0572291feb8b\",1],\
		[\"0xed99c5acb25eedf5\",3],[\"0xfbc577b9d747efd6\",1]],\"transactionVersion\":1,\"stateVersion\":1}";

	let runtime: RuntimeVersion = serde_json::from_str(runtime_str).unwrap();

	let finalized_block_runtime =
		Some(RuntimeEvent::Valid(RuntimeVersionEvent { spec: runtime.clone() }));
	// Runtime must always be reported with the first event.
	let expected = FollowEvent::Initialized(Initialized {
		finalized_block_hash: format!("{:?}", finalized_hash),
		finalized_block_runtime,
		with_runtime: false,
	});
	pretty_assertions::assert_eq!(event, expected);

	// Import a new block without runtime changes.
	// The runtime field must be None in this case.
	let block = client.new_block(Default::default()).unwrap().build().unwrap().block;
	let best_hash = block.header.hash();
	client.import(BlockOrigin::Own, block.clone()).await.unwrap();

	let event: FollowEvent<String> = get_next_event(&mut sub).await;
	let expected = FollowEvent::NewBlock(NewBlock {
		block_hash: format!("{:?}", best_hash),
		parent_block_hash: format!("{:?}", finalized_hash),
		new_runtime: None,
		with_runtime: false,
	});
	assert_eq!(event, expected);

	let event: FollowEvent<String> = get_next_event(&mut sub).await;
	let expected = FollowEvent::BestBlockChanged(BestBlockChanged {
		best_block_hash: format!("{:?}", best_hash),
	});
	assert_eq!(event, expected);

	client.finalize_block(best_hash, None).unwrap();

	let event: FollowEvent<String> = get_next_event(&mut sub).await;
	let expected = FollowEvent::Finalized(Finalized {
		finalized_block_hashes: vec![format!("{:?}", best_hash)],
		pruned_block_hashes: vec![],
	});
	assert_eq!(event, expected);

	let finalized_hash = best_hash;
	// The `RuntimeVersion` is embedded into the WASM blob at the `runtime_version`
	// section. Modify the `RuntimeVersion` and commit the changes to a new block.
	// The RPC must notify the runtime event change.
	let wasm = sp_maybe_compressed_blob::decompress(
		runtime::wasm_binary_unwrap(),
		sp_maybe_compressed_blob::CODE_BLOB_BOMB_LIMIT,
	)
	.unwrap();
	// Update the runtime spec version.
	let mut runtime = runtime;
	runtime.spec_version += 1;
	let embedded = sp_version::embed::embed_runtime_version(&wasm, runtime.clone()).unwrap();
	let wasm = sp_maybe_compressed_blob::compress(
		&embedded,
		sp_maybe_compressed_blob::CODE_BLOB_BOMB_LIMIT,
	)
	.unwrap();

	let mut builder = client.new_block(Default::default()).unwrap();
	builder.push_storage_change(CODE.to_vec(), Some(wasm)).unwrap();
	let block = builder.build().unwrap().block;
	let best_hash = block.header.hash();
	client.import(BlockOrigin::Own, block.clone()).await.unwrap();

	let new_runtime = Some(RuntimeEvent::Valid(RuntimeVersionEvent { spec: runtime.clone() }));
	let event: FollowEvent<String> = get_next_event(&mut sub).await;
	let expected = FollowEvent::NewBlock(NewBlock {
		block_hash: format!("{:?}", best_hash),
		parent_block_hash: format!("{:?}", finalized_hash),
		new_runtime,
		with_runtime: false,
	});
	assert_eq!(event, expected);
}

#[tokio::test]
async fn get_genesis() {
	let builder = TestClientBuilder::new();
	let backend = builder.backend();
	let client = Arc::new(builder.build());

	let api = ChainHead::new(
		client.clone(),
		backend,
		Arc::new(TaskExecutor::default()),
		CHAIN_GENESIS,
		MAX_PINNED_BLOCKS,
		Duration::from_secs(MAX_PINNED_SECS),
	)
	.into_rpc();

	let genesis: String =
		api.call("chainHead_unstable_genesisHash", EmptyParams::new()).await.unwrap();
	assert_eq!(genesis, hex_string(&CHAIN_GENESIS));
}

#[tokio::test]
async fn get_header() {
	let (_client, api, _sub, sub_id, block) = setup_api().await;
	let block_hash = format!("{:?}", block.header.hash());
	let invalid_hash = hex_string(&INVALID_HASH);

	// Invalid subscription ID must produce no results.
	let res: Option<String> = api
		.call("chainHead_unstable_header", ["invalid_sub_id", &invalid_hash])
		.await
		.unwrap();
	assert!(res.is_none());

	// Valid subscription with invalid block hash will error.
	let err = api
		.call::<_, serde_json::Value>("chainHead_unstable_header", [&sub_id, &invalid_hash])
		.await
		.unwrap_err();
	assert_matches!(err,
		Error::Call(CallError::Custom(ref err)) if err.code() == 2001 && err.message() == "Invalid block hash"
	);

	// Obtain the valid header.
	let res: String = api.call("chainHead_unstable_header", [&sub_id, &block_hash]).await.unwrap();
	let bytes = array_bytes::hex2bytes(&res).unwrap();
	let header: Header = Decode::decode(&mut &bytes[..]).unwrap();
	assert_eq!(header, block.header);
}

#[tokio::test]
async fn get_body() {
	let (mut client, api, mut block_sub, sub_id, block) = setup_api().await;
	let block_hash = format!("{:?}", block.header.hash());
	let invalid_hash = hex_string(&INVALID_HASH);

	// Subscription ID is invalid.
	let response: MethodResponse = api
		.call("chainHead_unstable_body", ["invalid_sub_id", &invalid_hash])
		.await
		.unwrap();
	assert_matches!(response, MethodResponse::LimitReached);

	// Block hash is invalid.
	let err = api
		.call::<_, serde_json::Value>("chainHead_unstable_body", [&sub_id, &invalid_hash])
		.await
		.unwrap_err();
	assert_matches!(err,
		Error::Call(CallError::Custom(ref err)) if err.code() == 2001 && err.message() == "Invalid block hash"
	);

	// Valid call.
	let response: MethodResponse =
		api.call("chainHead_unstable_body", [&sub_id, &block_hash]).await.unwrap();
	let operation_id = match response {
		MethodResponse::Started(started) => started.operation_id,
		MethodResponse::LimitReached => panic!("Expected started response"),
	};

	// Response propagated to `chainHead_follow`.
	assert_matches!(
			get_next_event::<FollowEvent<String>>(&mut block_sub).await,
			FollowEvent::OperationBodyDone(done) if done.operation_id == operation_id && done.value.is_empty()
	);

	// Import a block with extrinsics.
	let mut builder = client.new_block(Default::default()).unwrap();
	builder
		.push_transfer(runtime::Transfer {
			from: AccountKeyring::Alice.into(),
			to: AccountKeyring::Ferdie.into(),
			amount: 42,
			nonce: 0,
		})
		.unwrap();
	let block = builder.build().unwrap().block;
	let block_hash = format!("{:?}", block.header.hash());
	client.import(BlockOrigin::Own, block.clone()).await.unwrap();
	// Ensure the imported block is propagated and pinned for this subscription.
	assert_matches!(
		get_next_event::<FollowEvent<String>>(&mut block_sub).await,
		FollowEvent::NewBlock(_)
	);
	assert_matches!(
		get_next_event::<FollowEvent<String>>(&mut block_sub).await,
		FollowEvent::BestBlockChanged(_)
	);

	// Valid call to a block with extrinsics.
	let response: MethodResponse =
		api.call("chainHead_unstable_body", [&sub_id, &block_hash]).await.unwrap();
	let operation_id = match response {
		MethodResponse::Started(started) => started.operation_id,
		MethodResponse::LimitReached => panic!("Expected started response"),
	};

	// Response propagated to `chainHead_follow`.
	let expected_tx = hex_string(&block.extrinsics[0].encode());
	assert_matches!(
			get_next_event::<FollowEvent<String>>(&mut block_sub).await,
			FollowEvent::OperationBodyDone(done) if done.operation_id == operation_id && done.value == vec![expected_tx]
	);
}

#[tokio::test]
async fn call_runtime() {
	let (_client, api, mut block_sub, sub_id, block) = setup_api().await;
	let block_hash = format!("{:?}", block.header.hash());
	let invalid_hash = hex_string(&INVALID_HASH);

	// Subscription ID is invalid.
	let response: MethodResponse = api
		.call(
			"chainHead_unstable_call",
			["invalid_sub_id", &block_hash, "BabeApi_current_epoch", "0x00"],
		)
		.await
		.unwrap();
	assert_matches!(response, MethodResponse::LimitReached);

	// Block hash is invalid.
	let err = api
		.call::<_, serde_json::Value>(
			"chainHead_unstable_call",
			[&sub_id, &invalid_hash, "BabeApi_current_epoch", "0x00"],
		)
		.await
		.unwrap_err();
	assert_matches!(err,
		Error::Call(CallError::Custom(ref err)) if err.code() == 2001 && err.message() == "Invalid block hash"
	);

	// Pass an invalid parameters that cannot be decode.
	let err = api
		.call::<_, serde_json::Value>(
			"chainHead_unstable_call",
			// 0x0 is invalid.
			[&sub_id, &block_hash, "BabeApi_current_epoch", "0x0"],
		)
		.await
		.unwrap_err();
	assert_matches!(err,
		Error::Call(CallError::Custom(ref err)) if err.code() == 2003 && err.message().contains("Invalid parameter")
	);

	// Valid call.
	let alice_id = AccountKeyring::Alice.to_account_id();
	// Hex encoded scale encoded bytes representing the call parameters.
	let call_parameters = hex_string(&alice_id.encode());
	let response: MethodResponse = api
		.call(
			"chainHead_unstable_call",
			[&sub_id, &block_hash, "AccountNonceApi_account_nonce", &call_parameters],
		)
		.await
		.unwrap();
	let operation_id = match response {
		MethodResponse::Started(started) => started.operation_id,
		MethodResponse::LimitReached => panic!("Expected started response"),
	};

	// Response propagated to `chainHead_follow`.
	assert_matches!(
			get_next_event::<FollowEvent<String>>(&mut block_sub).await,
			FollowEvent::OperationCallDone(done) if done.operation_id == operation_id && done.output == "0x0000000000000000"
	);

	// The `current_epoch` takes no parameters and not draining the input buffer
	// will cause the execution to fail.
	let response: MethodResponse = api
		.call("chainHead_unstable_call", [&sub_id, &block_hash, "BabeApi_current_epoch", "0x00"])
		.await
		.unwrap();
	let operation_id = match response {
		MethodResponse::Started(started) => started.operation_id,
		MethodResponse::LimitReached => panic!("Expected started response"),
	};

	// Error propagated to `chainHead_follow`.
	assert_matches!(
			get_next_event::<FollowEvent<String>>(&mut block_sub).await,
			FollowEvent::OperationError(error) if error.operation_id == operation_id && error.error.contains("Execution failed")
	);
}

#[tokio::test]
async fn call_runtime_without_flag() {
	let builder = TestClientBuilder::new();
	let backend = builder.backend();
	let mut client = Arc::new(builder.build());

	let api = ChainHead::new(
		client.clone(),
		backend,
		Arc::new(TaskExecutor::default()),
		CHAIN_GENESIS,
		MAX_PINNED_BLOCKS,
		Duration::from_secs(MAX_PINNED_SECS),
	)
	.into_rpc();

	let mut sub = api.subscribe("chainHead_unstable_follow", [false]).await.unwrap();
	let sub_id = sub.subscription_id();
	let sub_id = serde_json::to_string(&sub_id).unwrap();

	let block = client.new_block(Default::default()).unwrap().build().unwrap().block;
	let block_hash = format!("{:?}", block.header.hash());
	client.import(BlockOrigin::Own, block.clone()).await.unwrap();

	// Ensure the imported block is propagated and pinned for this subscription.
	assert_matches!(
		get_next_event::<FollowEvent<String>>(&mut sub).await,
		FollowEvent::Initialized(_)
	);
	assert_matches!(
		get_next_event::<FollowEvent<String>>(&mut sub).await,
		FollowEvent::NewBlock(_)
	);
	assert_matches!(
		get_next_event::<FollowEvent<String>>(&mut sub).await,
		FollowEvent::BestBlockChanged(_)
	);

	// Valid runtime call on a subscription started with `with_runtime` false.
	let alice_id = AccountKeyring::Alice.to_account_id();
	let call_parameters = hex_string(&alice_id.encode());
	let err = api
		.call::<_, serde_json::Value>(
			"chainHead_unstable_call",
			[&sub_id, &block_hash, "AccountNonceApi_account_nonce", &call_parameters],
		)
		.await
		.unwrap_err();

	assert_matches!(err,
		Error::Call(CallError::Custom(ref err)) if err.code() == 2003 && err.message().contains("The runtime updates flag must be set")
	);
}

#[tokio::test]
async fn get_storage_hash() {
	let (mut client, api, mut block_sub, sub_id, block) = setup_api().await;
	let block_hash = format!("{:?}", block.header.hash());
	let invalid_hash = hex_string(&INVALID_HASH);
	let key = hex_string(&KEY);

	// Subscription ID is invalid.
	let response: MethodResponse = api
		.call(
			"chainHead_unstable_storage",
			rpc_params![
				"invalid_sub_id",
				&invalid_hash,
				vec![StorageQuery { key: key.clone(), query_type: StorageQueryType::Hash }]
			],
		)
		.await
		.unwrap();
	assert_matches!(response, MethodResponse::LimitReached);

	// Block hash is invalid.
	let err = api
		.call::<_, serde_json::Value>(
			"chainHead_unstable_storage",
			rpc_params![
				&sub_id,
				&invalid_hash,
				vec![StorageQuery { key: key.clone(), query_type: StorageQueryType::Hash }]
			],
		)
		.await
		.unwrap_err();
	assert_matches!(err,
		Error::Call(CallError::Custom(ref err)) if err.code() == 2001 && err.message() == "Invalid block hash"
	);

	// Valid call without storage at the key.
	let response: MethodResponse = api
		.call(
			"chainHead_unstable_storage",
			rpc_params![
				&sub_id,
				&block_hash,
				vec![StorageQuery { key: key.clone(), query_type: StorageQueryType::Hash }]
			],
		)
		.await
		.unwrap();
	let operation_id = match response {
		MethodResponse::Started(started) => started.operation_id,
		MethodResponse::LimitReached => panic!("Expected started response"),
	};
	// The `Done` event is generated directly since the key does not have any value associated.
	assert_matches!(
			get_next_event::<FollowEvent<String>>(&mut block_sub).await,
			FollowEvent::OperationStorageDone(done) if done.operation_id == operation_id
	);

	// Import a new block with storage changes.
	let mut builder = client.new_block(Default::default()).unwrap();
	builder.push_storage_change(KEY.to_vec(), Some(VALUE.to_vec())).unwrap();
	let block = builder.build().unwrap().block;
	let block_hash = format!("{:?}", block.header.hash());
	client.import(BlockOrigin::Own, block.clone()).await.unwrap();

	// Ensure the imported block is propagated and pinned for this subscription.
	assert_matches!(
		get_next_event::<FollowEvent<String>>(&mut block_sub).await,
		FollowEvent::NewBlock(_)
	);
	assert_matches!(
		get_next_event::<FollowEvent<String>>(&mut block_sub).await,
		FollowEvent::BestBlockChanged(_)
	);

	// Valid call with storage at the key.
	let response: MethodResponse = api
		.call(
			"chainHead_unstable_storage",
			rpc_params![
				&sub_id,
				&block_hash,
				vec![StorageQuery { key: key.clone(), query_type: StorageQueryType::Hash }]
			],
		)
		.await
		.unwrap();
	let operation_id = match response {
		MethodResponse::Started(started) => started.operation_id,
		MethodResponse::LimitReached => panic!("Expected started response"),
	};

	let expected_hash = format!("{:?}", Blake2Hasher::hash(&VALUE));
	assert_matches!(
			get_next_event::<FollowEvent<String>>(&mut block_sub).await,
			FollowEvent::OperationStorageItems(res) if res.operation_id == operation_id &&
				res.items.len() == 1 &&
				res.items[0].key == key && res.items[0].result == StorageResultType::Hash(expected_hash)
	);
	assert_matches!(
			get_next_event::<FollowEvent<String>>(&mut block_sub).await,
			FollowEvent::OperationStorageDone(done) if done.operation_id == operation_id
	);

	// Child value set in `setup_api`.
	let child_info = hex_string(&CHILD_STORAGE_KEY);
	let genesis_hash = format!("{:?}", client.genesis_hash());

	// Valid call with storage at the key.
	let response: MethodResponse = api
		.call(
			"chainHead_unstable_storage",
			rpc_params![
				&sub_id,
				&genesis_hash,
				vec![StorageQuery { key: key.clone(), query_type: StorageQueryType::Hash }],
				&child_info
			],
		)
		.await
		.unwrap();
	let operation_id = match response {
		MethodResponse::Started(started) => started.operation_id,
		MethodResponse::LimitReached => panic!("Expected started response"),
	};

	let expected_hash = format!("{:?}", Blake2Hasher::hash(&CHILD_VALUE));
	assert_matches!(
			get_next_event::<FollowEvent<String>>(&mut block_sub).await,
			FollowEvent::OperationStorageItems(res) if res.operation_id == operation_id &&
				res.items.len() == 1 &&
				res.items[0].key == key && res.items[0].result == StorageResultType::Hash(expected_hash)
	);
	assert_matches!(
			get_next_event::<FollowEvent<String>>(&mut block_sub).await,
			FollowEvent::OperationStorageDone(done) if done.operation_id == operation_id
	);
}

#[tokio::test]
async fn get_storage_multi_query_iter() {
	let (mut client, api, mut block_sub, sub_id, _) = setup_api().await;
	let key = hex_string(&KEY);

	// Import a new block with storage changes.
	let mut builder = client.new_block(Default::default()).unwrap();
	builder.push_storage_change(KEY.to_vec(), Some(VALUE.to_vec())).unwrap();
	let block = builder.build().unwrap().block;
	let block_hash = format!("{:?}", block.header.hash());
	client.import(BlockOrigin::Own, block.clone()).await.unwrap();

	// Ensure the imported block is propagated and pinned for this subscription.
	assert_matches!(
		get_next_event::<FollowEvent<String>>(&mut block_sub).await,
		FollowEvent::NewBlock(_)
	);
	assert_matches!(
		get_next_event::<FollowEvent<String>>(&mut block_sub).await,
		FollowEvent::BestBlockChanged(_)
	);

	// Valid call with storage at the key.
	let response: MethodResponse = api
		.call(
			"chainHead_unstable_storage",
			rpc_params![
				&sub_id,
				&block_hash,
				vec![
					StorageQuery {
						key: key.clone(),
						query_type: StorageQueryType::DescendantsHashes
					},
					StorageQuery {
						key: key.clone(),
						query_type: StorageQueryType::DescendantsValues
					}
				]
			],
		)
		.await
		.unwrap();
	let operation_id = match response {
		MethodResponse::Started(started) => started.operation_id,
		MethodResponse::LimitReached => panic!("Expected started response"),
	};

	let expected_hash = format!("{:?}", Blake2Hasher::hash(&VALUE));
	let expected_value = hex_string(&VALUE);
	assert_matches!(
		get_next_event::<FollowEvent<String>>(&mut block_sub).await,
		FollowEvent::OperationStorageItems(res) if res.operation_id == operation_id &&
			res.items.len() == 2 &&
			res.items[0].key == key &&
			res.items[1].key == key &&
			res.items[0].result == StorageResultType::Hash(expected_hash) &&
			res.items[1].result == StorageResultType::Value(expected_value)
	);
	assert_matches!(
			get_next_event::<FollowEvent<String>>(&mut block_sub).await,
			FollowEvent::OperationStorageDone(done) if done.operation_id == operation_id
	);

	// Child value set in `setup_api`.
	let child_info = hex_string(&CHILD_STORAGE_KEY);
	let genesis_hash = format!("{:?}", client.genesis_hash());
	let expected_hash = format!("{:?}", Blake2Hasher::hash(&CHILD_VALUE));
	let expected_value = hex_string(&CHILD_VALUE);
	let response: MethodResponse = api
		.call(
			"chainHead_unstable_storage",
			rpc_params![
				&sub_id,
				&genesis_hash,
				vec![
					StorageQuery {
						key: key.clone(),
						query_type: StorageQueryType::DescendantsHashes
					},
					StorageQuery {
						key: key.clone(),
						query_type: StorageQueryType::DescendantsValues
					}
				],
				&child_info
			],
		)
		.await
		.unwrap();
	let operation_id = match response {
		MethodResponse::Started(started) => started.operation_id,
		MethodResponse::LimitReached => panic!("Expected started response"),
	};

	assert_matches!(
		get_next_event::<FollowEvent<String>>(&mut block_sub).await,
		FollowEvent::OperationStorageItems(res) if res.operation_id == operation_id &&
			res.items.len() == 2 &&
			res.items[0].key == key &&
			res.items[1].key == key &&
			res.items[0].result == StorageResultType::Hash(expected_hash) &&
			res.items[1].result == StorageResultType::Value(expected_value)
	);
	assert_matches!(
			get_next_event::<FollowEvent<String>>(&mut block_sub).await,
			FollowEvent::OperationStorageDone(done) if done.operation_id == operation_id
	);
}

#[tokio::test]
async fn get_storage_value() {
	let (mut client, api, mut block_sub, sub_id, block) = setup_api().await;
	let block_hash = format!("{:?}", block.header.hash());
	let invalid_hash = hex_string(&INVALID_HASH);
	let key = hex_string(&KEY);

	// Subscription ID is invalid.
	let response: MethodResponse = api
		.call(
			"chainHead_unstable_storage",
			rpc_params![
				"invalid_sub_id",
				&invalid_hash,
				vec![StorageQuery { key: key.clone(), query_type: StorageQueryType::Value }]
			],
		)
		.await
		.unwrap();
	assert_matches!(response, MethodResponse::LimitReached);

	// Block hash is invalid.
	let err = api
		.call::<_, serde_json::Value>(
			"chainHead_unstable_storage",
			rpc_params![
				&sub_id,
				&invalid_hash,
				vec![StorageQuery { key: key.clone(), query_type: StorageQueryType::Value }]
			],
		)
		.await
		.unwrap_err();
	assert_matches!(err,
		Error::Call(CallError::Custom(ref err)) if err.code() == 2001 && err.message() == "Invalid block hash"
	);

	// Valid call without storage at the key.
	let response: MethodResponse = api
		.call(
			"chainHead_unstable_storage",
			rpc_params![
				&sub_id,
				&block_hash,
				vec![StorageQuery { key: key.clone(), query_type: StorageQueryType::Value }]
			],
		)
		.await
		.unwrap();
	let operation_id = match response {
		MethodResponse::Started(started) => started.operation_id,
		MethodResponse::LimitReached => panic!("Expected started response"),
	};
	// The `Done` event is generated directly since the key does not have any value associated.
	assert_matches!(
			get_next_event::<FollowEvent<String>>(&mut block_sub).await,
			FollowEvent::OperationStorageDone(done) if done.operation_id == operation_id
	);

	// Import a new block with storage changes.
	let mut builder = client.new_block(Default::default()).unwrap();
	builder.push_storage_change(KEY.to_vec(), Some(VALUE.to_vec())).unwrap();
	let block = builder.build().unwrap().block;
	let block_hash = format!("{:?}", block.header.hash());
	client.import(BlockOrigin::Own, block.clone()).await.unwrap();

	// Ensure the imported block is propagated and pinned for this subscription.
	assert_matches!(
		get_next_event::<FollowEvent<String>>(&mut block_sub).await,
		FollowEvent::NewBlock(_)
	);
	assert_matches!(
		get_next_event::<FollowEvent<String>>(&mut block_sub).await,
		FollowEvent::BestBlockChanged(_)
	);

	// Valid call with storage at the key.
	let response: MethodResponse = api
		.call(
			"chainHead_unstable_storage",
			rpc_params![
				&sub_id,
				&block_hash,
				vec![StorageQuery { key: key.clone(), query_type: StorageQueryType::Value }]
			],
		)
		.await
		.unwrap();
	let operation_id = match response {
		MethodResponse::Started(started) => started.operation_id,
		MethodResponse::LimitReached => panic!("Expected started response"),
	};

	let expected_value = hex_string(&VALUE);
	assert_matches!(
			get_next_event::<FollowEvent<String>>(&mut block_sub).await,
			FollowEvent::OperationStorageItems(res) if res.operation_id == operation_id &&
				res.items.len() == 1 &&
				res.items[0].key == key && res.items[0].result == StorageResultType::Value(expected_value)
	);
	assert_matches!(
			get_next_event::<FollowEvent<String>>(&mut block_sub).await,
			FollowEvent::OperationStorageDone(done) if done.operation_id == operation_id
	);

	// Child value set in `setup_api`.
	let child_info = hex_string(&CHILD_STORAGE_KEY);
	let genesis_hash = format!("{:?}", client.genesis_hash());

	let response: MethodResponse = api
		.call(
			"chainHead_unstable_storage",
			rpc_params![
				&sub_id,
				&genesis_hash,
				vec![StorageQuery { key: key.clone(), query_type: StorageQueryType::Value }],
				&child_info
			],
		)
		.await
		.unwrap();
	let operation_id = match response {
		MethodResponse::Started(started) => started.operation_id,
		MethodResponse::LimitReached => panic!("Expected started response"),
	};

	let expected_value = hex_string(&CHILD_VALUE);

	assert_matches!(
			get_next_event::<FollowEvent<String>>(&mut block_sub).await,
			FollowEvent::OperationStorageItems(res) if res.operation_id == operation_id &&
				res.items.len() == 1 &&
				res.items[0].key == key && res.items[0].result == StorageResultType::Value(expected_value)
	);
	assert_matches!(
			get_next_event::<FollowEvent<String>>(&mut block_sub).await,
			FollowEvent::OperationStorageDone(done) if done.operation_id == operation_id
	);
}

#[tokio::test]
async fn get_storage_non_queryable_key() {
	let (mut _client, api, mut block_sub, sub_id, block) = setup_api().await;
	let block_hash = format!("{:?}", block.header.hash());
	let key = hex_string(&KEY);

	// Key is prefixed by CHILD_STORAGE_KEY_PREFIX.
	let mut prefixed_key = well_known_keys::CHILD_STORAGE_KEY_PREFIX.to_vec();
	prefixed_key.extend_from_slice(&KEY);
	let prefixed_key = hex_string(&prefixed_key);

	let response: MethodResponse = api
		.call(
			"chainHead_unstable_storage",
			rpc_params![
				&sub_id,
				&block_hash,
				vec![StorageQuery { key: prefixed_key, query_type: StorageQueryType::Value }]
			],
		)
		.await
		.unwrap();
	let operation_id = match response {
		MethodResponse::Started(started) => started.operation_id,
		MethodResponse::LimitReached => panic!("Expected started response"),
	};
	// The `Done` event is generated directly since the key is not queryable.
	assert_matches!(
			get_next_event::<FollowEvent<String>>(&mut block_sub).await,
			FollowEvent::OperationStorageDone(done) if done.operation_id == operation_id
	);

	// Key is prefixed by DEFAULT_CHILD_STORAGE_KEY_PREFIX.
	let mut prefixed_key = well_known_keys::DEFAULT_CHILD_STORAGE_KEY_PREFIX.to_vec();
	prefixed_key.extend_from_slice(&KEY);
	let prefixed_key = hex_string(&prefixed_key);
	let response: MethodResponse = api
		.call(
			"chainHead_unstable_storage",
			rpc_params![
				&sub_id,
				&block_hash,
				vec![StorageQuery { key: prefixed_key, query_type: StorageQueryType::Value }]
			],
		)
		.await
		.unwrap();
	let operation_id = match response {
		MethodResponse::Started(started) => started.operation_id,
		MethodResponse::LimitReached => panic!("Expected started response"),
	};
	// The `Done` event is generated directly since the key is not queryable.
	assert_matches!(
			get_next_event::<FollowEvent<String>>(&mut block_sub).await,
			FollowEvent::OperationStorageDone(done) if done.operation_id == operation_id
	);

	// Child key is prefixed by CHILD_STORAGE_KEY_PREFIX.
	let mut prefixed_key = well_known_keys::CHILD_STORAGE_KEY_PREFIX.to_vec();
	prefixed_key.extend_from_slice(CHILD_STORAGE_KEY);
	let prefixed_key = hex_string(&prefixed_key);
	let response: MethodResponse = api
		.call(
			"chainHead_unstable_storage",
			rpc_params![
				&sub_id,
				&block_hash,
				vec![StorageQuery { key: key.clone(), query_type: StorageQueryType::Value }],
				&prefixed_key
			],
		)
		.await
		.unwrap();
	let operation_id = match response {
		MethodResponse::Started(started) => started.operation_id,
		MethodResponse::LimitReached => panic!("Expected started response"),
	};
	// The `Done` event is generated directly since the key is not queryable.
	assert_matches!(
			get_next_event::<FollowEvent<String>>(&mut block_sub).await,
			FollowEvent::OperationStorageDone(done) if done.operation_id == operation_id
	);

	// Child key is prefixed by DEFAULT_CHILD_STORAGE_KEY_PREFIX.
	let mut prefixed_key = well_known_keys::DEFAULT_CHILD_STORAGE_KEY_PREFIX.to_vec();
	prefixed_key.extend_from_slice(CHILD_STORAGE_KEY);
	let prefixed_key = hex_string(&prefixed_key);
	let response: MethodResponse = api
		.call(
			"chainHead_unstable_storage",
			rpc_params![
				&sub_id,
				&block_hash,
				vec![StorageQuery { key, query_type: StorageQueryType::Value }],
				&prefixed_key
			],
		)
		.await
		.unwrap();
	let operation_id = match response {
		MethodResponse::Started(started) => started.operation_id,
		MethodResponse::LimitReached => panic!("Expected started response"),
	};
	// The `Done` event is generated directly since the key is not queryable.
	assert_matches!(
			get_next_event::<FollowEvent<String>>(&mut block_sub).await,
			FollowEvent::OperationStorageDone(done) if done.operation_id == operation_id
	);
}

#[tokio::test]
async fn unique_operation_ids() {
	let (mut _client, api, mut block_sub, sub_id, block) = setup_api().await;
	let block_hash = format!("{:?}", block.header.hash());

	let mut op_ids = HashSet::new();

	// Ensure that operation IDs are unique for multiple method calls.
	for _ in 0..5 {
		// Valid `chainHead_unstable_body` call.
		let response: MethodResponse =
			api.call("chainHead_unstable_body", [&sub_id, &block_hash]).await.unwrap();
		let operation_id = match response {
			MethodResponse::Started(started) => started.operation_id,
			MethodResponse::LimitReached => panic!("Expected started response"),
		};
		assert_matches!(
				get_next_event::<FollowEvent<String>>(&mut block_sub).await,
				FollowEvent::OperationBodyDone(done) if done.operation_id == operation_id && done.value.is_empty()
		);
		// Ensure uniqueness.
		assert!(op_ids.insert(operation_id));

		// Valid `chainHead_unstable_storage` call.
		let key = hex_string(&KEY);
		let response: MethodResponse = api
			.call(
				"chainHead_unstable_storage",
				rpc_params![
					&sub_id,
					&block_hash,
					vec![StorageQuery { key: key.clone(), query_type: StorageQueryType::Value }]
				],
			)
			.await
			.unwrap();
		let operation_id = match response {
			MethodResponse::Started(started) => started.operation_id,
			MethodResponse::LimitReached => panic!("Expected started response"),
		};
		// The `Done` event is generated directly since the key does not have any value associated.
		assert_matches!(
				get_next_event::<FollowEvent<String>>(&mut block_sub).await,
				FollowEvent::OperationStorageDone(done) if done.operation_id == operation_id
		);
		// Ensure uniqueness.
		assert!(op_ids.insert(operation_id));

		// Valid `chainHead_unstable_call` call.
		let alice_id = AccountKeyring::Alice.to_account_id();
		let call_parameters = hex_string(&alice_id.encode());
		let response: MethodResponse = api
			.call(
				"chainHead_unstable_call",
				[&sub_id, &block_hash, "AccountNonceApi_account_nonce", &call_parameters],
			)
			.await
			.unwrap();
		let operation_id = match response {
			MethodResponse::Started(started) => started.operation_id,
			MethodResponse::LimitReached => panic!("Expected started response"),
		};
		// Response propagated to `chainHead_follow`.
		assert_matches!(
				get_next_event::<FollowEvent<String>>(&mut block_sub).await,
				FollowEvent::OperationCallDone(done) if done.operation_id == operation_id && done.output == "0x0000000000000000"
		);
		// Ensure uniqueness.
		assert!(op_ids.insert(operation_id));
	}
}

#[tokio::test]
async fn separate_operation_ids_for_subscriptions() {
	let builder = TestClientBuilder::new();
	let backend = builder.backend();
	let mut client = Arc::new(builder.build());

	let api = ChainHead::new(
		client.clone(),
		backend,
		Arc::new(TaskExecutor::default()),
		CHAIN_GENESIS,
		MAX_PINNED_BLOCKS,
		Duration::from_secs(MAX_PINNED_SECS),
	)
	.into_rpc();

	// Create two separate subscriptions.
	let mut sub_first = api.subscribe("chainHead_unstable_follow", [true]).await.unwrap();
	let sub_id_first = sub_first.subscription_id();
	let sub_id_first = serde_json::to_string(&sub_id_first).unwrap();

	let mut sub_second = api.subscribe("chainHead_unstable_follow", [true]).await.unwrap();
	let sub_id_second = sub_second.subscription_id();
	let sub_id_second = serde_json::to_string(&sub_id_second).unwrap();

	let block = client.new_block(Default::default()).unwrap().build().unwrap().block;
	client.import(BlockOrigin::Own, block.clone()).await.unwrap();
	let block_hash = format!("{:?}", block.header.hash());

	// Ensure the imported block is propagated and pinned.
	assert_matches!(
		get_next_event::<FollowEvent<String>>(&mut sub_first).await,
		FollowEvent::Initialized(_)
	);
	assert_matches!(
		get_next_event::<FollowEvent<String>>(&mut sub_first).await,
		FollowEvent::NewBlock(_)
	);
	assert_matches!(
		get_next_event::<FollowEvent<String>>(&mut sub_first).await,
		FollowEvent::BestBlockChanged(_)
	);

	assert_matches!(
		get_next_event::<FollowEvent<String>>(&mut sub_second).await,
		FollowEvent::Initialized(_)
	);
	assert_matches!(
		get_next_event::<FollowEvent<String>>(&mut sub_second).await,
		FollowEvent::NewBlock(_)
	);
	assert_matches!(
		get_next_event::<FollowEvent<String>>(&mut sub_second).await,
		FollowEvent::BestBlockChanged(_)
	);

	// Each `chainHead_follow` subscription receives a separate operation ID.
	let response: MethodResponse =
		api.call("chainHead_unstable_body", [&sub_id_first, &block_hash]).await.unwrap();
	let operation_id: String = match response {
		MethodResponse::Started(started) => started.operation_id,
		MethodResponse::LimitReached => panic!("Expected started response"),
	};
	assert_eq!(operation_id, "0");

	let response: MethodResponse = api
		.call("chainHead_unstable_body", [&sub_id_second, &block_hash])
		.await
		.unwrap();
	let operation_id_second: String = match response {
		MethodResponse::Started(started) => started.operation_id,
		MethodResponse::LimitReached => panic!("Expected started response"),
	};
	// The second subscription does not increment the operation ID of the first one.
	assert_eq!(operation_id_second, "0");
}

#[tokio::test]
async fn follow_generates_initial_blocks() {
	let builder = TestClientBuilder::new();
	let backend = builder.backend();
	let mut client = Arc::new(builder.build());

	let api = ChainHead::new(
		client.clone(),
		backend,
		Arc::new(TaskExecutor::default()),
		CHAIN_GENESIS,
		MAX_PINNED_BLOCKS,
		Duration::from_secs(MAX_PINNED_SECS),
	)
	.into_rpc();

	let finalized_hash = client.info().finalized_hash;

	// Block tree:
	// finalized -> block 1 -> block 2 -> block 4
	//           -> block 1 -> block 3
	let block_1 = client.new_block(Default::default()).unwrap().build().unwrap().block;
	let block_1_hash = block_1.header.hash();
	client.import(BlockOrigin::Own, block_1.clone()).await.unwrap();

	let block_2 = client.new_block(Default::default()).unwrap().build().unwrap().block;
	let block_2_hash = block_2.header.hash();
	client.import(BlockOrigin::Own, block_2.clone()).await.unwrap();

	let mut block_builder =
		client.new_block_at(block_1.header.hash(), Default::default(), false).unwrap();
	// This push is required as otherwise block 3 has the same hash as block 2 and won't get
	// imported
	block_builder
		.push_transfer(Transfer {
			from: AccountKeyring::Alice.into(),
			to: AccountKeyring::Ferdie.into(),
			amount: 41,
			nonce: 0,
		})
		.unwrap();
	let block_3 = block_builder.build().unwrap().block;
	let block_3_hash = block_3.header.hash();
	client.import(BlockOrigin::Own, block_3.clone()).await.unwrap();

	let mut sub = api.subscribe("chainHead_unstable_follow", [false]).await.unwrap();

	// Initialized must always be reported first.
	let event: FollowEvent<String> = get_next_event(&mut sub).await;
	let expected = FollowEvent::Initialized(Initialized {
		finalized_block_hash: format!("{:?}", finalized_hash),
		finalized_block_runtime: None,
		with_runtime: false,
	});
	assert_eq!(event, expected);

	// Check block 1.
	let event: FollowEvent<String> = get_next_event(&mut sub).await;
	let expected = FollowEvent::NewBlock(NewBlock {
		block_hash: format!("{:?}", block_1_hash),
		parent_block_hash: format!("{:?}", finalized_hash),
		new_runtime: None,
		with_runtime: false,
	});
	assert_eq!(event, expected);

	// Check block 2.
	let event: FollowEvent<String> = get_next_event(&mut sub).await;
	let expected = FollowEvent::NewBlock(NewBlock {
		block_hash: format!("{:?}", block_2_hash),
		parent_block_hash: format!("{:?}", block_1_hash),
		new_runtime: None,
		with_runtime: false,
	});
	assert_eq!(event, expected);
	// Check block 3.
	let event: FollowEvent<String> = get_next_event(&mut sub).await;
	let expected = FollowEvent::NewBlock(NewBlock {
		block_hash: format!("{:?}", block_3_hash),
		parent_block_hash: format!("{:?}", block_1_hash),
		new_runtime: None,
		with_runtime: false,
	});
	assert_eq!(event, expected);

	let event: FollowEvent<String> = get_next_event(&mut sub).await;
	let expected = FollowEvent::BestBlockChanged(BestBlockChanged {
		best_block_hash: format!("{:?}", block_2_hash),
	});
	assert_eq!(event, expected);

	// Import block 4.
	let block_4 = client.new_block(Default::default()).unwrap().build().unwrap().block;
	let block_4_hash = block_4.header.hash();
	client.import(BlockOrigin::Own, block_4.clone()).await.unwrap();

	let event: FollowEvent<String> = get_next_event(&mut sub).await;
	let expected = FollowEvent::NewBlock(NewBlock {
		block_hash: format!("{:?}", block_4_hash),
		parent_block_hash: format!("{:?}", block_2_hash),
		new_runtime: None,
		with_runtime: false,
	});
	assert_eq!(event, expected);

	let event: FollowEvent<String> = get_next_event(&mut sub).await;
	let expected = FollowEvent::BestBlockChanged(BestBlockChanged {
		best_block_hash: format!("{:?}", block_4_hash),
	});
	assert_eq!(event, expected);

	// Check the finalized event:
	//  - blocks 1, 2, 4 from canonical chain are finalized
	//  - block 3 from the fork is pruned
	client.finalize_block(block_4_hash, None).unwrap();

	let event: FollowEvent<String> = get_next_event(&mut sub).await;
	let expected = FollowEvent::Finalized(Finalized {
		finalized_block_hashes: vec![
			format!("{:?}", block_1_hash),
			format!("{:?}", block_2_hash),
			format!("{:?}", block_4_hash),
		],
		pruned_block_hashes: vec![format!("{:?}", block_3_hash)],
	});
	assert_eq!(event, expected);
}

#[tokio::test]
async fn follow_exceeding_pinned_blocks() {
	let builder = TestClientBuilder::new();
	let backend = builder.backend();
	let mut client = Arc::new(builder.build());

	let api = ChainHead::new(
		client.clone(),
		backend,
		Arc::new(TaskExecutor::default()),
		CHAIN_GENESIS,
		2,
		Duration::from_secs(MAX_PINNED_SECS),
	)
	.into_rpc();

	let mut sub = api.subscribe("chainHead_unstable_follow", [false]).await.unwrap();

	let block = client.new_block(Default::default()).unwrap().build().unwrap().block;
	client.import(BlockOrigin::Own, block.clone()).await.unwrap();

	// Ensure the imported block is propagated and pinned for this subscription.
	assert_matches!(
		get_next_event::<FollowEvent<String>>(&mut sub).await,
		FollowEvent::Initialized(_)
	);
	assert_matches!(
		get_next_event::<FollowEvent<String>>(&mut sub).await,
		FollowEvent::NewBlock(_)
	);
	assert_matches!(
		get_next_event::<FollowEvent<String>>(&mut sub).await,
		FollowEvent::BestBlockChanged(_)
	);

	// Block tree:
	//   finalized_block -> block -> block2
	// The first 2 blocks are pinned into the subscription, but the block2 will exceed the limit (2
	// blocks).
	let block2 = client.new_block(Default::default()).unwrap().build().unwrap().block;
	client.import(BlockOrigin::Own, block2.clone()).await.unwrap();

	assert_matches!(get_next_event::<FollowEvent<String>>(&mut sub).await, FollowEvent::Stop);

	// Subscription will not produce any more event for further blocks.
	let block3 = client.new_block(Default::default()).unwrap().build().unwrap().block;
	client.import(BlockOrigin::Own, block3.clone()).await.unwrap();

	assert!(sub.next::<FollowEvent<String>>().await.is_none());
}

#[tokio::test]
async fn follow_with_unpin() {
	let builder = TestClientBuilder::new();
	let backend = builder.backend();
	let mut client = Arc::new(builder.build());

	let api = ChainHead::new(
		client.clone(),
		backend,
		Arc::new(TaskExecutor::default()),
		CHAIN_GENESIS,
		2,
		Duration::from_secs(MAX_PINNED_SECS),
	)
	.into_rpc();

	let mut sub = api.subscribe("chainHead_unstable_follow", [false]).await.unwrap();
	let sub_id = sub.subscription_id();
	let sub_id = serde_json::to_string(&sub_id).unwrap();

	let block = client.new_block(Default::default()).unwrap().build().unwrap().block;
	let block_hash = format!("{:?}", block.header.hash());
	client.import(BlockOrigin::Own, block.clone()).await.unwrap();

	// Ensure the imported block is propagated and pinned for this subscription.
	assert_matches!(
		get_next_event::<FollowEvent<String>>(&mut sub).await,
		FollowEvent::Initialized(_)
	);
	assert_matches!(
		get_next_event::<FollowEvent<String>>(&mut sub).await,
		FollowEvent::NewBlock(_)
	);
	assert_matches!(
		get_next_event::<FollowEvent<String>>(&mut sub).await,
		FollowEvent::BestBlockChanged(_)
	);

	// Unpin an invalid subscription ID must return Ok(()).
	let invalid_hash = hex_string(&INVALID_HASH);
	let _res: () = api
		.call("chainHead_unstable_unpin", ["invalid_sub_id", &invalid_hash])
		.await
		.unwrap();

	// Valid subscription with invalid block hash.
	let invalid_hash = hex_string(&INVALID_HASH);
	let err = api
		.call::<_, serde_json::Value>("chainHead_unstable_unpin", [&sub_id, &invalid_hash])
		.await
		.unwrap_err();
	assert_matches!(err,
		Error::Call(CallError::Custom(ref err)) if err.code() == 2001 && err.message() == "Invalid block hash"
	);

	// To not exceed the number of pinned blocks, we need to unpin before the next import.
	let _res: () = api.call("chainHead_unstable_unpin", [&sub_id, &block_hash]).await.unwrap();

	// Block tree:
	//   finalized_block -> block -> block2
	//                      ^ has been unpinned
	let block2 = client.new_block(Default::default()).unwrap().build().unwrap().block;
	client.import(BlockOrigin::Own, block2.clone()).await.unwrap();

	assert_matches!(
		get_next_event::<FollowEvent<String>>(&mut sub).await,
		FollowEvent::NewBlock(_)
	);

	assert_matches!(
		get_next_event::<FollowEvent<String>>(&mut sub).await,
		FollowEvent::BestBlockChanged(_)
	);

	let block3 = client.new_block(Default::default()).unwrap().build().unwrap().block;
	client.import(BlockOrigin::Own, block3.clone()).await.unwrap();

	assert_matches!(get_next_event::<FollowEvent<String>>(&mut sub).await, FollowEvent::Stop);
	assert!(sub.next::<FollowEvent<String>>().await.is_none());
}

#[tokio::test]
async fn follow_prune_best_block() {
	let builder = TestClientBuilder::new();
	let backend = builder.backend();
	let mut client = Arc::new(builder.build());

	let api = ChainHead::new(
		client.clone(),
		backend,
		Arc::new(TaskExecutor::default()),
		CHAIN_GENESIS,
		MAX_PINNED_BLOCKS,
		Duration::from_secs(MAX_PINNED_SECS),
	)
	.into_rpc();

	let finalized_hash = client.info().finalized_hash;
	let mut sub = api.subscribe("chainHead_unstable_follow", [false]).await.unwrap();

	// Initialized must always be reported first.
	let event: FollowEvent<String> = get_next_event(&mut sub).await;
	let expected = FollowEvent::Initialized(Initialized {
		finalized_block_hash: format!("{:?}", finalized_hash),
		finalized_block_runtime: None,
		with_runtime: false,
	});
	assert_eq!(event, expected);

	// Block tree:
	//
	// finalized -> block 1 -> block 2
	//                         ^^^ best block reported
	//
	//           -> block 1 -> block 3 -> block 4
	//                                    ^^^ finalized
	//
	// The block 4 is needed on the longest chain because we want the
	// best block 2 to be reported as pruned. Pruning is happening at
	// height (N - 1), where N is the finalized block number.

	let block_1 = client.new_block(Default::default()).unwrap().build().unwrap().block;
	let block_1_hash = block_1.header.hash();
	client.import(BlockOrigin::Own, block_1.clone()).await.unwrap();

	let block_3 = client.new_block(Default::default()).unwrap().build().unwrap().block;
	let block_3_hash = block_3.header.hash();
	client.import(BlockOrigin::Own, block_3.clone()).await.unwrap();

	let block_4 = client.new_block(Default::default()).unwrap().build().unwrap().block;
	let block_4_hash = block_4.header.hash();
	client.import(BlockOrigin::Own, block_4.clone()).await.unwrap();

	// Import block 2 as best on the fork.
	let mut block_builder = client.new_block_at(block_1_hash, Default::default(), false).unwrap();
	// This push is required as otherwise block 3 has the same hash as block 2 and won't get
	// imported
	block_builder
		.push_transfer(Transfer {
			from: AccountKeyring::Alice.into(),
			to: AccountKeyring::Ferdie.into(),
			amount: 41,
			nonce: 0,
		})
		.unwrap();
	let block_2 = block_builder.build().unwrap().block;
	let block_2_hash = block_2.header.hash();
	client.import_as_best(BlockOrigin::Own, block_2.clone()).await.unwrap();

	// Check block 1.
	let event: FollowEvent<String> = get_next_event(&mut sub).await;
	let expected = FollowEvent::NewBlock(NewBlock {
		block_hash: format!("{:?}", block_1_hash),
		parent_block_hash: format!("{:?}", finalized_hash),
		new_runtime: None,
		with_runtime: false,
	});
	assert_eq!(event, expected);
	let event: FollowEvent<String> = get_next_event(&mut sub).await;
	let expected = FollowEvent::BestBlockChanged(BestBlockChanged {
		best_block_hash: format!("{:?}", block_1_hash),
	});
	assert_eq!(event, expected);

	// Check block 3.
	let event: FollowEvent<String> = get_next_event(&mut sub).await;
	let expected = FollowEvent::NewBlock(NewBlock {
		block_hash: format!("{:?}", block_3_hash),
		parent_block_hash: format!("{:?}", block_1_hash),
		new_runtime: None,
		with_runtime: false,
	});
	assert_eq!(event, expected);
	let event: FollowEvent<String> = get_next_event(&mut sub).await;
	let expected = FollowEvent::BestBlockChanged(BestBlockChanged {
		best_block_hash: format!("{:?}", block_3_hash),
	});
	assert_eq!(event, expected);

	// Check block 4.
	let event: FollowEvent<String> = get_next_event(&mut sub).await;
	let expected = FollowEvent::NewBlock(NewBlock {
		block_hash: format!("{:?}", block_4_hash),
		parent_block_hash: format!("{:?}", block_3_hash),
		new_runtime: None,
		with_runtime: false,
	});
	assert_eq!(event, expected);
	let event: FollowEvent<String> = get_next_event(&mut sub).await;
	let expected = FollowEvent::BestBlockChanged(BestBlockChanged {
		best_block_hash: format!("{:?}", block_4_hash),
	});
	assert_eq!(event, expected);

	// Check block 2, that we imported as custom best.
	let event: FollowEvent<String> = get_next_event(&mut sub).await;
	let expected = FollowEvent::NewBlock(NewBlock {
		block_hash: format!("{:?}", block_2_hash),
		parent_block_hash: format!("{:?}", block_1_hash),
		new_runtime: None,
		with_runtime: false,
	});
	assert_eq!(event, expected);
	let event: FollowEvent<String> = get_next_event(&mut sub).await;
	let expected = FollowEvent::BestBlockChanged(BestBlockChanged {
		best_block_hash: format!("{:?}", block_2_hash),
	});
	assert_eq!(event, expected);

	// Finalize the block 4 from the fork.
	client.finalize_block(block_4_hash, None).unwrap();

	// Expect to report the best block changed before the finalized event.
	let event: FollowEvent<String> = get_next_event(&mut sub).await;
	let expected = FollowEvent::BestBlockChanged(BestBlockChanged {
		best_block_hash: format!("{:?}", block_4_hash),
	});
	assert_eq!(event, expected);

	// Block 2 must be reported as pruned, even if it was the previous best.
	let event: FollowEvent<String> = get_next_event(&mut sub).await;
	let expected = FollowEvent::Finalized(Finalized {
		finalized_block_hashes: vec![
			format!("{:?}", block_1_hash),
			format!("{:?}", block_3_hash),
			format!("{:?}", block_4_hash),
		],
		pruned_block_hashes: vec![format!("{:?}", block_2_hash)],
	});
	assert_eq!(event, expected);

	// Pruned hash can be unpinned.
	let sub_id = sub.subscription_id();
	let sub_id = serde_json::to_string(&sub_id).unwrap();
	let hash = format!("{:?}", block_2_hash);
	let _res: () = api.call("chainHead_unstable_unpin", [&sub_id, &hash]).await.unwrap();
}

#[tokio::test]
async fn follow_forks_pruned_block() {
	let builder = TestClientBuilder::new();
	let backend = builder.backend();
	let mut client = Arc::new(builder.build());

	let api = ChainHead::new(
		client.clone(),
		backend,
		Arc::new(TaskExecutor::default()),
		CHAIN_GENESIS,
		MAX_PINNED_BLOCKS,
		Duration::from_secs(MAX_PINNED_SECS),
	)
	.into_rpc();

	// Block tree before the subscription:
	//
	// finalized -> block 1 -> block 2 -> block 3
	//                                        ^^^ finalized
	//           -> block 1 -> block 4 -> block 5
	//

	let block_1 = client.new_block(Default::default()).unwrap().build().unwrap().block;
	client.import(BlockOrigin::Own, block_1.clone()).await.unwrap();

	let block_2 = client.new_block(Default::default()).unwrap().build().unwrap().block;
	client.import(BlockOrigin::Own, block_2.clone()).await.unwrap();

	let block_3 = client.new_block(Default::default()).unwrap().build().unwrap().block;
	let block_3_hash = block_3.header.hash();
	client.import(BlockOrigin::Own, block_3.clone()).await.unwrap();

	// Block 4 with parent Block 1 is not the best imported.
	let mut block_builder =
		client.new_block_at(block_1.header.hash(), Default::default(), false).unwrap();
	// This push is required as otherwise block 4 has the same hash as block 2 and won't get
	// imported
	block_builder
		.push_transfer(Transfer {
			from: AccountKeyring::Alice.into(),
			to: AccountKeyring::Ferdie.into(),
			amount: 41,
			nonce: 0,
		})
		.unwrap();
	let block_4 = block_builder.build().unwrap().block;
	client.import(BlockOrigin::Own, block_4.clone()).await.unwrap();

	let mut block_builder =
		client.new_block_at(block_4.header.hash(), Default::default(), false).unwrap();
	block_builder
		.push_transfer(Transfer {
			from: AccountKeyring::Bob.into(),
			to: AccountKeyring::Ferdie.into(),
			amount: 41,
			nonce: 0,
		})
		.unwrap();
	let block_5 = block_builder.build().unwrap().block;
	client.import(BlockOrigin::Own, block_5.clone()).await.unwrap();

	// Block 4 and 5 are not pruned, pruning happens at height (N - 1).
	client.finalize_block(block_3_hash, None).unwrap();

	let mut sub = api.subscribe("chainHead_unstable_follow", [false]).await.unwrap();

	// Initialized must always be reported first.
	let event: FollowEvent<String> = get_next_event(&mut sub).await;
	let expected = FollowEvent::Initialized(Initialized {
		finalized_block_hash: format!("{:?}", block_3_hash),
		finalized_block_runtime: None,
		with_runtime: false,
	});
	assert_eq!(event, expected);

	// Block tree:
	//
	// finalized -> block 1 -> block 2 -> block 3 -> block 6
	//                                                  ^^^ finalized
	//           -> block 1 -> block 4 -> block 5
	//
	// Mark block 6 as finalized to force block 4 and 5 to get pruned.

	let block_6 = client.new_block(Default::default()).unwrap().build().unwrap().block;
	let block_6_hash = block_6.header.hash();
	client.import(BlockOrigin::Own, block_6.clone()).await.unwrap();

	client.finalize_block(block_6_hash, None).unwrap();

	// Check block 6.
	let event: FollowEvent<String> = get_next_event(&mut sub).await;
	let expected = FollowEvent::NewBlock(NewBlock {
		block_hash: format!("{:?}", block_6_hash),
		parent_block_hash: format!("{:?}", block_3_hash),
		new_runtime: None,
		with_runtime: false,
	});
	assert_eq!(event, expected);
	let event: FollowEvent<String> = get_next_event(&mut sub).await;
	let expected = FollowEvent::BestBlockChanged(BestBlockChanged {
		best_block_hash: format!("{:?}", block_6_hash),
	});
	assert_eq!(event, expected);

	// Block 4 and 5 must not be reported as pruned.
	let event: FollowEvent<String> = get_next_event(&mut sub).await;
	let expected = FollowEvent::Finalized(Finalized {
		finalized_block_hashes: vec![format!("{:?}", block_6_hash)],
		pruned_block_hashes: vec![],
	});
	assert_eq!(event, expected);
}

#[tokio::test]
async fn follow_report_multiple_pruned_block() {
	let builder = TestClientBuilder::new();
	let backend = builder.backend();
	let mut client = Arc::new(builder.build());

	let api = ChainHead::new(
		client.clone(),
		backend,
		Arc::new(TaskExecutor::default()),
		CHAIN_GENESIS,
		MAX_PINNED_BLOCKS,
		Duration::from_secs(MAX_PINNED_SECS),
	)
	.into_rpc();

	// Block tree:
	//
	// finalized -> block 1 -> block 2 -> block 3
	//                                        ^^^ finalized after subscription
	//           -> block 1 -> block 4 -> block 5

	let finalized_hash = client.info().finalized_hash;

	let block_1 = client.new_block(Default::default()).unwrap().build().unwrap().block;
	let block_1_hash = block_1.header.hash();
	client.import(BlockOrigin::Own, block_1.clone()).await.unwrap();

	let block_2 = client.new_block(Default::default()).unwrap().build().unwrap().block;
	let block_2_hash = block_2.header.hash();
	client.import(BlockOrigin::Own, block_2.clone()).await.unwrap();

	let block_3 = client.new_block(Default::default()).unwrap().build().unwrap().block;
	let block_3_hash = block_3.header.hash();
	client.import(BlockOrigin::Own, block_3.clone()).await.unwrap();

	// Block 4 with parent Block 1 is not the best imported.
	let mut block_builder =
		client.new_block_at(block_1.header.hash(), Default::default(), false).unwrap();
	// This push is required as otherwise block 4 has the same hash as block 2 and won't get
	// imported
	block_builder
		.push_transfer(Transfer {
			from: AccountKeyring::Alice.into(),
			to: AccountKeyring::Ferdie.into(),
			amount: 41,
			nonce: 0,
		})
		.unwrap();
	let block_4 = block_builder.build().unwrap().block;
	let block_4_hash = block_4.header.hash();
	client.import(BlockOrigin::Own, block_4.clone()).await.unwrap();

	let mut block_builder =
		client.new_block_at(block_4.header.hash(), Default::default(), false).unwrap();
	block_builder
		.push_transfer(Transfer {
			from: AccountKeyring::Bob.into(),
			to: AccountKeyring::Ferdie.into(),
			amount: 41,
			nonce: 0,
		})
		.unwrap();
	let block_5 = block_builder.build().unwrap().block;
	let block_5_hash = block_5.header.hash();
	client.import(BlockOrigin::Own, block_5.clone()).await.unwrap();
	let mut sub = api.subscribe("chainHead_unstable_follow", [false]).await.unwrap();

	// Initialized must always be reported first.
	let event: FollowEvent<String> = get_next_event(&mut sub).await;
	let expected = FollowEvent::Initialized(Initialized {
		finalized_block_hash: format!("{:?}", finalized_hash),
		finalized_block_runtime: None,
		with_runtime: false,
	});
	assert_eq!(event, expected);

	let event: FollowEvent<String> = get_next_event(&mut sub).await;
	let expected = FollowEvent::NewBlock(NewBlock {
		block_hash: format!("{:?}", block_1_hash),
		parent_block_hash: format!("{:?}", finalized_hash),
		new_runtime: None,
		with_runtime: false,
	});
	assert_eq!(event, expected);

	let event: FollowEvent<String> = get_next_event(&mut sub).await;
	let expected = FollowEvent::NewBlock(NewBlock {
		block_hash: format!("{:?}", block_2_hash),
		parent_block_hash: format!("{:?}", block_1_hash),
		new_runtime: None,
		with_runtime: false,
	});
	assert_eq!(event, expected);

	let event: FollowEvent<String> = get_next_event(&mut sub).await;
	let expected = FollowEvent::NewBlock(NewBlock {
		block_hash: format!("{:?}", block_3_hash),
		parent_block_hash: format!("{:?}", block_2_hash),
		new_runtime: None,
		with_runtime: false,
	});
	assert_eq!(event, expected);

	// The fork must also be reported.
	let event: FollowEvent<String> = get_next_event(&mut sub).await;
	let expected = FollowEvent::NewBlock(NewBlock {
		block_hash: format!("{:?}", block_4_hash),
		parent_block_hash: format!("{:?}", block_1_hash),
		new_runtime: None,
		with_runtime: false,
	});
	assert_eq!(event, expected);

	let event: FollowEvent<String> = get_next_event(&mut sub).await;
	let expected = FollowEvent::NewBlock(NewBlock {
		block_hash: format!("{:?}", block_5_hash),
		parent_block_hash: format!("{:?}", block_4_hash),
		new_runtime: None,
		with_runtime: false,
	});
	assert_eq!(event, expected);

	// The best block of the chain must also be reported.
	let event: FollowEvent<String> = get_next_event(&mut sub).await;
	let expected = FollowEvent::BestBlockChanged(BestBlockChanged {
		best_block_hash: format!("{:?}", block_3_hash),
	});
	assert_eq!(event, expected);

	// Block 4 and 5 are not pruned, pruning happens at height (N - 1).
	client.finalize_block(block_3_hash, None).unwrap();

	// Finalizing block 3 directly will also result in block 1 and 2 being finalized.
	let event: FollowEvent<String> = get_next_event(&mut sub).await;
	let expected = FollowEvent::Finalized(Finalized {
		finalized_block_hashes: vec![
			format!("{:?}", block_1_hash),
			format!("{:?}", block_2_hash),
			format!("{:?}", block_3_hash),
		],
		pruned_block_hashes: vec![],
	});
	assert_eq!(event, expected);

	// Block tree:
	//
	// finalized -> block 1 -> block 2 -> block 3 -> block 6
	//                                                  ^^^ finalized
	//           -> block 1 -> block 4 -> block 5
	//
	// Mark block 6 as finalized to force block 4 and 5 to get pruned.

	let block_6 = client.new_block(Default::default()).unwrap().build().unwrap().block;
	let block_6_hash = block_6.header.hash();
	client.import(BlockOrigin::Own, block_6.clone()).await.unwrap();

	client.finalize_block(block_6_hash, None).unwrap();

	// Check block 6.
	let event: FollowEvent<String> = get_next_event(&mut sub).await;
	let expected = FollowEvent::NewBlock(NewBlock {
		block_hash: format!("{:?}", block_6_hash),
		parent_block_hash: format!("{:?}", block_3_hash),
		new_runtime: None,
		with_runtime: false,
	});
	assert_eq!(event, expected);
	let event: FollowEvent<String> = get_next_event(&mut sub).await;
	let expected = FollowEvent::BestBlockChanged(BestBlockChanged {
		best_block_hash: format!("{:?}", block_6_hash),
	});
	assert_eq!(event, expected);

	// Block 4 and 5 be reported as pruned, not just the stale head (block 5).
	let event: FollowEvent<String> = get_next_event(&mut sub).await;
	let expected = FollowEvent::Finalized(Finalized {
		finalized_block_hashes: vec![format!("{:?}", block_6_hash)],
		pruned_block_hashes: vec![format!("{:?}", block_4_hash), format!("{:?}", block_5_hash)],
	});
	assert_eq!(event, expected);
}

#[tokio::test]
async fn pin_block_references() {
	// Manually construct an in-memory backend and client.
	let backend = Arc::new(sc_client_api::in_mem::Backend::new());
	let executor = substrate_test_runtime_client::new_native_or_wasm_executor();
	let client_config = sc_service::ClientConfig::default();

	let genesis_block_builder = sc_service::GenesisBlockBuilder::new(
		&substrate_test_runtime_client::GenesisParameters::default().genesis_storage(),
		!client_config.no_genesis,
		backend.clone(),
		executor.clone(),
	)
	.unwrap();

	let mut client = Arc::new(
		new_in_mem::<_, Block, _, RuntimeApi>(
			backend.clone(),
			executor,
			genesis_block_builder,
			None,
			None,
			Box::new(TaskExecutor::new()),
			client_config,
		)
		.unwrap(),
	);

	let api = ChainHead::new(
		client.clone(),
		backend.clone(),
		Arc::new(TaskExecutor::default()),
		CHAIN_GENESIS,
		3,
		Duration::from_secs(MAX_PINNED_SECS),
	)
	.into_rpc();

	async fn wait_pinned_references<Block: BlockT>(
		backend: &Arc<sc_client_api::in_mem::Backend<Block>>,
		hash: &Block::Hash,
		target: i64,
	) {
		// Retry for at most 2 minutes.
		let mut retries = 120;
		while backend.pin_refs(hash).unwrap() != target {
			if retries == 0 {
				panic!("Expected target={} pinned references for hash={:?}", target, hash);
			}
			retries -= 1;

			tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
		}
	}

	let mut sub = api.subscribe("chainHead_unstable_follow", [false]).await.unwrap();
	let sub_id = sub.subscription_id();
	let sub_id = serde_json::to_string(&sub_id).unwrap();

	let block = client.new_block(Default::default()).unwrap().build().unwrap().block;
	let hash = block.header.hash();
	let block_hash = format!("{:?}", hash);
	client.import(BlockOrigin::Own, block.clone()).await.unwrap();

	// Ensure the imported block is propagated for this subscription.
	assert_matches!(
		get_next_event::<FollowEvent<String>>(&mut sub).await,
		FollowEvent::Initialized(_)
	);
	assert_matches!(
		get_next_event::<FollowEvent<String>>(&mut sub).await,
		FollowEvent::NewBlock(_)
	);
	assert_matches!(
		get_next_event::<FollowEvent<String>>(&mut sub).await,
		FollowEvent::BestBlockChanged(_)
	);

	// We need to wait a bit for:
	// 1. `NewBlock` and `BestBlockChanged` notifications to propagate to the chainHead
	// subscription. (pin_refs == 2)
	// 2. The chainHead to call `pin_blocks` only once for the `NewBlock`
	// notification (pin_refs == 3)
	// 3. Both notifications to go out of scope (pin_refs ==  1 (total 3 - dropped 2)).
	wait_pinned_references(&backend, &hash, 1).await;

	// To not exceed the number of pinned blocks, we need to unpin before the next import.
	let _res: () = api.call("chainHead_unstable_unpin", [&sub_id, &block_hash]).await.unwrap();

	// Make sure unpin clears out the reference.
	let refs = backend.pin_refs(&hash).unwrap();
	assert_eq!(refs, 0);

	// Add another 2 blocks and make sure we drop the subscription with the blocks pinned.
	let mut hashes = Vec::new();
	for _ in 0..2 {
		let block = client.new_block(Default::default()).unwrap().build().unwrap().block;
		let hash = block.header.hash();
		client.import(BlockOrigin::Own, block.clone()).await.unwrap();

		// Ensure the imported block is propagated for this subscription.
		assert_matches!(
			get_next_event::<FollowEvent<String>>(&mut sub).await,
			FollowEvent::NewBlock(_)
		);
		assert_matches!(
			get_next_event::<FollowEvent<String>>(&mut sub).await,
			FollowEvent::BestBlockChanged(_)
		);

		hashes.push(hash);
	}

	// Make sure the pin was propagated.
	for hash in &hashes {
		wait_pinned_references(&backend, hash, 1).await;
	}

	// Drop the subscription and expect the pinned blocks to be released.
	drop(sub);
	// The `chainHead` detects the subscription was terminated when it tries
	// to send another block.
	let block = client.new_block(Default::default()).unwrap().build().unwrap().block;
	client.import(BlockOrigin::Own, block.clone()).await.unwrap();

	for hash in &hashes {
		wait_pinned_references(&backend, &hash, 0).await;
	}
}

#[tokio::test]
async fn follow_finalized_before_new_block() {
	let builder = TestClientBuilder::new();
	let backend = builder.backend();
	let mut client = Arc::new(builder.build());

	let client_mock = Arc::new(ChainHeadMockClient::new(client.clone()));

	let api = ChainHead::new(
		client_mock.clone(),
		backend,
		Arc::new(TaskExecutor::default()),
		CHAIN_GENESIS,
		MAX_PINNED_BLOCKS,
		Duration::from_secs(MAX_PINNED_SECS),
	)
	.into_rpc();

	// Make sure the block is imported for it to be pinned.
	let block_1 = client.new_block(Default::default()).unwrap().build().unwrap().block;
	let block_1_hash = block_1.header.hash();
	client.import(BlockOrigin::Own, block_1.clone()).await.unwrap();

	let mut sub = api.subscribe("chainHead_unstable_follow", [false]).await.unwrap();

	// Trigger the `FinalizedNotification` for block 1 before the `BlockImportNotification`, and
	// expect for the `chainHead` to generate `NewBlock`, `BestBlock` and `Finalized` events.

	// Trigger the Finalized notification before the NewBlock one.
	run_with_timeout(client_mock.trigger_finality_stream(block_1.header.clone())).await;

	// Initialized must always be reported first.
	let finalized_hash = client.info().finalized_hash;
	let event: FollowEvent<String> = get_next_event(&mut sub).await;
	let expected = FollowEvent::Initialized(Initialized {
		finalized_block_hash: format!("{:?}", finalized_hash),
		finalized_block_runtime: None,
		with_runtime: false,
	});
	assert_eq!(event, expected);

	// Block 1 must be reported because we triggered the finalized notification.
	let event: FollowEvent<String> = get_next_event(&mut sub).await;
	let expected = FollowEvent::NewBlock(NewBlock {
		block_hash: format!("{:?}", block_1_hash),
		parent_block_hash: format!("{:?}", finalized_hash),
		new_runtime: None,
		with_runtime: false,
	});
	assert_eq!(event, expected);

	let event: FollowEvent<String> = get_next_event(&mut sub).await;
	let expected = FollowEvent::BestBlockChanged(BestBlockChanged {
		best_block_hash: format!("{:?}", block_1_hash),
	});
	assert_eq!(event, expected);

	let event: FollowEvent<String> = get_next_event(&mut sub).await;
	let expected = FollowEvent::Finalized(Finalized {
		finalized_block_hashes: vec![format!("{:?}", block_1_hash)],
		pruned_block_hashes: vec![],
	});
	assert_eq!(event, expected);

	let block_2 = client.new_block(Default::default()).unwrap().build().unwrap().block;
	let block_2_hash = block_2.header.hash();
	client.import(BlockOrigin::Own, block_2.clone()).await.unwrap();

	// Triggering the `BlockImportNotification` notification for block 1 should have no effect
	// on the notification because the events were handled by the `FinalizedNotification`.
	// Also trigger the `BlockImportNotification` notification for block 2 to ensure
	// `NewBlock and `BestBlock` events are generated.

	// Trigger NewBlock notification for block 1 and block 2.
	run_with_timeout(client_mock.trigger_import_stream(block_1.header)).await;
	run_with_timeout(client_mock.trigger_import_stream(block_2.header)).await;

	let event: FollowEvent<String> = get_next_event(&mut sub).await;
	let expected = FollowEvent::NewBlock(NewBlock {
		block_hash: format!("{:?}", block_2_hash),
		parent_block_hash: format!("{:?}", block_1_hash),
		new_runtime: None,
		with_runtime: false,
	});
	assert_eq!(event, expected);

	let event: FollowEvent<String> = get_next_event(&mut sub).await;
	let expected = FollowEvent::BestBlockChanged(BestBlockChanged {
		best_block_hash: format!("{:?}", block_2_hash),
	});
	assert_eq!(event, expected);
}
