use super::*;
use assert_matches::assert_matches;
use codec::Encode;
use jsonrpsee::{
	core::{server::rpc_module::Subscription as RpcSubscription, Error},
	types::{error::CallError, EmptyParams},
	RpcModule,
};
use sc_block_builder::BlockBuilderProvider;
use sc_client_api::ChildInfo;
use sp_api::{BlockId, HeaderT};
use sp_consensus::BlockOrigin;
use sp_core::{hexdisplay::HexDisplay, testing::TaskExecutor};
use std::sync::Arc;
use substrate_test_runtime::Transfer;
use substrate_test_runtime_client::{prelude::*, runtime, Backend, Client, ClientBlockImportExt};

type Block = substrate_test_runtime_client::runtime::Block;
const CHAIN_GENESIS: [u8; 32] = [0; 32];
const INVALID_HASH: [u8; 32] = [1; 32];
const KEY: &[u8] = b":mock";
const VALUE: &[u8] = b"hello world";
const CHILD_STORAGE_KEY: &[u8] = b"child";
const CHILD_VALUE: &[u8] = b"child value";

async fn get_next_event<T: serde::de::DeserializeOwned>(sub: &mut RpcSubscription) -> T {
	let (event, _sub_id) = tokio::time::timeout(std::time::Duration::from_secs(1), sub.next())
		.await
		.unwrap()
		.unwrap()
		.unwrap();
	event
}

async fn setup_api(
) -> (Arc<Client<Backend>>, RpcModule<Archive<Backend, Block, Client<Backend>>>, Block) {
	let child_info = ChildInfo::new_default(CHILD_STORAGE_KEY);
	let builder = TestClientBuilder::new().add_extra_child_storage(
		&child_info,
		KEY.to_vec(),
		CHILD_VALUE.to_vec(),
	);
	let backend = builder.backend();
	let mut client = Arc::new(builder.build());

	let api =
		Archive::new(client.clone(), backend, Arc::new(TaskExecutor::default()), CHAIN_GENESIS)
			.into_rpc();

	let block = client.new_block(Default::default()).unwrap().build().unwrap().block;
	client.import(BlockOrigin::Own, block.clone()).await.unwrap();

	(client, api, block)
}

#[tokio::test]
async fn get_genesis() {
	let (_client, api, _block) = setup_api().await;

	let genesis: String =
		api.call("archive_unstable_genesisHash", EmptyParams::new()).await.unwrap();
	assert_eq!(genesis, format!("0x{}", HexDisplay::from(&CHAIN_GENESIS)));
}

#[tokio::test]
async fn get_header() {
	let (_client, api, block) = setup_api().await;
	let block_hash = format!("{:?}", block.header.hash());
	let invalid_hash = format!("0x{:?}", HexDisplay::from(&INVALID_HASH));

	// Invalid block hash.
	let mut sub = api.subscribe("archive_unstable_header", [&invalid_hash]).await.unwrap();
	let event: ArchiveEvent<String> = get_next_event(&mut sub).await;
	assert_eq!(event, ArchiveEvent::Inaccessible);

	// Valid block hash.
	let mut sub = api.subscribe("archive_unstable_header", [&block_hash]).await.unwrap();
	let event: ArchiveEvent<String> = get_next_event(&mut sub).await;
	let expected = {
		let result = format!("0x{}", HexDisplay::from(&block.header.encode()));
		ArchiveEvent::Done(ArchiveResult { result })
	};
	assert_eq!(event, expected);
}

#[tokio::test]
async fn get_body() {
	let (mut client, api, block) = setup_api().await;
	let block_hash = format!("{:?}", block.header.hash());
	let invalid_hash = format!("0x{:?}", HexDisplay::from(&INVALID_HASH));

	// Invalid block hash.
	let mut sub = api.subscribe("archive_unstable_body", [&invalid_hash]).await.unwrap();
	let event: ArchiveEvent<String> = get_next_event(&mut sub).await;
	assert_eq!(event, ArchiveEvent::Inaccessible);

	// Valid block hash with empty body.
	let mut sub = api.subscribe("archive_unstable_body", [&block_hash]).await.unwrap();
	let event: ArchiveEvent<String> = get_next_event(&mut sub).await;
	let expected = ArchiveEvent::Done(ArchiveResult { result: "0x00".into() });
	assert_eq!(event, expected);

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

	// Valid block hash with extrinsics.
	let mut sub = api.subscribe("archive_unstable_body", [&block_hash]).await.unwrap();
	let event: ArchiveEvent<String> = get_next_event(&mut sub).await;
	let expected = {
		let result = format!("0x{}", HexDisplay::from(&block.extrinsics.encode()));
		ArchiveEvent::Done(ArchiveResult { result })
	};
	assert_eq!(event, expected);
}

#[tokio::test]
async fn get_storage() {
	let (mut client, api, block) = setup_api().await;
	let block_hash = format!("{:?}", block.header.hash());
	let invalid_hash = format!("0x{:?}", HexDisplay::from(&INVALID_HASH));
	let key = format!("0x{:?}", HexDisplay::from(&KEY));

	// Invalid block hash.
	let mut sub = api.subscribe("archive_unstable_storage", [&invalid_hash, &key]).await.unwrap();
	let event: ArchiveEvent<Option<String>> = get_next_event(&mut sub).await;
	assert_matches!(event, ArchiveEvent::Error(ErrorEvent {error}) if error.contains("Header was not found"));

	// No storage at the block hash.
	let mut sub = api.subscribe("archive_unstable_storage", [&block_hash, &key]).await.unwrap();
	let event: ArchiveEvent<Option<String>> = get_next_event(&mut sub).await;
	let expected = ArchiveEvent::Done(ArchiveResult { result: None });
	assert_eq!(event, expected);

	// Import a new block with storage changes.
	let mut builder = client.new_block(Default::default()).unwrap();
	builder.push_storage_change(KEY.to_vec(), Some(VALUE.to_vec())).unwrap();
	let block = builder.build().unwrap().block;
	let block_hash = format!("{:?}", block.header.hash());
	client.import(BlockOrigin::Own, block.clone()).await.unwrap();

	// Valid call with storage at the key.
	let mut sub = api.subscribe("archive_unstable_storage", [&block_hash, &key]).await.unwrap();
	let event: ArchiveEvent<Option<String>> = get_next_event(&mut sub).await;
	let expected_value = Some(format!("0x{:?}", HexDisplay::from(&VALUE)));
	assert_matches!(event, ArchiveEvent::<Option<String>>::Done(done) if done.result == expected_value);

	// Child value set in `setup_api`.
	let child_info = format!("0x{:?}", HexDisplay::from(b"child"));
	let genesis_hash = format!("{:?}", client.genesis_hash());
	let expected_value = Some(format!("0x{:?}", HexDisplay::from(&CHILD_VALUE)));
	let mut sub = api
		.subscribe("archive_unstable_storage", [&genesis_hash, &key, &child_info])
		.await
		.unwrap();
	let event: ArchiveEvent<Option<String>> = get_next_event(&mut sub).await;
	assert_matches!(event, ArchiveEvent::<Option<String>>::Done(done) if done.result == expected_value);
}

#[tokio::test]
async fn get_hash_by_height() {
	let (mut client, api, _block) = setup_api().await;

	// Invalid parameter.
	let err = api.subscribe("archive_unstable_hashByHeight", ["0xdummy"]).await.unwrap_err();
	assert_matches!(err,
		Error::Call(CallError::Custom(ref err)) if err.code() == 3001 && err.message().contains("Invalid parameter")
	);

	// Genesis height.
	let mut sub = api.subscribe("archive_unstable_hashByHeight", ["0"]).await.unwrap();
	let event: ArchiveEvent<Vec<String>> = get_next_event(&mut sub).await;
	let expected =
		ArchiveEvent::Done(ArchiveResult { result: vec![format!("{:?}", client.genesis_hash())] });
	assert_eq!(event, expected);

	// Block tree:
	// finalized -> block 1 -> block 2 -> block 3
	//           -> block 1 -> block 4
	//
	//              ^^^ h = N
	//                         ^^^ h =  N + 1
	//                                     ^^^ h = N + 2
	let block_1 = client.new_block(Default::default()).unwrap().build().unwrap().block;
	let block_1_hash = block_1.header.hash();
	client.import(BlockOrigin::Own, block_1.clone()).await.unwrap();
	let block_2 = client.new_block(Default::default()).unwrap().build().unwrap().block;
	let block_2_hash = block_2.header.hash();
	client.import(BlockOrigin::Own, block_2.clone()).await.unwrap();
	let block_3 = client.new_block(Default::default()).unwrap().build().unwrap().block;
	let block_3_hash = block_3.header.hash();
	client.import(BlockOrigin::Own, block_3.clone()).await.unwrap();
	// Import block 4 fork.
	let mut block_builder = client
		.new_block_at(&BlockId::Hash(block_1_hash), Default::default(), false)
		.unwrap();
	// This push is required as otherwise block 3 has the same hash as block 1 and won't get
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

	// Test nonfinalized heights.
	// Height N must include block 1.
	let mut height = *block_1.header.number();
	let mut sub = api
		.subscribe("archive_unstable_hashByHeight", [&format!("{:?}", height)])
		.await
		.unwrap();
	let event: ArchiveEvent<Vec<String>> = get_next_event(&mut sub).await;
	let expected =
		ArchiveEvent::Done(ArchiveResult { result: vec![format!("{:?}", block_1_hash)] });
	assert_eq!(event, expected);

	// Height (N + 1) must include block 2 and 4.
	height += 1;
	let mut sub = api
		.subscribe("archive_unstable_hashByHeight", [&format!("{:?}", height)])
		.await
		.unwrap();
	let event: ArchiveEvent<Vec<String>> = get_next_event(&mut sub).await;
	let expected = ArchiveEvent::Done(ArchiveResult {
		result: vec![format!("{:?}", block_4_hash), format!("{:?}", block_2_hash)],
	});
	assert_eq!(event, expected);

	// Height (N + 2) must include block 3.
	height += 1;
	let mut sub = api
		.subscribe("archive_unstable_hashByHeight", [&format!("{:?}", height)])
		.await
		.unwrap();
	let event: ArchiveEvent<Vec<String>> = get_next_event(&mut sub).await;
	let expected =
		ArchiveEvent::Done(ArchiveResult { result: vec![format!("{:?}", block_3_hash)] });
	assert_eq!(event, expected);
}
