use super::*;
use codec::Encode;
use jsonrpsee::{
	core::server::rpc_module::Subscription as RpcSubscription, types::EmptyParams, RpcModule,
};
use sc_block_builder::BlockBuilderProvider;
use sp_consensus::BlockOrigin;
use sp_core::{hexdisplay::HexDisplay, testing::TaskExecutor};
use std::sync::Arc;
use substrate_test_runtime_client::{prelude::*, runtime, Backend, Client, ClientBlockImportExt};

type Block = substrate_test_runtime_client::runtime::Block;
const CHAIN_GENESIS: [u8; 32] = [0; 32];
const INVALID_HASH: [u8; 32] = [1; 32];

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
	let builder = TestClientBuilder::new();
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
