use super::*;
use assert_matches::assert_matches;
use codec::{Decode, Encode};
use jsonrpsee::{
	core::{error::Error, server::rpc_module::Subscription as RpcSubscription},
	types::{error::CallError, EmptyParams},
	RpcModule,
};
use sc_block_builder::BlockBuilderProvider;
use sp_blockchain::HeaderBackend;
use sp_consensus::BlockOrigin;
use sp_core::{hexdisplay::HexDisplay, testing::TaskExecutor};
use std::{future::Future, sync::Arc};
use substrate_test_runtime_client::{
	prelude::*, runtime, Backend, BlockBuilderExt, Client, ClientBlockImportExt,
};

type Header = substrate_test_runtime_client::runtime::Header;
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

async fn setup_api() -> (
	Arc<Client<Backend>>,
	RpcModule<ChainHead<Backend, Block, Client<Backend>>>,
	RpcSubscription,
	String,
	Block,
) {
	let mut client = Arc::new(substrate_test_runtime_client::new());
	let api =
		ChainHead::new(client.clone(), Arc::new(TaskExecutor::default()), CHAIN_GENESIS).into_rpc();

	let mut sub = api.subscribe("chainHead_unstable_follow", [false]).await.unwrap();
	// TODO: Jsonrpsee release for sub_id.
	// let sub_id = sub.subscription_id();
	// let sub_id = serde_json::to_string(&sub_id).unwrap();
	let sub_id: String = "A".into();

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
	let mut client = Arc::new(substrate_test_runtime_client::new());
	let api =
		ChainHead::new(client.clone(), Arc::new(TaskExecutor::default()), CHAIN_GENESIS).into_rpc();

	let finalized_hash = client.info().finalized_hash;
	let mut sub = api.subscribe("chainHead_unstable_follow", [false]).await.unwrap();

	// Initialized must always be reported first.
	let event: FollowEvent<String> = get_next_event(&mut sub).await;
	let expected = FollowEvent::Initialized(Initialized {
		finalized_block_hash: format!("{:?}", finalized_hash),
		finalized_block_runtime: None,
		runtime_updates: false,
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
		runtime_updates: false,
	});
	assert_eq!(event, expected);

	let event: FollowEvent<String> = get_next_event(&mut sub).await;
	let expected = FollowEvent::BestBlockChanged(BestBlockChanged {
		best_block_hash: format!("{:?}", best_hash),
	});
	assert_eq!(event, expected);

	client.finalize_block(&best_hash, None).unwrap();

	let event: FollowEvent<String> = get_next_event(&mut sub).await;
	let expected = FollowEvent::Finalized(Finalized {
		finalized_block_hashes: vec![format!("{:?}", best_hash)],
		pruned_block_hashes: vec![],
	});
	assert_eq!(event, expected);
}

#[tokio::test]
async fn get_genesis() {
	let client = Arc::new(substrate_test_runtime_client::new());
	let api =
		ChainHead::new(client.clone(), Arc::new(TaskExecutor::default()), CHAIN_GENESIS).into_rpc();

	let genesis: String =
		api.call("chainHead_unstable_genesisHash", EmptyParams::new()).await.unwrap();
	assert_eq!(genesis, format!("0x{}", HexDisplay::from(&CHAIN_GENESIS)));
}
