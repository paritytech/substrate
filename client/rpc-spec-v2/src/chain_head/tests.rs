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
