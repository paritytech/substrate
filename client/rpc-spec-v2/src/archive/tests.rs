use super::*;
use jsonrpsee::{types::EmptyParams, RpcModule};
use sc_block_builder::BlockBuilderProvider;
use sp_consensus::BlockOrigin;
use sp_core::{hexdisplay::HexDisplay, testing::TaskExecutor};
use std::sync::Arc;
use substrate_test_runtime_client::{prelude::*, Backend, Client, ClientBlockImportExt};

type Block = substrate_test_runtime_client::runtime::Block;
const CHAIN_GENESIS: [u8; 32] = [0; 32];

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
