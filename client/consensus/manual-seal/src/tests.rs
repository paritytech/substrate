use std::thread;
use std::time::Duration;

use super::*;
use substrate_test_runtime_client::{
	DefaultTestClientBuilderExt,
	TestClientBuilderExt,
	AccountKeyring::*,
	TestClientBuilder,
};
use sc_transaction_pool::{BasicPool, RevalidationType, txpool::Options};
use substrate_test_runtime_transaction_pool::{TestApi, uxt};
use sp_transaction_pool::{TransactionPool, MaintainedTransactionPool, TransactionSource};
use sp_runtime::generic::BlockId;
use sp_consensus::ImportedAux;
use sp_inherents::InherentDataProviders;
use sc_basic_authorship::ProposerFactory;
use sc_client_api::BlockBackend;

fn api() -> Arc<TestApi> {
	Arc::new(TestApi::empty())
}

const SOURCE: TransactionSource = TransactionSource::External;

#[tokio::test]
async fn instant_seal() {
	let builder = TestClientBuilder::new();
	let (client, select_chain) = builder.build_with_longest_chain();
	let client = Arc::new(client);
	let inherent_data_providers = InherentDataProviders::new();
	let spawner = sp_core::testing::TaskExecutor::new();
	let pool = Arc::new(BasicPool::with_revalidation_type(
		Options::default(), api(), None, RevalidationType::Full, spawner,
	));
	let env = ProposerFactory::new(
		client.clone(),
		pool.clone(),
		None,
	);
	// this test checks that blocks are created as soon as transactions are imported into the pool.
	let (sender, receiver) = futures::channel::oneshot::channel();
	let mut sender = Arc::new(Some(sender));
	let stream = pool.pool().validated_pool().import_notification_stream()
		.map(move |_| {
			// we're only going to submit one tx so this fn will only be called once.
			let mut_sender =  Arc::get_mut(&mut sender).unwrap();
			let sender = std::mem::take(mut_sender);
			EngineCommand::SealNewBlock {
				create_empty: false,
				finalize: true,
				parent_hash: None,
				sender
			}
		});
	let future = run_manual_seal(
		Box::new(client.clone()),
		env,
		client.clone(),
		pool.pool().clone(),
		stream,
		select_chain,
		inherent_data_providers,
	);
	thread::spawn(|| {
		let mut rt = tokio::runtime::Runtime::new().unwrap();
		// spawn the background authorship task
		rt.block_on(future);
	});
	// submit a transaction to pool.
	let result = pool.submit_one(&BlockId::Number(0), SOURCE, uxt(Alice, 0)).await;
	// assert that it was successfully imported
	assert!(result.is_ok());
	// assert that the background task returns ok
	let created_block = receiver.await.unwrap().unwrap();
	assert_eq!(
		created_block,
		CreatedBlock {
			hash: created_block.hash.clone(),
			aux: ImportedAux {
				header_only: false,
				clear_justification_requests: false,
				needs_justification: false,
				bad_justification: false,
				needs_finality_proof: false,
				is_new_best: true,
			}
		}
	);
	// assert that there's a new block in the db.
	assert!(client.header(&BlockId::Number(1)).unwrap().is_some())
}

#[tokio::test]
async fn manual_seal_and_finalization() {
	let builder = TestClientBuilder::new();
	let (client, select_chain) = builder.build_with_longest_chain();
	let client = Arc::new(client);
	let inherent_data_providers = InherentDataProviders::new();
	let spawner = sp_core::testing::TaskExecutor::new();
	let pool = Arc::new(BasicPool::with_revalidation_type(
		Options::default(), api(), None, RevalidationType::Full, spawner,
	));
	let env = ProposerFactory::new(
		client.clone(),
		pool.clone(),
		None,
	);
	// this test checks that blocks are created as soon as an engine command is sent over the stream.
	let (mut sink, stream) = futures::channel::mpsc::channel(1024);
	let future = run_manual_seal(
		Box::new(client.clone()),
		env,
		client.clone(),
		pool.pool().clone(),
		stream,
		select_chain,
		inherent_data_providers,
	);
	thread::spawn(|| {
		let mut rt = tokio::runtime::Runtime::new().unwrap();
		// spawn the background authorship task
		rt.block_on(future);
	});
	// submit a transaction to pool.
	let result = pool.submit_one(&BlockId::Number(0), SOURCE, uxt(Alice, 0)).await;
	// assert that it was successfully imported
	assert!(result.is_ok());
	let (tx, rx) = futures::channel::oneshot::channel();
	sink.send(EngineCommand::SealNewBlock {
		parent_hash: None,
		sender: Some(tx),
		create_empty: false,
		finalize: false,
	}).await.unwrap();
	let created_block = rx.await.unwrap().unwrap();

	// assert that the background task returns ok
	assert_eq!(
		created_block,
		CreatedBlock {
			hash: created_block.hash.clone(),
			aux: ImportedAux {
				header_only: false,
				clear_justification_requests: false,
				needs_justification: false,
				bad_justification: false,
				needs_finality_proof: false,
				is_new_best: true,
			}
		}
	);
	// assert that there's a new block in the db.
	let header = client.header(&BlockId::Number(1)).unwrap().unwrap();
	let (tx, rx) = futures::channel::oneshot::channel();
	sink.send(EngineCommand::FinalizeBlock {
		sender: Some(tx),
		hash: header.hash(),
		justification: None
	}).await.unwrap();
	// assert that the background task returns ok
	assert_eq!(rx.await.unwrap().unwrap(), ());
}

#[tokio::test]
async fn manual_seal_fork_blocks() {
	let builder = TestClientBuilder::new();
	let (client, select_chain) = builder.build_with_longest_chain();
	let client = Arc::new(client);
	let inherent_data_providers = InherentDataProviders::new();
	let pool_api = api();
	let spawner = sp_core::testing::TaskExecutor::new();
	let pool = Arc::new(BasicPool::with_revalidation_type(
		Options::default(), pool_api.clone(), None, RevalidationType::Full, spawner,
	));
	let env = ProposerFactory::new(
		client.clone(),
		pool.clone(),
		None,
	);
	// this test checks that blocks are created as soon as an engine command is sent over the stream.
	let (mut sink, stream) = futures::channel::mpsc::channel(1024);
	let future = run_manual_seal(
		Box::new(client.clone()),
		env,
		client.clone(),
		pool.pool().clone(),
		stream,
		select_chain,
		inherent_data_providers,
	);
	thread::spawn(|| {
		let mut rt = tokio::runtime::Runtime::new().unwrap();
		// spawn the background authorship task
		rt.block_on(future);
	});
	// submit a transaction to pool.
	let result = pool.submit_one(&BlockId::Number(0), SOURCE, uxt(Alice, 0)).await;
	// assert that it was successfully imported
	assert!(result.is_ok());

	let (tx, rx) = futures::channel::oneshot::channel();
	sink.send(EngineCommand::SealNewBlock {
		parent_hash: None,
		sender: Some(tx),
		create_empty: false,
		finalize: false,
	}).await.unwrap();
	let created_block = rx.await.unwrap().unwrap();
	pool_api.increment_nonce(Alice.into());

	// assert that the background task returns ok
	assert_eq!(
		created_block,
		CreatedBlock {
			hash: created_block.hash.clone(),
			aux: ImportedAux {
				header_only: false,
				clear_justification_requests: false,
				needs_justification: false,
				bad_justification: false,
				needs_finality_proof: false,
				is_new_best: true
			}
		}
	);
	let block = client.block(&BlockId::Number(1)).unwrap().unwrap().block;
	pool_api.add_block(block, true);
	assert!(pool.submit_one(&BlockId::Number(1), SOURCE, uxt(Alice, 1)).await.is_ok());

	let header = client.header(&BlockId::Number(1)).expect("db error").expect("imported above");
	pool.maintain(sp_transaction_pool::ChainEvent::NewBestBlock {
		hash: header.hash(),
		tree_route: None,
	}).await;

	let (tx1, rx1) = futures::channel::oneshot::channel();
	assert!(sink.send(EngineCommand::SealNewBlock {
		parent_hash: Some(created_block.hash),
		sender: Some(tx1),
		create_empty: false,
		finalize: false,
	}).await.is_ok());
	assert_matches::assert_matches!(
		rx1.await.expect("should be no error receiving"),
		Ok(_)
	);
	let block = client.block(&BlockId::Number(2)).unwrap().unwrap().block;
	pool_api.add_block(block, true);
	pool_api.increment_nonce(Alice.into());

	assert!(pool.submit_one(&BlockId::Number(1), SOURCE, uxt(Alice, 2)).await.is_ok());
	let (tx2, rx2) = futures::channel::oneshot::channel();
	assert!(sink.send(EngineCommand::SealNewBlock {
		parent_hash: Some(created_block.hash),
		sender: Some(tx2),
		create_empty: false,
		finalize: false,
	}).await.is_ok());
	let imported = rx2.await.unwrap().unwrap();
	// assert that fork block is in the db
	assert!(client.header(&BlockId::Hash(imported.hash)).unwrap().is_some())
}

#[tokio::test]
async fn heartbeat_stream_produce_block_regularly() {
	let builder = TestClientBuilder::new();
	let (client, select_chain) = builder.build_with_longest_chain();
	let client = Arc::new(client);
	let inherent_data_providers = InherentDataProviders::new();
	let spawner = sp_core::testing::TaskExecutor::new();
	let pool = Arc::new(BasicPool::with_revalidation_type(
		txpool::Options::default(), api(), None, RevalidationType::Full, spawner
	));
	let env = ProposerFactory::new(
		client.clone(),
		pool.clone(),
		None,
	);

	let (sender, receiver) = futures::channel::oneshot::channel();
	let mut sender = Arc::new(Some(sender));
	let cmds_stream = pool.pool().validated_pool().import_notification_stream()
		.map(move |_| {
			let mut_sender = Arc::get_mut(&mut sender).unwrap();
			let sender = std::mem::take(mut_sender);
			// Create a heartbeat_stream
			EngineCommand::<()>::SealNewBlock {
				create_empty: false,
				finalize: true,
				parent_hash: None,
				sender
			}
		});

	const BLOCK_TIMEOUT: u64 = 2;

	let hbo = HeartbeatOptions {
		timeout: BLOCK_TIMEOUT,
		min_blocktime: 1,
		finalize: false,
	};

	println!("get 10");

	let future = run_instant_seal(
		Box::new(client.clone()),
		env,
		client.clone(),
		pool.pool().clone(),
		select_chain,
		inherent_data_providers,
		false,
		Some(hbo)
	);

	println!("get 20");

	let sender = thread::spawn(|| {
		let mut rt = tokio::runtime::Runtime::new().unwrap();
		rt.block_on(future);
	});

	println!("get 30");

	// let created_block = receiver.await.unwrap().unwrap();
	// println!("{:?}", created_block);
	thread::sleep(Duration::from_secs(BLOCK_TIMEOUT));

	println!("get 35");

	let res = sender.join();

	println!("get 40");
}
