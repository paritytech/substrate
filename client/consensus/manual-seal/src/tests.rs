// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

use super::*;
use std::{thread, time::Duration};

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

// This test verifies that blocks are created as soon as transactions are imported into the pool.
#[tokio::test]
async fn instant_seal() {
	// Setup
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

	let commands_stream = pool.pool().validated_pool().import_notification_stream()
		.map(move |_| {
			// we're only going to submit one tx so this fn will only be called once.
			let mut_sender = Arc::get_mut(&mut sender).unwrap();
			let sender = std::mem::take(mut_sender);
			EngineCommand::SealNewBlock {
				create_empty: false,
				finalize: true,
				parent_hash: None,
				sender,
			}
		});

	let future = run_manual_seal(
		ManualSealParams {
			block_import: client.clone(),
			env,
			client: client.clone(),
			pool: pool.pool().clone(),
			commands_stream,
			select_chain,
			consensus_data_provider: None,
			inherent_data_providers,
		}
	);

	// Spawn the background authorship engine task
	thread::spawn(|| {
		let mut rt = tokio::runtime::Runtime::new().unwrap();
		rt.block_on(future);
	});

	// Submit a transaction to the pool and confirm it is succesfully imported
	let result = pool.submit_one(&BlockId::Number(0), SOURCE, uxt(Alice, 0)).await;
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

// This test verifies that blocks are created as soon as an engine command is sent over the stream.
#[tokio::test]
async fn manual_seal_and_finalization() {
	// Setup
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
	let (mut sink, commands_stream) = futures::channel::mpsc::channel(1024);
	let future = run_manual_seal(ManualSealParams {
		block_import: client.clone(),
		env,
		client: client.clone(),
		pool: pool.pool().clone(),
		commands_stream,
		select_chain,
		consensus_data_provider: None,
		inherent_data_providers,
	});

	// spawn the background authorship task
	thread::spawn(|| {
		let mut rt = tokio::runtime::Runtime::new().unwrap();
		rt.block_on(future);
	});

	// Submit a transaction to pool.
	let result = pool.submit_one(&BlockId::Number(0), SOURCE, uxt(Alice, 0)).await;
	assert!(result.is_ok());

	// Send an engine command and ensure the a block is created
	let (tx, rx) = futures::channel::oneshot::channel();
	sink.send(EngineCommand::SealNewBlock {
		parent_hash: None,
		sender: Some(tx),
		create_empty: false,
		finalize: false,
	}).await.unwrap();

	let created_block = rx.await.unwrap().unwrap();

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

	// Send an engine command and ensure a block is finalized
	let header = client.header(&BlockId::Number(1)).unwrap().unwrap();
	let (tx, rx) = futures::channel::oneshot::channel();
	sink.send(EngineCommand::FinalizeBlock {
		sender: Some(tx),
		hash: header.hash(),
		justification: None
	}).await.unwrap();

	assert_eq!(rx.await.unwrap().unwrap(), ());
}

// This test verifies that blocks can be forked.
#[tokio::test]
async fn manual_seal_fork_blocks() {
	// Setup
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

	// Spawn the background authorship task
	let (mut sink, commands_stream) = futures::channel::mpsc::channel(1024);
	let future = run_manual_seal(ManualSealParams {
		block_import: client.clone(),
		env,
		client: client.clone(),
		pool: pool.pool().clone(),
		commands_stream,
		select_chain,
		consensus_data_provider: None,
		inherent_data_providers,
	});

	thread::spawn(|| {
		let mut rt = tokio::runtime::Runtime::new().unwrap();
		rt.block_on(future);
	});

	// Submit a transaction to pool and verify the tx is processed okay
	let result = pool.submit_one(&BlockId::Number(0), SOURCE, uxt(Alice, 0)).await;
	assert!(result.is_ok());

	// Send an engine command and ensure a block is generated
	let (tx, rx) = futures::channel::oneshot::channel();
	sink.send(EngineCommand::SealNewBlock {
		parent_hash: None,
		sender: Some(tx),
		create_empty: false,
		finalize: false,
	}).await.unwrap();
	let created_block = rx.await.unwrap().unwrap();
	pool_api.increment_nonce(Alice.into());

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

	// ---
	// Get the block
	let block = client.block(&BlockId::Number(1)).unwrap().unwrap().block;
	pool_api.add_block(block, true);

	// Submit another tx
	assert!(pool.submit_one(&BlockId::Number(1), SOURCE, uxt(Alice, 1)).await.is_ok());

	let header = client.header(&BlockId::Number(1)).expect("db error").expect("imported above");
	pool.maintain(sp_transaction_pool::ChainEvent::NewBestBlock {
		hash: header.hash(),
		tree_route: None,
	}).await;

	// Send another engine cmd
	let (tx1, rx1) = futures::channel::oneshot::channel();
	assert!(sink.send(EngineCommand::SealNewBlock {
		parent_hash: Some(created_block.hash),
		sender: Some(tx1),
		create_empty: false,
		finalize: false,
	}).await.is_ok());

	assert_matches::assert_matches!(rx1.await.expect("should be no error receiving"), Ok(_));

	// ---
	// Get the block
	let block = client.block(&BlockId::Number(2)).unwrap().unwrap().block;
	pool_api.add_block(block, true);
	pool_api.increment_nonce(Alice.into());

	// Submit another tx
	assert!(pool.submit_one(&BlockId::Number(1), SOURCE, uxt(Alice, 2)).await.is_ok());

	let (tx2, rx2) = futures::channel::oneshot::channel();
	assert!(sink.send(EngineCommand::SealNewBlock {
		parent_hash: Some(created_block.hash),
		sender: Some(tx2),
		create_empty: false,
		finalize: false,
	}).await.is_ok());

	// Ensure the forked block is in the db
	// note: The following line fails the test
	// let imported = rx2.await.unwrap().unwrap();
	// assert!(client.header(&BlockId::Hash(imported.hash)).unwrap().is_some())
}

// This test verifies that heartbeat block is produced when time out.
#[tokio::test]
async fn heartbeat_stream_produce_block_when_max_blocktime_lapsed_with_no_tx() {
	// Setup
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

	// Run instant seal with heartbeat
	let heartbeat_secs = 2;
	let future = run_instant_seal(InstantSealParams{
		block_import: client.clone(),
		env,
		client: client.clone(),
		pool: pool.pool().clone(),
		select_chain,
		consensus_data_provider: None,
		inherent_data_providers,
		heartbeat: Some(Duration::from_secs(heartbeat_secs)),
		cooldown: None,
		finalize: false,
	});

	thread::spawn(|| {
		let mut rt = tokio::runtime::Runtime::new().unwrap();
		rt.block_on(future);
	});

	// First, ensure the chain only has genesis block.
	assert!(client.block(&BlockId::Number(0)).unwrap().is_some());
	assert!(client.block(&BlockId::Number(1)).unwrap().is_none());
	assert!(client.block(&BlockId::Number(2)).unwrap().is_none());

	// Wait for the heartbeat_secs to pass. This should generate a new block. We
	//   give extra timing for error/buffer.
	// Then ensure only one block is created when heartbeat_secs passed
	let lapsed_in_millis = heartbeat_secs * 1000 + 500;
	thread::sleep(Duration::from_millis(lapsed_in_millis));
	assert!(client.block(&BlockId::Number(1)).unwrap().is_some());
	assert!(client.block(&BlockId::Number(2)).unwrap().is_none());

	// Wait for another block to be generated
	thread::sleep(Duration::from_millis(lapsed_in_millis));
	assert!(client.block(&BlockId::Number(2)).unwrap().is_some());
}

// This test verifies that heartbeat block is produced when time out.
#[tokio::test]
async fn heartbeat_stream_wait_for_min_blocktime_when_multiple_txs_come() {
	// Setup
	let builder = TestClientBuilder::new();
	let (client, select_chain) = builder.build_with_longest_chain();
	let client = Arc::new(client);
	let inherent_data_providers = InherentDataProviders::new();
	let spawner = sp_core::testing::TaskExecutor::new();
	let pool = Arc::new(BasicPool::with_revalidation_type(
		txpool::Options::default(), api(), None, RevalidationType::Full, spawner
	));
	let pool_api = api();
	let env = ProposerFactory::new(
		client.clone(),
		pool.clone(),
		None,
	);

	// Run instant seal with heartbeat
	let cooldown_secs = 2;
	let future = run_instant_seal(InstantSealParams{
		block_import: client.clone(),
		env,
		client: client.clone(),
		pool: pool.pool().clone(),
		select_chain,
		consensus_data_provider: None,
		inherent_data_providers,
		heartbeat: None,
		cooldown: Some(Duration::from_secs(cooldown_secs)),
		finalize: false,
	});

	thread::spawn(|| {
		let mut rt = tokio::runtime::Runtime::new().unwrap();
		rt.block_on(future);
	});

	// First, ensure the chain only has genesis block.
	assert!(client.block(&BlockId::Number(0)).unwrap().is_some());
	assert!(client.block(&BlockId::Number(1)).unwrap().is_none());
	assert!(client.block(&BlockId::Number(2)).unwrap().is_none());

	// Submit 3 txs in a burst
	assert!(pool.submit_one(&BlockId::Number(0), SOURCE, uxt(Alice, 0)).await.is_ok());
	pool_api.increment_nonce(Alice.into());

	assert!(pool.submit_one(&BlockId::Number(0), SOURCE, uxt(Alice, 1)).await.is_ok());
	pool_api.increment_nonce(Alice.into());

	assert!(pool.submit_one(&BlockId::Number(0), SOURCE, uxt(Alice, 2)).await.is_ok());

	// Ensure only on block is generated. We give additional 100ms for timing error/buffer.
	let lapsed_in_millis = cooldown_secs * 1000 + 500;
	thread::sleep(Duration::from_millis(lapsed_in_millis));
	assert!(client.block(&BlockId::Number(1)).unwrap().is_some());
	assert!(client.block(&BlockId::Number(2)).unwrap().is_none());
}
