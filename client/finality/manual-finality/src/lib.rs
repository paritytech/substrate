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

//! A manual sealing engine: the engine listens for rpc calls to seal blocks and create forks.
//! This is suitable for a testing environment.

use futures::prelude::*;
use sp_consensus::{
	Environment, Proposer, ForkChoiceStrategy, BlockImportParams, BlockOrigin, SelectChain,
	import_queue::{BasicQueue, CacheKeyId, Verifier, BoxBlockImport},
};
use sp_blockchain::HeaderBackend;
use sp_inherents::InherentDataProviders;
use sp_runtime::{traits::Block as BlockT, Justification};
use sc_client_api::backend::{Backend as ClientBackend, Finalizer};
use sc_transaction_pool::txpool;
use std::{sync::Arc, marker::PhantomData};
use prometheus_endpoint::Registry;

mod error;
mod finalize_block;
mod seal_new_block;
pub mod rpc;

use self::{
	finalize_block::{finalize_block, FinalizeBlockParams},
	seal_new_block::{seal_new_block, SealBlockParams},
};
pub use self::{
	error::Error,
	rpc::{EngineCommand, CreatedBlock},
};

/// The verifier for the manual seal engine; instantly finalizes.
struct ManualSealVerifier;

impl<B: BlockT> Verifier<B> for ManualSealVerifier {
	fn verify(
		&mut self,
		origin: BlockOrigin,
		header: B::Header,
		justification: Option<Justification>,
		body: Option<Vec<B::Extrinsic>>,
	) -> Result<(BlockImportParams<B, ()>, Option<Vec<(CacheKeyId, Vec<u8>)>>), String> {
		let mut import_params = BlockImportParams::new(origin, header);
		import_params.justification = justification;
		import_params.body = body;
		import_params.finalized = false;
		import_params.fork_choice = Some(ForkChoiceStrategy::LongestChain);

		Ok((import_params, None))
	}
}

/// Instantiate the import queue for the manual seal consensus engine.
pub fn import_queue<Block, Transaction>(
	block_import: BoxBlockImport<Block, Transaction>,
	spawner: &impl sp_core::traits::SpawnNamed,
	registry: Option<&Registry>,
) -> BasicQueue<Block, Transaction>
	where
		Block: BlockT,
		Transaction: Send + Sync + 'static,
{
	BasicQueue::new(
		ManualSealVerifier,
		block_import,
		None,
		None,
		spawner,
		registry,
	)
}

/// Creates the background authorship task for the manual seal engine.
pub async fn run_manual_seal<B, CB, E, C, A, SC, S, T>(
	mut block_import: BoxBlockImport<B, T>,
	mut env: E,
	client: Arc<C>,
	pool: Arc<txpool::Pool<A>>,
	mut commands_stream: S,
	select_chain: SC,
	inherent_data_providers: InherentDataProviders,
)
	where
		A: txpool::ChainApi<Block=B> + 'static,
		B: BlockT + 'static,
		C: HeaderBackend<B> + Finalizer<B, CB> + 'static,
		CB: ClientBackend<B> + 'static,
		E: Environment<B> + 'static,
		E::Error: std::fmt::Display,
		<E::Proposer as Proposer<B>>::Error: std::fmt::Display,
		S: Stream<Item=EngineCommand<<B as BlockT>::Hash>> + Unpin + 'static,
		SC: SelectChain<B> + 'static,
{
	while let Some(command) = commands_stream.next().await {
		match command {
			EngineCommand::SealNewBlock {
				create_empty,
				finalize,
				parent_hash,
				sender,
			} => {
				seal_new_block(
					SealBlockParams {
						sender,
						parent_hash,
						finalize,
						create_empty,
						env: &mut env,
						select_chain: &select_chain,
						block_import: &mut block_import,
						inherent_data_provider: &inherent_data_providers,
						pool: pool.clone(),
						client: client.clone(),
					}
				).await;
			}
			EngineCommand::FinalizeBlock { hash, sender, justification } => {
				finalize_block(
					FinalizeBlockParams {
						hash,
						sender,
						justification,
						finalizer: client.clone(),
						_phantom: PhantomData,
					}
				).await
			}
		}
	}
}

/// runs the background authorship task for the instant seal engine.
/// instant-seal creates a new block for every transaction imported into
/// the transaction pool.
pub async fn run_instant_seal<B, CB, E, C, A, SC, T>(
	block_import: BoxBlockImport<B, T>,
	env: E,
	client: Arc<C>,
	pool: Arc<txpool::Pool<A>>,
	select_chain: SC,
	inherent_data_providers: InherentDataProviders,
)
	where
		A: txpool::ChainApi<Block=B> + 'static,
		B: BlockT + 'static,
		C: HeaderBackend<B> + Finalizer<B, CB> + 'static,
		CB: ClientBackend<B> + 'static,
		E: Environment<B> + 'static,
		E::Error: std::fmt::Display,
		<E::Proposer as Proposer<B>>::Error: std::fmt::Display,
		SC: SelectChain<B> + 'static
{
	// instant-seal creates blocks as soon as transactions are imported
	// into the transaction pool.
	let commands_stream = pool.validated_pool()
		.import_notification_stream()
		.map(|_| {
			EngineCommand::SealNewBlock {
				create_empty: false,
				finalize: false,
				parent_hash: None,
				sender: None,
			}
		});

	run_manual_seal(
		block_import,
		env,
		client,
		pool,
		commands_stream,
		select_chain,
		inherent_data_providers,
	).await
}

#[cfg(test)]
mod tests {
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
		std::thread::spawn(|| {
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
		std::thread::spawn(|| {
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
		std::thread::spawn(|| {
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
}
