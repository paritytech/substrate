// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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
use prometheus_endpoint::Registry;
use sc_client_api::backend::{Backend as ClientBackend, Finalizer};
use sc_consensus::{
	block_import::{BlockImport, BlockImportParams, ForkChoiceStrategy},
	import_queue::{BasicQueue, BoxBlockImport, Verifier},
};
use sp_blockchain::HeaderBackend;
use sp_consensus::{CacheKeyId, Environment, Proposer, SelectChain};
use sp_inherents::CreateInherentDataProviders;
use sp_runtime::{traits::Block as BlockT, ConsensusEngineId};
use std::{marker::PhantomData, sync::Arc};

mod error;
mod finalize_block;
mod seal_block;

pub mod consensus;
pub mod rpc;

pub use self::{
	consensus::ConsensusDataProvider,
	error::Error,
	finalize_block::{finalize_block, FinalizeBlockParams},
	rpc::{CreatedBlock, EngineCommand},
	seal_block::{seal_block, SealBlockParams, MAX_PROPOSAL_DURATION},
};
use sc_transaction_pool_api::TransactionPool;
use sp_api::{ProvideRuntimeApi, TransactionFor};

const LOG_TARGET: &str = "manual-seal";

/// The `ConsensusEngineId` of Manual Seal.
pub const MANUAL_SEAL_ENGINE_ID: ConsensusEngineId = [b'm', b'a', b'n', b'l'];

/// The verifier for the manual seal engine; instantly finalizes.
struct ManualSealVerifier;

#[async_trait::async_trait]
impl<B: BlockT> Verifier<B> for ManualSealVerifier {
	async fn verify(
		&mut self,
		mut block: BlockImportParams<B, ()>,
	) -> Result<(BlockImportParams<B, ()>, Option<Vec<(CacheKeyId, Vec<u8>)>>), String> {
		block.finalized = false;
		block.fork_choice = Some(ForkChoiceStrategy::LongestChain);
		Ok((block, None))
	}
}

/// Instantiate the import queue for the manual seal consensus engine.
pub fn import_queue<Block, Transaction>(
	block_import: BoxBlockImport<Block, Transaction>,
	spawner: &impl sp_core::traits::SpawnEssentialNamed,
	registry: Option<&Registry>,
) -> BasicQueue<Block, Transaction>
where
	Block: BlockT,
	Transaction: Send + Sync + 'static,
{
	BasicQueue::new(ManualSealVerifier, block_import, None, spawner, registry)
}

/// Params required to start the instant sealing authorship task.
pub struct ManualSealParams<B: BlockT, BI, E, C: ProvideRuntimeApi<B>, TP, SC, CS, CIDP, P> {
	/// Block import instance for well. importing blocks.
	pub block_import: BI,

	/// The environment we are producing blocks for.
	pub env: E,

	/// Client instance
	pub client: Arc<C>,

	/// Shared reference to the transaction pool.
	pub pool: Arc<TP>,

	/// Stream<Item = EngineCommands>, Basically the receiving end of a channel for sending
	/// commands to the authorship task.
	pub commands_stream: CS,

	/// SelectChain strategy.
	pub select_chain: SC,

	/// Digest provider for inclusion in blocks.
	pub consensus_data_provider:
		Option<Box<dyn ConsensusDataProvider<B, Proof = P, Transaction = TransactionFor<C, B>>>>,

	/// Something that can create the inherent data providers.
	pub create_inherent_data_providers: CIDP,
}

/// Params required to start the manual sealing authorship task.
pub struct InstantSealParams<B: BlockT, BI, E, C: ProvideRuntimeApi<B>, TP, SC, CIDP, P> {
	/// Block import instance for well. importing blocks.
	pub block_import: BI,

	/// The environment we are producing blocks for.
	pub env: E,

	/// Client instance
	pub client: Arc<C>,

	/// Shared reference to the transaction pool.
	pub pool: Arc<TP>,

	/// SelectChain strategy.
	pub select_chain: SC,

	/// Digest provider for inclusion in blocks.
	pub consensus_data_provider:
		Option<Box<dyn ConsensusDataProvider<B, Proof = P, Transaction = TransactionFor<C, B>>>>,

	/// Something that can create the inherent data providers.
	pub create_inherent_data_providers: CIDP,
}

/// Creates the background authorship task for the manual seal engine.
pub async fn run_manual_seal<B, BI, CB, E, C, TP, SC, CS, CIDP, P>(
	ManualSealParams {
		mut block_import,
		mut env,
		client,
		pool,
		mut commands_stream,
		select_chain,
		consensus_data_provider,
		create_inherent_data_providers,
	}: ManualSealParams<B, BI, E, C, TP, SC, CS, CIDP, P>,
) where
	B: BlockT + 'static,
	BI: BlockImport<B, Error = sp_consensus::Error, Transaction = sp_api::TransactionFor<C, B>>
		+ Send
		+ Sync
		+ 'static,
	C: HeaderBackend<B> + Finalizer<B, CB> + ProvideRuntimeApi<B> + 'static,
	CB: ClientBackend<B> + 'static,
	E: Environment<B> + 'static,
	E::Proposer: Proposer<B, Proof = P, Transaction = TransactionFor<C, B>>,
	CS: Stream<Item = EngineCommand<<B as BlockT>::Hash>> + Unpin + 'static,
	SC: SelectChain<B> + 'static,
	TransactionFor<C, B>: 'static,
	TP: TransactionPool<Block = B>,
	CIDP: CreateInherentDataProviders<B, ()>,
	P: Send + Sync + 'static,
{
	while let Some(command) = commands_stream.next().await {
		match command {
			EngineCommand::SealNewBlock { create_empty, finalize, parent_hash, sender } => {
				seal_block(SealBlockParams {
					sender,
					parent_hash,
					finalize,
					create_empty,
					env: &mut env,
					select_chain: &select_chain,
					block_import: &mut block_import,
					consensus_data_provider: consensus_data_provider.as_deref(),
					pool: pool.clone(),
					client: client.clone(),
					create_inherent_data_providers: &create_inherent_data_providers,
				})
				.await;
			},
			EngineCommand::FinalizeBlock { hash, sender, justification } => {
				let justification = justification.map(|j| (MANUAL_SEAL_ENGINE_ID, j));
				finalize_block(FinalizeBlockParams {
					hash,
					sender,
					justification,
					finalizer: client.clone(),
					_phantom: PhantomData,
				})
				.await
			},
		}
	}
}

/// runs the background authorship task for the instant seal engine.
/// instant-seal creates a new block for every transaction imported into
/// the transaction pool.
pub async fn run_instant_seal<B, BI, CB, E, C, TP, SC, CIDP, P>(
	InstantSealParams {
		block_import,
		env,
		client,
		pool,
		select_chain,
		consensus_data_provider,
		create_inherent_data_providers,
	}: InstantSealParams<B, BI, E, C, TP, SC, CIDP, P>,
) where
	B: BlockT + 'static,
	BI: BlockImport<B, Error = sp_consensus::Error, Transaction = sp_api::TransactionFor<C, B>>
		+ Send
		+ Sync
		+ 'static,
	C: HeaderBackend<B> + Finalizer<B, CB> + ProvideRuntimeApi<B> + 'static,
	CB: ClientBackend<B> + 'static,
	E: Environment<B> + 'static,
	E::Proposer: Proposer<B, Proof = P, Transaction = TransactionFor<C, B>>,
	SC: SelectChain<B> + 'static,
	TransactionFor<C, B>: 'static,
	TP: TransactionPool<Block = B>,
	CIDP: CreateInherentDataProviders<B, ()>,
	P: Send + Sync + 'static,
{
	// instant-seal creates blocks as soon as transactions are imported
	// into the transaction pool.
	let commands_stream = pool.import_notification_stream().map(|_| EngineCommand::SealNewBlock {
		create_empty: false,
		finalize: false,
		parent_hash: None,
		sender: None,
	});

	run_manual_seal(ManualSealParams {
		block_import,
		env,
		client,
		pool,
		commands_stream,
		select_chain,
		consensus_data_provider,
		create_inherent_data_providers,
	})
	.await
}

/// Runs the background authorship task for the instant seal engine.
/// instant-seal creates a new block for every transaction imported into
/// the transaction pool.
///
/// This function will finalize the block immediately as well. If you don't
/// want this behavior use `run_instant_seal` instead.
pub async fn run_instant_seal_and_finalize<B, BI, CB, E, C, TP, SC, CIDP, P>(
	InstantSealParams {
		block_import,
		env,
		client,
		pool,
		select_chain,
		consensus_data_provider,
		create_inherent_data_providers,
	}: InstantSealParams<B, BI, E, C, TP, SC, CIDP, P>,
) where
	B: BlockT + 'static,
	BI: BlockImport<B, Error = sp_consensus::Error, Transaction = sp_api::TransactionFor<C, B>>
		+ Send
		+ Sync
		+ 'static,
	C: HeaderBackend<B> + Finalizer<B, CB> + ProvideRuntimeApi<B> + 'static,
	CB: ClientBackend<B> + 'static,
	E: Environment<B> + 'static,
	E::Proposer: Proposer<B, Proof = P, Transaction = TransactionFor<C, B>>,
	SC: SelectChain<B> + 'static,
	TransactionFor<C, B>: 'static,
	TP: TransactionPool<Block = B>,
	CIDP: CreateInherentDataProviders<B, ()>,
	P: Send + Sync + 'static,
{
	// Creates and finalizes blocks as soon as transactions are imported
	// into the transaction pool.
	let commands_stream = pool.import_notification_stream().map(|_| EngineCommand::SealNewBlock {
		create_empty: false,
		finalize: true,
		parent_hash: None,
		sender: None,
	});

	run_manual_seal(ManualSealParams {
		block_import,
		env,
		client,
		pool,
		commands_stream,
		select_chain,
		consensus_data_provider,
		create_inherent_data_providers,
	})
	.await
}

#[cfg(test)]
mod tests {
	use super::*;
	use sc_basic_authorship::ProposerFactory;
	use sc_consensus::ImportedAux;
	use sc_transaction_pool::{BasicPool, FullChainApi, Options, RevalidationType};
	use sc_transaction_pool_api::{MaintainedTransactionPool, TransactionPool, TransactionSource};
	use sp_inherents::InherentData;
	use sp_runtime::generic::{BlockId, Digest, DigestItem};
	use substrate_test_runtime_client::{
		AccountKeyring::*, DefaultTestClientBuilderExt, TestClientBuilder, TestClientBuilderExt,
	};
	use substrate_test_runtime_transaction_pool::{uxt, TestApi};

	fn api() -> Arc<TestApi> {
		Arc::new(TestApi::empty())
	}

	const SOURCE: TransactionSource = TransactionSource::External;

	struct TestDigestProvider<C> {
		_client: Arc<C>,
	}
	impl<B, C> ConsensusDataProvider<B> for TestDigestProvider<C>
	where
		B: BlockT,
		C: ProvideRuntimeApi<B> + Send + Sync,
	{
		type Transaction = TransactionFor<C, B>;
		type Proof = ();

		fn create_digest(
			&self,
			_parent: &B::Header,
			_inherents: &InherentData,
		) -> Result<Digest, Error> {
			Ok(Digest { logs: vec![] })
		}

		fn append_block_import(
			&self,
			_parent: &B::Header,
			params: &mut BlockImportParams<B, Self::Transaction>,
			_inherents: &InherentData,
			_proof: Self::Proof,
		) -> Result<(), Error> {
			params.post_digests.push(DigestItem::Other(vec![1]));
			Ok(())
		}
	}

	#[tokio::test]
	async fn instant_seal() {
		let builder = TestClientBuilder::new();
		let (client, select_chain) = builder.build_with_longest_chain();
		let client = Arc::new(client);
		let spawner = sp_core::testing::TaskExecutor::new();
		let genesis_hash = client.info().genesis_hash;
		let pool = Arc::new(BasicPool::with_revalidation_type(
			Options::default(),
			true.into(),
			api(),
			None,
			RevalidationType::Full,
			spawner.clone(),
			0,
			genesis_hash,
			genesis_hash,
		));
		let env = ProposerFactory::new(spawner.clone(), client.clone(), pool.clone(), None, None);
		// this test checks that blocks are created as soon as transactions are imported into the
		// pool.
		let (sender, receiver) = futures::channel::oneshot::channel();
		let mut sender = Arc::new(Some(sender));
		let commands_stream =
			pool.pool().validated_pool().import_notification_stream().map(move |_| {
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
		let future = run_manual_seal(ManualSealParams {
			block_import: client.clone(),
			env,
			client: client.clone(),
			pool: pool.clone(),
			commands_stream,
			select_chain,
			create_inherent_data_providers: |_, _| async { Ok(()) },
			consensus_data_provider: None,
		});
		std::thread::spawn(|| {
			let rt = tokio::runtime::Runtime::new().unwrap();
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
				hash: created_block.hash,
				aux: ImportedAux {
					header_only: false,
					clear_justification_requests: false,
					needs_justification: false,
					bad_justification: false,
					is_new_best: true,
				}
			}
		);
		// assert that there's a new block in the db.
		assert!(client.header(created_block.hash).unwrap().is_some());
		assert_eq!(client.header(created_block.hash).unwrap().unwrap().number, 1)
	}

	#[tokio::test]
	async fn manual_seal_and_finalization() {
		let builder = TestClientBuilder::new();
		let (client, select_chain) = builder.build_with_longest_chain();
		let client = Arc::new(client);
		let spawner = sp_core::testing::TaskExecutor::new();
		let genesis_hash = client.info().genesis_hash;
		let pool = Arc::new(BasicPool::with_revalidation_type(
			Options::default(),
			true.into(),
			api(),
			None,
			RevalidationType::Full,
			spawner.clone(),
			0,
			genesis_hash,
			genesis_hash,
		));
		let env = ProposerFactory::new(spawner.clone(), client.clone(), pool.clone(), None, None);
		// this test checks that blocks are created as soon as an engine command is sent over the
		// stream.
		let (mut sink, commands_stream) = futures::channel::mpsc::channel(1024);
		let future = run_manual_seal(ManualSealParams {
			block_import: client.clone(),
			env,
			client: client.clone(),
			pool: pool.clone(),
			commands_stream,
			select_chain,
			consensus_data_provider: None,
			create_inherent_data_providers: |_, _| async { Ok(()) },
		});
		std::thread::spawn(|| {
			let rt = tokio::runtime::Runtime::new().unwrap();
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
		})
		.await
		.unwrap();
		let created_block = rx.await.unwrap().unwrap();

		// assert that the background task returns ok
		assert_eq!(
			created_block,
			CreatedBlock {
				hash: created_block.hash,
				aux: ImportedAux {
					header_only: false,
					clear_justification_requests: false,
					needs_justification: false,
					bad_justification: false,
					is_new_best: true,
				}
			}
		);
		// assert that there's a new block in the db.
		let header = client.header(created_block.hash).unwrap().unwrap();
		let (tx, rx) = futures::channel::oneshot::channel();
		sink.send(EngineCommand::FinalizeBlock {
			sender: Some(tx),
			hash: header.hash(),
			justification: None,
		})
		.await
		.unwrap();
		// check that the background task returns ok:
		rx.await.unwrap().unwrap();
	}

	#[tokio::test]
	async fn manual_seal_fork_blocks() {
		let builder = TestClientBuilder::new();
		let (client, select_chain) = builder.build_with_longest_chain();
		let client = Arc::new(client);
		let pool_api = Arc::new(FullChainApi::new(
			client.clone(),
			None,
			&sp_core::testing::TaskExecutor::new(),
		));
		let spawner = sp_core::testing::TaskExecutor::new();
		let genesis_hash = client.info().genesis_hash;
		let pool = Arc::new(BasicPool::with_revalidation_type(
			Options::default(),
			true.into(),
			pool_api.clone(),
			None,
			RevalidationType::Full,
			spawner.clone(),
			0,
			genesis_hash,
			genesis_hash,
		));
		let env = ProposerFactory::new(spawner.clone(), client.clone(), pool.clone(), None, None);
		// this test checks that blocks are created as soon as an engine command is sent over the
		// stream.
		let (mut sink, commands_stream) = futures::channel::mpsc::channel(1024);
		let future = run_manual_seal(ManualSealParams {
			block_import: client.clone(),
			env,
			client: client.clone(),
			pool: pool.clone(),
			commands_stream,
			select_chain,
			consensus_data_provider: None,
			create_inherent_data_providers: |_, _| async { Ok(()) },
		});
		std::thread::spawn(|| {
			let rt = tokio::runtime::Runtime::new().unwrap();
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
		})
		.await
		.unwrap();
		let created_block = rx.await.unwrap().unwrap();

		// assert that the background task returns ok
		assert_eq!(
			created_block,
			CreatedBlock {
				hash: created_block.hash,
				aux: ImportedAux {
					header_only: false,
					clear_justification_requests: false,
					needs_justification: false,
					bad_justification: false,
					is_new_best: true
				}
			}
		);

		assert!(pool.submit_one(&BlockId::Number(1), SOURCE, uxt(Alice, 1)).await.is_ok());

		let header = client.header(created_block.hash).expect("db error").expect("imported above");
		assert_eq!(header.number, 1);
		pool.maintain(sc_transaction_pool_api::ChainEvent::NewBestBlock {
			hash: header.hash(),
			tree_route: None,
		})
		.await;

		let (tx1, rx1) = futures::channel::oneshot::channel();
		assert!(sink
			.send(EngineCommand::SealNewBlock {
				parent_hash: Some(created_block.hash),
				sender: Some(tx1),
				create_empty: false,
				finalize: false,
			})
			.await
			.is_ok());
		assert_matches::assert_matches!(rx1.await.expect("should be no error receiving"), Ok(_));

		assert!(pool.submit_one(&BlockId::Number(1), SOURCE, uxt(Bob, 0)).await.is_ok());
		let (tx2, rx2) = futures::channel::oneshot::channel();
		assert!(sink
			.send(EngineCommand::SealNewBlock {
				parent_hash: Some(created_block.hash),
				sender: Some(tx2),
				create_empty: false,
				finalize: false,
			})
			.await
			.is_ok());
		let imported = rx2.await.unwrap().unwrap();
		// assert that fork block is in the db
		assert!(client.header(imported.hash).unwrap().is_some())
	}

	#[tokio::test]
	async fn manual_seal_post_hash() {
		let builder = TestClientBuilder::new();
		let (client, select_chain) = builder.build_with_longest_chain();
		let client = Arc::new(client);
		let spawner = sp_core::testing::TaskExecutor::new();
		let genesis_hash = client.header(client.info().genesis_hash).unwrap().unwrap().hash();
		let pool = Arc::new(BasicPool::with_revalidation_type(
			Options::default(),
			true.into(),
			api(),
			None,
			RevalidationType::Full,
			spawner.clone(),
			0,
			genesis_hash,
			genesis_hash,
		));
		let env = ProposerFactory::new(spawner.clone(), client.clone(), pool.clone(), None, None);

		let (mut sink, commands_stream) = futures::channel::mpsc::channel(1024);
		let future = run_manual_seal(ManualSealParams {
			block_import: client.clone(),
			env,
			client: client.clone(),
			pool: pool.clone(),
			commands_stream,
			select_chain,
			// use a provider that pushes some post digest data
			consensus_data_provider: Some(Box::new(TestDigestProvider { _client: client.clone() })),
			create_inherent_data_providers: |_, _| async { Ok(()) },
		});
		std::thread::spawn(|| {
			let rt = tokio::runtime::Runtime::new().unwrap();
			rt.block_on(future);
		});
		let (tx, rx) = futures::channel::oneshot::channel();
		sink.send(EngineCommand::SealNewBlock {
			parent_hash: None,
			sender: Some(tx),
			create_empty: true,
			finalize: false,
		})
		.await
		.unwrap();
		let created_block = rx.await.unwrap().unwrap();

		// assert that the background task returned the actual header hash
		let header = client.header(created_block.hash).unwrap().unwrap();
		assert_eq!(header.number, 1);
	}
}
