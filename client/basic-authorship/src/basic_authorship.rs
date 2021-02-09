// This file is part of Substrate.

// Copyright (C) 2018-2021 Parity Technologies (UK) Ltd.
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

//! A consensus proposer for "basic" chains which use the primitive inherent-data.

// FIXME #1021 move this into sp-consensus

use std::{pin::Pin, time, sync::Arc};
use sc_client_api::backend;
use codec::Decode;
use sp_consensus::{evaluation, Proposal, RecordProof};
use sp_core::traits::SpawnNamed;
use sp_inherents::InherentData;
use log::{error, info, debug, trace, warn};
use sp_runtime::{
	generic::BlockId,
	traits::{Block as BlockT, Hash as HashT, Header as HeaderT, DigestFor, BlakeTwo256},
};
use sp_transaction_pool::{TransactionPool, InPoolTransaction};
use sc_telemetry::{telemetry, CONSENSUS_INFO};
use sc_block_builder::{BlockBuilderApi, BlockBuilderProvider};
use sp_api::{ProvideRuntimeApi, ApiExt};
use futures::{future, future::{Future, FutureExt}, channel::oneshot, select};
use sp_blockchain::{HeaderBackend, ApplyExtrinsicFailed::Validity, Error::ApplyExtrinsicFailed};
use std::marker::PhantomData;

use prometheus_endpoint::Registry as PrometheusRegistry;
use sc_proposer_metrics::MetricsLink as PrometheusMetrics;

/// Default maximum block size in bytes used by [`Proposer`].
///
/// Can be overwritten by [`ProposerFactory::set_maximum_block_size`].
///
/// Be aware that there is also an upper packet size on what the networking code
/// will accept. If the block doesn't fit in such a package, it can not be
/// transferred to other nodes.
pub const DEFAULT_MAX_BLOCK_SIZE: usize = 4 * 1024 * 1024 + 512;

/// Proposer factory.
pub struct ProposerFactory<A, B, C> {
	spawn_handle: Box<dyn SpawnNamed>,
	/// The client instance.
	client: Arc<C>,
	/// The transaction pool.
	transaction_pool: Arc<A>,
	/// Prometheus Link,
	metrics: PrometheusMetrics,
	/// phantom member to pin the `Backend` type.
	_phantom: PhantomData<B>,
	max_block_size: usize,
}

impl<A, B, C> ProposerFactory<A, B, C> {
	pub fn new(
		spawn_handle: impl SpawnNamed + 'static,
		client: Arc<C>,
		transaction_pool: Arc<A>,
		prometheus: Option<&PrometheusRegistry>,
	) -> Self {
		ProposerFactory {
			spawn_handle: Box::new(spawn_handle),
			client,
			transaction_pool,
			metrics: PrometheusMetrics::new(prometheus),
			_phantom: PhantomData,
			max_block_size: DEFAULT_MAX_BLOCK_SIZE,
		}
	}

	/// Set the maximum block size in bytes.
	///
	/// The default value for the maximum block size is:
	/// [`DEFAULT_MAX_BLOCK_SIZE`].
	pub fn set_maximum_block_size(&mut self, size: usize) {
		self.max_block_size = size;
	}
}

impl<B, Block, C, A> ProposerFactory<A, B, C>
	where
		A: TransactionPool<Block = Block> + 'static,
		B: backend::Backend<Block> + Send + Sync + 'static,
		Block: BlockT,
		C: BlockBuilderProvider<B, Block, C> + HeaderBackend<Block> + ProvideRuntimeApi<Block>
			+ Send + Sync + 'static,
		C::Api: ApiExt<Block, StateBackend = backend::StateBackendFor<B, Block>>
			+ BlockBuilderApi<Block, Error = sp_blockchain::Error>,
{
	pub fn init_with_now(
		&mut self,
		parent_header: &<Block as BlockT>::Header,
		now: Box<dyn Fn() -> time::Instant + Send + Sync>,
	) -> Proposer<B, Block, C, A> {
		let parent_hash = parent_header.hash();

		let id = BlockId::hash(parent_hash);

		info!("🙌 Starting consensus session on top of parent {:?}", parent_hash);

		let proposer = Proposer {
			spawn_handle: self.spawn_handle.clone(),
			client: self.client.clone(),
			parent_hash,
			parent_id: id,
			parent_number: *parent_header.number(),
			transaction_pool: self.transaction_pool.clone(),
			now,
			metrics: self.metrics.clone(),
			_phantom: PhantomData,
			max_block_size: self.max_block_size,
		};

		proposer
	}
}

impl<A, B, Block, C> sp_consensus::Environment<Block> for
	ProposerFactory<A, B, C>
		where
			A: TransactionPool<Block = Block> + 'static,
			B: backend::Backend<Block> + Send + Sync + 'static,
			Block: BlockT,
			C: BlockBuilderProvider<B, Block, C> + HeaderBackend<Block> + ProvideRuntimeApi<Block>
				+ Send + Sync + 'static,
			C::Api: ApiExt<Block, StateBackend = backend::StateBackendFor<B, Block>>
				+ BlockBuilderApi<Block, Error = sp_blockchain::Error>,
{
	type CreateProposer = future::Ready<Result<Self::Proposer, Self::Error>>;
	type Proposer = Proposer<B, Block, C, A>;
	type Error = sp_blockchain::Error;

	fn init(
		&mut self,
		parent_header: &<Block as BlockT>::Header,
	) -> Self::CreateProposer {
		future::ready(Ok(self.init_with_now(parent_header, Box::new(time::Instant::now))))
	}
}

/// The proposer logic.
pub struct Proposer<B, Block: BlockT, C, A: TransactionPool> {
	spawn_handle: Box<dyn SpawnNamed>,
	client: Arc<C>,
	parent_hash: <Block as BlockT>::Hash,
	parent_id: BlockId<Block>,
	parent_number: <<Block as BlockT>::Header as HeaderT>::Number,
	transaction_pool: Arc<A>,
	now: Box<dyn Fn() -> time::Instant + Send + Sync>,
	metrics: PrometheusMetrics,
	_phantom: PhantomData<B>,
	max_block_size: usize,
}

impl<A, B, Block, C> sp_consensus::Proposer<Block> for
	Proposer<B, Block, C, A>
		where
			A: TransactionPool<Block = Block> + 'static,
			B: backend::Backend<Block> + Send + Sync + 'static,
			Block: BlockT,
			C: BlockBuilderProvider<B, Block, C> + HeaderBackend<Block> + ProvideRuntimeApi<Block>
				+ Send + Sync + 'static,
			C::Api: ApiExt<Block, StateBackend = backend::StateBackendFor<B, Block>>
				+ BlockBuilderApi<Block, Error = sp_blockchain::Error>,
{
	type Transaction = backend::TransactionFor<B, Block>;
	type Proposal = Pin<Box<dyn Future<
		Output = Result<Proposal<Block, Self::Transaction>, Self::Error>
	> + Send>>;
	type Error = sp_blockchain::Error;

	fn propose(
		self,
		inherent_data: InherentData,
		inherent_digests: DigestFor<Block>,
		max_duration: time::Duration,
		record_proof: RecordProof,
	) -> Self::Proposal {
		let (tx, rx) = oneshot::channel();
		let spawn_handle = self.spawn_handle.clone();

		spawn_handle.spawn_blocking("basic-authorship-proposer", Box::pin(async move {
			// leave some time for evaluation and block finalization (33%)
			let deadline = (self.now)() + max_duration - max_duration / 3;
			let res = self.propose_with(
				inherent_data,
				inherent_digests,
				deadline,
				record_proof,
			).await;
			if tx.send(res).is_err() {
				trace!("Could not send block production result to proposer!");
			}
		}));

		async move {
			rx.await?
		}.boxed()
	}
}

impl<A, B, Block, C> Proposer<B, Block, C, A>
	where
		A: TransactionPool<Block = Block>,
		B: backend::Backend<Block> + Send + Sync + 'static,
		Block: BlockT,
		C: BlockBuilderProvider<B, Block, C> + HeaderBackend<Block> + ProvideRuntimeApi<Block>
			+ Send + Sync + 'static,
		C::Api: ApiExt<Block, StateBackend = backend::StateBackendFor<B, Block>>
			+ BlockBuilderApi<Block, Error = sp_blockchain::Error>,
{
	async fn propose_with(
		self,
		inherent_data: InherentData,
		inherent_digests: DigestFor<Block>,
		deadline: time::Instant,
		record_proof: RecordProof,
	) -> Result<Proposal<Block, backend::TransactionFor<B, Block>>, sp_blockchain::Error> {
		/// If the block is full we will attempt to push at most
		/// this number of transactions before quitting for real.
		/// It allows us to increase block utilization.
		const MAX_SKIPPED_TRANSACTIONS: usize = 8;

		let mut block_builder = self.client.new_block_at(
			&self.parent_id,
			inherent_digests,
			record_proof,
		)?;

		for inherent in block_builder.create_inherents(inherent_data)? {
			match block_builder.push(inherent) {
				Err(ApplyExtrinsicFailed(Validity(e))) if e.exhausted_resources() =>
					warn!("⚠️  Dropping non-mandatory inherent from overweight block."),
				Err(ApplyExtrinsicFailed(Validity(e))) if e.was_mandatory() => {
					error!("❌️ Mandatory inherent extrinsic returned error. Block cannot be produced.");
					Err(ApplyExtrinsicFailed(Validity(e)))?
				}
				Err(e) => {
					warn!("❗️ Inherent extrinsic returned unexpected error: {}. Dropping.", e);
				}
				Ok(_) => {}
			}
		}

		// proceed with transactions
		let block_timer = time::Instant::now();
		let mut skipped = 0;
		let mut unqueue_invalid = Vec::new();

		let mut t1 = self.transaction_pool.ready_at(self.parent_number).fuse();
		let mut t2 = futures_timer::Delay::new(deadline.saturating_duration_since((self.now)()) / 8).fuse();

		let pending_iterator = select! {
			res = t1 => res,
			_ = t2 => {
				log::warn!(
					"Timeout fired waiting for transaction pool at block #{}. \
					Proceeding with production.",
					self.parent_number,
				);
				self.transaction_pool.ready()
			},
		};

		debug!("Attempting to push transactions from the pool.");
		debug!("Pool status: {:?}", self.transaction_pool.status());
		for pending_tx in pending_iterator {
			if (self.now)() > deadline {
				debug!(
					"Consensus deadline reached when pushing block transactions, \
					proceeding with proposing."
				);
				break;
			}

			let pending_tx_data = pending_tx.data().clone();
			let pending_tx_hash = pending_tx.hash().clone();
			trace!("[{:?}] Pushing to the block.", pending_tx_hash);
			match sc_block_builder::BlockBuilder::push(&mut block_builder, pending_tx_data) {
				Ok(()) => {
					debug!("[{:?}] Pushed to the block.", pending_tx_hash);
				}
				Err(ApplyExtrinsicFailed(Validity(e)))
						if e.exhausted_resources() => {
					if skipped < MAX_SKIPPED_TRANSACTIONS {
						skipped += 1;
						debug!(
							"Block seems full, but will try {} more transactions before quitting.",
							MAX_SKIPPED_TRANSACTIONS - skipped,
						);
					} else {
						debug!("Block is full, proceed with proposing.");
						break;
					}
				}
				Err(e) if skipped > 0 => {
					trace!(
						"[{:?}] Ignoring invalid transaction when skipping: {}",
						pending_tx_hash,
						e
					);
				}
				Err(e) => {
					debug!("[{:?}] Invalid transaction: {}", pending_tx_hash, e);
					unqueue_invalid.push(pending_tx_hash);
				}
			}
		}

		self.transaction_pool.remove_invalid(&unqueue_invalid);

		let (block, storage_changes, proof) = block_builder.build()?.into_inner();

		self.metrics.report(
			|metrics| {
				metrics.number_of_transactions.set(block.extrinsics().len() as u64);
				metrics.block_constructed.observe(block_timer.elapsed().as_secs_f64());
			}
		);

		info!("🎁 Prepared block for proposing at {} [hash: {:?}; parent_hash: {}; extrinsics ({}): [{}]]",
			block.header().number(),
			<Block as BlockT>::Hash::from(block.header().hash()),
			block.header().parent_hash(),
			block.extrinsics().len(),
			block.extrinsics()
				.iter()
				.map(|xt| format!("{}", BlakeTwo256::hash_of(xt)))
				.collect::<Vec<_>>()
				.join(", ")
		);
		telemetry!(CONSENSUS_INFO; "prepared_block_for_proposing";
			"number" => ?block.header().number(),
			"hash" => ?<Block as BlockT>::Hash::from(block.header().hash()),
		);

		if Decode::decode(&mut block.encode().as_slice()).as_ref() != Ok(&block) {
			error!("Failed to verify block encoding/decoding");
		}

		if let Err(err) = evaluation::evaluate_initial(
			&block,
			&self.parent_hash,
			self.parent_number,
			self.max_block_size,
		) {
			error!("Failed to evaluate authored block: {:?}", err);
		}

		Ok(Proposal { block, proof, storage_changes })
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	use parking_lot::Mutex;
	use sp_consensus::{BlockOrigin, Proposer};
	use substrate_test_runtime_client::{
		prelude::*, TestClientBuilder, runtime::{Extrinsic, Transfer}, TestClientBuilderExt,
	};
	use sp_transaction_pool::{ChainEvent, MaintainedTransactionPool, TransactionSource};
	use sc_transaction_pool::BasicPool;
	use sp_api::Core;
	use sp_blockchain::HeaderBackend;
	use sp_runtime::traits::NumberFor;
	use sc_client_api::Backend;

	const SOURCE: TransactionSource = TransactionSource::External;

	fn extrinsic(nonce: u64) -> Extrinsic {
		Transfer {
			amount: Default::default(),
			nonce,
			from: AccountKeyring::Alice.into(),
			to: Default::default(),
		}.into_signed_tx()
	}

	fn chain_event<B: BlockT>(header: B::Header) -> ChainEvent<B>
		where NumberFor<B>: From<u64>
	{
		ChainEvent::NewBestBlock {
			hash: header.hash(),
			tree_route: None,
		}
	}

	#[test]
	fn should_cease_building_block_when_deadline_is_reached() {
		// given
		let client = Arc::new(substrate_test_runtime_client::new());
		let spawner = sp_core::testing::TaskExecutor::new();
		let txpool = BasicPool::new_full(
			Default::default(),
			true.into(),
			None,
			spawner.clone(),
			client.clone(),
		);

		futures::executor::block_on(
			txpool.submit_at(&BlockId::number(0), SOURCE, vec![extrinsic(0), extrinsic(1)])
		).unwrap();

		futures::executor::block_on(
			txpool.maintain(chain_event(
				client.header(&BlockId::Number(0u64))
					.expect("header get error")
					.expect("there should be header")
			))
		);

		let mut proposer_factory = ProposerFactory::new(
			spawner.clone(),
			client.clone(),
			txpool.clone(),
			None,
		);

		let cell = Mutex::new((false, time::Instant::now()));
		let proposer = proposer_factory.init_with_now(
			&client.header(&BlockId::number(0)).unwrap().unwrap(),
			Box::new(move || {
				let mut value = cell.lock();
				if !value.0 {
					value.0 = true;
					return value.1;
				}
				let old = value.1;
				let new = old + time::Duration::from_secs(2);
				*value = (true, new);
				old
			})
		);

		// when
		let deadline = time::Duration::from_secs(3);
		let block = futures::executor::block_on(
			proposer.propose(Default::default(), Default::default(), deadline, RecordProof::No)
		).map(|r| r.block).unwrap();

		// then
		// block should have some extrinsics although we have some more in the pool.
		assert_eq!(block.extrinsics().len(), 1);
		assert_eq!(txpool.ready().count(), 2);
	}

	#[test]
	fn should_not_panic_when_deadline_is_reached() {
		let client = Arc::new(substrate_test_runtime_client::new());
		let spawner = sp_core::testing::TaskExecutor::new();
		let txpool = BasicPool::new_full(
			Default::default(),
			true.into(),
			None,
			spawner.clone(),
			client.clone(),
		);

		let mut proposer_factory = ProposerFactory::new(
			spawner.clone(),
			client.clone(),
			txpool.clone(),
			None,
		);

		let cell = Mutex::new((false, time::Instant::now()));
		let proposer = proposer_factory.init_with_now(
			&client.header(&BlockId::number(0)).unwrap().unwrap(),
			Box::new(move || {
				let mut value = cell.lock();
				if !value.0 {
					value.0 = true;
					return value.1;
				}
				let new = value.1 + time::Duration::from_secs(160);
				*value = (true, new);
				new
			})
		);

		let deadline = time::Duration::from_secs(1);
		futures::executor::block_on(
			proposer.propose(Default::default(), Default::default(), deadline, RecordProof::No)
		).map(|r| r.block).unwrap();
	}

	#[test]
	fn proposed_storage_changes_should_match_execute_block_storage_changes() {
		let (client, backend) = TestClientBuilder::new().build_with_backend();
		let client = Arc::new(client);
		let spawner = sp_core::testing::TaskExecutor::new();
		let txpool = BasicPool::new_full(
			Default::default(),
			true.into(),
			None,
			spawner.clone(),
			client.clone(),
		);

		let genesis_hash = client.info().best_hash;
		let block_id = BlockId::Hash(genesis_hash);

		futures::executor::block_on(
			txpool.submit_at(&BlockId::number(0), SOURCE, vec![extrinsic(0)]),
		).unwrap();

		futures::executor::block_on(
			txpool.maintain(chain_event(
				client.header(&BlockId::Number(0u64))
					.expect("header get error")
					.expect("there should be header"),
			))
		);

		let mut proposer_factory = ProposerFactory::new(
			spawner.clone(),
			client.clone(),
			txpool.clone(),
			None,
		);

		let proposer = proposer_factory.init_with_now(
			&client.header(&block_id).unwrap().unwrap(),
			Box::new(move || time::Instant::now()),
		);

		let deadline = time::Duration::from_secs(9);
		let proposal = futures::executor::block_on(
			proposer.propose(Default::default(), Default::default(), deadline, RecordProof::No),
		).unwrap();

		assert_eq!(proposal.block.extrinsics().len(), 1);

		let api = client.runtime_api();
		api.execute_block(&block_id, proposal.block).unwrap();

		let state = backend.state_at(block_id).unwrap();
		let changes_trie_state = backend::changes_tries_state_at_block(
			&block_id,
			backend.changes_trie_storage(),
		).unwrap();

		let storage_changes = api.into_storage_changes(
			&state,
			changes_trie_state.as_ref(),
			genesis_hash,
		).unwrap();

		assert_eq!(
			proposal.storage_changes.transaction_storage_root,
			storage_changes.transaction_storage_root,
		);
	}

	#[test]
	fn should_not_remove_invalid_transactions_when_skipping() {
		// given
		let mut client = Arc::new(substrate_test_runtime_client::new());
		let spawner = sp_core::testing::TaskExecutor::new();
		let txpool = BasicPool::new_full(
			Default::default(),
			true.into(),
			None,
			spawner.clone(),
			client.clone(),
		);

		futures::executor::block_on(
			txpool.submit_at(&BlockId::number(0), SOURCE, vec![
				extrinsic(0),
				extrinsic(1),
				Transfer {
					amount: Default::default(),
					nonce: 2,
					from: AccountKeyring::Alice.into(),
					to: Default::default(),
				}.into_resources_exhausting_tx(),
				extrinsic(3),
				Transfer {
					amount: Default::default(),
					nonce: 4,
					from: AccountKeyring::Alice.into(),
					to: Default::default(),
				}.into_resources_exhausting_tx(),
				extrinsic(5),
				extrinsic(6),
			])
		).unwrap();

		let mut proposer_factory = ProposerFactory::new(
			spawner.clone(),
			client.clone(),
			txpool.clone(),
			None,
		);
		let mut propose_block = |
			client: &TestClient,
			number,
			expected_block_extrinsics,
			expected_pool_transactions,
		| {
			let proposer = proposer_factory.init_with_now(
				&client.header(&BlockId::number(number)).unwrap().unwrap(),
				Box::new(move || time::Instant::now()),
			);

			// when
			let deadline = time::Duration::from_secs(9);
			let block = futures::executor::block_on(
				proposer.propose(Default::default(), Default::default(), deadline, RecordProof::No)
			).map(|r| r.block).unwrap();

			// then
			// block should have some extrinsics although we have some more in the pool.
			assert_eq!(block.extrinsics().len(), expected_block_extrinsics);
			assert_eq!(txpool.ready().count(), expected_pool_transactions);

			block
		};

		futures::executor::block_on(
			txpool.maintain(chain_event(
				client.header(&BlockId::Number(0u64))
					.expect("header get error")
					.expect("there should be header")
			))
		);

		// let's create one block and import it
		let block = propose_block(&client, 0, 2, 7);
		client.import(BlockOrigin::Own, block).unwrap();

		futures::executor::block_on(
			txpool.maintain(chain_event(
				client.header(&BlockId::Number(1))
					.expect("header get error")
					.expect("there should be header")
			))
		);

		// now let's make sure that we can still make some progress
		let block = propose_block(&client, 1, 2, 5);
		client.import(BlockOrigin::Own, block).unwrap();
	}
}
