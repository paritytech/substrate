// Copyright 2019 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

use crate::error;
use client::{
	Client, runtime_api,
	light::fetcher::{Fetcher, RemoteBodyRequest},
};
use futures::prelude::*;
use futures03::{
	future::{ready, Either},
	FutureExt, TryFutureExt,
};
use log::warn;
use parking_lot::Mutex;
use primitives::Blake2Hasher;
use sr_primitives::generic::BlockId;
use sr_primitives::traits::{
	Block as BlockT, Extrinsic, ProvideRuntimeApi, NumberFor,
	Header, SimpleArithmetic,
};
use std::{marker::PhantomData, sync::Arc, time::Instant};
use transaction_pool::txpool::{self, Pool as TransactionPool};

/// Transaction pool maintainer.
///
/// In brief, the task of transaction pool maintainer is to:
/// 1) make sure that ready in-pool transactions are valid;
/// 2) move 'future' transactions to the 'ready' queue;
/// 3) prune transactions that have been included in some block.
pub trait TransactionPoolMaintainer<Block>: Send + 'static where
	Block: BlockT<Hash = <Blake2Hasher as primitives::Hasher>::Out>,
{
	/// Maintain transaction pool.
	fn maintain<Api, Backend, Executor, PoolApi>(
		&self,
		id: &BlockId<Block>,
		client: &Arc<Client<Backend, Executor, Block, Api>>,
		transaction_pool: &Arc<TransactionPool<PoolApi>>,
		retracted: &[Block::Hash],
	) -> error::Result<Box<dyn Future<Item = (), Error = ()> + Send>> where
		Backend: 'static + client::backend::Backend<Block, Blake2Hasher>,
		Client<Backend, Executor, Block, Api>: ProvideRuntimeApi,
		<Client<Backend, Executor, Block, Api> as ProvideRuntimeApi>::Api: runtime_api::TaggedTransactionQueue<Block>,
		Executor: 'static + client::CallExecutor<Block, Blake2Hasher>,
		PoolApi: 'static + txpool::ChainApi<Hash = Block::Hash, Block = Block>,
		Api: 'static;
}

/// Default transaction pool maintainer for full clients.
pub struct DefaultFullTransactionPoolMaintainer;

impl<Block> TransactionPoolMaintainer<Block> for DefaultFullTransactionPoolMaintainer where
	Block: BlockT<Hash = <Blake2Hasher as primitives::Hasher>::Out>,
{
	fn maintain<Api, Backend, Executor, PoolApi>(
		&self,
		id: &BlockId<Block>,
		client: &Arc<Client<Backend, Executor, Block, Api>>,
		transaction_pool: &Arc<TransactionPool<PoolApi>>,
		retracted: &[Block::Hash],
	) -> error::Result<Box<dyn Future<Item = (), Error = ()> + Send>> where
		Backend: 'static + client::backend::Backend<Block, Blake2Hasher>,
		Client<Backend, Executor, Block, Api>: ProvideRuntimeApi,
		<Client<Backend, Executor, Block, Api> as ProvideRuntimeApi>::Api: runtime_api::TaggedTransactionQueue<Block>,
		Executor: 'static + client::CallExecutor<Block, Blake2Hasher>,
		PoolApi: 'static + txpool::ChainApi<Hash = Block::Hash, Block = Block>,
		Api: 'static,
	{
		// Put transactions from retracted blocks back into the pool.
		let client_copy = client.clone();
		let retracted_transactions = retracted.to_vec().into_iter()
			.filter_map(move |hash| client_copy.block(&BlockId::hash(hash)).ok().unwrap_or(None))
			.flat_map(|block| block.block.deconstruct().1.into_iter())
			.filter(|tx| tx.is_signed().unwrap_or(false));
		let resubmit_future = transaction_pool
			.submit_at(id, retracted_transactions, true)
			.then(|resubmit_result| ready(match resubmit_result {
				Ok(_) => Ok(()),
				Err(e) => {
					warn!("Error re-submitting transactions: {:?}", e);
					Ok(())
				}
			}))
			.compat();

		// Avoid calling into runtime if there is nothing to prune from the pool anyway.
		if transaction_pool.status().is_empty() {
			return Ok(Box::new(resubmit_future))
		}

		let block = client.block(id)?;
		Ok(match block {
			Some(block) => {
				let parent_id = BlockId::hash(*block.block.header().parent_hash());
				let prune_future = transaction_pool
					.prune(id, &parent_id, block.block.extrinsics())
					.boxed()
					.compat()
					.map_err(|e| { warn!("{:?}", e); });

				Box::new(resubmit_future.and_then(|_| prune_future))
			},
			None => Box::new(resubmit_future),
		})
	}
}

/// Default transaction pool maintainer for light clients.
pub struct DefaultLightTransactionPoolMaintainer<Block: BlockT, F> {
	fetcher: Arc<F>,
	revalidate_time_period: Option<std::time::Duration>,
	revalidate_block_period: Option<NumberFor<Block>>,
	revalidation_status: Arc<Mutex<TxPoolRevalidationStatus<NumberFor<Block>>>>,
	_phantom: PhantomData<Block>,
}

impl<Block: BlockT, F: Fetcher<Block>> DefaultLightTransactionPoolMaintainer<Block, F> {
	/// Create light pool maintainer with default constants.
	pub fn with_defaults(fetcher: Arc<F>) -> Self {
		// default constants are: revalidate every 60 seconds or every 20 blocks
		Self::new(
			fetcher,
			Some(std::time::Duration::from_secs(60)),
			Some(20.into()),
		)
	}

	/// Create light pool maintainer with passed constants.
	pub fn new(
		fetcher: Arc<F>,
		revalidate_time_period: Option<std::time::Duration>,
		revalidate_block_period: Option<NumberFor<Block>>,
	) -> Self {
		Self {
			fetcher,
			revalidate_time_period,
			revalidate_block_period,
			revalidation_status: Arc::new(Mutex::new(TxPoolRevalidationStatus::NotScheduled)),
			_phantom: Default::default(),
		}
	}

	/// Returns future that prunes block transactions from the pool.
	fn prune<PoolApi>(
		&self,
		id: &BlockId<Block>,
		header: &Block::Header,
		transaction_pool: &Arc<TransactionPool<PoolApi>>,
	) -> impl futures03::Future<Output = ()> where
		PoolApi: 'static + txpool::ChainApi<Hash = Block::Hash, Block = Block>,
	{
		// fetch transactions (possible future optimization: proofs of inclusion) that
		// have been included into new block and prune these from the pool
		let id = id.clone();
		let transaction_pool = transaction_pool.clone();
		self.fetcher.remote_body(RemoteBodyRequest {
			header: header.clone(),
			retry_count: None,
		})
		.then(move |transactions| ready(
			transactions
				.map_err(|e| format!("{}", e))
				.and_then(|transactions| {
					let hashes = transactions
						.into_iter()
						.map(|tx| transaction_pool.hash_of(&tx))
						.collect::<Vec<_>>();
					transaction_pool.prune_known(&id, &hashes)
						.map_err(|e| format!("{}", e))
				})
		))
		.then(|r| {
			if let Err(e) = r {
				warn!("Error pruning known transactions: {}", e)
			}
			ready(())
		})
	}

	/// Returns future that performs in-pool transations revalidation, if required.
	fn revalidate<PoolApi>(
		&self,
		id: &BlockId<Block>,
		header: &Block::Header,
		transaction_pool: &Arc<TransactionPool<PoolApi>>,
	) -> impl futures03::Future<Output = ()> where
		PoolApi: 'static + txpool::ChainApi<Hash = Block::Hash, Block = Block>,
	{
		// to determine whether ready transaction is still valid, we perform periodic revalidaton
		// of ready transactions
		let is_revalidation_required = self.revalidation_status.lock().is_required(
			*header.number(),
			self.revalidate_time_period,
			self.revalidate_block_period,
		);
		match is_revalidation_required {
			true => {
				let revalidation_status = self.revalidation_status.clone();
				Either::Left(transaction_pool
					.revalidate_ready(id)
					.map(|r| r.map_err(|e| warn!("Error revalidating known transactions: {}", e)))
					.map(move |_| revalidation_status.lock().clear()))
			},
			false => Either::Right(ready(())),
		}
	}
}

impl<Block, F> TransactionPoolMaintainer<Block> for DefaultLightTransactionPoolMaintainer<Block, F>
	where
		Block: BlockT<Hash = <Blake2Hasher as primitives::Hasher>::Out>,
		F: Fetcher<Block> + 'static,
{
	fn maintain<Api, Backend, Executor, PoolApi>(
		&self,
		id: &BlockId<Block>,
		client: &Arc<Client<Backend, Executor, Block, Api>>,
		transaction_pool: &Arc<TransactionPool<PoolApi>>,
		_retracted: &[Block::Hash],
	) -> error::Result<Box<dyn Future<Item = (), Error = ()> + Send>> where
		Backend: 'static + client::backend::Backend<Block, Blake2Hasher>,
		Client<Backend, Executor, Block, Api>: ProvideRuntimeApi,
		<Client<Backend, Executor, Block, Api> as ProvideRuntimeApi>::Api: runtime_api::TaggedTransactionQueue<Block>,
		Executor: 'static + client::CallExecutor<Block, Blake2Hasher>,
		PoolApi: 'static + txpool::ChainApi<Hash = Block::Hash, Block = Block>,
		Api: 'static,
	{
		// Do nothing if transaction pool is empty.
		if transaction_pool.status().is_empty() {
			self.revalidation_status.lock().clear();
			return Ok(Box::new(ready(Ok(())).compat()));
		}
		let header = client.header(id).and_then(|h| h.ok_or(client::error::Error::UnknownBlock(format!("{}", id))))?;

		// else prune block transactions from the pool
		let prune_future = self.prune(id, &header, transaction_pool);

		// and then (optionally) revalidate in-pool transactions
		let revalidate_future = self.revalidate(id, &header, transaction_pool);

		let maintain_future = futures03::future::join(
			prune_future,
			revalidate_future,
		).map(|_| Ok(()));

		Ok(Box::new(maintain_future.compat()))
	}
}

/// The status of transactions revalidation at light tx pool.
#[cfg_attr(test, derive(Debug))]
enum TxPoolRevalidationStatus<N> {
	/// The revalidation has never been completed.
	NotScheduled,
	/// The revalidation is scheduled.
	Scheduled(Option<std::time::Instant>, Option<N>),
	/// The revalidation is in progress.
	InProgress,
}

impl<N: Clone + Copy + SimpleArithmetic> TxPoolRevalidationStatus<N> {
	/// Called when revalidation is completed.
	pub fn clear(&mut self) {
		*self = TxPoolRevalidationStatus::NotScheduled;
	}

	/// Returns true if revalidation is required.
	pub fn is_required(
		&mut self,
		block: N,
		revalidate_time_period: Option<std::time::Duration>,
		revalidate_block_period: Option<N>,
	) -> bool {
		match *self {
			TxPoolRevalidationStatus::NotScheduled => {
				*self = TxPoolRevalidationStatus::Scheduled(
					revalidate_time_period.map(|period| Instant::now() + period),
					revalidate_block_period.map(|period| block + period),
				);
				false
			},
			TxPoolRevalidationStatus::Scheduled(revalidate_at_time, revalidate_at_block) => {
				let is_required = revalidate_at_time.map(|at| Instant::now() >= at).unwrap_or(false)
					|| revalidate_at_block.map(|at| block >= at).unwrap_or(false);
				if is_required {
					*self = TxPoolRevalidationStatus::InProgress;
				}
				is_required
			},
			TxPoolRevalidationStatus::InProgress => false,
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use futures03::executor::block_on;
	use codec::Encode;
	use consensus_common::{BlockOrigin, SelectChain};
	use substrate_test_runtime_client::{prelude::*, runtime::{Block, Transfer}};

	#[test]
	fn should_remove_transactions_from_the_full_pool() {
		let (client, longest_chain) = TestClientBuilder::new().build_with_longest_chain();
		let client = Arc::new(client);
		let pool = TransactionPool::new(Default::default(), ::transaction_pool::FullChainApi::new(client.clone()));
		let pool = Arc::new(pool);
		let transaction = Transfer {
			amount: 5,
			nonce: 0,
			from: AccountKeyring::Alice.into(),
			to: Default::default(),
		}.into_signed_tx();
		let best = longest_chain.best_chain().unwrap();

		// store the transaction in the pool
		block_on(pool.submit_one(&BlockId::hash(best.hash()), transaction.clone())).unwrap();

		// import the block
		let mut builder = client.new_block(Default::default()).unwrap();
		builder.push(transaction.clone()).unwrap();
		let block = builder.bake().unwrap();
		let id = BlockId::hash(block.header().hash());
		client.import(BlockOrigin::Own, block).unwrap();

		// fire notification - this should clean up the queue
		assert_eq!(pool.status().ready, 1);
		DefaultFullTransactionPoolMaintainer.maintain(
			&id,
			&client,
			&pool,
			&[]
		).unwrap().wait().unwrap();

		// then
		assert_eq!(pool.status().ready, 0);
		assert_eq!(pool.status().future, 0);
	}

	#[test]
	fn should_remove_transactions_from_the_light_pool() {
		let transaction = Transfer {
			amount: 5,
			nonce: 0,
			from: AccountKeyring::Alice.into(),
			to: Default::default(),
		}.into_signed_tx();
		let fetcher_transaction = transaction.clone();
		let fetcher = Arc::new(substrate_test_runtime_client::new_light_fetcher()
			.with_remote_body(Some(Box::new(move |_| Ok(vec![fetcher_transaction.clone()]))))
			.with_remote_call(Some(Box::new(move |_| {
				let validity: sr_primitives::transaction_validity::TransactionValidity =
					Ok(sr_primitives::transaction_validity::ValidTransaction {
						priority: 0,
						requires: Vec::new(),
						provides: vec![vec![42]],
						longevity: 0,
						propagate: true,
					});
				Ok(validity.encode())
			}))));

		let (client, longest_chain) = TestClientBuilder::new().build_with_longest_chain();
		let client = Arc::new(client);
		let pool = TransactionPool::new(Default::default(), ::transaction_pool::LightChainApi::new(
			client.clone(),
			fetcher.clone(),
		));
		let pool = Arc::new(pool);
		let best = longest_chain.best_chain().unwrap();

		// store the transaction in the pool
		block_on(pool.submit_one(&BlockId::hash(best.hash()), transaction.clone())).unwrap();

		// fire notification - this should clean up the queue
		assert_eq!(pool.status().ready, 1);
		DefaultLightTransactionPoolMaintainer::with_defaults(fetcher).maintain(
			&BlockId::Number(0),
			&client,
			&pool,
			&[]
		).unwrap().wait().unwrap();

		// then
		assert_eq!(pool.status().ready, 0);
		assert_eq!(pool.status().future, 0);
	}

	#[test]
	fn should_schedule_transactions_revalidation_at_light_pool() {
		// when revalidation is not scheduled, it became scheduled
		let mut status = TxPoolRevalidationStatus::NotScheduled;
		assert!(!status.is_required(10u32, None, None));
		match status {
			TxPoolRevalidationStatus::Scheduled(_, _) => (),
			_ => panic!("Unexpected status: {:?}", status),
		}

		// revalidation required at time
		let mut status = TxPoolRevalidationStatus::Scheduled(Some(Instant::now()), None);
		assert!(status.is_required(10u32, None, None));
		match status {
			TxPoolRevalidationStatus::InProgress => (),
			_ => panic!("Unexpected status: {:?}", status),
		}

		// revalidation required at block
		let mut status = TxPoolRevalidationStatus::Scheduled(None, Some(10));
		assert!(status.is_required(10u32, None, None));
		match status {
			TxPoolRevalidationStatus::InProgress => (),
			_ => panic!("Unexpected status: {:?}", status),
		}
	}

	#[test]
	fn should_revalidate_transactions_at_light_pool() {
		let build_fetcher = || {
			let validated = Arc::new(std::sync::atomic::AtomicBool::new(false));
			Arc::new(substrate_test_runtime_client::new_light_fetcher()
				.with_remote_body(Some(Box::new(move |_| Ok(vec![]))))
				.with_remote_call(Some(Box::new(move |_| {
					let is_inserted = validated.swap(true, std::sync::atomic::Ordering::SeqCst);
					let validity: sr_primitives::transaction_validity::TransactionValidity = if is_inserted {
						Err(sr_primitives::transaction_validity::TransactionValidityError::Invalid(
							sr_primitives::transaction_validity::InvalidTransaction::Custom(0)
						))
					} else {
						Ok(sr_primitives::transaction_validity::ValidTransaction {
							priority: 0,
							requires: Vec::new(),
							provides: vec![vec![42]],
							longevity: 0,
							propagate: true,
						})
					};
					Ok(validity.encode())
				}))))
		};

		fn with_fetcher_maintain<F: Fetcher<Block> + 'static>(
			fetcher: Arc<F>,
			maintainer: &DefaultLightTransactionPoolMaintainer<Block, F>,
		) -> transaction_pool::txpool::Status {
			// now let's prepare pool
			let (client, longest_chain) = TestClientBuilder::new().build_with_longest_chain();
			let client = Arc::new(client);
			let pool = TransactionPool::new(Default::default(), ::transaction_pool::LightChainApi::new(
				client.clone(),
				fetcher,
			));
			let pool = Arc::new(pool);
			let best = longest_chain.best_chain().unwrap();

			// store the transaction in the pool
			block_on(pool.submit_one(
				&BlockId::hash(best.hash()),
				Transfer {
					amount: 5,
					nonce: 0,
					from: AccountKeyring::Alice.into(),
					to: Default::default(),
				}.into_signed_tx(),
			)).unwrap();

			// and run maintain procedures
			maintainer.maintain(&BlockId::Number(0), &client, &pool, &[]).unwrap().wait().unwrap();

			pool.status()
		}

		// when revalidation is never required - nothing happens
		let fetcher = build_fetcher();
		let maintainer = DefaultLightTransactionPoolMaintainer::new(fetcher.clone(), None, None);
		let status = with_fetcher_maintain(fetcher, &maintainer);
		assert_eq!(status.ready, 1);

		// when revalidation is scheduled by time - it is performed
		let fetcher = build_fetcher();
		let maintainer = DefaultLightTransactionPoolMaintainer::new(fetcher.clone(), None, None);
		*maintainer.revalidation_status.lock() = TxPoolRevalidationStatus::Scheduled(Some(Instant::now()), None);
		let status = with_fetcher_maintain(fetcher, &maintainer);
		assert_eq!(status.ready, 0);

		// when revalidation is scheduled by block number - it is performed
		let fetcher = build_fetcher();
		let maintainer = DefaultLightTransactionPoolMaintainer::new(fetcher.clone(), None, None);
		*maintainer.revalidation_status.lock() = TxPoolRevalidationStatus::Scheduled(None, Some(0));
		let status = with_fetcher_maintain(fetcher, &maintainer);
		assert_eq!(status.ready, 0);
	}

	#[test]
	fn should_add_reverted_transactions_to_the_pool() {
		let (client, longest_chain) = TestClientBuilder::new().build_with_longest_chain();
		let client = Arc::new(client);
		let pool = TransactionPool::new(Default::default(), ::transaction_pool::FullChainApi::new(client.clone()));
		let pool = Arc::new(pool);
		let transaction = Transfer {
			amount: 5,
			nonce: 0,
			from: AccountKeyring::Alice.into(),
			to: Default::default(),
		}.into_signed_tx();
		let best = longest_chain.best_chain().unwrap();

		// store the transaction in the pool
		block_on(pool.submit_one(&BlockId::hash(best.hash()), transaction.clone())).unwrap();

		// import the block
		let mut builder = client.new_block(Default::default()).unwrap();
		builder.push(transaction.clone()).unwrap();
		let block = builder.bake().unwrap();
		let block1_hash = block.header().hash();
		let id = BlockId::hash(block1_hash.clone());
		client.import(BlockOrigin::Own, block).unwrap();

		// fire notification - this should clean up the queue
		assert_eq!(pool.status().ready, 1);
		DefaultFullTransactionPoolMaintainer.maintain(
			&id,
			&client,
			&pool,
			&[]
		).unwrap().wait().unwrap();

		// then
		assert_eq!(pool.status().ready, 0);
		assert_eq!(pool.status().future, 0);

		// import second block
		let builder = client.new_block_at(&BlockId::hash(best.hash()), Default::default()).unwrap();
		let block = builder.bake().unwrap();
		let id = BlockId::hash(block.header().hash());
		client.import(BlockOrigin::Own, block).unwrap();

		// fire notification - this should add the transaction back to the pool.
		DefaultFullTransactionPoolMaintainer.maintain(
			&id,
			&client,
			&pool,
			&[block1_hash]
		).unwrap().wait().unwrap();

		// then
		assert_eq!(pool.status().ready, 1);
		assert_eq!(pool.status().future, 0);
	}
}
