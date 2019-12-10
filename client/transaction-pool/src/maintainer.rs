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

use std::{
	marker::{PhantomData, Unpin},
	sync::Arc,
	time::Instant,
};
use futures::{
	Future, FutureExt,
	future::{Either, join, ready},
};
use log::{warn, debug, trace};
use parking_lot::Mutex;

use client_api::{
	client::BlockBody,
	light::{Fetcher, RemoteBodyRequest},
};
use primitives::{Blake2Hasher, H256};
use sp_runtime::{
	generic::BlockId,
	traits::{Block as BlockT, Extrinsic, Header, NumberFor, ProvideRuntimeApi, SimpleArithmetic},
};
use sp_blockchain::HeaderBackend;
use txpool_api::TransactionPoolMaintainer;
use txpool_api::runtime_api::TaggedTransactionQueue;

use txpool::{self, ChainApi};

/// Basic transaction pool maintainer for full clients.
pub struct FullBasicPoolMaintainer<Client, PoolApi: ChainApi> {
	pool: Arc<txpool::Pool<PoolApi>>,
	client: Arc<Client>,
}

impl<Client, PoolApi: ChainApi> FullBasicPoolMaintainer<Client, PoolApi> {
	/// Create new basic full pool maintainer.
	pub fn new(
		pool: Arc<txpool::Pool<PoolApi>>,
		client: Arc<Client>,
	) -> Self {
		FullBasicPoolMaintainer { pool, client }
	}
}

impl<Block, Client, PoolApi> TransactionPoolMaintainer
for
	FullBasicPoolMaintainer<Client, PoolApi>
where
	Block: BlockT<Hash = <Blake2Hasher as primitives::Hasher>::Out>,
	Client: ProvideRuntimeApi + HeaderBackend<Block> + BlockBody<Block> + 'static,
	Client::Api: TaggedTransactionQueue<Block>,
	PoolApi: ChainApi<Block = Block, Hash = H256> + 'static,
{
	type Block = Block;
	type Hash = Block::Hash;

	fn maintain(
		&self,
		id: &BlockId<Block>,
		retracted: &[Block::Hash],
	) -> Box<dyn Future<Output=()> + Send + Unpin> {
		let now = std::time::Instant::now();
		let took = move || format!("Took {} ms", now.elapsed().as_millis());

		let id = *id;
		trace!(target: "txpool", "[{:?}] Starting pool maintainance", id);
		// Put transactions from retracted blocks back into the pool.
		let client_copy = self.client.clone();
		let retracted_transactions = retracted.to_vec().into_iter()
			.filter_map(move |hash| client_copy.block_body(&BlockId::hash(hash)).ok().unwrap_or(None))
			.flat_map(|block| block.into_iter())
			// if signed information is not present, attempt to resubmit anyway.
			.filter(|tx| tx.is_signed().unwrap_or(true));
		let resubmit_future = self.pool
			.submit_at(&id, retracted_transactions, true)
			.then(move |resubmit_result| ready(match resubmit_result {
				Ok(_) => trace!(target: "txpool",
					"[{:?}] Re-submitting retracted done. {}", id, took()
				),
				Err(e) => debug!(target: "txpool",
					"[{:?}] Error re-submitting transactions: {:?}", id, e
				),
			}));

		// Avoid calling into runtime if there is nothing to prune from the pool anyway.
		if self.pool.status().is_empty() {
			return Box::new(resubmit_future)
		}

		let block = (self.client.header(id), self.client.block_body(&id));
		let prune_future = match block {
			(Ok(Some(header)), Ok(Some(extrinsics))) => {
				let parent_id = BlockId::hash(*header.parent_hash());
				let prune_future = self.pool
					.prune(&id, &parent_id, &extrinsics)
					.then(move |prune_result| ready(match prune_result {
						Ok(_) => trace!(target: "txpool",
							"[{:?}] Pruning done. {}", id, took()
						),
						Err(e) => warn!(target: "txpool",
							"[{:?}] Error pruning transactions: {:?}", id, e
						),
					}));

				Either::Left(resubmit_future.then(|_| prune_future))
			},
			(Ok(_), Ok(_)) => Either::Right(resubmit_future),
			err => {
				warn!(target: "txpool", "[{:?}] Error reading block: {:?}", id, err);
				Either::Right(resubmit_future)
			},
		};

		let revalidate_future = self.pool
			.revalidate_ready(&id, Some(16))
			.then(move |result| ready(match result {
				Ok(_) => debug!(target: "txpool",
					"[{:?}] Revalidation done: {}", id, took()
				),
				Err(e) => warn!(target: "txpool",
					"[{:?}] Encountered errors while revalidating transactions: {:?}", id, e
				),
			}));

		Box::new(prune_future.then(|_| revalidate_future))
	}
}

/// Basic transaction pool maintainer for light clients.
pub struct LightBasicPoolMaintainer<Block: BlockT, Client, PoolApi: ChainApi, F> {
	pool: Arc<txpool::Pool<PoolApi>>,
	client: Arc<Client>,
	fetcher: Arc<F>,
	revalidate_time_period: Option<std::time::Duration>,
	revalidate_block_period: Option<NumberFor<Block>>,
	revalidation_status: Arc<Mutex<TxPoolRevalidationStatus<NumberFor<Block>>>>,
	_phantom: PhantomData<Block>,
}

impl<Block, Client, PoolApi, F> LightBasicPoolMaintainer<Block, Client, PoolApi, F>
	where
		Block: BlockT<Hash = <Blake2Hasher as primitives::Hasher>::Out>,
		Client: ProvideRuntimeApi + HeaderBackend<Block> + BlockBody<Block> + 'static,
		Client::Api: TaggedTransactionQueue<Block>,
		PoolApi: ChainApi<Block = Block, Hash = H256> + 'static,
		F: Fetcher<Block> + 'static,
{
	/// Create light pool maintainer with default constants.
	///
	/// Default constants are: revalidate every 60 seconds or every 20 blocks
	/// (whatever happens first).
	pub fn with_defaults(
		pool: Arc<txpool::Pool<PoolApi>>,
		client: Arc<Client>,
		fetcher: Arc<F>,
	) -> Self {
		Self::new(
			pool,
			client,
			fetcher,
			Some(std::time::Duration::from_secs(60)),
			Some(20.into()),
		)
	}

	/// Create light pool maintainer with passed constants.
	pub fn new(
		pool: Arc<txpool::Pool<PoolApi>>,
		client: Arc<Client>,
		fetcher: Arc<F>,
		revalidate_time_period: Option<std::time::Duration>,
		revalidate_block_period: Option<NumberFor<Block>>,
	) -> Self {
		Self {
			pool,
			client,
			fetcher,
			revalidate_time_period,
			revalidate_block_period,
			revalidation_status: Arc::new(Mutex::new(TxPoolRevalidationStatus::NotScheduled)),
			_phantom: Default::default(),
		}
	}

	/// Returns future that prunes block transactions from the pool.
	fn prune(
		&self,
		id: &BlockId<Block>,
		header: &Block::Header,
	) -> impl std::future::Future<Output = ()> {
		// fetch transactions (possible future optimization: proofs of inclusion) that
		// have been included into new block and prune these from the pool
		let id = id.clone();
		let pool = self.pool.clone();
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
						.map(|tx| pool.hash_of(&tx))
						.collect::<Vec<_>>();
					pool.prune_known(&id, &hashes)
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
	fn revalidate(
		&self,
		id: &BlockId<Block>,
		header: &Block::Header,
	) -> impl std::future::Future<Output = ()> {
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
				Either::Left(self.pool
					.revalidate_ready(id, None)
					.map(|r| r.map_err(|e| warn!("Error revalidating known transactions: {}", e)))
					.map(move |_| revalidation_status.lock().clear()))
			},
			false => Either::Right(ready(())),
		}
	}
}

impl<Block, Client, PoolApi, F> TransactionPoolMaintainer
for
	LightBasicPoolMaintainer<Block, Client, PoolApi, F>
where
	Block: BlockT<Hash = <Blake2Hasher as primitives::Hasher>::Out>,
	Client: ProvideRuntimeApi + HeaderBackend<Block> + BlockBody<Block> + 'static,
	Client::Api: TaggedTransactionQueue<Block>,
	PoolApi: ChainApi<Block = Block, Hash = H256> + 'static,
	F: Fetcher<Block> + 'static,
{
	type Block = Block;
	type Hash = Block::Hash;

	fn maintain(
		&self,
		id: &BlockId<Block>,
		_retracted: &[Block::Hash],
	) -> Box<dyn Future<Output=()> + Send + Unpin> {
		// Do nothing if transaction pool is empty.
		if self.pool.status().is_empty() {
			self.revalidation_status.lock().clear();
			return Box::new(ready(()));
		}
		let header = self.client.header(*id)
			.and_then(|h| h.ok_or(sp_blockchain::Error::UnknownBlock(format!("{}", id))));
		let header = match header {
			Ok(header) => header,
			Err(err) => {
				println!("Failed to maintain light tx pool: {:?}", err);
				return Box::new(ready(()));
			}
		};

		// else prune block transactions from the pool
		let prune_future = self.prune(id, &header);

		// and then (optionally) revalidate in-pool transactions
		let revalidate_future = self.revalidate(id, &header);

		let maintain_future = join(
			prune_future,
			revalidate_future,
		).map(|_| ());

		Box::new(maintain_future)
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
	use futures::executor::block_on;
	use codec::Encode;
	use test_client::{prelude::*, runtime::{Block, Transfer}, consensus::{BlockOrigin, SelectChain}};
	use txpool_api::PoolStatus;
	use crate::api::{FullChainApi, LightChainApi};

	#[test]
	fn should_remove_transactions_from_the_full_pool() {
		let (client, longest_chain) = TestClientBuilder::new().build_with_longest_chain();
		let client = Arc::new(client);
		let pool = txpool::Pool::new(Default::default(), FullChainApi::new(client.clone()));
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
		block_on(FullBasicPoolMaintainer::new(pool.clone(), client).maintain(&id, &[]));

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
		let fetcher = Arc::new(test_client::new_light_fetcher()
			.with_remote_body(Some(Box::new(move |_| Ok(vec![fetcher_transaction.clone()]))))
			.with_remote_call(Some(Box::new(move |_| {
				let validity: sp_runtime::transaction_validity::TransactionValidity =
					Ok(sp_runtime::transaction_validity::ValidTransaction {
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
		let pool = txpool::Pool::new(Default::default(), LightChainApi::new(
			client.clone(),
			fetcher.clone(),
		));
		let pool = Arc::new(pool);
		let best = longest_chain.best_chain().unwrap();

		// store the transaction in the pool
		block_on(pool.submit_one(&BlockId::hash(best.hash()), transaction.clone())).unwrap();

		// fire notification - this should clean up the queue
		assert_eq!(pool.status().ready, 1);
		block_on(LightBasicPoolMaintainer::with_defaults(pool.clone(), client.clone(), fetcher).maintain(
			&BlockId::Number(0),
			&[],
		));

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
		use std::sync::atomic;
		use sp_runtime::transaction_validity::*;

		let build_fetcher = || {
			let validated = Arc::new(atomic::AtomicBool::new(false));
			Arc::new(test_client::new_light_fetcher()
				.with_remote_body(Some(Box::new(move |_| Ok(vec![]))))
				.with_remote_call(Some(Box::new(move |_| {
					let is_inserted = validated.swap(true, atomic::Ordering::SeqCst);
					let validity: TransactionValidity = if is_inserted {
						Err(TransactionValidityError::Invalid(
							InvalidTransaction::Custom(0)
						))
					} else {
						Ok(ValidTransaction {
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
			revalidate_time_period: Option<std::time::Duration>,
			revalidate_block_period: Option<u64>,
			prepare_maintainer: impl Fn(&Mutex<TxPoolRevalidationStatus<u64>>),
		) -> PoolStatus {
			let (client, longest_chain) = TestClientBuilder::new().build_with_longest_chain();
			let client = Arc::new(client);

			// now let's prepare pool
			let pool = txpool::Pool::new(Default::default(), LightChainApi::new(
				client.clone(),
				fetcher.clone(),
			));
			let pool = Arc::new(pool);
			let best = longest_chain.best_chain().unwrap();

			// let's prepare maintainer
			let maintainer = LightBasicPoolMaintainer::new(
				pool.clone(),
				client,
				fetcher,
				revalidate_time_period,
				revalidate_block_period,
			);
			prepare_maintainer(&*maintainer.revalidation_status);

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
			block_on(maintainer.maintain(&BlockId::Number(0), &[]));

			pool.status()
		}

		// when revalidation is never required - nothing happens
		let fetcher = build_fetcher();
		//let maintainer = DefaultLightTransactionPoolMaintainer::new(client.clone(), fetcher.clone(), None, None);
		let status = with_fetcher_maintain(fetcher, None, None, |_revalidation_status| {});
		assert_eq!(status.ready, 1);

		// when revalidation is scheduled by time - it is performed
		let fetcher = build_fetcher();
		let status = with_fetcher_maintain(fetcher, None, None, |revalidation_status|
			*revalidation_status.lock() = TxPoolRevalidationStatus::Scheduled(Some(Instant::now()), None)
		);
		assert_eq!(status.ready, 0);

		// when revalidation is scheduled by block number - it is performed
		let fetcher = build_fetcher();
		let status = with_fetcher_maintain(fetcher, None, None, |revalidation_status|
			*revalidation_status.lock() = TxPoolRevalidationStatus::Scheduled(None, Some(0))
		);
		assert_eq!(status.ready, 0);
	}

	#[test]
	fn should_add_reverted_transactions_to_the_pool() {
		let (client, longest_chain) = TestClientBuilder::new().build_with_longest_chain();
		let client = Arc::new(client);
		let pool = txpool::Pool::new(Default::default(), FullChainApi::new(client.clone()));
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
		block_on(FullBasicPoolMaintainer::new(pool.clone(), client.clone()).maintain(&id, &[]));

		// then
		assert_eq!(pool.status().ready, 0);
		assert_eq!(pool.status().future, 0);

		// import second block
		let builder = client.new_block_at(&BlockId::hash(best.hash()), Default::default()).unwrap();
		let block = builder.bake().unwrap();
		let id = BlockId::hash(block.header().hash());
		client.import(BlockOrigin::Own, block).unwrap();

		// fire notification - this should add the transaction back to the pool.
		block_on(FullBasicPoolMaintainer::new(pool.clone(), client).maintain(&id, &[block1_hash]));

		// then
		assert_eq!(pool.status().ready, 1);
		assert_eq!(pool.status().future, 0);
	}
}
