// Copyright 2018-2020 Parity Technologies (UK) Ltd.
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

//! Substrate transaction pool implementation.

#![warn(missing_docs)]
#![warn(unused_extern_crates)]

mod api;
pub mod error;

#[cfg(any(feature = "test-helpers", test))]
pub mod testing;

pub use sc_transaction_graph as txpool;
pub use crate::api::{FullChainApi, LightChainApi};

use std::{collections::HashMap, sync::Arc, pin::Pin};
use futures::{Future, FutureExt, future::ready};
use parking_lot::Mutex;

use sp_runtime::{
	generic::BlockId,
	traits::{Block as BlockT, NumberFor, AtLeast32Bit, Extrinsic},
};
use sp_transaction_pool::{
	TransactionPool, PoolStatus, ImportNotificationStream, TxHash, TransactionFor,
	TransactionStatusStreamFor, MaintainedTransactionPool, PoolFuture, ChainEvent,
};
use wasm_timer::Instant;

/// Basic implementation of transaction pool that can be customized by providing PoolApi.
pub struct BasicPool<PoolApi, Block>
	where
		Block: BlockT,
		PoolApi: sc_transaction_graph::ChainApi<Block=Block, Hash=Block::Hash>,
{
	pool: Arc<sc_transaction_graph::Pool<PoolApi>>,
	api: Arc<PoolApi>,
	revalidation_strategy: Arc<Mutex<RevalidationStrategy<NumberFor<Block>>>>,
}

#[cfg(not(target_os = "unknown"))]
impl<PoolApi, Block> parity_util_mem::MallocSizeOf for BasicPool<PoolApi, Block>
where
	PoolApi: sc_transaction_graph::ChainApi<Block=Block, Hash=Block::Hash>,
	PoolApi::Hash: parity_util_mem::MallocSizeOf,
	Block: BlockT,
{
	fn size_of(&self, ops: &mut parity_util_mem::MallocSizeOfOps) -> usize {
		// other entries insignificant or non-primary references
		self.pool.size_of(ops)
	}
}

/// Type of revalidation.
pub enum RevalidationType {
	/// Light revalidation type.
	///
	/// During maintenance, transaction pool makes periodic revalidation
	/// of all transactions depending on number of blocks or time passed.
	/// Also this kind of revalidation does not resubmit transactions from
	/// retracted blocks, since it is too expensive.
	Light,

	/// Full revalidation type.
	///
	/// During maintenance, transaction pool revalidates some fixed amount of
	/// transactions from the pool of valid transactions.
	Full,
}

impl<PoolApi, Block> BasicPool<PoolApi, Block>
	where
		Block: BlockT,
		PoolApi: sc_transaction_graph::ChainApi<Block=Block, Hash=Block::Hash>,
{
	/// Create new basic transaction pool with provided api.
	pub fn new(
		options: sc_transaction_graph::Options,
		pool_api: Arc<PoolApi>,
	) -> Self {
		Self::with_revalidation_type(options, pool_api, RevalidationType::Full)
	}

	/// Create new basic transaction pool with provided api and custom
	/// revalidation type.
	pub fn with_revalidation_type(
		options: sc_transaction_graph::Options,
		pool_api: Arc<PoolApi>,
		revalidation_type: RevalidationType,
	) -> Self {
		let cloned_api = pool_api.clone();
		BasicPool {
			api: cloned_api,
			pool: Arc::new(sc_transaction_graph::Pool::new(options, pool_api)),
			revalidation_strategy: Arc::new(Mutex::new(
				match revalidation_type {
					RevalidationType::Light => RevalidationStrategy::Light(RevalidationStatus::NotScheduled),
					RevalidationType::Full => RevalidationStrategy::Always,
				}
			)),
		}
	}

	/// Gets shared reference to the underlying pool.
	pub fn pool(&self) -> &Arc<sc_transaction_graph::Pool<PoolApi>> {
		&self.pool
	}
}

impl<PoolApi, Block> TransactionPool for BasicPool<PoolApi, Block>
	where
		Block: BlockT,
		PoolApi: 'static + sc_transaction_graph::ChainApi<Block=Block, Hash=Block::Hash>,
{
	type Block = PoolApi::Block;
	type Hash = sc_transaction_graph::ExHash<PoolApi>;
	type InPoolTransaction = sc_transaction_graph::base_pool::Transaction<TxHash<Self>, TransactionFor<Self>>;
	type Error = PoolApi::Error;

	fn submit_at(
		&self,
		at: &BlockId<Self::Block>,
		xts: Vec<TransactionFor<Self>>,
	) -> PoolFuture<Vec<Result<TxHash<Self>, Self::Error>>, Self::Error> {
		let pool = self.pool.clone();
		let at = *at;
		async move {
			pool.submit_at(&at, xts, false).await
		}.boxed()
	}

	fn submit_one(
		&self,
		at: &BlockId<Self::Block>,
		xt: TransactionFor<Self>,
	) -> PoolFuture<TxHash<Self>, Self::Error> {
		let pool = self.pool.clone();
		let at = *at;
		async move {
			pool.submit_one(&at, xt).await
		}.boxed()
	}

	fn submit_and_watch(
		&self,
		at: &BlockId<Self::Block>,
		xt: TransactionFor<Self>,
	) -> PoolFuture<Box<TransactionStatusStreamFor<Self>>, Self::Error> {
		let at = *at;
		let pool = self.pool.clone();

		async move {
			pool.submit_and_watch(&at, xt)
				.map(|result| result.map(|watcher| Box::new(watcher.into_stream()) as _))
				.await
		}.boxed()
	}

	fn remove_invalid(&self, hashes: &[TxHash<Self>]) -> Vec<Arc<Self::InPoolTransaction>> {
		self.pool.validated_pool().remove_invalid(hashes)
	}

	fn status(&self) -> PoolStatus {
		self.pool.validated_pool().status()
	}

	fn ready(&self) -> Box<dyn Iterator<Item=Arc<Self::InPoolTransaction>>> {
		Box::new(self.pool.validated_pool().ready())
	}

	fn import_notification_stream(&self) -> ImportNotificationStream<TxHash<Self>> {
		self.pool.validated_pool().import_notification_stream()
	}

	fn hash_of(&self, xt: &TransactionFor<Self>) -> TxHash<Self> {
		self.pool.hash_of(xt)
	}

	fn on_broadcasted(&self, propagations: HashMap<TxHash<Self>, Vec<String>>) {
		self.pool.validated_pool().on_broadcasted(propagations)
	}

	fn ready_transaction(&self, hash: &TxHash<Self>) -> Option<Arc<Self::InPoolTransaction>> {
		self.pool.validated_pool().ready_by_hash(hash)
	}
}

#[cfg_attr(test, derive(Debug))]
enum RevalidationStatus<N> {
	/// The revalidation has never been completed.
	NotScheduled,
	/// The revalidation is scheduled.
	Scheduled(Option<Instant>, Option<N>),
	/// The revalidation is in progress.
	InProgress,
}

enum RevalidationStrategy<N> {
	Always,
	Light(RevalidationStatus<N>),
}

struct RevalidationAction {
	revalidate: bool,
	resubmit: bool,
	revalidate_amount: Option<usize>,
}

impl<N: Clone + Copy + AtLeast32Bit> RevalidationStrategy<N> {
	pub fn clear(&mut self) {
		if let Self::Light(status) = self {
			status.clear()
		}
	}

	pub fn next(
		&mut self,
		block: N,
		revalidate_time_period: Option<std::time::Duration>,
		revalidate_block_period: Option<N>,
	) -> RevalidationAction {
		match self {
			Self::Light(status) => RevalidationAction {
				revalidate: status.next_required(
					block,
					revalidate_time_period,
					revalidate_block_period,
				),
				resubmit: false,
				revalidate_amount: None,
			},
			Self::Always => RevalidationAction {
				revalidate: true,
				resubmit: true,
				revalidate_amount: Some(16),
			}
		}
	}
}

impl<N: Clone + Copy + AtLeast32Bit> RevalidationStatus<N> {
	/// Called when revalidation is completed.
	pub fn clear(&mut self) {
		*self = Self::NotScheduled;
	}

	/// Returns true if revalidation is required.
	pub fn next_required(
		&mut self,
		block: N,
		revalidate_time_period: Option<std::time::Duration>,
		revalidate_block_period: Option<N>,
	) -> bool {
		match *self {
			Self::NotScheduled => {
				*self = Self::Scheduled(
					revalidate_time_period.map(|period| Instant::now() + period),
					revalidate_block_period.map(|period| block + period),
				);
				false
			}
			Self::Scheduled(revalidate_at_time, revalidate_at_block) => {
				let is_required = revalidate_at_time.map(|at| Instant::now() >= at).unwrap_or(false)
					|| revalidate_at_block.map(|at| block >= at).unwrap_or(false);
				if is_required {
					*self = Self::InProgress;
				}
				is_required
			}
			Self::InProgress => false,
		}
	}
}

impl<PoolApi, Block> MaintainedTransactionPool for BasicPool<PoolApi, Block>
	where
		Block: BlockT,
		PoolApi: 'static + sc_transaction_graph::ChainApi<Block=Block, Hash=Block::Hash>,
{
	fn maintain(&self, event: ChainEvent<Self::Block>) -> Pin<Box<dyn Future<Output=()> + Send>> {
		match event {
			ChainEvent::NewBlock { id, retracted, .. } => {
				let id = id.clone();
				let pool = self.pool.clone();
				let api = self.api.clone();

				let block_number = match api.block_id_to_number(&id) {
					Ok(Some(number)) => number,
					_ => {
						log::trace!(target: "txqueue", "Skipping chain event - no number for that block {:?}", id);
						return Box::pin(ready(()));
					}
				};

				let next_action = self.revalidation_strategy.lock().next(
					block_number,
					Some(std::time::Duration::from_secs(60)),
					Some(20.into()),
				);
				let revalidation_strategy = self.revalidation_strategy.clone();
				let retracted = retracted.clone();

				async move {
					// We don't query block if we won't prune anything
					if !pool.validated_pool().status().is_empty() {
						let hashes = api.block_body(&id).await
							.unwrap_or_else(|e| {
								log::warn!("Prune known transactions: error request {:?}!", e);
								None
							})
							.unwrap_or_default()
							.into_iter()
							.map(|tx| pool.hash_of(&tx))
							.collect::<Vec<_>>();

						if let Err(e) = pool.prune_known(&id, &hashes) {
							log::error!("Cannot prune known in the pool {:?}!", e);
						}
					}

					if next_action.resubmit {
						let mut resubmit_transactions = Vec::new();

						for retracted_hash in retracted {
							// notify txs awaiting finality that it has been retracted
							pool.validated_pool().on_block_retracted(retracted_hash.clone());

							let block_transactions = api.block_body(&BlockId::hash(retracted_hash.clone())).await
								.unwrap_or_else(|e| {
									log::warn!("Failed to fetch block body {:?}!", e);
									None
								})
								.unwrap_or_default()
								.into_iter()
								.filter(|tx| tx.is_signed().unwrap_or(true));

							resubmit_transactions.extend(block_transactions);
						}
						if let Err(e) = pool.submit_at(&id, resubmit_transactions, true).await {
							log::debug!(
								target: "txpool",
								"[{:?}] Error re-submitting transactions: {:?}", id, e
							)
						}
					}

					if next_action.revalidate {
						if let Err(e) = pool.revalidate_ready(&id, next_action.revalidate_amount).await {
							log::warn!("Revalidate ready failed {:?}", e);
						}
					}

					revalidation_strategy.lock().clear();
				}.boxed()
			}
			ChainEvent::Finalized { hash } => {
				let pool = self.pool.clone();
				async move {
					if let Err(e) = pool.validated_pool().on_block_finalized(hash).await {
						log::warn!(
							target: "txpool",
							"Error [{}] occurred while attempting to notify watchers of finalization {}",
							e, hash
						)
					}
				}.boxed()
			}
		}
	}
}
