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

#![recursion_limit="256"]
#![warn(missing_docs)]
#![warn(unused_extern_crates)]

mod api;
mod revalidation;
mod metrics;

pub mod error;

#[cfg(any(feature = "test-helpers", test))]
pub mod testing;

pub use sc_transaction_graph as txpool;
pub use crate::api::{FullChainApi, LightChainApi};

use std::{collections::HashMap, sync::Arc, pin::Pin};
use futures::{prelude::*, future::ready, channel::oneshot};
use parking_lot::Mutex;

use sp_runtime::{
	generic::BlockId,
	traits::{Block as BlockT, NumberFor, AtLeast32Bit, Extrinsic, Zero},
};
use sp_transaction_pool::{
	TransactionPool, PoolStatus, ImportNotificationStream, TxHash, TransactionFor,
	TransactionStatusStreamFor, MaintainedTransactionPool, PoolFuture, ChainEvent,
	TransactionSource,
};
use wasm_timer::Instant;

use prometheus_endpoint::Registry as PrometheusRegistry;
use crate::metrics::MetricsLink as PrometheusMetrics;

type BoxedReadyIterator<Hash, Data> = Box<dyn Iterator<Item=Arc<sc_transaction_graph::base_pool::Transaction<Hash, Data>>> + Send>;

type ReadyIteratorFor<PoolApi> = BoxedReadyIterator<sc_transaction_graph::ExHash<PoolApi>, sc_transaction_graph::ExtrinsicFor<PoolApi>>;

type PolledIterator<PoolApi> = Pin<Box<dyn Future<Output=ReadyIteratorFor<PoolApi>> + Send>>;

/// Basic implementation of transaction pool that can be customized by providing PoolApi.
pub struct BasicPool<PoolApi, Block>
	where
		Block: BlockT,
		PoolApi: sc_transaction_graph::ChainApi<Block=Block, Hash=Block::Hash>,
{
	pool: Arc<sc_transaction_graph::Pool<PoolApi>>,
	api: Arc<PoolApi>,
	revalidation_strategy: Arc<Mutex<RevalidationStrategy<NumberFor<Block>>>>,
	revalidation_queue: Arc<revalidation::RevalidationQueue<PoolApi>>,
	ready_poll: Arc<Mutex<ReadyPoll<ReadyIteratorFor<PoolApi>, Block>>>,
	metrics: PrometheusMetrics,
}

struct ReadyPoll<T, Block: BlockT> {
	updated_at: NumberFor<Block>,
	pollers: Vec<(NumberFor<Block>, oneshot::Sender<T>)>,
}

impl<T, Block: BlockT> Default for ReadyPoll<T, Block> {
	fn default() -> Self {
		Self {
			updated_at: NumberFor::<Block>::zero(),
			pollers: Default::default(),
		}
	}
}

impl<T, Block: BlockT> ReadyPoll<T, Block> {
	fn trigger(&mut self, number: NumberFor<Block>, iterator_factory: impl Fn() -> T) {
		self.updated_at = number;

		let mut idx = 0;
		while idx < self.pollers.len() {
			if self.pollers[idx].0 <= number {
				let poller_sender = self.pollers.swap_remove(idx);
				log::debug!(target: "txpool", "Sending ready signal at block {}", number);
				let _ = poller_sender.1.send(iterator_factory());
			} else {
				idx += 1;
			}
		}
	}

	fn add(&mut self, number: NumberFor<Block>) -> oneshot::Receiver<T> {
		let (sender, receiver) = oneshot::channel();
		self.pollers.push((number, sender));
		receiver
	}

	fn updated_at(&self) -> NumberFor<Block> {
		self.updated_at
	}
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
		PoolApi: sc_transaction_graph::ChainApi<Block=Block, Hash=Block::Hash> + 'static,
{
	/// Create new basic transaction pool with provided api.
	///
	/// It will also optionally return background task that might be started by the
	/// caller.
	pub fn new(
		options: sc_transaction_graph::Options,
		pool_api: Arc<PoolApi>,
		prometheus: Option<&PrometheusRegistry>,
	) -> (Self, Option<Pin<Box<dyn Future<Output=()> + Send>>>) {
		Self::with_revalidation_type(options, pool_api, prometheus, RevalidationType::Full)
	}

	/// Create new basic transaction pool with provided api, for tests.
	#[cfg(test)]
	pub fn new_test(
		pool_api: Arc<PoolApi>,
	) -> (Self, Pin<Box<dyn Future<Output=()> + Send>>, intervalier::BackSignalControl) {
		let pool = Arc::new(sc_transaction_graph::Pool::new(Default::default(), pool_api.clone()));
		let (revalidation_queue, background_task, notifier) =
			revalidation::RevalidationQueue::new_test(pool_api.clone(), pool.clone());
		(
			BasicPool {
				api: pool_api,
				pool,
				revalidation_queue: Arc::new(revalidation_queue),
				revalidation_strategy: Arc::new(Mutex::new(RevalidationStrategy::Always)),
				ready_poll: Default::default(),
				metrics: Default::default(),
			},
			background_task,
			notifier,
		)
	}

	/// Create new basic transaction pool with provided api and custom
	/// revalidation type.
	pub fn with_revalidation_type(
		options: sc_transaction_graph::Options,
		pool_api: Arc<PoolApi>,
		prometheus: Option<&PrometheusRegistry>,
		revalidation_type: RevalidationType,
	) -> (Self, Option<Pin<Box<dyn Future<Output=()> + Send>>>) {
		let pool = Arc::new(sc_transaction_graph::Pool::new(options, pool_api.clone()));
		let (revalidation_queue, background_task) = match revalidation_type {
			RevalidationType::Light => (revalidation::RevalidationQueue::new(pool_api.clone(), pool.clone()), None),
			RevalidationType::Full => {
				let (queue, background) = revalidation::RevalidationQueue::new_background(pool_api.clone(), pool.clone());
				(queue, Some(background))
			},
		};

		(
			BasicPool {
				api: pool_api,
				pool,
				revalidation_queue: Arc::new(revalidation_queue),
				revalidation_strategy: Arc::new(Mutex::new(
					match revalidation_type {
						RevalidationType::Light => RevalidationStrategy::Light(RevalidationStatus::NotScheduled),
						RevalidationType::Full => RevalidationStrategy::Always,
					}
				)),
				ready_poll: Default::default(),
				metrics: PrometheusMetrics::new(prometheus),
			},
			background_task,
		)
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
		source: TransactionSource,
		xts: Vec<TransactionFor<Self>>,
	) -> PoolFuture<Vec<Result<TxHash<Self>, Self::Error>>, Self::Error> {
		let pool = self.pool.clone();
		let at = *at;

		self.metrics.report(|metrics| metrics.validations_scheduled.inc_by(xts.len() as u64));

		let metrics = self.metrics.clone();
		async move {
			let tx_count = xts.len();
			let res = pool.submit_at(&at, source, xts, false).await;
			metrics.report(|metrics| metrics.validations_finished.inc_by(tx_count as u64));
			res
		}.boxed()
	}

	fn submit_one(
		&self,
		at: &BlockId<Self::Block>,
		source: TransactionSource,
		xt: TransactionFor<Self>,
	) -> PoolFuture<TxHash<Self>, Self::Error> {
		let pool = self.pool.clone();
		let at = *at;

		self.metrics.report(|metrics| metrics.validations_scheduled.inc());

		let metrics = self.metrics.clone();
		async move {
			let res = pool.submit_one(&at, source, xt).await;

			metrics.report(|metrics| metrics.validations_finished.inc());
			res

		}.boxed()
	}

	fn submit_and_watch(
		&self,
		at: &BlockId<Self::Block>,
		source: TransactionSource,
		xt: TransactionFor<Self>,
	) -> PoolFuture<Box<TransactionStatusStreamFor<Self>>, Self::Error> {
		let at = *at;
		let pool = self.pool.clone();

		self.metrics.report(|metrics| metrics.validations_scheduled.inc());

		let metrics = self.metrics.clone();
		async move {
			let result = pool.submit_and_watch(&at, source, xt)
				.map(|result| result.map(|watcher| Box::new(watcher.into_stream()) as _))
				.await;

			metrics.report(|metrics| metrics.validations_finished.inc());

			result
		}.boxed()
	}

	fn remove_invalid(&self, hashes: &[TxHash<Self>]) -> Vec<Arc<Self::InPoolTransaction>> {
		self.pool.validated_pool().remove_invalid(hashes)
	}

	fn status(&self) -> PoolStatus {
		self.pool.validated_pool().status()
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

	fn ready_at(&self, at: NumberFor<Self::Block>) -> PolledIterator<PoolApi> {
		if self.ready_poll.lock().updated_at() >= at {
			let iterator: ReadyIteratorFor<PoolApi> = Box::new(self.pool.validated_pool().ready());
			return Box::pin(futures::future::ready(iterator));
		}

		Box::pin(
			self.ready_poll
				.lock()
				.add(at)
				.map(|received| received.unwrap_or_else(|e| {
					log::warn!("Error receiving pending set: {:?}", e);
					Box::new(vec![].into_iter())
				}))
		)
	}

	fn ready(&self) -> ReadyIteratorFor<PoolApi> {
		Box::new(self.pool.validated_pool().ready())
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
			},
			Self::Always => RevalidationAction {
				revalidate: true,
				resubmit: true,
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
						log::trace!(target: "txpool", "Skipping chain event - no number for that block {:?}", id);
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
				let revalidation_queue = self.revalidation_queue.clone();
				let ready_poll = self.ready_poll.clone();

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

					let extra_pool = pool.clone();
					// After #5200 lands, this arguably might be moved to the handler of "all blocks notification".
					ready_poll.lock().trigger(block_number, move || Box::new(extra_pool.validated_pool().ready()));

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
						if let Err(e) = pool.submit_at(
							&id,
							// These transactions are coming from retracted blocks, we should
							// simply consider them external.
							TransactionSource::External,
							resubmit_transactions,
							true
						).await {
							log::debug!(
								target: "txpool",
								"[{:?}] Error re-submitting transactions: {:?}", id, e
							)
						}
					}

					if next_action.revalidate {
						let hashes = pool.validated_pool().ready().map(|tx| tx.hash.clone()).collect();
						revalidation_queue.revalidate_later(block_number, hashes).await;
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
