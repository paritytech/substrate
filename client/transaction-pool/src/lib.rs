// This file is part of Substrate.

// Copyright (C) 2018-2022 Parity Technologies (UK) Ltd.
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

//! Substrate transaction pool implementation.

#![recursion_limit = "256"]
#![warn(missing_docs)]
#![warn(unused_extern_crates)]

mod api;
pub mod error;
mod graph;
mod metrics;
mod revalidation;
#[cfg(test)]
mod tests;

pub use crate::api::FullChainApi;
use async_trait::async_trait;
use futures::{
	channel::oneshot,
	future::{self, ready},
	prelude::*,
};
pub use graph::{
	base_pool::Limit as PoolLimit, ChainApi, Options, Pool, Transaction, ValidatedTransaction,
};
use parking_lot::Mutex;
use std::{
	collections::{HashMap, HashSet},
	pin::Pin,
	sync::Arc,
};

use graph::{ExtrinsicHash, IsValidator};
use sc_transaction_pool_api::{
	error::Error as TxPoolError, ChainEvent, ImportNotificationStream, MaintainedTransactionPool,
	PoolFuture, PoolStatus, ReadyTransactions, TransactionFor, TransactionPool, TransactionSource,
	TransactionStatusStreamFor, TxHash,
};
use sp_core::traits::SpawnEssentialNamed;
use sp_runtime::{
	generic::BlockId,
	traits::{AtLeast32Bit, Block as BlockT, Extrinsic, Header as HeaderT, NumberFor, Zero},
};
use std::time::Instant;

use crate::metrics::MetricsLink as PrometheusMetrics;
use prometheus_endpoint::Registry as PrometheusRegistry;

use sp_blockchain::TreeRoute;

type BoxedReadyIterator<Hash, Data> =
	Box<dyn ReadyTransactions<Item = Arc<graph::base_pool::Transaction<Hash, Data>>> + Send>;

type ReadyIteratorFor<PoolApi> =
	BoxedReadyIterator<graph::ExtrinsicHash<PoolApi>, graph::ExtrinsicFor<PoolApi>>;

type PolledIterator<PoolApi> = Pin<Box<dyn Future<Output = ReadyIteratorFor<PoolApi>> + Send>>;

/// A transaction pool for a full node.
pub type FullPool<Block, Client> = BasicPool<FullChainApi<Client, Block>, Block>;

/// Basic implementation of transaction pool that can be customized by providing PoolApi.
pub struct BasicPool<PoolApi, Block>
where
	Block: BlockT,
	PoolApi: graph::ChainApi<Block = Block>,
{
	pool: Arc<graph::Pool<PoolApi>>,
	api: Arc<PoolApi>,
	revalidation_strategy: Arc<Mutex<RevalidationStrategy<NumberFor<Block>>>>,
	revalidation_queue: Arc<revalidation::RevalidationQueue<PoolApi>>,
	ready_poll: Arc<Mutex<ReadyPoll<ReadyIteratorFor<PoolApi>, Block>>>,
	metrics: PrometheusMetrics,
	enactment_state: Arc<Mutex<EnactmentState<Block>>>,
}

struct ReadyPoll<T, Block: BlockT> {
	updated_at: NumberFor<Block>,
	pollers: Vec<(NumberFor<Block>, oneshot::Sender<T>)>,
}

impl<T, Block: BlockT> Default for ReadyPoll<T, Block> {
	fn default() -> Self {
		Self { updated_at: NumberFor::<Block>::zero(), pollers: Default::default() }
	}
}

impl<T, Block: BlockT> ReadyPoll<T, Block> {
	fn new(best_block_number: NumberFor<Block>) -> Self {
		Self { updated_at: best_block_number, pollers: Default::default() }
	}

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

impl<PoolApi, Block> parity_util_mem::MallocSizeOf for BasicPool<PoolApi, Block>
where
	PoolApi: graph::ChainApi<Block = Block>,
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
	PoolApi: graph::ChainApi<Block = Block> + 'static,
{
	/// Create new basic transaction pool with provided api, for tests.
	pub fn new_test(
		pool_api: Arc<PoolApi>,
		best_block_hash: Block::Hash,
		finalized_hash: Block::Hash,
	) -> (Self, Pin<Box<dyn Future<Output = ()> + Send>>) {
		let pool = Arc::new(graph::Pool::new(Default::default(), true.into(), pool_api.clone()));
		let (revalidation_queue, background_task) =
			revalidation::RevalidationQueue::new_background(pool_api.clone(), pool.clone());
		(
			Self {
				api: pool_api,
				pool,
				revalidation_queue: Arc::new(revalidation_queue),
				revalidation_strategy: Arc::new(Mutex::new(RevalidationStrategy::Always)),
				ready_poll: Default::default(),
				metrics: Default::default(),
				enactment_state: Arc::new(Mutex::new(EnactmentState::new(
					best_block_hash,
					finalized_hash,
				))),
			},
			background_task,
		)
	}

	/// Create new basic transaction pool with provided api and custom
	/// revalidation type.
	pub fn with_revalidation_type(
		options: graph::Options,
		is_validator: IsValidator,
		pool_api: Arc<PoolApi>,
		prometheus: Option<&PrometheusRegistry>,
		revalidation_type: RevalidationType,
		spawner: impl SpawnEssentialNamed,
		best_block_number: NumberFor<Block>,
		best_block_hash: Block::Hash,
		finalized_hash: Block::Hash,
	) -> Self {
		let pool = Arc::new(graph::Pool::new(options, is_validator, pool_api.clone()));
		let (revalidation_queue, background_task) = match revalidation_type {
			RevalidationType::Light =>
				(revalidation::RevalidationQueue::new(pool_api.clone(), pool.clone()), None),
			RevalidationType::Full => {
				let (queue, background) =
					revalidation::RevalidationQueue::new_background(pool_api.clone(), pool.clone());
				(queue, Some(background))
			},
		};

		if let Some(background_task) = background_task {
			spawner.spawn_essential("txpool-background", Some("transaction-pool"), background_task);
		}

		Self {
			api: pool_api,
			pool,
			revalidation_queue: Arc::new(revalidation_queue),
			revalidation_strategy: Arc::new(Mutex::new(match revalidation_type {
				RevalidationType::Light =>
					RevalidationStrategy::Light(RevalidationStatus::NotScheduled),
				RevalidationType::Full => RevalidationStrategy::Always,
			})),
			ready_poll: Arc::new(Mutex::new(ReadyPoll::new(best_block_number))),
			metrics: PrometheusMetrics::new(prometheus),
			enactment_state: Arc::new(Mutex::new(EnactmentState::new(
				best_block_hash,
				finalized_hash,
			))),
		}
	}

	/// Gets shared reference to the underlying pool.
	pub fn pool(&self) -> &Arc<graph::Pool<PoolApi>> {
		&self.pool
	}

	/// Get access to the underlying api
	pub fn api(&self) -> &PoolApi {
		&self.api
	}
}

impl<PoolApi, Block> TransactionPool for BasicPool<PoolApi, Block>
where
	Block: BlockT,
	PoolApi: 'static + graph::ChainApi<Block = Block>,
{
	type Block = PoolApi::Block;
	type Hash = graph::ExtrinsicHash<PoolApi>;
	type InPoolTransaction = graph::base_pool::Transaction<TxHash<Self>, TransactionFor<Self>>;
	type Error = PoolApi::Error;

	fn submit_at(
		&self,
		at: &BlockId<Self::Block>,
		source: TransactionSource,
		xts: Vec<TransactionFor<Self>>,
	) -> PoolFuture<Vec<Result<TxHash<Self>, Self::Error>>, Self::Error> {
		let pool = self.pool.clone();
		let at = *at;

		self.metrics
			.report(|metrics| metrics.submitted_transactions.inc_by(xts.len() as u64));

		async move { pool.submit_at(&at, source, xts).await }.boxed()
	}

	fn submit_one(
		&self,
		at: &BlockId<Self::Block>,
		source: TransactionSource,
		xt: TransactionFor<Self>,
	) -> PoolFuture<TxHash<Self>, Self::Error> {
		let pool = self.pool.clone();
		let at = *at;

		self.metrics.report(|metrics| metrics.submitted_transactions.inc());

		async move { pool.submit_one(&at, source, xt).await }.boxed()
	}

	fn submit_and_watch(
		&self,
		at: &BlockId<Self::Block>,
		source: TransactionSource,
		xt: TransactionFor<Self>,
	) -> PoolFuture<Pin<Box<TransactionStatusStreamFor<Self>>>, Self::Error> {
		let at = *at;
		let pool = self.pool.clone();

		self.metrics.report(|metrics| metrics.submitted_transactions.inc());

		async move {
			let watcher = pool.submit_and_watch(&at, source, xt).await?;

			Ok(watcher.into_stream().boxed())
		}
		.boxed()
	}

	fn remove_invalid(&self, hashes: &[TxHash<Self>]) -> Vec<Arc<Self::InPoolTransaction>> {
		let removed = self.pool.validated_pool().remove_invalid(hashes);
		self.metrics
			.report(|metrics| metrics.validations_invalid.inc_by(removed.len() as u64));
		removed
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
		let status = self.status();
		// If there are no transactions in the pool, it is fine to return early.
		//
		// There could be transaction being added because of some re-org happening at the relevant
		// block, but this is relative unlikely.
		if status.ready == 0 && status.future == 0 {
			return async { Box::new(std::iter::empty()) as Box<_> }.boxed()
		}

		if self.ready_poll.lock().updated_at() >= at {
			log::trace!(target: "txpool", "Transaction pool already processed block  #{}", at);
			let iterator: ReadyIteratorFor<PoolApi> = Box::new(self.pool.validated_pool().ready());
			return async move { iterator }.boxed()
		}

		self.ready_poll
			.lock()
			.add(at)
			.map(|received| {
				received.unwrap_or_else(|e| {
					log::warn!("Error receiving pending set: {:?}", e);
					Box::new(std::iter::empty())
				})
			})
			.boxed()
	}

	fn ready(&self) -> ReadyIteratorFor<PoolApi> {
		Box::new(self.pool.validated_pool().ready())
	}
}

impl<Block, Client> FullPool<Block, Client>
where
	Block: BlockT,
	Client: sp_api::ProvideRuntimeApi<Block>
		+ sc_client_api::BlockBackend<Block>
		+ sc_client_api::blockchain::HeaderBackend<Block>
		+ sp_runtime::traits::BlockIdTo<Block>
		+ sc_client_api::ExecutorProvider<Block>
		+ sc_client_api::UsageProvider<Block>
		+ sp_blockchain::HeaderMetadata<Block, Error = sp_blockchain::Error>
		+ Send
		+ Sync
		+ 'static,
	Client::Api: sp_transaction_pool::runtime_api::TaggedTransactionQueue<Block>,
{
	/// Create new basic transaction pool for a full node with the provided api.
	pub fn new_full(
		options: graph::Options,
		is_validator: IsValidator,
		prometheus: Option<&PrometheusRegistry>,
		spawner: impl SpawnEssentialNamed,
		client: Arc<Client>,
	) -> Arc<Self> {
		let pool_api = Arc::new(FullChainApi::new(client.clone(), prometheus, &spawner));
		let pool = Arc::new(Self::with_revalidation_type(
			options,
			is_validator,
			pool_api,
			prometheus,
			RevalidationType::Full,
			spawner,
			client.usage_info().chain.best_number,
			client.usage_info().chain.best_hash,
			client.usage_info().chain.finalized_hash,
		));

		// make transaction pool available for off-chain runtime calls.
		client.execution_extensions().register_transaction_pool(&pool);

		pool
	}
}

impl<Block, Client> sc_transaction_pool_api::LocalTransactionPool
	for BasicPool<FullChainApi<Client, Block>, Block>
where
	Block: BlockT,
	Client: sp_api::ProvideRuntimeApi<Block>
		+ sc_client_api::BlockBackend<Block>
		+ sc_client_api::blockchain::HeaderBackend<Block>
		+ sp_runtime::traits::BlockIdTo<Block>
		+ sp_blockchain::HeaderMetadata<Block, Error = sp_blockchain::Error>,
	Client: Send + Sync + 'static,
	Client::Api: sp_transaction_pool::runtime_api::TaggedTransactionQueue<Block>,
{
	type Block = Block;
	type Hash = graph::ExtrinsicHash<FullChainApi<Client, Block>>;
	type Error = <FullChainApi<Client, Block> as graph::ChainApi>::Error;

	fn submit_local(
		&self,
		at: &BlockId<Self::Block>,
		xt: sc_transaction_pool_api::LocalTransactionFor<Self>,
	) -> Result<Self::Hash, Self::Error> {
		use sp_runtime::{
			traits::SaturatedConversion, transaction_validity::TransactionValidityError,
		};

		let validity = self
			.api
			.validate_transaction_blocking(at, TransactionSource::Local, xt.clone())?
			.map_err(|e| {
				Self::Error::Pool(match e {
					TransactionValidityError::Invalid(i) => TxPoolError::InvalidTransaction(i),
					TransactionValidityError::Unknown(u) => TxPoolError::UnknownTransaction(u),
				})
			})?;

		let (hash, bytes) = self.pool.validated_pool().api().hash_and_length(&xt);
		let block_number = self
			.api
			.block_id_to_number(at)?
			.ok_or_else(|| error::Error::BlockIdConversion(format!("{:?}", at)))?;

		let validated = ValidatedTransaction::valid_at(
			block_number.saturated_into::<u64>(),
			hash,
			TransactionSource::Local,
			xt,
			bytes,
			validity,
		);

		self.pool.validated_pool().submit(vec![validated]).remove(0)
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
			Self::Always => RevalidationAction { revalidate: true, resubmit: true },
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
			},
			Self::Scheduled(revalidate_at_time, revalidate_at_block) => {
				let is_required =
					revalidate_at_time.map(|at| Instant::now() >= at).unwrap_or(false) ||
						revalidate_at_block.map(|at| block >= at).unwrap_or(false);
				if is_required {
					*self = Self::InProgress;
				}
				is_required
			},
			Self::InProgress => false,
		}
	}
}

/// Prune the known txs for the given block.
async fn prune_known_txs_for_block<Block: BlockT, Api: graph::ChainApi<Block = Block>>(
	block_id: BlockId<Block>,
	api: &Api,
	pool: &graph::Pool<Api>,
) -> Vec<ExtrinsicHash<Api>> {
	let extrinsics = api
		.block_body(&block_id)
		.await
		.unwrap_or_else(|e| {
			log::warn!("Prune known transactions: error request: {}", e);
			None
		})
		.unwrap_or_default();

	let hashes = extrinsics.iter().map(|tx| pool.hash_of(tx)).collect::<Vec<_>>();

	log::trace!(target: "txpool", "Pruning transactions: {:?}", hashes);

	let header = match api.block_header(&block_id) {
		Ok(Some(h)) => h,
		Ok(None) => {
			log::debug!(target: "txpool", "Could not find header for {:?}.", block_id);
			return hashes
		},
		Err(e) => {
			log::debug!(target: "txpool", "Error retrieving header for {:?}: {}", block_id, e);
			return hashes
		},
	};

	if let Err(e) = pool.prune(&block_id, &BlockId::hash(*header.parent_hash()), &extrinsics).await
	{
		log::error!("Cannot prune known in the pool: {}", e);
	}

	hashes
}

impl<PoolApi, Block> BasicPool<PoolApi, Block>
where
	Block: BlockT,
	PoolApi: 'static + graph::ChainApi<Block = Block>,
{
	/// Part of `MaintainedTransactionPool::maintain` procedure. Handles enactment and retraction of
	/// blocks, sends transaction notifications.
	async fn handle_enactment(&self, hash: Block::Hash, tree_route: TreeRoute<Block>) {
		log::trace!(target: "txpool", "handle_enactment hash:{hash:?} tree_route: {tree_route:?}");
		let pool = self.pool.clone();
		let api = self.api.clone();

		let id = BlockId::hash(hash);
		let block_number = match api.block_id_to_number(&id) {
			Ok(Some(number)) => number,
			_ => {
				log::trace!(
				target: "txpool",
				"Skipping chain event - no number for that block {:?}",
				id,
				);
				return
			},
		};

		let next_action = self.revalidation_strategy.lock().next(
			block_number,
			Some(std::time::Duration::from_secs(60)),
			Some(20u32.into()),
		);
		let revalidation_strategy = self.revalidation_strategy.clone();
		let revalidation_queue = self.revalidation_queue.clone();
		let ready_poll = self.ready_poll.clone();
		let metrics = self.metrics.clone();

		// We keep track of everything we prune so that later we won't add
		// transactions with those hashes from the retracted blocks.
		let mut pruned_log = HashSet::<ExtrinsicHash<PoolApi>>::new();

		// If there is a tree route, we use this to prune known tx based on the enacted
		// blocks. Before pruning enacted transactions, we inform the listeners about
		// retracted blocks and their transactions. This order is important, because
		// if we enact and retract the same transaction at the same time, we want to
		// send first the retract and than the prune event.
		for retracted in tree_route.retracted() {
			// notify txs awaiting finality that it has been retracted
			pool.validated_pool().on_block_retracted(retracted.hash);
		}

		future::join_all(
			tree_route
				.enacted()
				.iter()
				.map(|h| prune_known_txs_for_block(BlockId::Hash(h.hash), &*api, &*pool)),
		)
		.await
		.into_iter()
		.for_each(|enacted_log| {
			pruned_log.extend(enacted_log);
		});

		metrics.report(|metrics| metrics.block_transactions_pruned.inc_by(pruned_log.len() as u64));

		if next_action.resubmit {
			let mut resubmit_transactions = Vec::new();

			for retracted in tree_route.retracted() {
				let hash = retracted.hash;

				let block_transactions = api
					.block_body(&BlockId::hash(hash))
					.await
					.unwrap_or_else(|e| {
						log::warn!("Failed to fetch block body: {}", e);
						None
					})
					.unwrap_or_default()
					.into_iter()
					.filter(|tx| tx.is_signed().unwrap_or(true));

				let mut resubmitted_to_report = 0;

				resubmit_transactions.extend(block_transactions.into_iter().filter(|tx| {
					let tx_hash = pool.hash_of(tx);
					let contains = pruned_log.contains(&tx_hash);

					// need to count all transactions, not just filtered, here
					resubmitted_to_report += 1;

					if !contains {
						log::debug!(
						target: "txpool",
						"[{:?}]: Resubmitting from retracted block {:?}",
						tx_hash,
						hash,
						);
					}
					!contains
				}));

				metrics.report(|metrics| {
					metrics.block_transactions_resubmitted.inc_by(resubmitted_to_report)
				});
			}

			if let Err(e) = pool
				.resubmit_at(
					&id,
					// These transactions are coming from retracted blocks, we should
					// simply consider them external.
					TransactionSource::External,
					resubmit_transactions,
				)
				.await
			{
				log::debug!(
				target: "txpool",
				"[{:?}] Error re-submitting transactions: {}",
				id,
				e,
				)
			}
		}

		let extra_pool = pool.clone();
		// After #5200 lands, this arguably might be moved to the
		// handler of "all blocks notification".
		ready_poll
			.lock()
			.trigger(block_number, move || Box::new(extra_pool.validated_pool().ready()));

		if next_action.revalidate {
			let hashes = pool.validated_pool().ready().map(|tx| tx.hash).collect();
			revalidation_queue.revalidate_later(block_number, hashes).await;

			revalidation_strategy.lock().clear();
		}
	}
}

#[async_trait]
impl<PoolApi, Block> MaintainedTransactionPool for BasicPool<PoolApi, Block>
where
	Block: BlockT,
	PoolApi: 'static + graph::ChainApi<Block = Block>,
{
	async fn maintain(&self, event: ChainEvent<Self::Block>) {
		let prev_finalized_block = self.enactment_state.lock().recent_finalized_block;
		let compute_tree_route = |from, to| -> Result<TreeRoute<Block>, String> {
			match self.api.tree_route(from, to) {
				Ok(tree_route) => Ok(tree_route),
				Err(e) =>
					return Err(format!(
						"Error [{e}] occured while computing tree_route from {from:?} to \
					 previously finalized: {to:?}"
					)),
			}
		};

		let result = self
			.enactment_state
			.lock()
			.update_and_check_if_new_enactment_is_valid(&event, &compute_tree_route);
		match result {
			Err(msg) => {
				log::warn!(target: "txpool", "{msg}");
				return
			},
			Ok(None) => {},
			Ok(Some(tree_route)) => {
				let hash = match event {
					ChainEvent::NewBestBlock { hash, .. } | ChainEvent::Finalized { hash, .. } =>
						hash,
				};

				self.handle_enactment(hash, tree_route).await;
			},
		};

		if let ChainEvent::Finalized { hash, tree_route } = event {
			log::trace!(target:"txpool", "on-finalized enacted: {tree_route:?}, previously finalized: \
						{prev_finalized_block:?}");
			for hash in tree_route.iter().chain(std::iter::once(&hash)) {
				if let Err(e) = self.pool.validated_pool().on_block_finalized(*hash).await {
					log::warn!(
						target: "txpool",
						"Error [{}] occurred while attempting to notify watchers about finalization {}",
						hash, e
					)
				}
			}
		}
	}
}

/// Helper struct for deciding if core part of maintenance procedure shall be executed.
/// It is publicly exposed only for tests purposes (due to cyclic deps sc_transaction_pool and
/// substrate_test_runtime_transaction_pool).
///
/// For the following chain:
///   B1-C1-D1-E1
///  /
/// A
///  \
///   B2-C2-D2-E2
///
/// Some scenarios and expected behavior for seqeunce of `NewBestBlock` (nbb) and `Finalized` (f)
/// events: `nbb(C1)`, `f(C1)` -> false (handle_enactment was already performed in `nbb(C1))`
/// `f(C1)`, `nbb(C1)` -> false (handle_enactment was already performed in `f(C1))`
///
/// `f(C1)`, `nbb(D2)` -> false (handle_enactment was already performed in `f(C1)`, we should not
/// retract finalized block)
/// `f(C1)`, `f(C2)`, `nbb(C1)` -> false
/// `nbb(C1)`, `nbb(C2)` -> true (switching fork is OK)
/// `nbb(B1)`, `nbb(B2)` -> true
/// `nbb(B1)`, `nbb(C1)`, `f(C1)` -> false (handle_enactment was already performed in `nbb(B1)`
/// `nbb(C1)`, `f(B1)` -> false (handle_enactment was already performed in `nbb(B2)`
struct EnactmentState<Block>
where
	Block: BlockT,
{
	recent_best_block: Block::Hash,
	recent_finalized_block: Block::Hash,
}

impl<Block> EnactmentState<Block>
where
	Block: BlockT,
{
	fn new(recent_best_block: Block::Hash, recent_finalized_block: Block::Hash) -> Self {
		EnactmentState { recent_best_block, recent_finalized_block }
	}

	/// This function returns `Some(tree_route)` if blocks enact/retract process (implemented
	/// in `handle_enactment` function) should be performed based on:
	/// - recent_finalized_block
	/// - recent_best_block
	/// - newly provided block in event
	/// `tree_route` contains blocks to be enacted/retracted.
	///
	/// If enactment process is not needed then `None` is returned.
	/// An error message is returned when computing `tree_route` fails.
	fn update_and_check_if_new_enactment_is_valid<F>(
		&mut self,
		event: &ChainEvent<Block>,
		tree_route: &F,
	) -> Result<Option<TreeRoute<Block>>, String>
	where
		F: Fn(Block::Hash, Block::Hash) -> Result<TreeRoute<Block>, String>,
	{
		let (new_hash, finalized) = match event {
			ChainEvent::NewBestBlock { hash, .. } => (*hash, false),
			ChainEvent::Finalized { hash, .. } => (*hash, true),
		};

		// compute actual tree route from best_block to notified block, and use it instead of
		// tree_route provided with event
		let tree_route = tree_route(self.recent_best_block, new_hash)?;

		log::trace!(
			target: "txpool",
			"resolve hash:{:?} finalized:{:?} tree_route:{:?} best_block:{:?} finalized_block:{:?}",
			new_hash, finalized, tree_route, self.recent_best_block, self.recent_finalized_block
		);

		// block was already finalized
		if self.recent_finalized_block == new_hash {
			log::trace!(target:"txpool", "handle_enactment: block already finalized");
			return Ok(None)
		}

		// check if recently finalized block is on retracted path...
		if tree_route.retracted().iter().any(|x| x.hash == self.recent_finalized_block) {
			log::debug!(
				target: "txpool",
				"Recently finalized block {} would be retracted by ChainEvent {}, skipping",
				self.recent_finalized_block, new_hash
			);
			return Ok(None)
		}

		if finalized {
			self.recent_finalized_block = new_hash;
			// If there are no enacted blocks in best_block -> hash tree_route, it means that
			// block being finalized was already enacted. (This case also covers best_block ==
			// new_hash) recent_best_block remains valid
			if tree_route.enacted().is_empty() {
				log::trace!(
					target: "txpool",
					"handle_enactment: no newly enacted blocks since recent best block"
				);
				return Ok(None)
			}
			//otherwise enacted finalized block becomes best block...
		}

		self.recent_best_block = new_hash;

		Ok(Some(tree_route))
	}
}

/// Inform the transaction pool about imported and finalized blocks.
pub async fn notification_future<Client, Pool, Block>(client: Arc<Client>, txpool: Arc<Pool>)
where
	Block: BlockT,
	Client: sc_client_api::BlockchainEvents<Block>,
	Pool: MaintainedTransactionPool<Block = Block>,
{
	let import_stream = client
		.import_notification_stream()
		.filter_map(|n| ready(n.try_into().ok()))
		.fuse();
	let finality_stream = client.finality_notification_stream().map(Into::into).fuse();

	futures::stream::select(import_stream, finality_stream)
		.for_each(|evt| txpool.maintain(evt))
		.await
}

#[cfg(test)]
mod enactment_state_tests {
	use sp_blockchain::{HashAndNumber, TreeRoute};
	use substrate_test_runtime_client::runtime::{Block, Hash};

	// some helpers for convenient blocks' hash naming
	fn a() -> HashAndNumber<Block> {
		HashAndNumber { number: 1, hash: Hash::from([0xAA; 32]) }
	}
	fn b1() -> HashAndNumber<Block> {
		HashAndNumber { number: 2, hash: Hash::from([0xB1; 32]) }
	}
	fn c1() -> HashAndNumber<Block> {
		HashAndNumber { number: 3, hash: Hash::from([0xC1; 32]) }
	}
	fn d1() -> HashAndNumber<Block> {
		HashAndNumber { number: 4, hash: Hash::from([0xD1; 32]) }
	}
	fn e1() -> HashAndNumber<Block> {
		HashAndNumber { number: 5, hash: Hash::from([0xE1; 32]) }
	}
	fn b2() -> HashAndNumber<Block> {
		HashAndNumber { number: 2, hash: Hash::from([0xB2; 32]) }
	}
	fn c2() -> HashAndNumber<Block> {
		HashAndNumber { number: 3, hash: Hash::from([0xC2; 32]) }
	}
	fn d2() -> HashAndNumber<Block> {
		HashAndNumber { number: 4, hash: Hash::from([0xD2; 32]) }
	}
	fn e2() -> HashAndNumber<Block> {
		HashAndNumber { number: 5, hash: Hash::from([0xE2; 32]) }
	}

	/// mock tree_route computing function for simple two-forks chain
	fn tree_route(from: Hash, to: Hash) -> Result<TreeRoute<Block>, String> {
		let chain = vec![e1(), d1(), c1(), b1(), a(), b2(), c2(), d2(), e2()];
		let pivot = 4_usize;

		let from = chain
			.iter()
			.position(|bn| bn.hash == from)
			.ok_or("existing block should be given")?;
		let to = chain
			.iter()
			.position(|bn| bn.hash == to)
			.ok_or("existing block should be given")?;

		//    B1-C1-D1-E1
		//   /
		//  A
		//   \
		//    B2-C2-D2-E2
		//
		//  [E1 D1 C1 B1 A B2 C2 D2 E2]

		let vec: Vec<HashAndNumber<Block>> = if from < to {
			chain.into_iter().skip(from).take(to - from + 1).collect()
		} else {
			chain.into_iter().skip(to).take(from - to + 1).rev().collect()
		};

		let pivot = if from <= pivot && to <= pivot {
			if from < to {
				to - from
			} else {
				0
			}
		} else if from >= pivot && to >= pivot {
			if from < to {
				0
			} else {
				from - to
			}
		} else {
			if from < to {
				pivot - from
			} else {
				from - pivot
			}
		};

		Ok(TreeRoute::new(vec, pivot))
	}

	mod mock_tree_route_tests {
		use super::*;

		/// asserts that tree routes are equal
		fn assert_treeroute_eq(expected: TreeRoute<Block>, result: TreeRoute<Block>) {
			assert_eq!(result.common_block().hash, expected.common_block().hash);
			assert_eq!(result.enacted().len(), expected.enacted().len());
			assert_eq!(result.retracted().len(), expected.retracted().len());
			assert!(result
				.enacted()
				.iter()
				.zip(expected.enacted().iter())
				.all(|(a, b)| a.hash == b.hash));
			assert!(result
				.retracted()
				.iter()
				.zip(expected.retracted().iter())
				.all(|(a, b)| a.hash == b.hash));
		}

		// some tests for mock tree_route function
		#[test]
		fn tree_route_mock_test_01() {
			let result = tree_route(b1().hash, a().hash).expect("tree route exists");
			let expected = TreeRoute::new(vec![b1(), a()], 1);
			assert_treeroute_eq(result, expected);
		}

		#[test]
		fn tree_route_mock_test_02() {
			let result = tree_route(a().hash, b1().hash).expect("tree route exists");
			let expected = TreeRoute::new(vec![a(), b1()], 0);
			assert_treeroute_eq(result, expected);
		}

		#[test]
		fn tree_route_mock_test_03() {
			let result = tree_route(a().hash, c2().hash).expect("tree route exists");
			let expected = TreeRoute::new(vec![a(), b2(), c2()], 0);
			assert_treeroute_eq(result, expected);
		}

		#[test]
		fn tree_route_mock_test_04() {
			let result = tree_route(e2().hash, a().hash).expect("tree route exists");
			let expected = TreeRoute::new(vec![e2(), d2(), c2(), b2(), a()], 4);
			assert_treeroute_eq(result, expected);
		}

		#[test]
		fn tree_route_mock_test_05() {
			let result = tree_route(d1().hash, b1().hash).expect("tree route exists");
			let expected = TreeRoute::new(vec![d1(), c1(), b1()], 2);
			assert_treeroute_eq(result, expected);
		}

		#[test]
		fn tree_route_mock_test_06() {
			let result = tree_route(d2().hash, b2().hash).expect("tree route exists");
			let expected = TreeRoute::new(vec![d2(), c2(), b2()], 2);
			assert_treeroute_eq(result, expected);
		}

		#[test]
		fn tree_route_mock_test_07() {
			let result = tree_route(b1().hash, d1().hash).expect("tree route exists");
			let expected = TreeRoute::new(vec![b1(), c1(), d1()], 0);
			assert_treeroute_eq(result, expected);
		}

		#[test]
		fn tree_route_mock_test_08() {
			let result = tree_route(b2().hash, d2().hash).expect("tree route exists");
			let expected = TreeRoute::new(vec![b2(), c2(), d2()], 0);
			assert_treeroute_eq(result, expected);
		}

		#[test]
		fn tree_route_mock_test_09() {
			let result = tree_route(e2().hash, e1().hash).expect("tree route exists");
			let expected =
				TreeRoute::new(vec![e2(), d2(), c2(), b2(), a(), b1(), c1(), d1(), e1()], 4);
			assert_treeroute_eq(result, expected);
		}

		#[test]
		fn tree_route_mock_test_10() {
			let result = tree_route(e1().hash, e2().hash).expect("tree route exists");
			let expected =
				TreeRoute::new(vec![e1(), d1(), c1(), b1(), a(), b2(), c2(), d2(), e2()], 4);
			assert_treeroute_eq(result, expected);
		}
		#[test]
		fn tree_route_mock_test_11() {
			let result = tree_route(b1().hash, c2().hash).expect("tree route exists");
			let expected = TreeRoute::new(vec![b1(), a(), b2(), c2()], 1);
			assert_treeroute_eq(result, expected);
		}

		#[test]
		fn tree_route_mock_test_12() {
			let result = tree_route(d2().hash, b1().hash).expect("tree route exists");
			let expected = TreeRoute::new(vec![d2(), c2(), b2(), a(), b1()], 3);
			assert_treeroute_eq(result, expected);
		}

		#[test]
		fn tree_route_mock_test_13() {
			let result = tree_route(c2().hash, e1().hash).expect("tree route exists");
			let expected = TreeRoute::new(vec![c2(), b2(), a(), b1(), c1(), d1(), e1()], 2);
			assert_treeroute_eq(result, expected);
		}

		#[test]
		fn tree_route_mock_test_14() {
			let result = tree_route(b1().hash, b1().hash).expect("tree route exists");
			let expected = TreeRoute::new(vec![b1()], 0);
			assert_treeroute_eq(result, expected);
		}

		#[test]
		fn tree_route_mock_test_15() {
			let result = tree_route(b2().hash, b2().hash).expect("tree route exists");
			let expected = TreeRoute::new(vec![b2()], 0);
			assert_treeroute_eq(result, expected);
		}

		#[test]
		fn tree_route_mock_test_16() {
			let result = tree_route(a().hash, a().hash).expect("tree route exists");
			let expected = TreeRoute::new(vec![a()], 0);
			assert_treeroute_eq(result, expected);
		}
	}

	use super::EnactmentState;
	use sc_transaction_pool_api::ChainEvent;
	use std::sync::Arc;

	fn trigger_new_best_block(
		state: &mut EnactmentState<Block>,
		from: HashAndNumber<Block>,
		acted_on: HashAndNumber<Block>,
	) -> bool {
		let (from, acted_on) = (from.hash, acted_on.hash);

		let event_tree_route = tree_route(from, acted_on).expect("Tree route exists");

		state
			.update_and_check_if_new_enactment_is_valid(
				&ChainEvent::NewBestBlock {
					hash: acted_on,
					tree_route: Some(Arc::new(event_tree_route)),
				},
				&tree_route,
			)
			.unwrap()
			.is_some()
	}

	fn trigger_finalized(
		state: &mut EnactmentState<Block>,
		from: HashAndNumber<Block>,
		acted_on: HashAndNumber<Block>,
	) -> bool {
		let (from, acted_on) = (from.hash, acted_on.hash);

		let v = tree_route(from, acted_on)
			.expect("Tree route exists")
			.enacted()
			.iter()
			.map(|h| h.hash)
			.collect::<Vec<_>>();

		state
			.update_and_check_if_new_enactment_is_valid(
				&ChainEvent::Finalized { hash: acted_on, tree_route: v.into() },
				&tree_route,
			)
			.unwrap()
			.is_some()
	}

	fn assert_es_eq(
		es: &EnactmentState<Block>,
		expected_best_block: HashAndNumber<Block>,
		expected_finalized_block: HashAndNumber<Block>,
	) {
		assert_eq!(es.recent_best_block, expected_best_block.hash);
		assert_eq!(es.recent_finalized_block, expected_finalized_block.hash);
	}

	#[test]
	fn test_enactment_helper() {
		sp_tracing::try_init_simple();
		let mut es = EnactmentState::new(a().hash, a().hash);

		//   B1-C1-D1-E1
		//  /
		// A
		//  \
		//   B2-C2-D2-E2

		let result = trigger_new_best_block(&mut es, a(), d1());
		assert!(result);
		assert_es_eq(&es, d1(), a());

		let result = trigger_new_best_block(&mut es, d1(), e1());
		assert!(result);
		assert_es_eq(&es, e1(), a());

		let result = trigger_finalized(&mut es, a(), d2());
		assert!(result);
		assert_es_eq(&es, d2(), d2());

		let result = trigger_new_best_block(&mut es, d2(), e1());
		assert_eq!(result, false);
		assert_es_eq(&es, d2(), d2());

		let result = trigger_finalized(&mut es, a(), b2());
		assert_eq!(result, false);
		assert_es_eq(&es, d2(), d2());

		let result = trigger_finalized(&mut es, a(), b1());
		assert_eq!(result, false);
		assert_es_eq(&es, d2(), d2());

		let result = trigger_new_best_block(&mut es, a(), d2());
		assert_eq!(result, false);
		assert_es_eq(&es, d2(), d2());

		let result = trigger_finalized(&mut es, a(), d2());
		assert_eq!(result, false);
		assert_es_eq(&es, d2(), d2());

		let result = trigger_new_best_block(&mut es, a(), c2());
		assert_eq!(result, false);
		assert_es_eq(&es, d2(), d2());

		let result = trigger_new_best_block(&mut es, a(), c1());
		assert_eq!(result, false);
		assert_es_eq(&es, d2(), d2());

		let result = trigger_new_best_block(&mut es, d2(), e2());
		assert!(result);
		assert_es_eq(&es, e2(), d2());

		let result = trigger_finalized(&mut es, d2(), e2());
		assert_eq!(result, false);
		assert_es_eq(&es, e2(), e2());
	}

	#[test]
	fn test_enactment_helper_2() {
		sp_tracing::try_init_simple();
		let mut es = EnactmentState::new(a().hash, a().hash);

		// A-B1-C1-D1-E1

		let result = trigger_new_best_block(&mut es, a(), b1());
		assert!(result);
		assert_es_eq(&es, b1(), a());

		let result = trigger_new_best_block(&mut es, b1(), c1());
		assert!(result);
		assert_es_eq(&es, c1(), a());

		let result = trigger_new_best_block(&mut es, c1(), d1());
		assert!(result);
		assert_es_eq(&es, d1(), a());

		let result = trigger_new_best_block(&mut es, d1(), e1());
		assert!(result);
		assert_es_eq(&es, e1(), a());

		let result = trigger_finalized(&mut es, a(), c1());
		assert_eq!(result, false);
		assert_es_eq(&es, e1(), c1());

		let result = trigger_finalized(&mut es, c1(), e1());
		assert_eq!(result, false);
		assert_es_eq(&es, e1(), e1());
	}

	#[test]
	fn test_enactment_helper_3() {
		sp_tracing::try_init_simple();
		let mut es = EnactmentState::new(a().hash, a().hash);

		// A-B1-C1-D1-E1

		let result = trigger_new_best_block(&mut es, a(), e1());
		assert!(result);
		assert_es_eq(&es, e1(), a());

		let result = trigger_finalized(&mut es, a(), b1());
		assert_eq!(result, false);
		assert_es_eq(&es, e1(), b1());
	}

	#[test]
	fn test_enactment_helper_4() {
		sp_tracing::try_init_simple();
		let mut es = EnactmentState::new(a().hash, a().hash);

		// A-B1-C1-D1-E1

		let result = trigger_finalized(&mut es, a(), e1());
		assert!(result);
		assert_es_eq(&es, e1(), e1());

		let result = trigger_finalized(&mut es, e1(), b1());
		assert_eq!(result, false);
		assert_es_eq(&es, e1(), e1());
	}

	#[test]
	fn test_enactment_helper_5() {
		sp_tracing::try_init_simple();
		let mut es = EnactmentState::new(a().hash, a().hash);

		//   B1-C1-D1-E1
		//  /
		// A
		//  \
		//   B2-C2-D2-E2

		let result = trigger_finalized(&mut es, a(), e1());
		assert!(result);
		assert_es_eq(&es, e1(), e1());

		let result = trigger_finalized(&mut es, e1(), e2());
		assert_eq!(result, false);
		assert_es_eq(&es, e1(), e1());
	}

	#[test]
	fn test_enactment_helper_6() {
		sp_tracing::try_init_simple();
		let mut es = EnactmentState::new(a().hash, a().hash);

		// A-B1-C1-D1-E1

		let result = trigger_new_best_block(&mut es, a(), b1());
		assert!(result);
		assert_es_eq(&es, b1(), a());

		let result = trigger_finalized(&mut es, a(), d1());
		assert!(result);
		assert_es_eq(&es, d1(), d1());

		let result = trigger_new_best_block(&mut es, a(), e1());
		assert!(result);
		assert_es_eq(&es, e1(), d1());

		let result = trigger_new_best_block(&mut es, a(), c1());
		assert_eq!(result, false);
		assert_es_eq(&es, e1(), d1());
	}
}
