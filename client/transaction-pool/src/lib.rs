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

//! Substrate transaction pool implementation.

#![recursion_limit="256"]
#![warn(missing_docs)]
#![warn(unused_extern_crates)]

mod api;
mod revalidation;
mod metrics;

pub mod error;

#[cfg(test)]
pub mod testing;

pub use sc_transaction_graph as txpool;
pub use crate::api::{FullChainApi, LightChainApi};

use std::{collections::{HashMap, HashSet}, sync::Arc, pin::Pin, convert::TryInto};
use futures::{prelude::*, future::{self, ready}, channel::oneshot};
use parking_lot::Mutex;

use sp_runtime::{
	generic::BlockId,
	traits::{Block as BlockT, NumberFor, AtLeast32Bit, Extrinsic, Zero},
};
use sp_core::traits::SpawnNamed;
use sp_transaction_pool::{
	TransactionPool, PoolStatus, ImportNotificationStream, TxHash, TransactionFor,
	TransactionStatusStreamFor, MaintainedTransactionPool, PoolFuture, ChainEvent,
	TransactionSource,
};
use sc_transaction_graph::{ChainApi, ExtrinsicHash};
use wasm_timer::Instant;

use prometheus_endpoint::Registry as PrometheusRegistry;
use crate::metrics::MetricsLink as PrometheusMetrics;

type BoxedReadyIterator<Hash, Data> = Box<
	dyn Iterator<Item=Arc<sc_transaction_graph::base_pool::Transaction<Hash, Data>>> + Send
>;

type ReadyIteratorFor<PoolApi> = BoxedReadyIterator<
	sc_transaction_graph::ExtrinsicHash<PoolApi>, sc_transaction_graph::ExtrinsicFor<PoolApi>
>;

type PolledIterator<PoolApi> = Pin<Box<dyn Future<Output=ReadyIteratorFor<PoolApi>> + Send>>;

/// A transaction pool for a full node.
pub type FullPool<Block, Client> = BasicPool<FullChainApi<Client, Block>, Block>;
/// A transaction pool for a light node.
pub type LightPool<Block, Client, Fetcher> = BasicPool<LightChainApi<Client, Fetcher, Block>, Block>;

/// Basic implementation of transaction pool that can be customized by providing PoolApi.
pub struct BasicPool<PoolApi, Block>
	where
		Block: BlockT,
		PoolApi: ChainApi<Block=Block>,
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
	PoolApi: ChainApi<Block=Block>,
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
		PoolApi: ChainApi<Block=Block> + 'static,
{
	/// Create new basic transaction pool with provided api, for tests.
	#[cfg(test)]
	pub fn new_test(
		pool_api: Arc<PoolApi>,
	) -> (Self, Pin<Box<dyn Future<Output=()> + Send>>, intervalier::BackSignalControl) {
		let pool = Arc::new(sc_transaction_graph::Pool::new(Default::default(), true.into(), pool_api.clone()));
		let (revalidation_queue, background_task, notifier) =
			revalidation::RevalidationQueue::new_test(pool_api.clone(), pool.clone());
		(
			Self {
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
		is_validator: txpool::IsValidator,
		pool_api: Arc<PoolApi>,
		prometheus: Option<&PrometheusRegistry>,
		revalidation_type: RevalidationType,
		spawner: impl SpawnNamed,
	) -> Self {
		let pool = Arc::new(sc_transaction_graph::Pool::new(options, is_validator, pool_api.clone()));
		let (revalidation_queue, background_task) = match revalidation_type {
			RevalidationType::Light => (revalidation::RevalidationQueue::new(pool_api.clone(), pool.clone()), None),
			RevalidationType::Full => {
				let (queue, background) = revalidation::RevalidationQueue::new_background(pool_api.clone(), pool.clone());
				(queue, Some(background))
			},
		};

		if let Some(background_task) = background_task {
			spawner.spawn("txpool-background", background_task);
		}

		Self {
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
		PoolApi: 'static + ChainApi<Block=Block>,
{
	type Block = PoolApi::Block;
	type Hash = sc_transaction_graph::ExtrinsicHash<PoolApi>;
	type InPoolTransaction = sc_transaction_graph::base_pool::Transaction<
		TxHash<Self>, TransactionFor<Self>
	>;
	type Error = PoolApi::Error;

	fn submit_at(
		&self,
		at: &BlockId<Self::Block>,
		source: TransactionSource,
		xts: Vec<TransactionFor<Self>>,
	) -> PoolFuture<Vec<Result<TxHash<Self>, Self::Error>>, Self::Error> {
		let pool = self.pool.clone();
		let at = *at;

		self.metrics.report(|metrics| metrics.submitted_transactions.inc_by(xts.len() as u64));

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
	) -> PoolFuture<Box<TransactionStatusStreamFor<Self>>, Self::Error> {
		let at = *at;
		let pool = self.pool.clone();

		self.metrics.report(|metrics| metrics.submitted_transactions.inc());

		async move {
			pool.submit_and_watch(&at, source, xt)
				.map(|result| result.map(|watcher| Box::new(watcher.into_stream()) as _))
				.await
		}.boxed()
	}

	fn remove_invalid(&self, hashes: &[TxHash<Self>]) -> Vec<Arc<Self::InPoolTransaction>> {
		let removed = self.pool.validated_pool().remove_invalid(hashes);
		self.metrics.report(|metrics| metrics.validations_invalid.inc_by(removed.len() as u64));
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
		if self.ready_poll.lock().updated_at() >= at {
			log::trace!(target: "txpool", "Transaction pool already processed block  #{}", at);
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

impl<Block, Client, Fetcher> LightPool<Block, Client, Fetcher>
where
	Block: BlockT,
	Client: sp_blockchain::HeaderBackend<Block> + 'static,
	Fetcher: sc_client_api::Fetcher<Block> + 'static,
{
	/// Create new basic transaction pool for a light node with the provided api.
	pub fn new_light(
		options: sc_transaction_graph::Options,
		prometheus: Option<&PrometheusRegistry>,
		spawner: impl SpawnNamed,
		client: Arc<Client>,
		fetcher: Arc<Fetcher>,
	) -> Self {
		let pool_api = Arc::new(LightChainApi::new(client, fetcher));
		Self::with_revalidation_type(
			options, false.into(), pool_api, prometheus, RevalidationType::Light, spawner,
		)
	}
}

impl<Block, Client> FullPool<Block, Client>
where
	Block: BlockT,
	Client: sp_api::ProvideRuntimeApi<Block>
		+ sc_client_api::BlockBackend<Block>
		+ sp_runtime::traits::BlockIdTo<Block>,
	Client: sc_client_api::ExecutorProvider<Block> + Send + Sync + 'static,
	Client::Api: sp_transaction_pool::runtime_api::TaggedTransactionQueue<Block>,
{
	/// Create new basic transaction pool for a full node with the provided api.
	pub fn new_full(
		options: sc_transaction_graph::Options,
		is_validator: txpool::IsValidator,
		prometheus: Option<&PrometheusRegistry>,
		spawner: impl SpawnNamed,
		client: Arc<Client>,
	) -> Arc<Self> {
		let pool_api = Arc::new(FullChainApi::new(client.clone(), prometheus));
		let pool = Arc::new(Self::with_revalidation_type(
			options, is_validator, pool_api, prometheus, RevalidationType::Full, spawner
		));

		// make transaction pool available for off-chain runtime calls.
		client.execution_extensions().register_transaction_pool(&pool);

		pool
	}
}

impl<Block, Client> sp_transaction_pool::LocalTransactionPool
	for BasicPool<FullChainApi<Client, Block>, Block>
where
	Block: BlockT,
	Client: sp_api::ProvideRuntimeApi<Block>
		+ sc_client_api::BlockBackend<Block>
		+ sp_runtime::traits::BlockIdTo<Block>,
	Client: Send + Sync + 'static,
	Client::Api: sp_transaction_pool::runtime_api::TaggedTransactionQueue<Block>,
{
	type Block = Block;
	type Hash = sc_transaction_graph::ExtrinsicHash<FullChainApi<Client, Block>>;
	type Error = <FullChainApi<Client, Block> as ChainApi>::Error;

	fn submit_local(
		&self,
		at: &BlockId<Self::Block>,
		xt: sp_transaction_pool::LocalTransactionFor<Self>,
	) -> Result<Self::Hash, Self::Error> {
		use sc_transaction_graph::ValidatedTransaction;
		use sp_runtime::traits::SaturatedConversion;
		use sp_runtime::transaction_validity::TransactionValidityError;

		let validity = self
			.api
			.validate_transaction_blocking(at, TransactionSource::Local, xt.clone())?
			.map_err(|e| {
				Self::Error::Pool(match e {
					TransactionValidityError::Invalid(i) => i.into(),
					TransactionValidityError::Unknown(u) => u.into(),
				})
			})?;

		let (hash, bytes) = self.pool.validated_pool().api().hash_and_length(&xt);
		let block_number = self
			.api
			.block_id_to_number(at)?
			.ok_or_else(|| error::Error::BlockIdConversion(format!("{:?}", at)))?;

		let validated = ValidatedTransaction::valid_at(
			block_number.saturated_into::<u64>(),
			hash.clone(),
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

/// Prune the known txs for the given block.
async fn prune_known_txs_for_block<Block: BlockT, Api: ChainApi<Block = Block>>(
	block_id: BlockId<Block>,
	api: &Api,
	pool: &sc_transaction_graph::Pool<Api>,
) -> Vec<ExtrinsicHash<Api>> {
	let hashes = api.block_body(&block_id).await
		.unwrap_or_else(|e| {
			log::warn!("Prune known transactions: error request {:?}!", e);
			None
		})
		.unwrap_or_default()
		.into_iter()
		.map(|tx| pool.hash_of(&tx))
		.collect::<Vec<_>>();

	log::trace!(target: "txpool", "Pruning transactions: {:?}", hashes);

	if let Err(e) = pool.prune_known(&block_id, &hashes) {
		log::error!("Cannot prune known in the pool {:?}!", e);
	}

	hashes
}

impl<PoolApi, Block> MaintainedTransactionPool for BasicPool<PoolApi, Block>
	where
		Block: BlockT,
		PoolApi: 'static + ChainApi<Block=Block>,
{
	fn maintain(&self, event: ChainEvent<Self::Block>) -> Pin<Box<dyn Future<Output=()> + Send>> {
		match event {
			ChainEvent::NewBestBlock { hash, tree_route } => {
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
						return Box::pin(ready(()));
					}
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

				async move {
					// We keep track of everything we prune so that later we won't add
					// transactions with those hashes from the retracted blocks.
					let mut pruned_log = HashSet::<ExtrinsicHash<PoolApi>>::new();

					// If there is a tree route, we use this to prune known tx based on the enacted
					// blocks. Before pruning enacted transactions, we inform the listeners about
					// retracted blocks and their transactions. This order is important, because
					// if we enact and retract the same transaction at the same time, we want to
					// send first the retract and than the prune event.
					if let Some(ref tree_route) = tree_route {
						for retracted in tree_route.retracted() {
							// notify txs awaiting finality that it has been retracted
							pool.validated_pool().on_block_retracted(retracted.hash.clone());
						}

						future::join_all(
							tree_route
								.enacted()
								.iter()
								.map(|h|
									prune_known_txs_for_block(
										BlockId::Hash(h.hash.clone()),
										&*api,
										&*pool,
									),
								),
						).await.into_iter().for_each(|enacted_log|{
							pruned_log.extend(enacted_log);
						})
					}

					pruned_log.extend(prune_known_txs_for_block(id.clone(), &*api, &*pool).await);

					metrics.report(
						|metrics| metrics.block_transactions_pruned.inc_by(pruned_log.len() as u64)
					);

					if let (true, Some(tree_route)) = (next_action.resubmit, tree_route) {
						let mut resubmit_transactions = Vec::new();

						for retracted in tree_route.retracted() {
							let hash = retracted.hash.clone();

							let block_transactions = api.block_body(&BlockId::hash(hash))
								.await
								.unwrap_or_else(|e| {
									log::warn!("Failed to fetch block body {:?}!", e);
									None
								})
								.unwrap_or_default()
								.into_iter()
								.filter(|tx| tx.is_signed().unwrap_or(true));

							let mut resubmitted_to_report = 0;

							resubmit_transactions.extend(
								block_transactions.into_iter().filter(|tx| {
									let tx_hash = pool.hash_of(&tx);
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
								})
							);

							metrics.report(
								|metrics| metrics.block_transactions_resubmitted.inc_by(resubmitted_to_report)
							);
						}

						if let Err(e) = pool.resubmit_at(
							&id,
							// These transactions are coming from retracted blocks, we should
							// simply consider them external.
							TransactionSource::External,
							resubmit_transactions,
						).await {
							log::debug!(
								target: "txpool",
								"[{:?}] Error re-submitting transactions: {:?}",
								id,
								e,
							)
						}
					}

					let extra_pool = pool.clone();
					// After #5200 lands, this arguably might be moved to the
					// handler of "all blocks notification".
					ready_poll.lock().trigger(
						block_number,
						move || Box::new(extra_pool.validated_pool().ready()),
					);

					if next_action.revalidate {
						let hashes = pool.validated_pool()
							.ready()
							.map(|tx| tx.hash.clone())
							.collect();
						revalidation_queue.revalidate_later(block_number, hashes).await;

						revalidation_strategy.lock().clear();
					}
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

/// Inform the transaction pool about imported and finalized blocks.
pub async fn notification_future<Client, Pool, Block>(
	client: Arc<Client>,
	txpool: Arc<Pool>
)
	where
		Block: BlockT,
		Client: sc_client_api::BlockchainEvents<Block>,
		Pool: MaintainedTransactionPool<Block=Block>,
{
	let import_stream = client.import_notification_stream()
		.filter_map(|n| ready(n.try_into().ok()))
		.fuse();
	let finality_stream = client.finality_notification_stream()
		.map(Into::into)
		.fuse();

	futures::stream::select(import_stream, finality_stream)
		.for_each(|evt| txpool.maintain(evt))
		.await
}
