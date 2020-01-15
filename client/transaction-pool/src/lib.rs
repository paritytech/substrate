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

#[cfg(test)]
mod tests;

pub use sc_transaction_graph as txpool;
pub use crate::api::{FullChainApi, LightChainApi};

use std::{collections::HashMap, sync::Arc, pin::Pin, time::Instant};
use futures::{Future, FutureExt, future::ready};
use parking_lot::Mutex;

use sp_runtime::{
	generic::BlockId,
	traits::{Block as BlockT, NumberFor, SimpleArithmetic},
};
use sp_transaction_pool::{
	TransactionPool, PoolStatus, ImportNotificationStream,
	TxHash, TransactionFor, TransactionStatusStreamFor, BlockHash,
	MaintainedTransactionPool,
};

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

/// Type of revalidation.
pub enum RevalidationType {
	/// Light revalidation type.
	///
	/// During maintaince, transaction pool makes periodic revalidation
	/// depending on number of blocks or time passed.
	Light,

	/// Full revalidation type.
	///
	/// During maintaince, transaction pool revalidates some transactions
	/// from the pool of valid transactions.
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
		pool_api: PoolApi,
	) -> Self {
		Self::with_revalidation_type(options, pool_api, RevalidationType::Full)
	}

	/// Create new basic transaction pool with provided api and custom
	/// revalidation type.
	pub fn with_revalidation_type(
		options: sc_transaction_graph::Options,
		pool_api: PoolApi,
		revalidation_type: RevalidationType,
	) -> Self {
		let api = Arc::new(pool_api);
		let cloned_api = api.clone();
		BasicPool {
			api: cloned_api,
			pool: Arc::new(sc_transaction_graph::Pool::new(options, api)),
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

	#[cfg(test)]
	pub fn api(&self) -> &Arc<PoolApi> {
		&self.api
	}
}

impl<PoolApi, Block> TransactionPool for BasicPool<PoolApi, Block>
	where
		Block: BlockT,
		PoolApi: 'static + sc_transaction_graph::ChainApi<Block=Block, Hash=Block::Hash, Error=error::Error>,
{
	type Block = PoolApi::Block;
	type Hash = sc_transaction_graph::ExHash<PoolApi>;
	type InPoolTransaction = sc_transaction_graph::base_pool::Transaction<TxHash<Self>, TransactionFor<Self>>;
	type Error = error::Error;

	fn submit_at(
		&self,
		at: &BlockId<Self::Block>,
		xts: impl IntoIterator<Item=TransactionFor<Self>> + 'static,
	) -> Box<dyn Future<Output=Result<Vec<Result<TxHash<Self>, Self::Error>>, Self::Error>> + Send + Unpin> {
		Box::new(self.pool.submit_at(at, xts, false))
	}

	fn submit_one(
		&self,
		at: &BlockId<Self::Block>,
		xt: TransactionFor<Self>,
	) -> Box<dyn Future<Output=Result<TxHash<Self>, Self::Error>> + Send + Unpin> {
		Box::new(self.pool.submit_one(at, xt))
	}

	fn submit_and_watch(
		&self,
		at: &BlockId<Self::Block>,
		xt: TransactionFor<Self>,
	) -> Box<dyn Future<Output=Result<Box<TransactionStatusStreamFor<Self>>, Self::Error>> + Send + Unpin> {
		Box::new(
			self.pool.submit_and_watch(at, xt)
				.map(|result| result.map(|watcher| Box::new(watcher.into_stream()) as _))
		)
	}

	fn remove_invalid(&self, hashes: &[TxHash<Self>]) -> Vec<Arc<Self::InPoolTransaction>> {
		self.pool.remove_invalid(hashes)
	}

	fn status(&self) -> PoolStatus {
		self.pool.status()
	}

	fn ready(&self) -> Box<dyn Iterator<Item=Arc<Self::InPoolTransaction>>> {
		Box::new(self.pool.ready())
	}

	fn import_notification_stream(&self) -> ImportNotificationStream {
		self.pool.import_notification_stream()
	}

	fn hash_of(&self, xt: &TransactionFor<Self>) -> TxHash<Self> {
		self.pool.hash_of(xt)
	}

	fn on_broadcasted(&self, propagations: HashMap<TxHash<Self>, Vec<String>>) {
		self.pool.on_broadcasted(propagations)
	}
}

#[cfg_attr(test, derive(Debug))]
enum RevalidationStatus<N> {
	/// The revalidation has never been completed.
	NotScheduled,
	/// The revalidation is scheduled.
	Scheduled(Option<std::time::Instant>, Option<N>),
	/// The revalidation is in progress.
	InProgress,
}

enum RevalidationStrategy<N> {
	Always,
	Light(RevalidationStatus<N>)
}

impl<N: Clone + Copy + SimpleArithmetic> RevalidationStrategy<N> {
	pub fn clear(&mut self) {
		if let Self::Light(status) = self { status.clear() }
	}

	pub fn resubmit_required(&mut self) -> bool {
		if let Self::Light(_) = self { return false } else { return true }
	}

	pub fn is_required(
		&mut self,
		block: N,
		revalidate_time_period: Option<std::time::Duration>,
		revalidate_block_period: Option<N>,
	) -> bool {
		if let Self::Light(status) = self {
			status.is_required(block, revalidate_time_period, revalidate_block_period)
		} else { true }
	}

	pub fn amount(&self) -> Option<usize> {
		match self {
			Self::Light(_) => None,
			Self::Always => Some(16),
		}
	}
}

impl<N: Clone + Copy + SimpleArithmetic> RevalidationStatus<N> {
	/// Called when revalidation is completed.
	pub fn clear(&mut self) {
		*self = Self::NotScheduled;
	}

	/// Returns true if revalidation is required.
	pub fn is_required(
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
				let is_required = revalidate_at_time.map(|at| Instant::now() >= at).unwrap_or(false)
					|| revalidate_at_block.map(|at| block >= at).unwrap_or(false);
				if is_required {
					*self = Self::InProgress;
				}
				is_required
			},
			Self::InProgress => false,
		}
	}
}

impl<PoolApi, Block> MaintainedTransactionPool for BasicPool<PoolApi, Block>
where
	Block: BlockT,
	PoolApi: 'static + sc_transaction_graph::ChainApi<Block=Block, Hash=Block::Hash, Error=error::Error>,
{
	fn maintain(&self, id: &BlockId<Self::Block>, retracted: &[BlockHash<Self>]) -> Pin<Box<dyn Future<Output=()> + Send>> {
		let id = id.clone();
		let pool = self.pool.clone();
		let api = self.api.clone();

		let block_number = match api.block_id_to_number(&id) {
			Ok(Some(number)) => number,
			_ => {
				log::trace!(target: "txqueue", "Skipping chain event - no numbrer for that block {:?}", id);
				return Box::pin(ready(()));
			}
		};

		let (is_revalidation_required, is_resubmit_required) = {
			let mut lock = self.revalidation_strategy.lock();
			(
				lock.is_required(
					block_number,
					Some(std::time::Duration::from_secs(60)),
					Some(20.into()),
				),
				lock.resubmit_required()
			)
		};

		let revalidation_status = self.revalidation_strategy.clone();
		let revalidation_amount = revalidation_status.lock().amount();
		let retracted = retracted.to_vec();

		async move {
			let hashes = api.block_body(&id).await
				.unwrap_or_else(|e| {
					log::warn!("Prune known transactions: error request {:?}!", e);
					None
				})
				.unwrap_or(Vec::new())
				.into_iter()
				.map(|tx| pool.hash_of(&tx))
				.collect::<Vec<_>>();

			if let Err(e) = pool.prune_known(&id, &hashes) {
				log::warn!("Cannot prune known in the pool {:?}!", e);
			}

			if is_resubmit_required {
				let mut resubmit_transactions = Vec::new();

				for retracted_hash in retracted.into_iter() {
					let txes = api.block_body(&BlockId::hash(retracted_hash.clone())).await
						.unwrap_or(None)
						.unwrap_or(Vec::new());
					for tx in txes {
						resubmit_transactions.push(tx)
					}
				}
				if let Err(e) = pool.submit_at(&id, resubmit_transactions, true).await {
					log::debug!(target: "txpool",
						"[{:?}] Error re-submitting transactions: {:?}", id, e
					)
				}
			}

			if is_revalidation_required {
				if let Err(e) = pool.revalidate_ready(&id, revalidation_amount).await {
					log::warn!("revalidate ready failed {:?}", e);
				}
			}

			revalidation_status.lock().clear();
		}.boxed()
	}
}
