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

//! Pool periodic revalidation.

use std::{sync::Arc, pin::Pin, collections::{HashMap, HashSet, BTreeMap}};

use sc_transaction_graph::{ChainApi, Pool, ExtrinsicHash, NumberFor, ValidatedTransaction};
use sp_runtime::traits::{Zero, SaturatedConversion};
use sp_runtime::generic::BlockId;
use sp_runtime::transaction_validity::TransactionValidityError;
use sp_utils::mpsc::{tracing_unbounded, TracingUnboundedSender, TracingUnboundedReceiver};

use futures::prelude::*;
use std::time::Duration;

#[cfg(not(test))]
const BACKGROUND_REVALIDATION_INTERVAL: Duration = Duration::from_millis(200);
#[cfg(test)]
pub const BACKGROUND_REVALIDATION_INTERVAL: Duration = Duration::from_millis(1);

const MIN_BACKGROUND_REVALIDATION_BATCH_SIZE: usize = 20;

/// Payload from queue to worker.
struct WorkerPayload<Api: ChainApi> {
	at: NumberFor<Api>,
	transactions: Vec<ExtrinsicHash<Api>>,
}

/// Async revalidation worker.
///
/// Implements future and can be spawned in place or in background.
struct RevalidationWorker<Api: ChainApi> {
	api: Arc<Api>,
	pool: Arc<Pool<Api>>,
	best_block: NumberFor<Api>,
	block_ordered: BTreeMap<NumberFor<Api>, HashSet<ExtrinsicHash<Api>>>,
	members: HashMap<ExtrinsicHash<Api>, NumberFor<Api>>,
}

impl<Api: ChainApi> Unpin for RevalidationWorker<Api> {}

/// Revalidate batch of transaction.
///
/// Each transaction is validated  against chain, and invalid are
/// removed from the `pool`, while valid are resubmitted.
async fn batch_revalidate<Api: ChainApi>(
	pool: Arc<Pool<Api>>,
	api: Arc<Api>,
	at: NumberFor<Api>,
	batch: impl IntoIterator<Item=ExtrinsicHash<Api>>,
) {
	let mut invalid_hashes = Vec::new();
	let mut revalidated = HashMap::new();

	let validation_results = futures::future::join_all(
		batch.into_iter().filter_map(|ext_hash| {
			pool.validated_pool().ready_by_hash(&ext_hash).map(|ext| {
				api.validate_transaction(&BlockId::Number(at), ext.source, ext.data.clone())
					.map(move |validation_result| (validation_result, ext_hash, ext))
			})
		})
	).await;

	for (validation_result, ext_hash, ext) in validation_results {
		match validation_result {
			Ok(Err(TransactionValidityError::Invalid(err))) => {
				log::debug!(target: "txpool", "[{:?}]: Revalidation: invalid {:?}", ext_hash, err);
				invalid_hashes.push(ext_hash);
			},
			Ok(Err(TransactionValidityError::Unknown(err))) => {
				// skipping unknown, they might be pushed by valid or invalid transaction
				// when latter resubmitted.
				log::trace!(target: "txpool", "[{:?}]: Unknown during revalidation: {:?}", ext_hash, err);
			},
			Ok(Ok(validity)) => {
				revalidated.insert(
					ext_hash.clone(),
					ValidatedTransaction::valid_at(
						at.saturated_into::<u64>(),
						ext_hash,
						ext.source,
						ext.data.clone(),
						api.hash_and_length(&ext.data).1,
						validity,
					)
				);
			},
			Err(validation_err) => {
				log::debug!(
					target: "txpool",
					"[{:?}]: Error during revalidation: {:?}. Removing.",
					ext_hash,
					validation_err
				);
				invalid_hashes.push(ext_hash);
			}
		}
	}

	pool.validated_pool().remove_invalid(&invalid_hashes);
	if revalidated.len() > 0 {
		pool.resubmit(revalidated);
	}
}

impl<Api: ChainApi> RevalidationWorker<Api> {
	fn new(
		api: Arc<Api>,
		pool: Arc<Pool<Api>>,
	) -> Self {
		Self {
			api,
			pool,
			block_ordered: Default::default(),
			members: Default::default(),
			best_block: Zero::zero(),
		}
	}

	fn prepare_batch(&mut self) -> Vec<ExtrinsicHash<Api>> {
		let mut queued_exts = Vec::new();
		let mut left = std::cmp::max(MIN_BACKGROUND_REVALIDATION_BATCH_SIZE, self.members.len() / 4);

		// Take maximum of count transaction by order
		// which they got into the pool
		while left > 0 {
			let first_block = match self.block_ordered.keys().next().cloned() {
				Some(bn) => bn,
				None => break,
			};
			let mut block_drained = false;
			if let Some(extrinsics) = self.block_ordered.get_mut(&first_block) {
				let to_queue = extrinsics.iter().take(left).cloned().collect::<Vec<_>>();
				if to_queue.len() == extrinsics.len() {
					block_drained = true;
				} else {
					for xt in &to_queue {
						extrinsics.remove(xt);
					}
				}
				left -= to_queue.len();
				queued_exts.extend(to_queue);
			}

			if block_drained {
				self.block_ordered.remove(&first_block);
			}
		}

		for hash in queued_exts.iter() {
			self.members.remove(hash);
		}

		queued_exts
	}

	fn len(&self) -> usize {
		self.block_ordered.iter().map(|b| b.1.len()).sum()
	}

	fn push(&mut self, worker_payload: WorkerPayload<Api>) {
		// we don't add something that already scheduled for revalidation
		let transactions = worker_payload.transactions;
		let block_number = worker_payload.at;

		for ext_hash in transactions {
			// we don't add something that already scheduled for revalidation
			if self.members.contains_key(&ext_hash) {
				log::trace!(
					target: "txpool",
					"[{:?}] Skipped adding for revalidation: Already there.",
					ext_hash,
				);

				continue;
			}

			self.block_ordered.entry(block_number)
				.and_modify(|value| { value.insert(ext_hash.clone()); })
				.or_insert_with(|| {
					let mut bt = HashSet::new();
					bt.insert(ext_hash.clone());
					bt
				});
			self.members.insert(ext_hash.clone(), block_number);
		}
	}

	/// Background worker main loop.
	///
	/// It does two things: periodically tries to process some transactions
	/// from the queue and also accepts messages to enqueue some more
	/// transactions from the pool.
	pub async fn run<R: intervalier::IntoStream>(
		mut self,
		from_queue: TracingUnboundedReceiver<WorkerPayload<Api>>,
		interval: R,
	) where R: Send, R::Guard: Send {
		let interval = interval.into_stream().fuse();
		let from_queue = from_queue.fuse();
		futures::pin_mut!(interval, from_queue);
		let this = &mut self;

		loop {
			futures::select! {
				_guard = interval.next() => {
					let next_batch = this.prepare_batch();
					let batch_len = next_batch.len();

					batch_revalidate(this.pool.clone(), this.api.clone(), this.best_block, next_batch).await;

					#[cfg(test)]
					{
						use intervalier::Guard;
						// only trigger test events if something was processed
						if batch_len == 0 {
							_guard.expect("Always some() in tests").skip();
						}
					}

					if batch_len > 0 || this.len() > 0 {
						log::debug!(
							target: "txpool",
							"Revalidated {} transactions. Left in the queue for revalidation: {}.",
							batch_len,
							this.len(),
						);
					}
				},
				workload = from_queue.next() => {
					match workload {
						Some(worker_payload) => {
							this.best_block = worker_payload.at;
							this.push(worker_payload);

							if this.members.len() > 0 {
								log::debug!(
									target: "txpool",
									"Updated revalidation queue at {:?}. Transactions: {:?}",
									this.best_block,
									this.members,
								);
							}

							continue;
						},
						// R.I.P. worker!
						None => break,
					}
				}
			}
		}
	}
}


/// Revalidation queue.
///
/// Can be configured background (`new_background`)
/// or immediate (just `new`).
pub struct RevalidationQueue<Api: ChainApi> {
	pool: Arc<Pool<Api>>,
	api: Arc<Api>,
	background: Option<TracingUnboundedSender<WorkerPayload<Api>>>,
}

impl<Api: ChainApi> RevalidationQueue<Api>
where
	Api: 'static,
{
	/// New revalidation queue without background worker.
	pub fn new(api: Arc<Api>, pool: Arc<Pool<Api>>) -> Self {
		Self {
			api,
			pool,
			background: None,
		}
	}

	pub fn new_with_interval<R: intervalier::IntoStream>(
		api: Arc<Api>,
		pool: Arc<Pool<Api>>,
		interval: R,
	) -> (Self, Pin<Box<dyn Future<Output=()> + Send>>) where R: Send + 'static, R::Guard: Send {
		let (to_worker, from_queue) = tracing_unbounded("mpsc_revalidation_queue");

		let worker = RevalidationWorker::new(api.clone(), pool.clone());

		let queue =
			Self {
				api,
				pool,
				background: Some(to_worker),
			};

		(queue, worker.run(from_queue, interval).boxed())
	}

	/// New revalidation queue with background worker.
	pub fn new_background(api: Arc<Api>, pool: Arc<Pool<Api>>) ->
		(Self, Pin<Box<dyn Future<Output=()> + Send>>)
	{
		Self::new_with_interval(api, pool, intervalier::Interval::new(BACKGROUND_REVALIDATION_INTERVAL))
	}

	/// New revalidation queue with background worker and test signal.
	#[cfg(test)]
	pub fn new_test(api: Arc<Api>, pool: Arc<Pool<Api>>) ->
		(Self, Pin<Box<dyn Future<Output=()> + Send>>, intervalier::BackSignalControl)
	{
		let (interval, notifier) = intervalier::BackSignalInterval::new(BACKGROUND_REVALIDATION_INTERVAL);
		let (queue, background) = Self::new_with_interval(api, pool, interval);

		(queue, background, notifier)
	}

	/// Queue some transaction for later revalidation.
	///
	/// If queue configured with background worker, this will return immediately.
	/// If queue configured without background worker, this will resolve after
	/// revalidation is actually done.
	pub async fn revalidate_later(
		&self,
		at: NumberFor<Api>,
		transactions: Vec<ExtrinsicHash<Api>>,
	) {
		if transactions.len() > 0 {
			log::debug!(
				target: "txpool", "Sent {} transactions to revalidation queue",
				transactions.len(),
			);
		}

		if let Some(ref to_worker) = self.background {
			if let Err(e) = to_worker.unbounded_send(WorkerPayload { at, transactions }) {
				log::warn!(target: "txpool", "Failed to update background worker: {:?}", e);
			}
		} else {
			let pool = self.pool.clone();
			let api = self.api.clone();
			batch_revalidate(pool, api, at, transactions).await
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use sc_transaction_graph::Pool;
	use sp_transaction_pool::TransactionSource;
	use substrate_test_runtime_transaction_pool::{TestApi, uxt};
	use futures::executor::block_on;
	use substrate_test_runtime_client::AccountKeyring::*;

	fn setup() -> (Arc<TestApi>, Pool<TestApi>) {
		let test_api = Arc::new(TestApi::empty());
		let pool = Pool::new(Default::default(), test_api.clone());
		(test_api, pool)
	}

	#[test]
	fn smoky() {
		let (api, pool) = setup();
		let pool = Arc::new(pool);
		let queue = Arc::new(RevalidationQueue::new(api.clone(), pool.clone()));

		let uxt = uxt(Alice, 0);
		let uxt_hash = block_on(
			pool.submit_one(&BlockId::number(0), TransactionSource::External, uxt.clone())
		).expect("Should be valid");

		block_on(queue.revalidate_later(0, vec![uxt_hash]));

		// revalidated in sync offload 2nd time
		assert_eq!(api.validation_requests().len(), 2);
		// number of ready
		assert_eq!(pool.validated_pool().status().ready, 1);
	}
}
