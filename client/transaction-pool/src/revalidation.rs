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

//! Pool periodic revalidation.

use std::{sync::Arc, collections::{HashMap, HashSet, BTreeMap}};
use sc_transaction_graph::{ChainApi, Pool, ExHash, NumberFor, ValidatedTransaction, Transaction};
use sp_runtime::traits::{Zero, SaturatedConversion};
use sp_runtime::generic::BlockId;
use sp_runtime::transaction_validity::TransactionValidityError;

use futures::{prelude::*, channel::mpsc, task::Poll, stream::unfold};
use std::pin::Pin;
use std::time::Duration;
use futures_timer::Delay;

#[cfg(not(test))]
const BACKGROUND_REVALIDATION_INTERVAL: Duration = Duration::from_millis(200);
#[cfg(test)]
const BACKGROUND_REVALIDATION_INTERVAL: Duration = Duration::from_millis(5);

const BACKGROUND_REVALIDATION_BATCH_SIZE: usize = 20;

/// Payload from queue to worker.
struct WorkerPayload<Api: ChainApi> {
	at: NumberFor<Api>,
	transactions: Vec<ExHash<Api>>,
}

/// Async revalidation worker.
///
/// Implements future and can be spawned in place or in background.
struct RevalidationWorker<Api: ChainApi> {
	api: Arc<Api>,
	pool: Arc<Pool<Api>>,
	best_block: NumberFor<Api>,
	block_ordered: BTreeMap<NumberFor<Api>, HashSet<ExHash<Api>>>,
	members: HashMap<ExHash<Api>, NumberFor<Api>>,
}

impl<Api: ChainApi> Unpin for RevalidationWorker<Api> {}

fn interval(duration: Duration) -> impl Stream<Item=()> + Unpin {
	unfold((), move |_| {
		Delay::new(duration).map(|_| Some(((), ())))
	}).map(drop)
}

/// Actual async revalidation batch.
async fn batch_revalidate<Api: ChainApi>(
	pool: Arc<Pool<Api>>,
	api: Arc<Api>,
	at: NumberFor<Api>,
	batch: impl IntoIterator<Item=ExHash<Api>>,
) {
	let mut invalid_hashes = Vec::new();
	let mut revalidated = HashMap::new();

	for ext_hash in batch {
		let ext = match pool.ready_transaction(&ext_hash) {
			Some(ext) => ext,
			None => continue,
		};

		match api.validate_transaction(&BlockId::Number(at), ext.data.clone()).await {
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
				let data = ext.data.clone();
				let (_, bytes) = api.hash_and_length(&data);
				revalidated.insert(
					ext_hash.clone(),
					ValidatedTransaction::Valid(
						Transaction {
							data: ext.data.clone(),
							bytes,
							hash: ext_hash.clone(),
							priority: validity.priority,
							requires: validity.requires,
							provides: validity.provides,
							propagate: validity.propagate,
							valid_till: at
								.saturated_into::<u64>()
								.saturating_add(validity.longevity),
					}),
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

	pool.remove_invalid(&invalid_hashes);
	pool.resubmit(revalidated);
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

	fn prepare_batch(&mut self) -> Vec<ExHash<Api>> {
		let mut queued_exts = Vec::new();
		let mut empty = Vec::<NumberFor<Api>>::new();

		// Take maximum of count transaction by order
		// which they got into the pool
		for (block_number, ext_map) in self.block_ordered.iter_mut() {
			if queued_exts.len() >= BACKGROUND_REVALIDATION_BATCH_SIZE { break; }

			loop {
				let next_key = match ext_map.iter().nth(0) {
					Some(k) => k.clone(),
					None => { break; }
				};

				ext_map.remove(&next_key);
				self.members.remove(&next_key);

				queued_exts.push(next_key);

				if ext_map.len() == 0 { empty.push(*block_number); }

				if queued_exts.len() >= BACKGROUND_REVALIDATION_BATCH_SIZE { break; }
			}
		}

		// retain only non-empty
		for empty_block_number in empty.into_iter() { self.block_ordered.remove(&empty_block_number); }

		queued_exts
	}

	fn push(&mut self, worker_payload: WorkerPayload<Api>) {
		// we don't add something that already scheduled for revalidation
		let transactions = worker_payload.transactions;
		let block_number = worker_payload.at;

		for ext_hash in transactions {
			// we don't add something that already scheduled for revalidation
			if self.members.contains_key(&ext_hash) { continue; }

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

	pub async fn run(mut self, from_queue: mpsc::UnboundedReceiver<WorkerPayload<Api>>) {
		let interval = interval(BACKGROUND_REVALIDATION_INTERVAL).fuse();
		let from_queue = from_queue.fuse();
		futures::pin_mut!(interval, from_queue);
		let this = &mut self;

		loop {
			futures::select! {
				_ = interval.next() => {
					let next_batch = this.prepare_batch();
					batch_revalidate(this.pool.clone(), this.api.clone(), this.best_block, next_batch).await;
				},
				workload = from_queue.next() => {
					match workload {
						Some(worker_payload) => {
							this.best_block = worker_payload.at;
							this.push(worker_payload);
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

/// Background state for revalidation queue.
struct BackgroundConfig<Api: ChainApi> {
	to_worker: mpsc::UnboundedSender<WorkerPayload<Api>>,
	_spawner: futures::executor::ThreadPool,
}

/// Revalidation queue.
///
/// Can be configured background (`new_background`)
/// or immediate (just `new`).
pub struct RevalidationQueue<Api: ChainApi> {
	pool: Arc<Pool<Api>>,
	api: Arc<Api>,
	background: Option<BackgroundConfig<Api>>,
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

	/// New revalidation queue with background worker.
	pub fn new_background(api: Arc<Api>, pool: Arc<Pool<Api>>) -> Self {
		let spawner = futures::executor::ThreadPool::builder()
			.name_prefix("txpool-worker")
			.pool_size(1)
			.create()
			.expect("Creating worker thread task failed");

		let (to_worker, from_queue) = mpsc::unbounded();

		let worker = RevalidationWorker::new(api.clone(), pool.clone());
		spawner.spawn_ok(worker.run(from_queue));

		Self {
			api,
			pool,
			background: Some(
				BackgroundConfig { _spawner: spawner, to_worker }
			),
		}
	}

	/// Queue some transaction for later revalidation.
	///
	/// If queue configured with background worker, this will return immediately.
	/// If queue configured without background worker, this will resolve after
	/// revalidation is actually done.
	pub async fn revalidate_later(&self, at: NumberFor<Api>, transactions: Vec<ExHash<Api>>) {
		if let Some(ref background) = self.background {
			background.to_worker.unbounded_send(WorkerPayload { at, transactions })
				.expect("background task is never dropped");
			return;
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
	use substrate_test_runtime_transaction_pool::{TestApi, uxt};
	use futures::executor::block_on;
	use substrate_test_runtime_client::{
		AccountKeyring::*,
	};

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
		let uxt_hash = block_on(pool.submit_one(&BlockId::number(0), uxt.clone())).expect("Should be valid");

		block_on(queue.revalidate_later(0, vec![uxt_hash]));

		// revalidated in sync offload 2nd time
		assert_eq!(api.validation_requests().len(), 2);
		// number of ready
		assert_eq!(pool.status().ready, 1);
	}
}