// Copyright 2018-2019 Parity Technologies (UK) Ltd.
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
	collections::{HashSet, HashMap},
	fmt,
	hash,
	time,
};

use crate::base_pool as base;
use crate::error;
use crate::listener::Listener;
use crate::rotator::PoolRotator;
use crate::watcher::Watcher;
use serde::Serialize;
use log::debug;

use futures::channel::mpsc;
use parking_lot::{Mutex, RwLock};
use sr_primitives::{
	generic::BlockId,
	traits::{self, SaturatedConversion},
	transaction_validity::TransactionTag as Tag,
};

use crate::base_pool::PruneStatus;
use crate::pool::{EventStream, Options, ChainApi, BlockHash, ExHash, ExtrinsicFor, TransactionFor};

/// Pre-validated transaction. Validated pool only accepts transactions wrapped in this enum.
#[derive(Debug)]
pub enum ValidatedTransaction<Hash, Ex, Error> {
	/// Transaction that has been validated successfully.
	Valid(base::Transaction<Hash, Ex>),
	/// Transaction that is invalid.
	Invalid(Hash, Error),
	/// Transaction which validity can't be determined.
	///
	/// We're notifying watchers about failure, if 'unknown' transaction is submitted.
	Unknown(Hash, Error),
}

/// A type of validated transaction stored in the pool.
pub type ValidatedTransactionFor<B> = ValidatedTransaction<
	ExHash<B>,
	ExtrinsicFor<B>,
	<B as ChainApi>::Error,
>;

/// Pool that deals with validated transactions.
pub(crate) struct ValidatedPool<B: ChainApi> {
	api: B,
	options: Options,
	listener: RwLock<Listener<ExHash<B>, BlockHash<B>>>,
	pool: RwLock<base::BasePool<
		ExHash<B>,
		ExtrinsicFor<B>,
	>>,
	import_notification_sinks: Mutex<Vec<mpsc::UnboundedSender<()>>>,
	rotator: PoolRotator<ExHash<B>>,
}

impl<B: ChainApi> ValidatedPool<B> {
	/// Create a new transaction pool.
	pub fn new(options: Options, api: B) -> Self {
		ValidatedPool {
			api,
			options,
			listener: Default::default(),
			pool: Default::default(),
			import_notification_sinks: Default::default(),
			rotator: Default::default(),
		}
	}

	/// Bans given set of hashes.
	pub fn ban(&self, now: &std::time::Instant, hashes: impl IntoIterator<Item=ExHash<B>>) {
		self.rotator.ban(now, hashes)
	}

	/// Returns true if transaction with given hash is currently banned from the pool.
	pub fn is_banned(&self, hash: &ExHash<B>) -> bool {
		self.rotator.is_banned(hash)
	}

	/// Imports a bunch of pre-validated transactions to the pool.
	pub fn submit<T>(&self, txs: T) -> Vec<Result<ExHash<B>, B::Error>> where
		T: IntoIterator<Item=ValidatedTransactionFor<B>>
	{
		let results = txs.into_iter()
			.map(|validated_tx| self.submit_one(validated_tx))
			.collect::<Vec<_>>();

		let removed = self.enforce_limits();

		results.into_iter().map(|res| match res {
			Ok(ref hash) if removed.contains(hash) => Err(error::Error::ImmediatelyDropped.into()),
			other => other,
		}).collect()
	}

	/// Submit single pre-validated transaction to the pool.
	fn submit_one(&self, tx: ValidatedTransactionFor<B>) -> Result<ExHash<B>, B::Error> {
		match tx {
			ValidatedTransaction::Valid(tx) => {
				let imported = self.pool.write().import(tx)?;

				if let base::Imported::Ready { .. } = imported {
					self.import_notification_sinks.lock().retain(|sink| sink.unbounded_send(()).is_ok());
				}

				let mut listener = self.listener.write();
				fire_events(&mut *listener, &imported);
				Ok(imported.hash().clone())
			}
			ValidatedTransaction::Invalid(hash, err) => {
				self.rotator.ban(&std::time::Instant::now(), std::iter::once(hash));
				Err(err.into())
			},
			ValidatedTransaction::Unknown(hash, err) => {
				self.listener.write().invalid(&hash);
				Err(err.into())
			}
		}
	}

	fn enforce_limits(&self) -> HashSet<ExHash<B>> {
		let status = self.pool.read().status();
		let ready_limit = &self.options.ready;
		let future_limit = &self.options.future;

		debug!(target: "txpool", "Pool Status: {:?}", status);

		if ready_limit.is_exceeded(status.ready, status.ready_bytes)
			|| future_limit.is_exceeded(status.future, status.future_bytes) {
			// clean up the pool
			let removed = {
				let mut pool = self.pool.write();
				let removed = pool.enforce_limits(ready_limit, future_limit)
					.into_iter().map(|x| x.hash.clone()).collect::<HashSet<_>>();
				// ban all removed transactions
				self.rotator.ban(&std::time::Instant::now(), removed.iter().map(|x| x.clone()));
				removed
			};
			// run notifications
			let mut listener = self.listener.write();
			for h in &removed {
				listener.dropped(h, None);
			}

			removed
		} else {
			Default::default()
		}
	}

	/// Import a single extrinsic and starts to watch their progress in the pool.
	pub fn submit_and_watch(
		&self,
		tx: ValidatedTransactionFor<B>,
	) -> Result<Watcher<ExHash<B>, BlockHash<B>>, B::Error> {
		match tx {
			ValidatedTransaction::Valid(tx) => {
				let hash = self.api.hash_and_length(&tx.data).0;
				let watcher = self.listener.write().create_watcher(hash);
				self.submit(std::iter::once(ValidatedTransaction::Valid(tx)))
					.pop()
					.expect("One extrinsic passed; one result returned; qed")
					.map(|_| watcher)
			},
			ValidatedTransaction::Invalid(hash, err) => {
				self.rotator.ban(&std::time::Instant::now(), std::iter::once(hash));
				Err(err.into())
			},
			ValidatedTransaction::Unknown(_, err) => Err(err.into()),
		}
	}

	/// For each extrinsic, returns tags that it provides (if known), or None (if it is unknown).
	pub fn extrinsics_tags(&self, extrinsics: &[ExtrinsicFor<B>]) -> (Vec<ExHash<B>>, Vec<Option<Vec<Tag>>>) {
		let hashes = extrinsics.iter().map(|extrinsic| self.api.hash_and_length(extrinsic).0).collect::<Vec<_>>();
		let in_pool = self.pool.read().by_hash(&hashes);
		(
			hashes,
			in_pool.into_iter()
				.map(|existing_in_pool| existing_in_pool
					.map(|transaction| transaction.provides.iter().cloned()
					.collect()))
				.collect(),
		)
	}

	/// Prunes ready transactions that provide given list of tags.
	pub fn prune_tags(
		&self,
		tags: impl IntoIterator<Item=Tag>,
	) -> Result<PruneStatus<ExHash<B>, ExtrinsicFor<B>>, B::Error> {
		// Perform tag-based pruning in the base pool
		let status = self.pool.write().prune_tags(tags);
		// Notify event listeners of all transactions
		// that were promoted to `Ready` or were dropped.
		{
			let mut listener = self.listener.write();
			for promoted in &status.promoted {
				fire_events(&mut *listener, promoted);
			}
			for f in &status.failed {
				listener.dropped(f, None);
			}
		}

		Ok(status)
	}

	/// Resubmit transactions that have been revalidated after prune_tags call.
	pub fn resubmit_pruned(
		&self,
		at: &BlockId<B::Block>,
		known_imported_hashes: impl IntoIterator<Item=ExHash<B>> + Clone,
		pruned_hashes: Vec<ExHash<B>>,
		pruned_xts: Vec<ValidatedTransactionFor<B>>,
	) -> Result<(), B::Error> {
		debug_assert_eq!(pruned_hashes.len(), pruned_xts.len());

		// Resubmit pruned transactions
		let results = self.submit(pruned_xts);

		// Collect the hashes of transactions that now became invalid (meaning that they are successfully pruned).
		let hashes = results
			.into_iter()
			.enumerate()
			.filter_map(|(idx, r)| match r.map_err(error::IntoPoolError::into_pool_error) {
				Err(Ok(error::Error::InvalidTransaction(_))) => Some(pruned_hashes[idx].clone()),
				_ => None,
			});
		// Fire `pruned` notifications for collected hashes and make sure to include
		// `known_imported_hashes` since they were just imported as part of the block.
		let hashes = hashes.chain(known_imported_hashes.into_iter());
		{
			let header_hash = self.api.block_id_to_hash(at)?
				.ok_or_else(|| error::Error::InvalidBlockId(format!("{:?}", at)).into())?;
			let mut listener = self.listener.write();
			for h in hashes {
				listener.pruned(header_hash, &h);
			}
		}
		// perform regular cleanup of old transactions in the pool
		// and update temporary bans.
		self.clear_stale(at)?;
		Ok(())
	}

	/// Removes stale transactions from the pool.
	///
	/// Stale transactions are transaction beyond their longevity period.
	/// Note this function does not remove transactions that are already included in the chain.
	/// See `prune_tags` if you want this.
	pub fn clear_stale(&self, at: &BlockId<B::Block>) -> Result<(), B::Error> {
		let block_number = self.api.block_id_to_number(at)?
				.ok_or_else(|| error::Error::InvalidBlockId(format!("{:?}", at)).into())?
				.saturated_into::<u64>();
		let now = time::Instant::now();
		let to_remove = {
			self.ready()
				.filter(|tx| self.rotator.ban_if_stale(&now, block_number, &tx))
				.map(|tx| tx.hash.clone())
				.collect::<Vec<_>>()
		};
		let futures_to_remove: Vec<ExHash<B>> = {
			let p = self.pool.read();
			let mut hashes = Vec::new();
			for tx in p.futures() {
				if self.rotator.ban_if_stale(&now, block_number, &tx) {
					hashes.push(tx.hash.clone());
				}
			}
			hashes
		};
		// removing old transactions
		self.remove_invalid(&to_remove);
		self.remove_invalid(&futures_to_remove);
		// clear banned transactions timeouts
		self.rotator.clear_timeouts(&now);

		Ok(())
	}

	/// Get rotator reference.
	#[cfg(test)]
	pub fn rotator(&self) -> &PoolRotator<ExHash<B>> {
		&self.rotator
	}

	/// Get api reference.
	pub fn api(&self) -> &B {
		&self.api
	}

	/// Return an event stream of transactions imported to the pool.
	pub fn import_notification_stream(&self) -> EventStream {
		let (sink, stream) = mpsc::unbounded();
		self.import_notification_sinks.lock().push(sink);
		stream
	}

	/// Invoked when extrinsics are broadcasted.
	pub fn on_broadcasted(&self, propagated: HashMap<ExHash<B>, Vec<String>>) {
		let mut listener = self.listener.write();
		for (hash, peers) in propagated.into_iter() {
			listener.broadcasted(&hash, peers);
		}
	}

	/// Remove from the pool.
	pub fn remove_invalid(&self, hashes: &[ExHash<B>]) -> Vec<TransactionFor<B>> {
		// temporarily ban invalid transactions
		debug!(target: "txpool", "Banning invalid transactions: {:?}", hashes);
		self.rotator.ban(&time::Instant::now(), hashes.iter().cloned());

		let invalid = self.pool.write().remove_invalid(hashes);

		let mut listener = self.listener.write();
		for tx in &invalid {
			listener.invalid(&tx.hash);
		}

		invalid
	}

	/// Get an iterator for ready transactions ordered by priority
	pub fn ready(&self) -> impl Iterator<Item=TransactionFor<B>> {
		self.pool.read().ready()
	}

	/// Returns pool status.
	pub fn status(&self) -> base::Status {
		self.pool.read().status()
	}
}

fn fire_events<H, H2, Ex>(
	listener: &mut Listener<H, H2>,
	imported: &base::Imported<H, Ex>,
) where
	H: hash::Hash + Eq + traits::Member + Serialize,
	H2: Clone + fmt::Debug,
{
	match *imported {
		base::Imported::Ready { ref promoted, ref failed, ref removed, ref hash } => {
			listener.ready(hash, None);
			for f in failed {
				listener.invalid(f);
			}
			for r in removed {
				listener.dropped(&r.hash, Some(hash));
			}
			for p in promoted {
				listener.ready(p, None);
			}
		},
		base::Imported::Future { ref hash } => {
			listener.future(hash)
		},
	}
}
