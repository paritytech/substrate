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

use std::{
	collections::{HashMap, HashSet},
	hash,
	sync::Arc,
};

use futures::channel::mpsc::{channel, Sender};
use parking_lot::{Mutex, RwLock};
use retain_mut::RetainMut;
use sc_transaction_pool_api::{error, PoolStatus};
use serde::Serialize;
use sp_runtime::{
	generic::BlockId,
	traits::{self, SaturatedConversion},
	transaction_validity::{TransactionSource, TransactionTag as Tag, ValidTransaction},
};
use std::time::Instant;

use super::{
	base_pool::{self as base, PruneStatus},
	listener::Listener,
	pool::{
		BlockHash, ChainApi, EventStream, ExtrinsicFor, ExtrinsicHash, Options, TransactionFor,
	},
	rotator::PoolRotator,
	watcher::Watcher,
};

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

impl<Hash, Ex, Error> ValidatedTransaction<Hash, Ex, Error> {
	/// Consume validity result, transaction data and produce ValidTransaction.
	pub fn valid_at(
		at: u64,
		hash: Hash,
		source: TransactionSource,
		data: Ex,
		bytes: usize,
		validity: ValidTransaction,
	) -> Self {
		Self::Valid(base::Transaction {
			data,
			bytes,
			hash,
			source,
			priority: validity.priority,
			requires: validity.requires,
			provides: validity.provides,
			propagate: validity.propagate,
			valid_till: at.saturated_into::<u64>().saturating_add(validity.longevity),
		})
	}
}

/// A type of validated transaction stored in the pool.
pub type ValidatedTransactionFor<B> =
	ValidatedTransaction<ExtrinsicHash<B>, ExtrinsicFor<B>, <B as ChainApi>::Error>;

/// A closure that returns true if the local node is a validator that can author blocks.
pub struct IsValidator(Box<dyn Fn() -> bool + Send + Sync>);

impl From<bool> for IsValidator {
	fn from(is_validator: bool) -> Self {
		Self(Box::new(move || is_validator))
	}
}

impl From<Box<dyn Fn() -> bool + Send + Sync>> for IsValidator {
	fn from(is_validator: Box<dyn Fn() -> bool + Send + Sync>) -> Self {
		Self(is_validator)
	}
}

/// Pool that deals with validated transactions.
pub struct ValidatedPool<B: ChainApi> {
	api: Arc<B>,
	is_validator: IsValidator,
	options: Options,
	listener: RwLock<Listener<ExtrinsicHash<B>, B>>,
	pool: RwLock<base::BasePool<ExtrinsicHash<B>, ExtrinsicFor<B>>>,
	import_notification_sinks: Mutex<Vec<Sender<ExtrinsicHash<B>>>>,
	rotator: PoolRotator<ExtrinsicHash<B>>,
}

#[cfg(not(target_os = "unknown"))]
impl<B: ChainApi> parity_util_mem::MallocSizeOf for ValidatedPool<B>
where
	ExtrinsicFor<B>: parity_util_mem::MallocSizeOf,
{
	fn size_of(&self, ops: &mut parity_util_mem::MallocSizeOfOps) -> usize {
		// other entries insignificant or non-primary references
		self.pool.size_of(ops)
	}
}

impl<B: ChainApi> ValidatedPool<B> {
	/// Create a new transaction pool.
	pub fn new(options: Options, is_validator: IsValidator, api: Arc<B>) -> Self {
		let base_pool = base::BasePool::new(options.reject_future_transactions);
		Self {
			is_validator,
			options,
			listener: Default::default(),
			api,
			pool: RwLock::new(base_pool),
			import_notification_sinks: Default::default(),
			rotator: Default::default(),
		}
	}

	/// Bans given set of hashes.
	pub fn ban(&self, now: &Instant, hashes: impl IntoIterator<Item = ExtrinsicHash<B>>) {
		self.rotator.ban(now, hashes)
	}

	/// Returns true if transaction with given hash is currently banned from the pool.
	pub fn is_banned(&self, hash: &ExtrinsicHash<B>) -> bool {
		self.rotator.is_banned(hash)
	}

	/// A fast check before doing any further processing of a transaction, like validation.
	///
	/// If `ignore_banned` is `true`, it will not check if the transaction is banned.
	///
	/// It checks if the transaction is already imported or banned. If so, it returns an error.
	pub fn check_is_known(
		&self,
		tx_hash: &ExtrinsicHash<B>,
		ignore_banned: bool,
	) -> Result<(), B::Error> {
		if !ignore_banned && self.is_banned(tx_hash) {
			Err(error::Error::TemporarilyBanned.into())
		} else if self.pool.read().is_imported(tx_hash) {
			Err(error::Error::AlreadyImported(Box::new(*tx_hash)).into())
		} else {
			Ok(())
		}
	}

	/// Imports a bunch of pre-validated transactions to the pool.
	pub fn submit(
		&self,
		txs: impl IntoIterator<Item = ValidatedTransactionFor<B>>,
	) -> Vec<Result<ExtrinsicHash<B>, B::Error>> {
		let results = txs
			.into_iter()
			.map(|validated_tx| self.submit_one(validated_tx))
			.collect::<Vec<_>>();

		// only enforce limits if there is at least one imported transaction
		let removed = if results.iter().any(|res| res.is_ok()) {
			self.enforce_limits()
		} else {
			Default::default()
		};

		results
			.into_iter()
			.map(|res| match res {
				Ok(ref hash) if removed.contains(hash) =>
					Err(error::Error::ImmediatelyDropped.into()),
				other => other,
			})
			.collect()
	}

	/// Submit single pre-validated transaction to the pool.
	fn submit_one(&self, tx: ValidatedTransactionFor<B>) -> Result<ExtrinsicHash<B>, B::Error> {
		match tx {
			ValidatedTransaction::Valid(tx) => {
				if !tx.propagate && !(self.is_validator.0)() {
					return Err(error::Error::Unactionable.into())
				}

				let imported = self.pool.write().import(tx)?;

				if let base::Imported::Ready { ref hash, .. } = imported {
					self.import_notification_sinks.lock().retain_mut(|sink| {
						match sink.try_send(*hash) {
							Ok(()) => true,
							Err(e) =>
								if e.is_full() {
									log::warn!(
										target: "txpool",
										"[{:?}] Trying to notify an import but the channel is full",
										hash,
									);
									true
								} else {
									false
								},
						}
					});
				}

				let mut listener = self.listener.write();
				fire_events(&mut *listener, &imported);
				Ok(*imported.hash())
			},
			ValidatedTransaction::Invalid(hash, err) => {
				self.rotator.ban(&Instant::now(), std::iter::once(hash));
				Err(err)
			},
			ValidatedTransaction::Unknown(hash, err) => {
				self.listener.write().invalid(&hash);
				Err(err)
			},
		}
	}

	fn enforce_limits(&self) -> HashSet<ExtrinsicHash<B>> {
		let status = self.pool.read().status();
		let ready_limit = &self.options.ready;
		let future_limit = &self.options.future;

		log::debug!(target: "txpool", "Pool Status: {:?}", status);
		if ready_limit.is_exceeded(status.ready, status.ready_bytes) ||
			future_limit.is_exceeded(status.future, status.future_bytes)
		{
			log::debug!(
				target: "txpool",
				"Enforcing limits ({}/{}kB ready, {}/{}kB future",
				ready_limit.count, ready_limit.total_bytes / 1024,
				future_limit.count, future_limit.total_bytes / 1024,
			);

			// clean up the pool
			let removed = {
				let mut pool = self.pool.write();
				let removed = pool
					.enforce_limits(ready_limit, future_limit)
					.into_iter()
					.map(|x| x.hash)
					.collect::<HashSet<_>>();
				// ban all removed transactions
				self.rotator.ban(&Instant::now(), removed.iter().copied());
				removed
			};
			if !removed.is_empty() {
				log::debug!(target: "txpool", "Enforcing limits: {} dropped", removed.len());
			}

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
	) -> Result<Watcher<ExtrinsicHash<B>, ExtrinsicHash<B>>, B::Error> {
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
				self.rotator.ban(&Instant::now(), std::iter::once(hash));
				Err(err)
			},
			ValidatedTransaction::Unknown(_, err) => Err(err),
		}
	}

	/// Resubmits revalidated transactions back to the pool.
	///
	/// Removes and then submits passed transactions and all dependent transactions.
	/// Transactions that are missing from the pool are not submitted.
	pub fn resubmit(
		&self,
		mut updated_transactions: HashMap<ExtrinsicHash<B>, ValidatedTransactionFor<B>>,
	) {
		#[derive(Debug, Clone, Copy, PartialEq)]
		enum Status {
			Future,
			Ready,
			Failed,
			Dropped,
		}

		let (mut initial_statuses, final_statuses) = {
			let mut pool = self.pool.write();

			// remove all passed transactions from the ready/future queues
			// (this may remove additional transactions as well)
			//
			// for every transaction that has an entry in the `updated_transactions`,
			// we store updated validation result in txs_to_resubmit
			// for every transaction that has no entry in the `updated_transactions`,
			// we store last validation result (i.e. the pool entry) in txs_to_resubmit
			let mut initial_statuses = HashMap::new();
			let mut txs_to_resubmit = Vec::with_capacity(updated_transactions.len());
			while !updated_transactions.is_empty() {
				let hash = updated_transactions
					.keys()
					.next()
					.cloned()
					.expect("transactions is not empty; qed");

				// note we are not considering tx with hash invalid here - we just want
				// to remove it along with dependent transactions and `remove_subtree()`
				// does exactly what we need
				let removed = pool.remove_subtree(&[hash]);
				for removed_tx in removed {
					let removed_hash = removed_tx.hash;
					let updated_transaction = updated_transactions.remove(&removed_hash);
					let tx_to_resubmit = if let Some(updated_tx) = updated_transaction {
						updated_tx
					} else {
						// in most cases we'll end up in successful `try_unwrap`, but if not
						// we still need to reinsert transaction back to the pool => duplicate call
						let transaction = match Arc::try_unwrap(removed_tx) {
							Ok(transaction) => transaction,
							Err(transaction) => transaction.duplicate(),
						};
						ValidatedTransaction::Valid(transaction)
					};

					initial_statuses.insert(removed_hash, Status::Ready);
					txs_to_resubmit.push((removed_hash, tx_to_resubmit));
				}
				// make sure to remove the hash even if it's not present in the pool any more.
				updated_transactions.remove(&hash);
			}

			// if we're rejecting future transactions, then insertion order matters here:
			// if tx1 depends on tx2, then if tx1 is inserted before tx2, then it goes
			// to the future queue and gets rejected immediately
			// => let's temporary stop rejection and clear future queue before return
			pool.with_futures_enabled(|pool, reject_future_transactions| {
				// now resubmit all removed transactions back to the pool
				let mut final_statuses = HashMap::new();
				for (hash, tx_to_resubmit) in txs_to_resubmit {
					match tx_to_resubmit {
						ValidatedTransaction::Valid(tx) => match pool.import(tx) {
							Ok(imported) => match imported {
								base::Imported::Ready { promoted, failed, removed, .. } => {
									final_statuses.insert(hash, Status::Ready);
									for hash in promoted {
										final_statuses.insert(hash, Status::Ready);
									}
									for hash in failed {
										final_statuses.insert(hash, Status::Failed);
									}
									for tx in removed {
										final_statuses.insert(tx.hash, Status::Dropped);
									}
								},
								base::Imported::Future { .. } => {
									final_statuses.insert(hash, Status::Future);
								},
							},
							Err(err) => {
								// we do not want to fail if single transaction import has failed
								// nor we do want to propagate this error, because it could tx
								// unknown to caller => let's just notify listeners (and issue debug
								// message)
								log::warn!(
									target: "txpool",
									"[{:?}] Removing invalid transaction from update: {}",
									hash,
									err,
								);
								final_statuses.insert(hash, Status::Failed);
							},
						},
						ValidatedTransaction::Invalid(_, _) |
						ValidatedTransaction::Unknown(_, _) => {
							final_statuses.insert(hash, Status::Failed);
						},
					}
				}

				// if the pool is configured to reject future transactions, let's clear the future
				// queue, updating final statuses as required
				if reject_future_transactions {
					for future_tx in pool.clear_future() {
						final_statuses.insert(future_tx.hash, Status::Dropped);
					}
				}

				(initial_statuses, final_statuses)
			})
		};

		// and now let's notify listeners about status changes
		let mut listener = self.listener.write();
		for (hash, final_status) in final_statuses {
			let initial_status = initial_statuses.remove(&hash);
			if initial_status.is_none() || Some(final_status) != initial_status {
				match final_status {
					Status::Future => listener.future(&hash),
					Status::Ready => listener.ready(&hash, None),
					Status::Dropped => listener.dropped(&hash, None),
					Status::Failed => listener.invalid(&hash),
				}
			}
		}
	}

	/// For each extrinsic, returns tags that it provides (if known), or None (if it is unknown).
	pub fn extrinsics_tags(&self, hashes: &[ExtrinsicHash<B>]) -> Vec<Option<Vec<Tag>>> {
		self.pool
			.read()
			.by_hashes(&hashes)
			.into_iter()
			.map(|existing_in_pool| {
				existing_in_pool.map(|transaction| transaction.provides.to_vec())
			})
			.collect()
	}

	/// Get ready transaction by hash
	pub fn ready_by_hash(&self, hash: &ExtrinsicHash<B>) -> Option<TransactionFor<B>> {
		self.pool.read().ready_by_hash(hash)
	}

	/// Prunes ready transactions that provide given list of tags.
	pub fn prune_tags(
		&self,
		tags: impl IntoIterator<Item = Tag>,
	) -> Result<PruneStatus<ExtrinsicHash<B>, ExtrinsicFor<B>>, B::Error> {
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
		known_imported_hashes: impl IntoIterator<Item = ExtrinsicHash<B>> + Clone,
		pruned_hashes: Vec<ExtrinsicHash<B>>,
		pruned_xts: Vec<ValidatedTransactionFor<B>>,
	) -> Result<(), B::Error> {
		debug_assert_eq!(pruned_hashes.len(), pruned_xts.len());

		// Resubmit pruned transactions
		let results = self.submit(pruned_xts);

		// Collect the hashes of transactions that now became invalid (meaning that they are
		// successfully pruned).
		let hashes = results.into_iter().enumerate().filter_map(|(idx, r)| {
			match r.map_err(error::IntoPoolError::into_pool_error) {
				Err(Ok(error::Error::InvalidTransaction(_))) => Some(pruned_hashes[idx]),
				_ => None,
			}
		});
		// Fire `pruned` notifications for collected hashes and make sure to include
		// `known_imported_hashes` since they were just imported as part of the block.
		let hashes = hashes.chain(known_imported_hashes.into_iter());
		self.fire_pruned(at, hashes)?;

		// perform regular cleanup of old transactions in the pool
		// and update temporary bans.
		self.clear_stale(at)?;
		Ok(())
	}

	/// Fire notifications for pruned transactions.
	pub fn fire_pruned(
		&self,
		at: &BlockId<B::Block>,
		hashes: impl Iterator<Item = ExtrinsicHash<B>>,
	) -> Result<(), B::Error> {
		let header_hash = self
			.api
			.block_id_to_hash(at)?
			.ok_or_else(|| error::Error::InvalidBlockId(format!("{:?}", at)))?;
		let mut listener = self.listener.write();
		let mut set = HashSet::with_capacity(hashes.size_hint().0);
		for h in hashes {
			// `hashes` has possibly duplicate hashes.
			// we'd like to send out the `InBlock` notification only once.
			if !set.contains(&h) {
				listener.pruned(header_hash, &h);
				set.insert(h);
			}
		}
		Ok(())
	}

	/// Removes stale transactions from the pool.
	///
	/// Stale transactions are transaction beyond their longevity period.
	/// Note this function does not remove transactions that are already included in the chain.
	/// See `prune_tags` if you want this.
	pub fn clear_stale(&self, at: &BlockId<B::Block>) -> Result<(), B::Error> {
		let block_number = self
			.api
			.block_id_to_number(at)?
			.ok_or_else(|| error::Error::InvalidBlockId(format!("{:?}", at)))?
			.saturated_into::<u64>();
		let now = Instant::now();
		let to_remove = {
			self.ready()
				.filter(|tx| self.rotator.ban_if_stale(&now, block_number, &tx))
				.map(|tx| tx.hash)
				.collect::<Vec<_>>()
		};
		let futures_to_remove: Vec<ExtrinsicHash<B>> = {
			let p = self.pool.read();
			let mut hashes = Vec::new();
			for tx in p.futures() {
				if self.rotator.ban_if_stale(&now, block_number, &tx) {
					hashes.push(tx.hash);
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
	#[cfg(feature = "test-helpers")]
	pub fn rotator(&self) -> &PoolRotator<ExtrinsicHash<B>> {
		&self.rotator
	}

	/// Get api reference.
	pub fn api(&self) -> &B {
		&self.api
	}

	/// Return an event stream of notifications for when transactions are imported to the pool.
	///
	/// Consumers of this stream should use the `ready` method to actually get the
	/// pending transactions in the right order.
	pub fn import_notification_stream(&self) -> EventStream<ExtrinsicHash<B>> {
		const CHANNEL_BUFFER_SIZE: usize = 1024;

		let (sink, stream) = channel(CHANNEL_BUFFER_SIZE);
		self.import_notification_sinks.lock().push(sink);
		stream
	}

	/// Invoked when extrinsics are broadcasted.
	pub fn on_broadcasted(&self, propagated: HashMap<ExtrinsicHash<B>, Vec<String>>) {
		let mut listener = self.listener.write();
		for (hash, peers) in propagated.into_iter() {
			listener.broadcasted(&hash, peers);
		}
	}

	/// Remove a subtree of transactions from the pool and mark them invalid.
	///
	/// The transactions passed as an argument will be additionally banned
	/// to prevent them from entering the pool right away.
	/// Note this is not the case for the dependent transactions - those may
	/// still be valid so we want to be able to re-import them.
	pub fn remove_invalid(&self, hashes: &[ExtrinsicHash<B>]) -> Vec<TransactionFor<B>> {
		// early exit in case there is no invalid transactions.
		if hashes.is_empty() {
			return vec![]
		}

		log::debug!(target: "txpool", "Removing invalid transactions: {:?}", hashes);

		// temporarily ban invalid transactions
		self.rotator.ban(&Instant::now(), hashes.iter().cloned());

		let invalid = self.pool.write().remove_subtree(hashes);

		log::debug!(target: "txpool", "Removed invalid transactions: {:?}", invalid);

		let mut listener = self.listener.write();
		for tx in &invalid {
			listener.invalid(&tx.hash);
		}

		invalid
	}

	/// Get an iterator for ready transactions ordered by priority
	pub fn ready(&self) -> impl Iterator<Item = TransactionFor<B>> + Send {
		self.pool.read().ready()
	}

	/// Returns a Vec of hashes and extrinsics in the future pool.
	pub fn futures(&self) -> Vec<(ExtrinsicHash<B>, ExtrinsicFor<B>)> {
		self.pool
			.read()
			.futures()
			.map(|tx| (tx.hash.clone(), tx.data.clone()))
			.collect()
	}

	/// Returns pool status.
	pub fn status(&self) -> PoolStatus {
		self.pool.read().status()
	}

	/// Notify all watchers that transactions in the block with hash have been finalized
	pub async fn on_block_finalized(&self, block_hash: BlockHash<B>) -> Result<(), B::Error> {
		log::trace!(target: "txpool", "Attempting to notify watchers of finalization for {}", block_hash);
		self.listener.write().finalized(block_hash);
		Ok(())
	}

	/// Notify the listener of retracted blocks
	pub fn on_block_retracted(&self, block_hash: BlockHash<B>) {
		self.listener.write().retracted(block_hash)
	}
}

fn fire_events<H, B, Ex>(listener: &mut Listener<H, B>, imported: &base::Imported<H, Ex>)
where
	H: hash::Hash + Eq + traits::Member + Serialize,
	B: ChainApi,
{
	match *imported {
		base::Imported::Ready { ref promoted, ref failed, ref removed, ref hash } => {
			listener.ready(hash, None);
			failed.into_iter().for_each(|f| listener.invalid(f));
			removed.into_iter().for_each(|r| listener.dropped(&r.hash, Some(hash)));
			promoted.into_iter().for_each(|p| listener.ready(p, None));
		},
		base::Imported::Future { ref hash } => listener.future(hash),
	}
}
