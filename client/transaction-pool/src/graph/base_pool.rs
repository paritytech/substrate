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

//! A basic version of the dependency graph.
//!
//! For a more full-featured pool, have a look at the `pool` module.

use std::{
	collections::HashSet,
	fmt,
	hash,
	sync::Arc,
};

use log::{trace, debug, warn};
use serde::Serialize;
use sp_core::hexdisplay::HexDisplay;
use sp_runtime::traits::Member;
use sp_runtime::transaction_validity::{
	TransactionTag as Tag,
	TransactionLongevity as Longevity,
	TransactionPriority as Priority,
	TransactionSource as Source,
};
use sc_transaction_pool_api::{error, PoolStatus, InPoolTransaction};

use super::{
	future::{FutureTransactions, WaitingTransaction},
	ready::ReadyTransactions,
};

/// Successful import result.
#[derive(Debug, PartialEq, Eq)]
pub enum Imported<Hash, Ex> {
	/// Transaction was successfully imported to Ready queue.
	Ready {
		/// Hash of transaction that was successfully imported.
		hash: Hash,
		/// Transactions that got promoted from the Future queue.
		promoted: Vec<Hash>,
		/// Transactions that failed to be promoted from the Future queue and are now discarded.
		failed: Vec<Hash>,
		/// Transactions removed from the Ready pool (replaced).
		removed: Vec<Arc<Transaction<Hash, Ex>>>,
	},
	/// Transaction was successfully imported to Future queue.
	Future {
		/// Hash of transaction that was successfully imported.
		hash: Hash,
	}
}

impl<Hash, Ex> Imported<Hash, Ex> {
	/// Returns the hash of imported transaction.
	pub fn hash(&self) -> &Hash {
		use self::Imported::*;
		match *self {
			Ready { ref hash, .. } => hash,
			Future { ref hash, .. } => hash,
		}
	}
}

/// Status of pruning the queue.
#[derive(Debug)]
pub struct PruneStatus<Hash, Ex> {
	/// A list of imports that satisfying the tag triggered.
	pub promoted: Vec<Imported<Hash, Ex>>,
	/// A list of transactions that failed to be promoted and now are discarded.
	pub failed: Vec<Hash>,
	/// A list of transactions that got pruned from the ready queue.
	pub pruned: Vec<Arc<Transaction<Hash, Ex>>>,
}

/// Immutable transaction
#[cfg_attr(test, derive(Clone))]
#[derive(PartialEq, Eq, parity_util_mem::MallocSizeOf)]
pub struct Transaction<Hash, Extrinsic> {
	/// Raw extrinsic representing that transaction.
	pub data: Extrinsic,
	/// Number of bytes encoding of the transaction requires.
	pub bytes: usize,
	/// Transaction hash (unique)
	pub hash: Hash,
	/// Transaction priority (higher = better)
	pub priority: Priority,
	/// At which block the transaction becomes invalid?
	pub valid_till: Longevity,
	/// Tags required by the transaction.
	pub requires: Vec<Tag>,
	/// Tags that this transaction provides.
	pub provides: Vec<Tag>,
	/// Should that transaction be propagated.
	pub propagate: bool,
	/// Source of that transaction.
	pub source: Source,
}

impl<Hash, Extrinsic> AsRef<Extrinsic> for Transaction<Hash, Extrinsic> {
	fn as_ref(&self) -> &Extrinsic {
		&self.data
	}
}

impl<Hash, Extrinsic> InPoolTransaction for Transaction<Hash, Extrinsic> {
	type Transaction = Extrinsic;
	type Hash = Hash;

	fn data(&self) -> &Extrinsic {
		&self.data
	}

	fn hash(&self) -> &Hash {
		&self.hash
	}

	fn priority(&self) -> &Priority {
		&self.priority
	}

	fn longevity(&self) ->&Longevity {
		&self.valid_till
	}

	fn requires(&self) -> &[Tag] {
		&self.requires
	}

	fn provides(&self) -> &[Tag] {
		&self.provides
	}

	fn is_propagable(&self) -> bool {
		self.propagate
	}
}

impl<Hash: Clone, Extrinsic: Clone> Transaction<Hash, Extrinsic> {
	/// Explicit transaction clone.
	///
	/// Transaction should be cloned only if absolutely necessary && we want
	/// every reason to be commented. That's why we `Transaction` is not `Clone`,
	/// but there's explicit `duplicate` method.
	pub fn duplicate(&self) -> Self {
		Self {
			data: self.data.clone(),
			bytes: self.bytes,
			hash: self.hash.clone(),
			priority: self.priority,
			source: self.source,
			valid_till: self.valid_till,
			requires: self.requires.clone(),
			provides: self.provides.clone(),
			propagate: self.propagate,
		}
	}
}

impl<Hash, Extrinsic> fmt::Debug for Transaction<Hash, Extrinsic> where
	Hash: fmt::Debug,
	Extrinsic: fmt::Debug,
{
	fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
		let join_tags = |tags: &[Tag]| {
			tags.iter().map(|tag| HexDisplay::from(tag).to_string()).collect::<Vec<_>>().join(", ")
		};

		write!(fmt, "Transaction {{ ")?;
		write!(fmt, "hash: {:?}, ", &self.hash)?;
		write!(fmt, "priority: {:?}, ", &self.priority)?;
		write!(fmt, "valid_till: {:?}, ", &self.valid_till)?;
		write!(fmt, "bytes: {:?}, ", &self.bytes)?;
		write!(fmt, "propagate: {:?}, ", &self.propagate)?;
		write!(fmt, "source: {:?}, ", &self.source)?;
		write!(fmt, "requires: [{}], ", join_tags(&self.requires))?;
		write!(fmt, "provides: [{}], ", join_tags(&self.provides))?;
		write!(fmt, "data: {:?}", &self.data)?;
		write!(fmt, "}}")?;
		Ok(())
	}
}

/// Store last pruned tags for given number of invocations.
const RECENTLY_PRUNED_TAGS: usize = 2;

/// Transaction pool.
///
/// Builds a dependency graph for all transactions in the pool and returns
/// the ones that are currently ready to be executed.
///
/// General note:
/// If function returns some transactions it usually means that importing them
/// as-is for the second time will fail or produce unwanted results.
/// Most likely it is required to revalidate them and recompute set of
/// required tags.
#[derive(Debug)]
#[cfg_attr(not(target_os = "unknown"), derive(parity_util_mem::MallocSizeOf))]
pub struct BasePool<Hash: hash::Hash + Eq, Ex> {
	reject_future_transactions: bool,
	future: FutureTransactions<Hash, Ex>,
	ready: ReadyTransactions<Hash, Ex>,
	/// Store recently pruned tags (for last two invocations).
	///
	/// This is used to make sure we don't accidentally put
	/// transactions to future in case they were just stuck in verification.
	recently_pruned: [HashSet<Tag>; RECENTLY_PRUNED_TAGS],
	recently_pruned_index: usize,
}

impl<Hash: hash::Hash + Member + Serialize, Ex: std::fmt::Debug> Default for BasePool<Hash, Ex> {
	fn default() -> Self {
		Self::new(false)
	}
}

impl<Hash: hash::Hash + Member + Serialize, Ex: std::fmt::Debug> BasePool<Hash, Ex> {
	/// Create new pool given reject_future_transactions flag.
	pub fn new(reject_future_transactions: bool) -> Self {
		Self {
			reject_future_transactions,
			future: Default::default(),
			ready: Default::default(),
			recently_pruned: Default::default(),
			recently_pruned_index: 0,
		}
	}

	/// Temporary enables future transactions, runs closure and then restores
	/// `reject_future_transactions` flag back to previous value.
	///
	/// The closure accepts the mutable reference to the pool and original value
	/// of the `reject_future_transactions` flag.
	pub(crate) fn with_futures_enabled<T>(&mut self, closure: impl FnOnce(&mut Self, bool) -> T) -> T {
		let previous = self.reject_future_transactions;
		self.reject_future_transactions = false;
		let return_value = closure(self, previous);
		self.reject_future_transactions = previous;
		return_value
	}

	/// Returns if the transaction for the given hash is already imported.
	pub fn is_imported(&self, tx_hash: &Hash) -> bool {
		self.future.contains(tx_hash) || self.ready.contains(tx_hash)
	}

	/// Imports transaction to the pool.
	///
	/// The pool consists of two parts: Future and Ready.
	/// The former contains transactions that require some tags that are not yet provided by
	/// other transactions in the pool.
	/// The latter contains transactions that have all the requirements satisfied and are
	/// ready to be included in the block.
	pub fn import(
		&mut self,
		tx: Transaction<Hash, Ex>,
	) -> error::Result<Imported<Hash, Ex>> {
		if self.is_imported(&tx.hash) {
			return Err(error::Error::AlreadyImported(Box::new(tx.hash)))
		}

		let tx = WaitingTransaction::new(
			tx,
			self.ready.provided_tags(),
			&self.recently_pruned,
		);
		trace!(target: "txpool", "[{:?}] {:?}", tx.transaction.hash, tx);
		debug!(
			target: "txpool",
			"[{:?}] Importing to {}",
			tx.transaction.hash,
			if tx.is_ready() { "ready" } else { "future" }
		);

		// If all tags are not satisfied import to future.
		if !tx.is_ready() {
			if self.reject_future_transactions {
				return Err(error::Error::RejectedFutureTransaction);
			}

			let hash = tx.transaction.hash.clone();
			self.future.import(tx);
			return Ok(Imported::Future { hash });
		}

		self.import_to_ready(tx)
	}

	/// Imports transaction to ready queue.
	///
	/// NOTE the transaction has to have all requirements satisfied.
	fn import_to_ready(&mut self, tx: WaitingTransaction<Hash, Ex>) -> error::Result<Imported<Hash, Ex>> {
		let hash = tx.transaction.hash.clone();
		let mut promoted = vec![];
		let mut failed = vec![];
		let mut removed = vec![];

		let mut first = true;
		let mut to_import = vec![tx];

		// take first transaction from the list
		while let Some(tx) = to_import.pop() {
			// find transactions in Future that it unlocks
			to_import.append(&mut self.future.satisfy_tags(&tx.transaction.provides));

			// import this transaction
			let current_hash = tx.transaction.hash.clone();
			match self.ready.import(tx) {
				Ok(mut replaced) => {
					if !first {
						promoted.push(current_hash);
					}
					// The transactions were removed from the ready pool. We might attempt to re-import them.
					removed.append(&mut replaced);
				},
				// transaction failed to be imported.
				Err(e) => if first {
					debug!(target: "txpool", "[{:?}] Error importing: {:?}", current_hash, e);
					return Err(e)
				} else {
					failed.push(current_hash);
				},
			}
			first = false;
		}

		// An edge case when importing transaction caused
		// some future transactions to be imported and that
		// future transactions pushed out current transaction.
		// This means that there is a cycle and the transactions should
		// be moved back to future, since we can't resolve it.
		if removed.iter().any(|tx| tx.hash == hash) {
			// We still need to remove all transactions that we promoted
			// since they depend on each other and will never get to the best iterator.
			self.ready.remove_subtree(&promoted);

			debug!(target: "txpool", "[{:?}] Cycle detected, bailing.", hash);
			return Err(error::Error::CycleDetected)
		}

		Ok(Imported::Ready {
			hash,
			promoted,
			failed,
			removed,
		})
	}

	/// Returns an iterator over ready transactions in the pool.
	pub fn ready(&self) -> impl Iterator<Item=Arc<Transaction<Hash, Ex>>> {
		self.ready.get()
	}

	/// Returns an iterator over future transactions in the pool.
	pub fn futures(&self) -> impl Iterator<Item=&Transaction<Hash, Ex>> {
		self.future.all()
	}

	/// Returns pool transactions given list of hashes.
	///
	/// Includes both ready and future pool. For every hash in the `hashes`
	/// iterator an `Option` is produced (so the resulting `Vec` always have the same length).
	pub fn by_hashes(&self, hashes: &[Hash]) -> Vec<Option<Arc<Transaction<Hash, Ex>>>> {
		let ready = self.ready.by_hashes(hashes);
		let future = self.future.by_hashes(hashes);

		ready
			.into_iter()
			.zip(future)
			.map(|(a, b)| a.or(b))
			.collect()
	}

	/// Returns pool transaction by hash.
	pub fn ready_by_hash(&self, hash: &Hash) -> Option<Arc<Transaction<Hash, Ex>>> {
		self.ready.by_hash(hash)
	}

	/// Makes sure that the transactions in the queues stay within provided limits.
	///
	/// Removes and returns worst transactions from the queues and all transactions that depend on them.
	/// Technically the worst transaction should be evaluated by computing the entire pending set.
	/// We use a simplified approach to remove the transaction that occupies the pool for the longest time.
	pub fn enforce_limits(&mut self, ready: &Limit, future: &Limit) -> Vec<Arc<Transaction<Hash, Ex>>> {
		let mut removed = vec![];

		while ready.is_exceeded(self.ready.len(), self.ready.bytes()) {
			// find the worst transaction
			let minimal = self.ready
				.fold(|minimal, current| {
					let transaction = &current.transaction;
					match minimal {
						None => Some(transaction.clone()),
						Some(ref tx) if tx.insertion_id > transaction.insertion_id => {
							Some(transaction.clone())
						},
						other => other,
					}
				});

			if let Some(minimal) = minimal {
				removed.append(&mut self.remove_subtree(&[minimal.transaction.hash.clone()]))
			} else {
				break;
			}
		}

		while future.is_exceeded(self.future.len(), self.future.bytes()) {
			// find the worst transaction
			let minimal = self.future
				.fold(|minimal, current| {
					match minimal {
						None => Some(current.clone()),
						Some(ref tx) if tx.imported_at > current.imported_at => {
							Some(current.clone())
						},
						other => other,
					}
				});

			if let Some(minimal) = minimal {
				removed.append(&mut self.remove_subtree(&[minimal.transaction.hash.clone()]))
			} else {
				break;
			}
		}

		removed
	}

	/// Removes all transactions represented by the hashes and all other transactions
	/// that depend on them.
	///
	/// Returns a list of actually removed transactions.
	/// NOTE some transactions might still be valid, but were just removed because
	/// they were part of a chain, you may attempt to re-import them later.
	/// NOTE If you want to remove ready transactions that were already used
	/// and you don't want them to be stored in the pool use `prune_tags` method.
	pub fn remove_subtree(&mut self, hashes: &[Hash]) -> Vec<Arc<Transaction<Hash, Ex>>> {
		let mut removed = self.ready.remove_subtree(hashes);
		removed.extend(self.future.remove(hashes));
		removed
	}

	/// Removes and returns all transactions from the future queue.
	pub fn clear_future(&mut self) -> Vec<Arc<Transaction<Hash, Ex>>> {
		self.future.clear()
	}

	/// Prunes transactions that provide given list of tags.
	///
	/// This will cause all transactions that provide these tags to be removed from the pool,
	/// but unlike `remove_subtree`, dependent transactions are not touched.
	/// Additional transactions from future queue might be promoted to ready if you satisfy tags
	/// that the pool didn't previously know about.
	pub fn prune_tags(&mut self, tags: impl IntoIterator<Item=Tag>) -> PruneStatus<Hash, Ex> {
		let mut to_import = vec![];
		let mut pruned = vec![];
		let recently_pruned = &mut self.recently_pruned[self.recently_pruned_index];
		self.recently_pruned_index = (self.recently_pruned_index + 1) % RECENTLY_PRUNED_TAGS;
		recently_pruned.clear();

		for tag in tags {
			// make sure to promote any future transactions that could be unlocked
			to_import.append(&mut self.future.satisfy_tags(std::iter::once(&tag)));
			// and actually prune transactions in ready queue
			pruned.append(&mut self.ready.prune_tags(tag.clone()));
			// store the tags for next submission
			recently_pruned.insert(tag);
		}

		let mut promoted = vec![];
		let mut failed = vec![];
		for tx in to_import {
			let hash = tx.transaction.hash.clone();
			match self.import_to_ready(tx) {
				Ok(res) => promoted.push(res),
				Err(e) => {
					warn!(target: "txpool", "[{:?}] Failed to promote during pruning: {:?}", hash, e);
					failed.push(hash)
				},
			}
		}

		PruneStatus {
			pruned,
			failed,
			promoted,
		}
	}

	/// Get pool status.
	pub fn status(&self) -> PoolStatus {
		PoolStatus {
			ready: self.ready.len(),
			ready_bytes: self.ready.bytes(),
			future: self.future.len(),
			future_bytes: self.future.bytes(),
		}
	}
}

/// Queue limits
#[derive(Debug, Clone)]
pub struct Limit {
	/// Maximal number of transactions in the queue.
	pub count: usize,
	/// Maximal size of encodings of all transactions in the queue.
	pub total_bytes: usize,
}

impl Limit {
	/// Returns true if any of the provided values exceeds the limit.
	pub fn is_exceeded(&self, count: usize, bytes: usize) -> bool {
		self.count < count || self.total_bytes < bytes
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	type Hash = u64;

	fn pool() -> BasePool<Hash, Vec<u8>> {
		BasePool::default()
	}

	const DEFAULT_TX: Transaction::<Hash, Vec<u8>> = Transaction {
		data: vec![],
		bytes: 1,
		hash: 1u64,
		priority: 5u64,
		valid_till: 64u64,
		requires: vec![],
		provides: vec![],
		propagate: true,
		source: Source::External,
	};

	#[test]
	fn should_import_transaction_to_ready() {
		// given
		let mut pool = pool();

		// when
		pool.import(Transaction {
			data: vec![1u8],
			provides: vec![vec![1]],
			.. DEFAULT_TX.clone()
		}).unwrap();

		// then
		assert_eq!(pool.ready().count(), 1);
		assert_eq!(pool.ready.len(), 1);
	}

	#[test]
	fn should_not_import_same_transaction_twice() {
		// given
		let mut pool = pool();

		// when
		pool.import(Transaction {
			data: vec![1u8],
			provides: vec![vec![1]],
			.. DEFAULT_TX.clone()
		}).unwrap();
		pool.import(Transaction {
			data: vec![1u8],
			provides: vec![vec![1]],
			.. DEFAULT_TX.clone()
		}).unwrap_err();

		// then
		assert_eq!(pool.ready().count(), 1);
		assert_eq!(pool.ready.len(), 1);
	}

	#[test]
	fn should_import_transaction_to_future_and_promote_it_later() {
		// given
		let mut pool = pool();

		// when
		pool.import(Transaction {
			data: vec![1u8],
			requires: vec![vec![0]],
			provides: vec![vec![1]],
			.. DEFAULT_TX.clone()
		}).unwrap();
		assert_eq!(pool.ready().count(), 0);
		assert_eq!(pool.ready.len(), 0);
		pool.import(Transaction {
			data: vec![2u8],
			hash: 2,
			provides: vec![vec![0]],
			.. DEFAULT_TX.clone()
		}).unwrap();

		// then
		assert_eq!(pool.ready().count(), 2);
		assert_eq!(pool.ready.len(), 2);
	}

	#[test]
	fn should_promote_a_subgraph() {
		// given
		let mut pool = pool();

		// when
		pool.import(Transaction {
			data: vec![1u8],
			requires: vec![vec![0]],
			provides: vec![vec![1]],
			.. DEFAULT_TX.clone()
		}).unwrap();
		pool.import(Transaction {
			data: vec![3u8],
			hash: 3,
			requires: vec![vec![2]],
			.. DEFAULT_TX.clone()
		}).unwrap();
		pool.import(Transaction {
			data: vec![2u8],
			hash: 2,
			requires: vec![vec![1]],
			provides: vec![vec![3], vec![2]],
			.. DEFAULT_TX.clone()
		}).unwrap();
		pool.import(Transaction {
			data: vec![4u8],
			hash: 4,
			priority: 1_000u64,
			requires: vec![vec![3], vec![4]],
			.. DEFAULT_TX.clone()
		}).unwrap();
		assert_eq!(pool.ready().count(), 0);
		assert_eq!(pool.ready.len(), 0);

		let res = pool.import(Transaction {
			data: vec![5u8],
			hash: 5,
			provides: vec![vec![0], vec![4]],
			.. DEFAULT_TX.clone()
		}).unwrap();

		// then
		let mut it = pool.ready().into_iter().map(|tx| tx.data[0]);

		assert_eq!(it.next(), Some(5));
		assert_eq!(it.next(), Some(1));
		assert_eq!(it.next(), Some(2));
		assert_eq!(it.next(), Some(4));
		assert_eq!(it.next(), Some(3));
		assert_eq!(it.next(), None);
		assert_eq!(res, Imported::Ready {
			hash: 5,
			promoted: vec![1, 2, 3, 4],
			failed: vec![],
			removed: vec![],
		});
	}

	#[test]
	fn should_handle_a_cycle() {
		// given
		let mut pool = pool();
		pool.import(Transaction {
			data: vec![1u8],
			requires: vec![vec![0]],
			provides: vec![vec![1]],
			.. DEFAULT_TX.clone()
		}).unwrap();
		pool.import(Transaction {
			data: vec![3u8],
			hash: 3,
			requires: vec![vec![1]],
			provides: vec![vec![2]],
			.. DEFAULT_TX.clone()
		}).unwrap();
		assert_eq!(pool.ready().count(), 0);
		assert_eq!(pool.ready.len(), 0);

		// when
		pool.import(Transaction {
			data: vec![2u8],
			hash: 2,
			requires: vec![vec![2]],
			provides: vec![vec![0]],
			.. DEFAULT_TX.clone()
		}).unwrap();

		// then
		{
			let mut it = pool.ready().into_iter().map(|tx| tx.data[0]);
			assert_eq!(it.next(), None);
		}
		// all transactions occupy the Future queue - it's fine
		assert_eq!(pool.future.len(), 3);

		// let's close the cycle with one additional transaction
		let res = pool.import(Transaction {
			data: vec![4u8],
			hash: 4,
			priority: 50u64,
			provides: vec![vec![0]],
			.. DEFAULT_TX.clone()
		}).unwrap();
		let mut it = pool.ready().into_iter().map(|tx| tx.data[0]);
		assert_eq!(it.next(), Some(4));
		assert_eq!(it.next(), Some(1));
		assert_eq!(it.next(), Some(3));
		assert_eq!(it.next(), None);
		assert_eq!(res, Imported::Ready {
			hash: 4,
			promoted: vec![1, 3],
			failed: vec![2],
			removed: vec![],
		});
		assert_eq!(pool.future.len(), 0);
	}

	#[test]
	fn should_handle_a_cycle_with_low_priority() {
		// given
		let mut pool = pool();
		pool.import(Transaction {
			data: vec![1u8],
			requires: vec![vec![0]],
			provides: vec![vec![1]],
			.. DEFAULT_TX.clone()
		}).unwrap();
		pool.import(Transaction {
			data: vec![3u8],
			hash: 3,
			requires: vec![vec![1]],
			provides: vec![vec![2]],
			.. DEFAULT_TX.clone()
		}).unwrap();
		assert_eq!(pool.ready().count(), 0);
		assert_eq!(pool.ready.len(), 0);

		// when
		pool.import(Transaction {
			data: vec![2u8],
			hash: 2,
			requires: vec![vec![2]],
			provides: vec![vec![0]],
			.. DEFAULT_TX.clone()
		}).unwrap();

		// then
		{
			let mut it = pool.ready().into_iter().map(|tx| tx.data[0]);
			assert_eq!(it.next(), None);
		}
		// all transactions occupy the Future queue - it's fine
		assert_eq!(pool.future.len(), 3);

		// let's close the cycle with one additional transaction
		let err = pool.import(Transaction {
			data: vec![4u8],
			hash: 4,
			priority: 1u64, // lower priority than Tx(2)
			provides: vec![vec![0]],
			.. DEFAULT_TX.clone()
		}).unwrap_err();
		let mut it = pool.ready().into_iter().map(|tx| tx.data[0]);
		assert_eq!(it.next(), None);
		assert_eq!(pool.ready.len(), 0);
		assert_eq!(pool.future.len(), 0);
		if let error::Error::CycleDetected = err {
		} else {
			assert!(false, "Invalid error kind: {:?}", err);
		}
	}

	#[test]
	fn can_track_heap_size() {
		let mut pool = pool();
		pool.import(Transaction {
			data: vec![5u8; 1024],
			hash: 5,
			provides: vec![vec![0], vec![4]],
			.. DEFAULT_TX.clone()
		}).expect("import 1 should be ok");
		pool.import(Transaction {
			data: vec![3u8; 1024],
			hash: 7,
			provides: vec![vec![2], vec![7]],
			.. DEFAULT_TX.clone()
		}).expect("import 2 should be ok");

		assert!(parity_util_mem::malloc_size(&pool) > 5000);
	}

	#[test]
	fn should_remove_invalid_transactions() {
		// given
		let mut pool = pool();
		pool.import(Transaction {
			data: vec![5u8],
			hash: 5,
			provides: vec![vec![0], vec![4]],
			.. DEFAULT_TX.clone()
		}).unwrap();
		pool.import(Transaction {
			data: vec![1u8],
			requires: vec![vec![0]],
			provides: vec![vec![1]],
			.. DEFAULT_TX.clone()
		}).unwrap();
		pool.import(Transaction {
			data: vec![3u8],
			hash: 3,
			requires: vec![vec![2]],
			.. DEFAULT_TX.clone()
		}).unwrap();
		pool.import(Transaction {
			data: vec![2u8],
			hash: 2,
			requires: vec![vec![1]],
			provides: vec![vec![3], vec![2]],
			.. DEFAULT_TX.clone()
		}).unwrap();
		pool.import(Transaction {
			data: vec![4u8],
			hash: 4,
			priority: 1_000u64,
			requires: vec![vec![3], vec![4]],
			.. DEFAULT_TX.clone()
		}).unwrap();
		// future
		pool.import(Transaction {
			data: vec![6u8],
			hash: 6,
			priority: 1_000u64,
			requires: vec![vec![11]],
			.. DEFAULT_TX.clone()
		}).unwrap();
		assert_eq!(pool.ready().count(), 5);
		assert_eq!(pool.future.len(), 1);

		// when
		pool.remove_subtree(&[6, 1]);

		// then
		assert_eq!(pool.ready().count(), 1);
		assert_eq!(pool.future.len(), 0);
	}

	#[test]
	fn should_prune_ready_transactions() {
		// given
		let mut pool = pool();
		// future (waiting for 0)
		pool.import(Transaction {
			data: vec![5u8],
			hash: 5,
			requires: vec![vec![0]],
			provides: vec![vec![100]],
			.. DEFAULT_TX.clone()
		}).unwrap();
		// ready
		pool.import(Transaction {
			data: vec![1u8],
			provides: vec![vec![1]],
			.. DEFAULT_TX.clone()
		}).unwrap();
		pool.import(Transaction {
			data: vec![2u8],
			hash: 2,
			requires: vec![vec![2]],
			provides: vec![vec![3]],
			.. DEFAULT_TX.clone()
		}).unwrap();
		pool.import(Transaction {
			data: vec![3u8],
			hash: 3,
			requires: vec![vec![1]],
			provides: vec![vec![2]],
			.. DEFAULT_TX.clone()
		}).unwrap();
		pool.import(Transaction {
			data: vec![4u8],
			hash: 4,
			priority: 1_000u64,
			requires: vec![vec![3], vec![2]],
			provides: vec![vec![4]],
			.. DEFAULT_TX.clone()
		}).unwrap();

		assert_eq!(pool.ready().count(), 4);
		assert_eq!(pool.future.len(), 1);

		// when
		let result = pool.prune_tags(vec![vec![0], vec![2]]);

		// then
		assert_eq!(result.pruned.len(), 2);
		assert_eq!(result.failed.len(), 0);
		assert_eq!(result.promoted[0], Imported::Ready {
			hash: 5,
			promoted: vec![],
			failed: vec![],
			removed: vec![],
		});
		assert_eq!(result.promoted.len(), 1);
		assert_eq!(pool.future.len(), 0);
		assert_eq!(pool.ready.len(), 3);
		assert_eq!(pool.ready().count(), 3);
	}

	#[test]
	fn transaction_debug() {
		assert_eq!(
			format!("{:?}", Transaction {
				data: vec![4u8],
				hash: 4,
				priority: 1_000u64,
				requires: vec![vec![3], vec![2]],
				provides: vec![vec![4]],
				.. DEFAULT_TX.clone()
			}),
			"Transaction { \
hash: 4, priority: 1000, valid_till: 64, bytes: 1, propagate: true, \
source: TransactionSource::External, requires: [03, 02], provides: [04], data: [4]}".to_owned()
		);
	}

	#[test]
	fn transaction_propagation() {
		assert_eq!(Transaction {
				data: vec![4u8],
				hash: 4,
				priority: 1_000u64,
				requires: vec![vec![3], vec![2]],
				provides: vec![vec![4]],
				.. DEFAULT_TX.clone()
		}.is_propagable(), true);

		assert_eq!(Transaction {
				data: vec![4u8],
				hash: 4,
				priority: 1_000u64,
				requires: vec![vec![3], vec![2]],
				provides: vec![vec![4]],
				propagate: false,
				.. DEFAULT_TX.clone()
		}.is_propagable(), false);
	}

	#[test]
	fn should_reject_future_transactions() {
		// given
		let mut pool = pool();

		// when
		pool.reject_future_transactions = true;

		// then
		let err = pool.import(Transaction {
			data: vec![5u8],
			hash: 5,
			requires: vec![vec![0]],
			.. DEFAULT_TX.clone()
		});

		if let Err(error::Error::RejectedFutureTransaction) = err {
		} else {
			assert!(false, "Invalid error kind: {:?}", err);
		}
	}

	#[test]
	fn should_clear_future_queue() {
		// given
		let mut pool = pool();

		// when
		pool.import(Transaction {
			data: vec![5u8],
			hash: 5,
			requires: vec![vec![0]],
			.. DEFAULT_TX.clone()
		}).unwrap();

		// then
		assert_eq!(pool.future.len(), 1);

		// and then when
		assert_eq!(pool.clear_future().len(), 1);

		// then
		assert_eq!(pool.future.len(), 0);
	}

	#[test]
	fn should_accept_future_transactions_when_explicitly_asked_to() {
		// given
		let mut pool = pool();
		pool.reject_future_transactions = true;

		// when
		let flag_value = pool.with_futures_enabled(|pool, flag| {
			pool.import(Transaction {
				data: vec![5u8],
				hash: 5,
				requires: vec![vec![0]],
				.. DEFAULT_TX.clone()
			}).unwrap();

			flag
		});

		// then
		assert_eq!(flag_value, true);
		assert_eq!(pool.reject_future_transactions, true);
		assert_eq!(pool.future.len(), 1);
	}
}
