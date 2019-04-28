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

//! A basic version of the dependency graph.
//!
//! For a more full-featured pool, have a look at the `pool` module.

use std::{
	collections::HashSet,
	fmt,
	hash,
	sync::Arc,
};

use error_chain::bail;
use log::{trace, debug, warn};
use serde::Serialize;
use substrate_primitives::hexdisplay::HexDisplay;
use sr_primitives::traits::Member;
use sr_primitives::transaction_validity::{
	TransactionTag as Tag,
	TransactionLongevity as Longevity,
	TransactionPriority as Priority,
};

use crate::error;
use crate::future::{FutureTransactions, WaitingTransaction};
use crate::ready::ReadyTransactions;

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
#[derive(PartialEq, Eq)]
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
}

impl<Hash, Extrinsic> fmt::Debug for Transaction<Hash, Extrinsic> where
	Hash: fmt::Debug,
	Extrinsic: fmt::Debug,
{
	fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
		fn print_tags(fmt: &mut fmt::Formatter, tags: &[Tag]) -> fmt::Result {
			let mut it = tags.iter();
			if let Some(t) = it.next() {
				write!(fmt, "{}", HexDisplay::from(t))?;
			}
			for t in it {
				write!(fmt, ",{}", HexDisplay::from(t))?;
			}
			Ok(())
		}

		write!(fmt, "Transaction {{ ")?;
		write!(fmt, "hash: {:?}, ", &self.hash)?;
		write!(fmt, "priority: {:?}, ", &self.priority)?;
		write!(fmt, "valid_till: {:?}, ", &self.valid_till)?;
		write!(fmt, "bytes: {:?}, ", &self.bytes)?;
		write!(fmt, "requires: [")?;
		print_tags(fmt, &self.requires)?;
		write!(fmt, "], provides: [")?;
		print_tags(fmt, &self.provides)?;
		write!(fmt, "], ")?;
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
pub struct BasePool<Hash: hash::Hash + Eq, Ex> {
	future: FutureTransactions<Hash, Ex>,
	ready: ReadyTransactions<Hash, Ex>,
	/// Store recently pruned tags (for last two invocations).
	///
	/// This is used to make sure we don't accidentally put
	/// transactions to future in case they were just stuck in verification.
	recently_pruned: [HashSet<Tag>; RECENTLY_PRUNED_TAGS],
	recently_pruned_index: usize,
}

impl<Hash: hash::Hash + Eq, Ex> Default for BasePool<Hash, Ex> {
	fn default() -> Self {
		BasePool {
			future: Default::default(),
			ready: Default::default(),
			recently_pruned: Default::default(),
			recently_pruned_index: 0,
		}
	}
}

impl<Hash: hash::Hash + Member + Serialize, Ex: ::std::fmt::Debug> BasePool<Hash, Ex> {
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
		if self.future.contains(&tx.hash) || self.ready.contains(&tx.hash) {
			bail!(error::ErrorKind::AlreadyImported(Box::new(tx.hash.clone())))
		}

		let tx = WaitingTransaction::new(
			tx,
			self.ready.provided_tags(),
			&self.recently_pruned,
		);
		trace!(target: "txpool", "[{:?}] {:?}", tx.transaction.hash, tx);
		debug!(target: "txpool", "[{:?}] Importing to {}", tx.transaction.hash, if tx.is_ready() { "ready" } else { "future" });

		// If all tags are not satisfied import to future.
		if !tx.is_ready() {
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

		loop {
			// take first transaction from the list
			let tx = match to_import.pop() {
				Some(tx) => tx,
				None => break,
			};

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
			self.ready.remove_invalid(&promoted);

			debug!(target: "txpool", "[{:?}] Cycle detected, bailing.", hash);
			bail!(error::ErrorKind::CycleDetected)
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
	pub fn by_hash(&self, hashes: &[Hash]) -> Vec<Option<Arc<Transaction<Hash, Ex>>>> {
		let ready = self.ready.by_hash(hashes);
		let future = self.future.by_hash(hashes);

		ready
			.into_iter()
			.zip(future)
			.map(|(a, b)| a.or(b))
			.collect()
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
				removed.append(&mut self.remove_invalid(&[minimal.transaction.hash.clone()]))
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
				removed.append(&mut self.remove_invalid(&[minimal.transaction.hash.clone()]))
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
	pub fn remove_invalid(&mut self, hashes: &[Hash]) -> Vec<Arc<Transaction<Hash, Ex>>> {
		let mut removed = self.ready.remove_invalid(hashes);
		removed.extend(self.future.remove(hashes));
		removed
	}

	/// Prunes transactions that provide given list of tags.
	///
	/// This will cause all transactions that provide these tags to be removed from the pool,
	/// but unlike `remove_invalid`, dependent transactions are not touched.
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
			to_import.append(&mut self.future.satisfy_tags(::std::iter::once(&tag)));
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
	pub fn status(&self) -> Status {
		Status {
			ready: self.ready.len(),
			ready_bytes: self.ready.bytes(),
			future: self.future.len(),
			future_bytes: self.future.bytes(),
		}
	}
}

/// Pool status
#[derive(Debug)]
pub struct Status {
	/// Number of transactions in the ready queue.
	pub ready: usize,
	/// Sum of bytes of ready transaction encodings.
	pub ready_bytes: usize,
	/// Number of transactions in the future queue.
	pub future: usize,
	/// Sum of bytes of ready transaction encodings.
	pub future_bytes: usize,
}

impl Status {
	/// Returns true if the are no transactions in the pool.
	pub fn is_empty(&self) -> bool {
		self.ready == 0 && self.future == 0
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

	#[test]
	fn should_import_transaction_to_ready() {
		// given
		let mut pool = pool();

		// when
		pool.import(Transaction {
			data: vec![1u8],
			bytes: 1,
			hash: 1u64,
			priority: 5u64,
			valid_till: 64u64,
			requires: vec![],
			provides: vec![vec![1]],
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
			bytes: 1,
			hash: 1,
			priority: 5u64,
			valid_till: 64u64,
			requires: vec![],
			provides: vec![vec![1]],
		}).unwrap();
		pool.import(Transaction {
			data: vec![1u8],
			bytes: 1,
			hash: 1,
			priority: 5u64,
			valid_till: 64u64,
			requires: vec![],
			provides: vec![vec![1]],
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
			bytes: 1,
			hash: 1,
			priority: 5u64,
			valid_till: 64u64,
			requires: vec![vec![0]],
			provides: vec![vec![1]],
		}).unwrap();
		assert_eq!(pool.ready().count(), 0);
		assert_eq!(pool.ready.len(), 0);
		pool.import(Transaction {
			data: vec![2u8],
			bytes: 1,
			hash: 2,
			priority: 5u64,
			valid_till: 64u64,
			requires: vec![],
			provides: vec![vec![0]],
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
			bytes: 1,
			hash: 1,
			priority: 5u64,
			valid_till: 64u64,
			requires: vec![vec![0]],
			provides: vec![vec![1]],
		}).unwrap();
		pool.import(Transaction {
			data: vec![3u8],
			bytes: 1,
			hash: 3,
			priority: 5u64,
			valid_till: 64u64,
			requires: vec![vec![2]],
			provides: vec![],
		}).unwrap();
		pool.import(Transaction {
			data: vec![2u8],
			bytes: 1,
			hash: 2,
			priority: 5u64,
			valid_till: 64u64,
			requires: vec![vec![1]],
			provides: vec![vec![3], vec![2]],
		}).unwrap();
		pool.import(Transaction {
			data: vec![4u8],
			bytes: 1,
			hash: 4,
			priority: 1_000u64,
			valid_till: 64u64,
			requires: vec![vec![3], vec![4]],
			provides: vec![],
		}).unwrap();
		assert_eq!(pool.ready().count(), 0);
		assert_eq!(pool.ready.len(), 0);

		let res = pool.import(Transaction {
			data: vec![5u8],
			bytes: 1,
			hash: 5,
			priority: 5u64,
			valid_till: 64u64,
			requires: vec![],
			provides: vec![vec![0], vec![4]],
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
			bytes: 1,
			hash: 1,
			priority: 5u64,
			valid_till: 64u64,
			requires: vec![vec![0]],
			provides: vec![vec![1]],
		}).unwrap();
		pool.import(Transaction {
			data: vec![3u8],
			bytes: 1,
			hash: 3,
			priority: 5u64,
			valid_till: 64u64,
			requires: vec![vec![1]],
			provides: vec![vec![2]],
		}).unwrap();
		assert_eq!(pool.ready().count(), 0);
		assert_eq!(pool.ready.len(), 0);

		// when
		pool.import(Transaction {
			data: vec![2u8],
			bytes: 1,
			hash: 2,
			priority: 5u64,
			valid_till: 64u64,
			requires: vec![vec![2]],
			provides: vec![vec![0]],
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
			bytes: 1,
			hash: 4,
			priority: 50u64,
			valid_till: 64u64,
			requires: vec![],
			provides: vec![vec![0]],
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
			bytes: 1,
			hash: 1,
			priority: 5u64,
			valid_till: 64u64,
			requires: vec![vec![0]],
			provides: vec![vec![1]],
		}).unwrap();
		pool.import(Transaction {
			data: vec![3u8],
			bytes: 1,
			hash: 3,
			priority: 5u64,
			valid_till: 64u64,
			requires: vec![vec![1]],
			provides: vec![vec![2]],
		}).unwrap();
		assert_eq!(pool.ready().count(), 0);
		assert_eq!(pool.ready.len(), 0);

		// when
		pool.import(Transaction {
			data: vec![2u8],
			bytes: 1,
			hash: 2,
			priority: 5u64,
			valid_till: 64u64,
			requires: vec![vec![2]],
			provides: vec![vec![0]],
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
			bytes: 1,
			hash: 4,
			priority: 1u64, // lower priority than Tx(2)
			valid_till: 64u64,
			requires: vec![],
			provides: vec![vec![0]],
		}).unwrap_err();
		let mut it = pool.ready().into_iter().map(|tx| tx.data[0]);
		assert_eq!(it.next(), None);
		assert_eq!(pool.ready.len(), 0);
		assert_eq!(pool.future.len(), 0);
		if let error::ErrorKind::CycleDetected = *err.kind() {
		} else {
			assert!(false, "Invalid error kind: {:?}", err.kind());
		}
	}

	#[test]
	fn should_remove_invalid_transactions() {
		// given
		let mut pool = pool();
		pool.import(Transaction {
			data: vec![5u8],
			bytes: 1,
			hash: 5,
			priority: 5u64,
			valid_till: 64u64,
			requires: vec![],
			provides: vec![vec![0], vec![4]],
		}).unwrap();
		pool.import(Transaction {
			data: vec![1u8],
			bytes: 1,
			hash: 1,
			priority: 5u64,
			valid_till: 64u64,
			requires: vec![vec![0]],
			provides: vec![vec![1]],
		}).unwrap();
		pool.import(Transaction {
			data: vec![3u8],
			bytes: 1,
			hash: 3,
			priority: 5u64,
			valid_till: 64u64,
			requires: vec![vec![2]],
			provides: vec![],
		}).unwrap();
		pool.import(Transaction {
			data: vec![2u8],
			bytes: 1,
			hash: 2,
			priority: 5u64,
			valid_till: 64u64,
			requires: vec![vec![1]],
			provides: vec![vec![3], vec![2]],
		}).unwrap();
		pool.import(Transaction {
			data: vec![4u8],
			bytes: 1,
			hash: 4,
			priority: 1_000u64,
			valid_till: 64u64,
			requires: vec![vec![3], vec![4]],
			provides: vec![],
		}).unwrap();
		// future
		pool.import(Transaction {
			data: vec![6u8],
			bytes: 1,
			hash: 6,
			priority: 1_000u64,
			valid_till: 64u64,
			requires: vec![vec![11]],
			provides: vec![],
		}).unwrap();
		assert_eq!(pool.ready().count(), 5);
		assert_eq!(pool.future.len(), 1);

		// when
		pool.remove_invalid(&[6, 1]);

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
			bytes: 1,
			hash: 5,
			priority: 5u64,
			valid_till: 64u64,
			requires: vec![vec![0]],
			provides: vec![vec![100]],
		}).unwrap();
		// ready
		pool.import(Transaction {
			data: vec![1u8],
			bytes: 1,
			hash: 1,
			priority: 5u64,
			valid_till: 64u64,
			requires: vec![],
			provides: vec![vec![1]],
		}).unwrap();
		pool.import(Transaction {
			data: vec![2u8],
			bytes: 1,
			hash: 2,
			priority: 5u64,
			valid_till: 64u64,
			requires: vec![vec![2]],
			provides: vec![vec![3]],
		}).unwrap();
		pool.import(Transaction {
			data: vec![3u8],
			bytes: 1,
			hash: 3,
			priority: 5u64,
			valid_till: 64u64,
			requires: vec![vec![1]],
			provides: vec![vec![2]],
		}).unwrap();
		pool.import(Transaction {
			data: vec![4u8],
			bytes: 1,
			hash: 4,
			priority: 1_000u64,
			valid_till: 64u64,
			requires: vec![vec![3], vec![2]],
			provides: vec![vec![4]],
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
				bytes: 1,
				hash: 4,
				priority: 1_000u64,
				valid_till: 64u64,
				requires: vec![vec![3], vec![2]],
				provides: vec![vec![4]],
			}),
			r#"Transaction { hash: 4, priority: 1000, valid_till: 64, bytes: 1, requires: [03,02], provides: [04], data: [4]}"#.to_owned()
		);
	}
}
