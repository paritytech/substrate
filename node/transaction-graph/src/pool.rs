// Copyright 2018 Parity Technologies (UK) Ltd.
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
	fmt,
	hash,
	sync::Arc,
};

use primitives::UncheckedExtrinsic;
use sr_primitives::transaction_validity::{
	TransactionTag as Tag,
	TransactionLongevity as Longevity,
	TransactionPriority as Priority,
};

use error;
use future::{FutureTransactions, WaitingTransaction};
use ready::ReadyTransactions;

pub type BlockNumber = u64;

/// Successful import result.
#[derive(Debug, PartialEq, Eq)]
pub enum Imported<Hash> {
	/// Transaction was successfuly imported to Ready queue.
	Ready {
		/// Hash of transaction that was successfuly imported.
		hash: Hash,
		/// Transactions that got promoted from the Future queue.
		promoted: Vec<Hash>,
		/// Transactions that failed to be promoted from the Future queue and are now discarded.
		failed: Vec<Hash>,
		/// Transactions removed from the Ready pool (replaced).
		removed: Vec<Arc<Transaction<Hash>>>,
	},
	/// Transaction was successfuly imported to Future queue.
	Future {
		/// Hash of transaction that was successfuly imported.
		hash: Hash,
	}
}

/// Immutable transaction
#[cfg_attr(test, derive(Clone))]
#[derive(Debug, PartialEq, Eq)]
pub struct Transaction<Hash> {
	/// Raw extrinsic representing that transaction.
	pub ex: UncheckedExtrinsic,
	/// Transaction hash (unique)
	pub hash: Hash,
	/// Transaction priority (higher = better)
	pub priority: Priority,
	/// How many blocks the transaction is valid for.
	pub longevity: Longevity,
	/// Tags required by the transaction.
	pub requires: Vec<Tag>,
	/// Tags that this transaction provides.
	pub provides: Vec<Tag>,
}

/// Transaction pool.
///
/// Builds a dependency graph for all transactions in the pool and returns
/// the ones that are currently ready to be executed.
#[derive(Default, Debug)]
pub struct Pool<Hash: hash::Hash + Eq> {
	future: FutureTransactions<Hash>,
	ready: ReadyTransactions<Hash>,
}

impl<Hash: hash::Hash + fmt::Debug + Ord + Eq + Clone> Pool<Hash> {
	/// Imports transaction to the pool.
	///
	/// The pool consists of two parts: Future and Ready.
	/// The former contains transactions that require some tags that are not yet provided by
	/// other transactions in the pool.
	/// The latter contains transactions that have all the requirements satisfied and are
	/// ready to be included in the block.
	pub fn import(
		&mut self,
		block_number: BlockNumber,
		tx: Transaction<Hash>,
	) -> error::Result<Imported<Hash>> {
		let hash = tx.hash.clone();
		if self.future.contains(&hash) || self.ready.contains(&hash) {
			bail!(error::ErrorKind::AlreadyImported)
		}

		let tx = WaitingTransaction::new(tx, self.ready.provided_tags());
		trace!(target: "txpool", "[{:?}] {:?}", hash, tx);
		debug!(target: "txpool", "[{:?}] Importing to {}", hash, if tx.is_ready() { "ready" } else { "future" });

		// If all tags are not satisfied import to future.
		if !tx.is_ready() {
			self.future.import(tx);
			return Ok(Imported::Future { hash });
		}

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
			match self.ready.import(tx, block_number) {
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
	pub fn ready<'a>(&'a self) -> impl Iterator<Item=Arc<Transaction<Hash>>> + 'a {
		self.ready.get()
	}

	/// Removes all transactions represented by the hashes and all other transactions
	/// that depend on them.
	///
	/// Returns a list of actually removed transactions.
	/// NOTE some transactions might still be valid, but were just removed because
	/// they were part of a chain, you may attempt to re-import them later.
	/// NOTE If you want to just mark ready transactions that were already used
	/// and you no longer need to store them use `mark_used` method.
	pub fn remove_invalid<'a>(&mut self, hashes: &[Hash]) -> Vec<Arc<Transaction<Hash>>> where
		Hash: 'a,
	{
		let mut removed = self.ready.remove_invalid(hashes);
		removed.extend(self.future.remove(hashes).into_iter().map(Arc::new));
		removed
	}

	/// Satisfies given list of tags.
	///
	/// This will cause all transactions that provide these tags to be removed from the pool,
	/// but unlike `remove_invalid`, dependent transactions are not touched.
	/// Additional transactions from future queue might be promoted to ready if you satisfy tags
	/// that the pool didn't previously know about.
	pub fn satisfy_tags(&mut self, _tags: impl Iterator<Item=Tag>) {
		unimplemented!()
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	type Hash = u64;

	fn pool() -> Pool<Hash> {
		Pool::default()
	}

	#[test]
	fn should_import_transaction_to_ready() {
		// given
		let mut pool = pool();

		// when
		pool.import(1, Transaction {
			ex: UncheckedExtrinsic(vec![1u8]),
			hash: 1u64,
			priority: 5u64,
			longevity: 64u64,
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
		pool.import(1, Transaction {
			ex: UncheckedExtrinsic(vec![1u8]),
			hash: 1,
			priority: 5u64,
			longevity: 64u64,
			requires: vec![],
			provides: vec![vec![1]],
		}).unwrap();
		pool.import(1, Transaction {
			ex: UncheckedExtrinsic(vec![1u8]),
			hash: 1,
			priority: 5u64,
			longevity: 64u64,
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
		pool.import(1, Transaction {
			ex: UncheckedExtrinsic(vec![1u8]),
			hash: 1,
			priority: 5u64,
			longevity: 64u64,
			requires: vec![vec![0]],
			provides: vec![vec![1]],
		}).unwrap();
		assert_eq!(pool.ready().count(), 0);
		assert_eq!(pool.ready.len(), 0);
		pool.import(1, Transaction {
			ex: UncheckedExtrinsic(vec![2u8]),
			hash: 2,
			priority: 5u64,
			longevity: 64u64,
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
		pool.import(1, Transaction {
			ex: UncheckedExtrinsic(vec![1u8]),
			hash: 1,
			priority: 5u64,
			longevity: 64u64,
			requires: vec![vec![0]],
			provides: vec![vec![1]],
		}).unwrap();
		pool.import(1, Transaction {
			ex: UncheckedExtrinsic(vec![3u8]),
			hash: 3,
			priority: 5u64,
			longevity: 64u64,
			requires: vec![vec![2]],
			provides: vec![],
		}).unwrap();
		pool.import(1, Transaction {
			ex: UncheckedExtrinsic(vec![2u8]),
			hash: 2,
			priority: 5u64,
			longevity: 64u64,
			requires: vec![vec![1]],
			provides: vec![vec![3], vec![2]],
		}).unwrap();
		pool.import(1, Transaction {
			ex: UncheckedExtrinsic(vec![4u8]),
			hash: 4,
			priority: 1_000u64,
			longevity: 64u64,
			requires: vec![vec![3], vec![4]],
			provides: vec![],
		}).unwrap();
		assert_eq!(pool.ready().count(), 0);
		assert_eq!(pool.ready.len(), 0);

		let res = pool.import(1, Transaction {
			ex: UncheckedExtrinsic(vec![5u8]),
			hash: 5,
			priority: 5u64,
			longevity: 64u64,
			requires: vec![],
			provides: vec![vec![0], vec![4]],
		}).unwrap();

		// then
		let mut it = pool.ready().into_iter().map(|tx| tx.ex.0[0]);

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
		pool.import(1, Transaction {
			ex: UncheckedExtrinsic(vec![1u8]),
			hash: 1,
			priority: 5u64,
			longevity: 64u64,
			requires: vec![vec![0]],
			provides: vec![vec![1]],
		}).unwrap();
		pool.import(1, Transaction {
			ex: UncheckedExtrinsic(vec![3u8]),
			hash: 3,
			priority: 5u64,
			longevity: 64u64,
			requires: vec![vec![1]],
			provides: vec![vec![2]],
		}).unwrap();
		assert_eq!(pool.ready().count(), 0);
		assert_eq!(pool.ready.len(), 0);

		// when
		pool.import(1, Transaction {
			ex: UncheckedExtrinsic(vec![2u8]),
			hash: 2,
			priority: 5u64,
			longevity: 64u64,
			requires: vec![vec![2]],
			provides: vec![vec![0]],
		}).unwrap();

		// then
		{
			let mut it = pool.ready().into_iter().map(|tx| tx.ex.0[0]);
			assert_eq!(it.next(), None);
		}
		// all transactions occupy the Future queue - it's fine
		assert_eq!(pool.future.len(), 3);

		// let's close the cycle with one additional transaction
		let res = pool.import(1, Transaction {
			ex: UncheckedExtrinsic(vec![4u8]),
			hash: 4,
			priority: 50u64,
			longevity: 64u64,
			requires: vec![],
			provides: vec![vec![0]],
		}).unwrap();
		let mut it = pool.ready().into_iter().map(|tx| tx.ex.0[0]);
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
		pool.import(1, Transaction {
			ex: UncheckedExtrinsic(vec![1u8]),
			hash: 1,
			priority: 5u64,
			longevity: 64u64,
			requires: vec![vec![0]],
			provides: vec![vec![1]],
		}).unwrap();
		pool.import(1, Transaction {
			ex: UncheckedExtrinsic(vec![3u8]),
			hash: 3,
			priority: 5u64,
			longevity: 64u64,
			requires: vec![vec![1]],
			provides: vec![vec![2]],
		}).unwrap();
		assert_eq!(pool.ready().count(), 0);
		assert_eq!(pool.ready.len(), 0);

		// when
		pool.import(1, Transaction {
			ex: UncheckedExtrinsic(vec![2u8]),
			hash: 2,
			priority: 5u64,
			longevity: 64u64,
			requires: vec![vec![2]],
			provides: vec![vec![0]],
		}).unwrap();

		// then
		{
			let mut it = pool.ready().into_iter().map(|tx| tx.ex.0[0]);
			assert_eq!(it.next(), None);
		}
		// all transactions occupy the Future queue - it's fine
		assert_eq!(pool.future.len(), 3);

		// let's close the cycle with one additional transaction
		let err = pool.import(1, Transaction {
			ex: UncheckedExtrinsic(vec![4u8]),
			hash: 4,
			priority: 1u64, // lower priority than Tx(2)
			longevity: 64u64,
			requires: vec![],
			provides: vec![vec![0]],
		}).unwrap_err();
		let mut it = pool.ready().into_iter().map(|tx| tx.ex.0[0]);
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
		pool.import(1, Transaction {
			ex: UncheckedExtrinsic(vec![5u8]),
			hash: 5,
			priority: 5u64,
			longevity: 64u64,
			requires: vec![],
			provides: vec![vec![0], vec![4]],
		}).unwrap();
		pool.import(1, Transaction {
			ex: UncheckedExtrinsic(vec![1u8]),
			hash: 1,
			priority: 5u64,
			longevity: 64u64,
			requires: vec![vec![0]],
			provides: vec![vec![1]],
		}).unwrap();
		pool.import(1, Transaction {
			ex: UncheckedExtrinsic(vec![3u8]),
			hash: 3,
			priority: 5u64,
			longevity: 64u64,
			requires: vec![vec![2]],
			provides: vec![],
		}).unwrap();
		pool.import(1, Transaction {
			ex: UncheckedExtrinsic(vec![2u8]),
			hash: 2,
			priority: 5u64,
			longevity: 64u64,
			requires: vec![vec![1]],
			provides: vec![vec![3], vec![2]],
		}).unwrap();
		pool.import(1, Transaction {
			ex: UncheckedExtrinsic(vec![4u8]),
			hash: 4,
			priority: 1_000u64,
			longevity: 64u64,
			requires: vec![vec![3], vec![4]],
			provides: vec![],
		}).unwrap();
		// future
		pool.import(1, Transaction {
			ex: UncheckedExtrinsic(vec![6u8]),
			hash: 6,
			priority: 1_000u64,
			longevity: 64u64,
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
}
