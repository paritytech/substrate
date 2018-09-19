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
		removed: Vec<Arc<Transaction>>,
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
pub struct Transaction {
	/// Raw extrinsic representing that transaction.
	pub ex: UncheckedExtrinsic,
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
pub struct Pool<Hash: hash::Hash + Eq> {
	future: FutureTransactions<Hash>,
	ready: ReadyTransactions<Hash>,
	hasher: Box<Fn(&UncheckedExtrinsic) -> Hash>,
}

impl<Hash: hash::Hash + fmt::Debug + Eq> fmt::Debug for Pool<Hash> {
	fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
		fmt.debug_struct("Pool")
			.field("future", &self.future)
			.field("ready", &self.ready)
			.finish()
	}
}

impl<Hash: hash::Hash + Ord + Eq + Clone> Pool<Hash> {
	/// Creates new transaction pool with given hasher.
	pub fn new<F>(hasher: F) -> Self
	where
		F: Fn(&UncheckedExtrinsic) -> Hash + 'static,
	{
		Pool {
			future: Default::default(),
			ready: Default::default(),
			hasher: Box::new(hasher),
		}
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
		block_number: BlockNumber,
		tx: Transaction,
	) -> error::Result<Imported<Hash>> {
		let hash = (self.hasher)(&tx.ex);
		if self.future.contains(&hash) || self.ready.contains(&hash) {
			bail!(error::ErrorKind::AlreadyImported)
		}

		let tx = WaitingTransaction::new(tx, hash.clone(), self.ready.provided_tags());

		// Tags provided from Ready queue satisfy all requirements, so just add to Ready.
		if tx.is_ready() {
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
				let hash = tx.hash.clone();
				match self.ready.import(tx, block_number) {
					Ok(mut replaced) => {
						if !first {
							promoted.push(hash);
						}
						// The transactions were removed from the ready pool. We might attempt to re-import them.
						removed.append(&mut replaced);
					},
					// transaction failed to be imported.
					Err(e) => if first {
						return Err(e)
					} else {
						failed.push(hash);
					},
				}
				first = false;
			}

			Ok(Imported::Ready {
				hash,
				promoted,
				failed,
				removed,
			})
		} else {
			self.future.import(tx);
			Ok(Imported::Future { hash })
		}
	}

	/// Returns an iterator over ready transactions in the pool.
	pub fn ready<'a>(&'a self) -> impl Iterator<Item=Arc<Transaction>> + 'a {
		self.ready.get()
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	type Hash = u64;

	fn pool() -> Pool<Hash> {
		Pool::new(|ex| ex.0[0] as u64)
	}

	#[test]
	fn should_import_transaction_to_ready() {
		// given
		let mut pool = pool();

		// when
		pool.import(1, Transaction {
			ex: UncheckedExtrinsic(vec![1u8]),
			priority: 5u64,
			longevity: 64u64,
			requires: vec![],
			provides: vec![vec![1]],
		}).unwrap();

		// then
		assert_eq!(pool.ready().count(), 1);
	}

	#[test]
	fn should_not_import_same_transaction_twice() {
		// given
		let mut pool = pool();

		// when
		pool.import(1, Transaction {
			ex: UncheckedExtrinsic(vec![1u8]),
			priority: 5u64,
			longevity: 64u64,
			requires: vec![],
			provides: vec![vec![1]],
		}).unwrap();
		pool.import(1, Transaction {
			ex: UncheckedExtrinsic(vec![1u8]),
			priority: 5u64,
			longevity: 64u64,
			requires: vec![],
			provides: vec![vec![1]],
		}).unwrap_err();

		// then
		assert_eq!(pool.ready().count(), 1);
	}


	#[test]
	fn should_import_transaction_to_future_and_promote_it_later() {
		// given
		let mut pool = pool();

		// when
		pool.import(1, Transaction {
			ex: UncheckedExtrinsic(vec![1u8]),
			priority: 5u64,
			longevity: 64u64,
			requires: vec![vec![0]],
			provides: vec![vec![1]],
		}).unwrap();
		assert_eq!(pool.ready().count(), 0);
		pool.import(1, Transaction {
			ex: UncheckedExtrinsic(vec![2u8]),
			priority: 5u64,
			longevity: 64u64,
			requires: vec![],
			provides: vec![vec![0]],
		}).unwrap();

		// then
		assert_eq!(pool.ready().count(), 2);
	}

	#[test]
	fn should_promote_a_subgraph() {
		// given
		let mut pool = pool();

		// when
		pool.import(1, Transaction {
			ex: UncheckedExtrinsic(vec![1u8]),
			priority: 5u64,
			longevity: 64u64,
			requires: vec![vec![0]],
			provides: vec![vec![1]],
		}).unwrap();
		pool.import(1, Transaction {
			ex: UncheckedExtrinsic(vec![3u8]),
			priority: 5u64,
			longevity: 64u64,
			requires: vec![vec![2]],
			provides: vec![],
		}).unwrap();
		pool.import(1, Transaction {
			ex: UncheckedExtrinsic(vec![2u8]),
			priority: 5u64,
			longevity: 64u64,
			requires: vec![vec![1]],
			provides: vec![vec![3], vec![2]],
		}).unwrap();
		pool.import(1, Transaction {
			ex: UncheckedExtrinsic(vec![4u8]),
			priority: 1_000u64,
			longevity: 64u64,
			requires: vec![vec![3], vec![4]],
			provides: vec![],
		}).unwrap();
		assert_eq!(pool.ready().count(), 0);

		let res = pool.import(1, Transaction {
			ex: UncheckedExtrinsic(vec![5u8]),
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
			priority: 5u64,
			longevity: 64u64,
			requires: vec![vec![0]],
			provides: vec![vec![1]],
		}).unwrap();
		pool.import(1, Transaction {
			ex: UncheckedExtrinsic(vec![3u8]),
			priority: 5u64,
			longevity: 64u64,
			requires: vec![vec![1]],
			provides: vec![vec![2]],
		}).unwrap();
		assert_eq!(pool.ready().count(), 0);

		// when
		pool.import(1, Transaction {
			ex: UncheckedExtrinsic(vec![2u8]),
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
}
