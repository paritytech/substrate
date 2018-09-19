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
	collections::{HashMap, HashSet, BTreeSet},
	cmp,
	hash,
	sync::Arc,
};

use sr_primitives::transaction_validity::{
	TransactionTag as Tag,
};

use error;
use future::WaitingTransaction;
use pool::{BlockNumber, Transaction};

#[derive(Debug, Clone)]
pub struct TransactionRef<Hash> {
	pub transaction: Arc<Transaction>,
	pub hash: Hash,
	pub valid_till: BlockNumber,
	pub insertion_id: u64,
}

impl<Hash> Ord for TransactionRef<Hash> {
	fn cmp(&self, other: &Self) -> cmp::Ordering {
		self.transaction.priority.cmp(&other.transaction.priority)
			.then(other.valid_till.cmp(&self.valid_till))
			.then(other.insertion_id.cmp(&self.insertion_id))
	}
}

impl<Hash> PartialOrd for TransactionRef<Hash> {
	fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
		Some(self.cmp(other))
	}
}

impl<Hash> PartialEq for TransactionRef<Hash> {
	fn eq(&self, other: &Self) -> bool {
		self.cmp(other) == cmp::Ordering::Equal
	}
}
impl<Hash> Eq for TransactionRef<Hash> {}

#[derive(Debug)]
struct ReadyTx<Hash> {
	pub transaction: TransactionRef<Hash>,
	pub unlocks: Vec<Hash>,
}

const HASH_READY: &str = "Every hash is in ready map; qed";

#[derive(Debug)]
pub struct ReadyTransactions<Hash: hash::Hash + Eq> {
	/// Insertion id
	insertion_id: u64,
	/// tags that are provided by Ready transactions
	provided_tags: HashMap<Tag, Hash>,
	/// Transactions that are ready (i.e. don't have any requirements external to the pool)
	ready: HashMap<Hash, ReadyTx<Hash>>,
	// ^^ TODO [ToDr] Consider wrapping this into `Arc<RwLock<>>` and allow multiple concurrent iterators
	/// Best transactions that are ready to be included to the block without any other previous transaction.
	best: BTreeSet<TransactionRef<Hash>>,
}

impl<Hash: hash::Hash + Eq> Default for ReadyTransactions<Hash> {
	fn default() -> Self {
		ReadyTransactions {
			insertion_id: Default::default(),
			provided_tags: Default::default(),
			ready: Default::default(),
			best: Default::default(),
		}
	}
}

impl<Hash: hash::Hash + Eq + Clone> ReadyTransactions<Hash> {
	/// Borrows a map of tags that are provided by transactions in this queue.
	pub fn provided_tags(&self) -> &HashMap<Tag, Hash> {
		&self.provided_tags
	}

	/// Returns an iterator of ready transactions.
	///
	/// Transactions are returned in order:
	/// 1. First by the dependencies:
	///	- never return transaction that requires a tag, which was not provided by one of the previously returned transactions
	/// 2. Then by priority:
	/// - If there are two transactions with all requirements satisfied the one with higher priority goes first.
	/// 3. Then by the ttl that's left
	/// - transactions that are valid for a shorter time go first
	/// 4. Lastly we sort by the time in the queue
	/// - transactions that are longer in the queue go first
	pub fn get<'a>(&'a self) -> impl Iterator<Item=Arc<Transaction>> + 'a {
		BestIterator {
			all: &self.ready,
			best: self.best.clone(),
			awaiting: Default::default(),
		}
	}

	/// Imports transactions to the pool of ready transactions.
	///
	/// The transaction needs to have all tags satisfied (be ready) by transactions
	/// that are in this queue.
	pub fn import(
		&mut self,
		tx: WaitingTransaction<Hash>,
		block_number: BlockNumber,
	) -> error::Result<Vec<Arc<Transaction>>> {
		assert!(tx.is_ready(), "Only ready transactions can be imported.");
		assert!(!self.ready.contains_key(&tx.hash), "Transaction is already imported.");

		self.insertion_id += 1;
		let insertion_id = self.insertion_id;
		let hash = tx.hash;
		let tx = tx.transaction;

		let replaced = self.replace_previous(&tx)?;

		let mut goes_to_best = true;
		// Add links to transactions that unlock the current one
		for tag in &tx.requires {
			// Check if the transaction that satisfies the tag is still in the queue.
			if let Some(other) = self.provided_tags.get(tag) {
				let mut tx = self.ready.get_mut(other).expect(HASH_READY);
				tx.unlocks.push(hash.clone());
				// this transaction depends on some other, so it doesn't go to best directly.
				goes_to_best = false;
			}
	 	}

		// update provided_tags
		for tag in tx.provides.clone() {
			self.provided_tags.insert(tag, hash.clone());
		}

		let transaction = TransactionRef {
			insertion_id,
			hash: hash.clone(),
			valid_till: block_number + tx.longevity,
			transaction: Arc::new(tx),
		};

		// insert to best if it doesn't require any other transaction to be included before it
		if goes_to_best {
			self.best.insert(transaction.clone());
		}

		// insert to Ready
		self.ready.insert(hash, ReadyTx {
			transaction,
			unlocks: vec![],
		});

		Ok(replaced)
	}

	/// Returns true if given hash is part of the queue.
	pub fn contains(&self, hash: &Hash) -> bool {
		self.ready.contains_key(hash)
	}

	/// Checks if the transaction is providing the same tags as other transactions.
	///
	/// In case that's true it determines if the priority of transactions that
	/// we are about to replace is lower than the priority of the replacement transaction.
	/// We remove/replace old transactions in case they have lower priority.
	///
	/// In case replacement is succesful returns a list of removed transactions.
	fn replace_previous(&mut self, tx: &Transaction) -> error::Result<Vec<Arc<Transaction>>> {
		let mut to_remove = {
			// check if we are replacing a transaction
			let replace_hashes = tx.provides
				.iter()
				.filter_map(|tag| self.provided_tags.get(tag))
				.collect::<HashSet<_>>();

			// early exit if we are not replacing anything.
			if replace_hashes.is_empty() {
				return Ok(vec![]);
			}

			// now check if collective priority is lower than the replacement transaction.
			let old_priority = replace_hashes
				.iter()
				.filter_map(|hash| self.ready.get(hash))
				.fold(0u64, |total, tx| total.saturating_add(tx.transaction.transaction.priority));

			// bail - the transaction has too low priority to replace the old ones
			if old_priority >= tx.priority {
				bail!(error::ErrorKind::TooLowPriority(old_priority, tx.priority))
			}

			replace_hashes.into_iter().cloned().collect::<Vec<_>>()
		};

		let new_provides = tx.provides.iter().cloned().collect::<HashSet<_>>();
		let mut removed = vec![];
		loop {
			let hash = match to_remove.pop() {
				Some(hash) => hash,
				None => return Ok(removed),
			};

			let tx = self.ready.remove(&hash).expect(HASH_READY);
			// check if this transaction provides stuff that is not provided by the new one.
			let (mut unlocks, tx) = (tx.unlocks, tx.transaction.transaction);
			{
				let invalidated = tx.provides
					.iter()
					.filter(|tag| !new_provides.contains(&**tag));

				for tag in invalidated {
					// remove the tag since it's no longer provided by any transaction
					self.provided_tags.remove(tag);
					// add more transactions to remove
					to_remove.append(&mut unlocks);
				}
			}

			removed.push(tx);
		}
	}


}

pub struct BestIterator<'a, Hash: 'a> {
	all: &'a HashMap<Hash, ReadyTx<Hash>>,
	awaiting: HashMap<Hash, (usize, TransactionRef<Hash>)>,
	best: BTreeSet<TransactionRef<Hash>>,
}

impl<'a, Hash: 'a + hash:: Hash + Eq + Clone> BestIterator<'a, Hash> {
	/// Depending on number of satisfied requirements insert given ref
	/// either to awaiting set or to best set.
	fn best_or_awaiting(&mut self, satisfied: usize, tx_ref: TransactionRef<Hash>) {
		if satisfied == tx_ref.transaction.requires.len() {
			// If we have satisfied all deps insert to best
			self.best.insert(tx_ref);

		} else {
			// otherwise we're still awaiting for some deps
			self.awaiting.insert(tx_ref.hash.clone(), (satisfied, tx_ref));
		}
	}
}

impl<'a, Hash: 'a + hash::Hash + Eq + Clone> Iterator for BestIterator<'a, Hash> {
	type Item = Arc<Transaction>;

	fn next(&mut self) -> Option<Self::Item> {
		let best = self.best.iter().next_back()?.clone();
		let best = self.best.take(&best)?;

		let ready = match self.all.get(&best.hash) {
			Some(ready) => ready,
			// The transaction is not in all, maybe it was removed in the meantime?
			None => return self.next(),
		};

		// Insert transactions that just got unlocked.
		for hash in &ready.unlocks {
			// first check local awaiting transactions
			if let Some((mut satisfied, tx_ref)) = self.awaiting.remove(hash) {
				satisfied += 1;
				self.best_or_awaiting(satisfied, tx_ref);
			// then get from the pool
			} else if let Some(next) = self.all.get(hash) {
				self.best_or_awaiting(1, next.transaction.clone());
			}
		}

		Some(best.transaction.clone())
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use primitives::UncheckedExtrinsic;

	fn tx(id: u8) -> Transaction {
		Transaction {
			ex: UncheckedExtrinsic(vec![id]),
			priority: 1,
			longevity: 2,
			requires: vec![vec![1], vec![2]],
			provides: vec![vec![3], vec![4]],
		}
	}

	#[test]
	fn should_replace_transaction_that_provides_the_same_tag() {
		// given
		let mut ready = ReadyTransactions::default();
		let block_number = 1;
		let mut tx1 = tx(1);
		tx1.requires.clear();
		let mut tx2 = tx(2);
		tx2.requires.clear();
		tx2.provides = vec![vec![3]];
		let mut tx3 = tx(3);
		tx3.requires.clear();
		tx3.provides = vec![vec![4]];

		// when
		let x = WaitingTransaction::new(tx2, 102, &ready.provided_tags());
		ready.import(x, block_number).unwrap();
		let x = WaitingTransaction::new(tx3, 103, &ready.provided_tags());
		ready.import(x, block_number).unwrap();
		assert_eq!(ready.get().count(), 2);

		// too low priority
		let x = WaitingTransaction::new(tx1.clone(), 101, &ready.provided_tags());
		ready.import(x, block_number).unwrap_err();

		tx1.priority = 10;
		let x = WaitingTransaction::new(tx1.clone(), 101, &ready.provided_tags());
		ready.import(x, block_number).unwrap();

		// then
		assert_eq!(ready.get().count(), 1);
	}


	#[test]
	fn should_return_best_transactions_in_correct_order() {
		// given
		let mut ready = ReadyTransactions::default();
		let mut tx1 = tx(1);
		tx1.requires.clear();
		let mut tx2 = tx(2);
		tx2.requires = tx1.provides.clone();
		tx2.provides = vec![vec![106]];
		let mut tx3 = tx(3);
		tx3.requires = vec![tx1.provides[0].clone(), vec![106]];
		tx3.provides = vec![];
		let mut tx4 = tx(4);
		tx4.requires = vec![tx1.provides[0].clone()];
		tx4.provides = vec![];
		let block_number = 1;

		// when
		let x = WaitingTransaction::new(tx1, 101, &ready.provided_tags());
		ready.import(x, block_number).unwrap();
		let x = WaitingTransaction::new(tx2, 102, &ready.provided_tags());
		ready.import(x, block_number).unwrap();
		let x = WaitingTransaction::new(tx3, 103, &ready.provided_tags());
		ready.import(x, block_number).unwrap();
		let x = WaitingTransaction::new(tx4, 104, &ready.provided_tags());
		ready.import(x, block_number).unwrap();

		// then
		assert_eq!(ready.best.len(), 1);

		let mut it = ready.get().map(|tx| tx.ex.0[0]);

		assert_eq!(it.next(), Some(1));
		assert_eq!(it.next(), Some(2));
		assert_eq!(it.next(), Some(3));
		assert_eq!(it.next(), Some(4));
		assert_eq!(it.next(), None);
	}

	#[test]
	fn should_order_refs() {
		let mut id = 1;
		let mut with_priority = |priority| {
			id += 1;
			let mut tx = tx(id);
			tx.priority = priority;
			tx
		};
		// higher priority = better
		assert!(TransactionRef {
			transaction: Arc::new(with_priority(3)),
			hash: 3,
			valid_till: 3,
			insertion_id: 1,
		} > TransactionRef {
			transaction: Arc::new(with_priority(2)),
			hash: 3,
			valid_till: 3,
			insertion_id: 2,
		});
		// lower validity = better
		assert!(TransactionRef {
			transaction: Arc::new(with_priority(3)),
			hash: 3,
			valid_till: 2,
			insertion_id: 1,
		} > TransactionRef {
			transaction: Arc::new(with_priority(3)),
			hash: 3,
			valid_till: 3,
			insertion_id: 2,
		});
		// lower insertion_id = better
		assert!(TransactionRef {
			transaction: Arc::new(with_priority(3)),
			hash: 3,
			valid_till: 3,
			insertion_id: 1,
		} > TransactionRef {
			transaction: Arc::new(with_priority(3)),
			hash: 3,
			valid_till: 3,
			insertion_id: 2,
		});
	}
}
