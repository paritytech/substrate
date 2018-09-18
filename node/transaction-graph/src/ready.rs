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
	collections::{HashMap, BTreeSet},
	cmp,
	hash,
	sync::Arc,
};

use sr_primitives::transaction_validity::{
	TransactionTag as Tag,
	TransactionPriority as Priority,
};

use super::pool::BlockNumber;
use super::pool::{Transaction, WaitingTransaction};

#[derive(Debug, Clone)]
pub struct TransactionRef<Hash> {
	pub transaction: Arc<Transaction>,
	pub hash: Hash,
	pub valid_till: BlockNumber,
	pub insertion_id: u64,
}

// TODO [ToDr] Testme
impl<Hash> Ord for TransactionRef<Hash> {
	fn cmp(&self, other: &Self) -> cmp::Ordering {
		self.transaction.priority.cmp(&other.transaction.priority)
			.then(self.valid_till.cmp(&other.valid_till))
			.then(self.insertion_id.cmp(&other.insertion_id))
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

#[derive(Debug)]
pub struct ReadyTransactions<Hash: hash::Hash + Eq> {
	/// tags that are provided by ready transactions
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
			provided_tags: Default::default(),
			ready: Default::default(),
			best: Default::default(),
		}
	}
}

impl<Hash: hash::Hash + Eq + Clone> ReadyTransactions<Hash> {
	pub fn provided_tags(&self) -> &HashMap<Tag, Hash> {
		&self.provided_tags
	}

	pub fn get<'a>(&'a self) -> impl Iterator<Item=Arc<Transaction>> + 'a {
		BestIterator {
			ready: &self.ready,
			best: self.best.clone(),
		}
	}

	pub fn import(&mut self, tx: WaitingTransaction<Hash>, insertion_id: u64, block_number: BlockNumber) {
		assert!(tx.is_ready(), "Only ready transactions can be imported.");

		let hash = tx.hash;
		let tx = tx.transaction;
		let mut goes_to_best = true;
		// Add info what transactions unlock this one.
		for tag in &tx.requires {
			// Check if the transaction that satisfies the tag is still in the queue.
			if let Some(other) = self.provided_tags.get(tag) {
				let mut tx = self.ready.get_mut(other).expect("All hashes are present in ready; qed");
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

		// insert to ready
		self.ready.insert(hash, ReadyTx {
			transaction,
			unlocks: vec![],
		});
	}
}

pub struct BestIterator<'a, Hash: 'a> {
	ready: &'a HashMap<Hash, ReadyTx<Hash>>,
	best: BTreeSet<TransactionRef<Hash>>,
}

impl<'a, Hash: 'a + hash::Hash + Eq + Clone> Iterator for BestIterator<'a, Hash> {
	type Item = Arc<Transaction>;

	fn next(&mut self) -> Option<Self::Item> {
		let best = self.best.iter().next()?.clone();
		let best = self.best.take(&best)?;

		let ready = self.ready.get(&best.hash)?;

		// Insert transactions that just got unlocked.
		for hash in &ready.unlocks {
			// TODO [ToDr] This is actually invalid.
			// We need to check if all `requires` were already returned.
			if let Some(other) = self.ready.get(hash) {
				self.best.insert(other.transaction.clone());
			}
		}

		Some(best.transaction.clone())
	}
}

#[cfg(test)]
mod tests {

	#[test]
	fn should_sort_best_transactions() {
		assert_eq!(true, false);
	}
}
