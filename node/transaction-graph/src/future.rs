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
	collections::{HashMap, HashSet},
	hash,
};

use sr_primitives::transaction_validity::{
	TransactionTag as Tag,
};

use pool::Transaction;

#[derive(Debug)]
pub struct WaitingTransaction<Hash> {
	pub transaction: Transaction<Hash>,
	pub missing_tags: HashSet<Tag>,
}

impl<Hash> WaitingTransaction<Hash> {
	pub fn new(transaction: Transaction<Hash>, provided: &HashMap<Tag, Hash>) -> Self {
		let missing_tags = transaction.requires
			.iter()
			.filter(|tag| !provided.contains_key(&**tag))
			.cloned()
			.collect();

		WaitingTransaction {
			transaction,
			missing_tags,
		}
	}

	pub fn satisfy_tag(&mut self, tag: &Tag) {
		self.missing_tags.remove(tag);
	}

	pub fn is_ready(&self) -> bool {
		self.missing_tags.is_empty()
	}
}

#[derive(Debug)]
pub struct FutureTransactions<Hash: hash::Hash + Eq> {
	/// tags that are not yet provided by any transaction and we await for them
	wanted_tags: HashMap<Tag, HashSet<Hash>>,
	/// Transactions waiting for a particular other transaction
	waiting: HashMap<Hash, WaitingTransaction<Hash>>,
}

impl<Hash: hash::Hash + Eq> Default for FutureTransactions<Hash> {
	fn default() -> Self {
		FutureTransactions {
			wanted_tags: Default::default(),
			waiting: Default::default(),
		}
	}
}

impl<Hash: hash::Hash + Eq + Clone> FutureTransactions<Hash> {
	/// Import transaction to Future queue.
	///
	/// Only transactions that don't have all their tags satisfied should occupy
	/// the Future queue.
	/// As soon as required tags are provided by some other transactions that are ready
	/// we should remove the transactions from here and move them to the Ready queue.
	pub fn import(&mut self, tx: WaitingTransaction<Hash>) {
		assert!(!tx.is_ready(), "Transaction is ready.");
		assert!(!self.waiting.contains_key(&tx.transaction.hash), "Transaction is already imported.");

		// Add all tags that are missing
		for tag in &tx.missing_tags {
			let mut entry = self.wanted_tags.entry(tag.clone()).or_insert_with(HashSet::new);
			entry.insert(tx.transaction.hash.clone());
		}

		// Add the transaction to a by-hash waiting map
		self.waiting.insert(tx.transaction.hash.clone(), tx);
	}

	/// Returns true if given hash is part of the queue.
	pub fn contains(&self, hash: &Hash) -> bool {
		self.waiting.contains_key(hash)
	}

	/// Satisfies provided tags in transactions that are waiting for them.
	///
	/// Returns (and removes) transactions that became ready after their last tag got
	/// satisfied and now we can remove them from Future and move to Ready queue.
	pub fn satisfy_tags(&mut self, tags: &[Tag]) -> Vec<WaitingTransaction<Hash>> {
		let mut became_ready = vec![];

		for tag in tags {
			if let Some(hashes) = self.wanted_tags.remove(tag) {
				for hash in hashes {
					let is_ready = {
						let mut tx = self.waiting.get_mut(&hash)
							.expect("Every transaction in wanted_tags is present in waiting; qed");
						tx.satisfy_tag(tag);
						tx.is_ready()
					};

					if is_ready {
						let tx = self.waiting.remove(&hash)
							.expect("We just get_mut the entry; qed");
						became_ready.push(tx);
					}
				}
			}
		}

		became_ready
	}

	/// Removes transactions for given list of hashes.
	///
	/// Returns a list of actually removed transactions.
	pub fn remove(&mut self, hashes: &[Hash]) -> Vec<Transaction<Hash>> {
		let mut removed = vec![];
		for hash in hashes {
			if let Some(waiting_tx) = self.waiting.remove(hash) {
				// remove from wanted_tags as well
				for tag in waiting_tx.missing_tags {
					let remove = if let Some(mut wanted) = self.wanted_tags.get_mut(&tag) {
						wanted.remove(hash);
						wanted.is_empty()
					} else { false };
					if remove {
						self.wanted_tags.remove(&tag);
					}
				}
				// add to result
				removed.push(waiting_tx.transaction)
			}
		}
		removed
	}

	/// Returns number of transactions in the Future queue.
	#[cfg(test)]
	pub fn len(&self) -> usize {
		self.waiting.len()
	}
}
