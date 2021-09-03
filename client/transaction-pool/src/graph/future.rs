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
	fmt, hash,
	sync::Arc,
};

use sp_core::hexdisplay::HexDisplay;
use sp_runtime::transaction_validity::TransactionTag as Tag;
use std::time::Instant;

use super::base_pool::Transaction;

#[cfg_attr(not(target_os = "unknown"), derive(parity_util_mem::MallocSizeOf))]
/// Transaction with partially satisfied dependencies.
pub struct WaitingTransaction<Hash, Ex> {
	/// Transaction details.
	pub transaction: Arc<Transaction<Hash, Ex>>,
	/// Tags that are required and have not been satisfied yet by other transactions in the pool.
	pub missing_tags: HashSet<Tag>,
	/// Time of import to the Future Queue.
	pub imported_at: Instant,
}

impl<Hash: fmt::Debug, Ex: fmt::Debug> fmt::Debug for WaitingTransaction<Hash, Ex> {
	fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
		write!(fmt, "WaitingTransaction {{ ")?;
		write!(fmt, "imported_at: {:?}, ", self.imported_at)?;
		write!(fmt, "transaction: {:?}, ", self.transaction)?;
		write!(
			fmt,
			"missing_tags: {{{}}}",
			self.missing_tags
				.iter()
				.map(|tag| HexDisplay::from(tag).to_string())
				.collect::<Vec<_>>()
				.join(", "),
		)?;
		write!(fmt, "}}")
	}
}

impl<Hash, Ex> Clone for WaitingTransaction<Hash, Ex> {
	fn clone(&self) -> Self {
		Self {
			transaction: self.transaction.clone(),
			missing_tags: self.missing_tags.clone(),
			imported_at: self.imported_at,
		}
	}
}

impl<Hash, Ex> WaitingTransaction<Hash, Ex> {
	/// Creates a new `WaitingTransaction`.
	///
	/// Computes the set of missing tags based on the requirements and tags that
	/// are provided by all transactions in the ready queue.
	pub fn new(
		transaction: Transaction<Hash, Ex>,
		provided: &HashMap<Tag, Hash>,
		recently_pruned: &[HashSet<Tag>],
	) -> Self {
		let missing_tags = transaction
			.requires
			.iter()
			.filter(|tag| {
				// is true if the tag is already satisfied either via transaction in the pool
				// or one that was recently included.
				let is_provided = provided.contains_key(&**tag) ||
					recently_pruned.iter().any(|x| x.contains(&**tag));
				!is_provided
			})
			.cloned()
			.collect();

		Self { transaction: Arc::new(transaction), missing_tags, imported_at: Instant::now() }
	}

	/// Marks the tag as satisfied.
	pub fn satisfy_tag(&mut self, tag: &Tag) {
		self.missing_tags.remove(tag);
	}

	/// Returns true if transaction has all requirements satisfied.
	pub fn is_ready(&self) -> bool {
		self.missing_tags.is_empty()
	}
}

/// A pool of transactions that are not yet ready to be included in the block.
///
/// Contains transactions that are still awaiting for some other transactions that
/// could provide a tag that they require.
#[derive(Debug)]
#[cfg_attr(not(target_os = "unknown"), derive(parity_util_mem::MallocSizeOf))]
pub struct FutureTransactions<Hash: hash::Hash + Eq, Ex> {
	/// tags that are not yet provided by any transaction and we await for them
	wanted_tags: HashMap<Tag, HashSet<Hash>>,
	/// Transactions waiting for a particular other transaction
	waiting: HashMap<Hash, WaitingTransaction<Hash, Ex>>,
}

impl<Hash: hash::Hash + Eq, Ex> Default for FutureTransactions<Hash, Ex> {
	fn default() -> Self {
		Self { wanted_tags: Default::default(), waiting: Default::default() }
	}
}

const WAITING_PROOF: &str = r"#
In import we always insert to `waiting` if we push to `wanted_tags`;
when removing from `waiting` we always clear `wanted_tags`;
every hash from `wanted_tags` is always present in `waiting`;
qed
#";

impl<Hash: hash::Hash + Eq + Clone, Ex> FutureTransactions<Hash, Ex> {
	/// Import transaction to Future queue.
	///
	/// Only transactions that don't have all their tags satisfied should occupy
	/// the Future queue.
	/// As soon as required tags are provided by some other transactions that are ready
	/// we should remove the transactions from here and move them to the Ready queue.
	pub fn import(&mut self, tx: WaitingTransaction<Hash, Ex>) {
		assert!(!tx.is_ready(), "Transaction is ready.");
		assert!(
			!self.waiting.contains_key(&tx.transaction.hash),
			"Transaction is already imported."
		);

		// Add all tags that are missing
		for tag in &tx.missing_tags {
			let entry = self.wanted_tags.entry(tag.clone()).or_insert_with(HashSet::new);
			entry.insert(tx.transaction.hash.clone());
		}

		// Add the transaction to a by-hash waiting map
		self.waiting.insert(tx.transaction.hash.clone(), tx);
	}

	/// Returns true if given hash is part of the queue.
	pub fn contains(&self, hash: &Hash) -> bool {
		self.waiting.contains_key(hash)
	}

	/// Returns a list of known transactions
	pub fn by_hashes(&self, hashes: &[Hash]) -> Vec<Option<Arc<Transaction<Hash, Ex>>>> {
		hashes
			.iter()
			.map(|h| self.waiting.get(h).map(|x| x.transaction.clone()))
			.collect()
	}

	/// Satisfies provided tags in transactions that are waiting for them.
	///
	/// Returns (and removes) transactions that became ready after their last tag got
	/// satisfied and now we can remove them from Future and move to Ready queue.
	pub fn satisfy_tags<T: AsRef<Tag>>(
		&mut self,
		tags: impl IntoIterator<Item = T>,
	) -> Vec<WaitingTransaction<Hash, Ex>> {
		let mut became_ready = vec![];

		for tag in tags {
			if let Some(hashes) = self.wanted_tags.remove(tag.as_ref()) {
				for hash in hashes {
					let is_ready = {
						let tx = self.waiting.get_mut(&hash).expect(WAITING_PROOF);
						tx.satisfy_tag(tag.as_ref());
						tx.is_ready()
					};

					if is_ready {
						let tx = self.waiting.remove(&hash).expect(WAITING_PROOF);
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
	pub fn remove(&mut self, hashes: &[Hash]) -> Vec<Arc<Transaction<Hash, Ex>>> {
		let mut removed = vec![];
		for hash in hashes {
			if let Some(waiting_tx) = self.waiting.remove(hash) {
				// remove from wanted_tags as well
				for tag in waiting_tx.missing_tags {
					let remove = if let Some(wanted) = self.wanted_tags.get_mut(&tag) {
						wanted.remove(hash);
						wanted.is_empty()
					} else {
						false
					};
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

	/// Fold a list of future transactions to compute a single value.
	pub fn fold<R, F: FnMut(Option<R>, &WaitingTransaction<Hash, Ex>) -> Option<R>>(
		&mut self,
		f: F,
	) -> Option<R> {
		self.waiting.values().fold(None, f)
	}

	/// Returns iterator over all future transactions
	pub fn all(&self) -> impl Iterator<Item = &Transaction<Hash, Ex>> {
		self.waiting.values().map(|waiting| &*waiting.transaction)
	}

	/// Removes and returns all future transactions.
	pub fn clear(&mut self) -> Vec<Arc<Transaction<Hash, Ex>>> {
		self.wanted_tags.clear();
		self.waiting.drain().map(|(_, tx)| tx.transaction).collect()
	}

	/// Returns number of transactions in the Future queue.
	pub fn len(&self) -> usize {
		self.waiting.len()
	}

	/// Returns sum of encoding lengths of all transactions in this queue.
	pub fn bytes(&self) -> usize {
		self.waiting.values().fold(0, |acc, tx| acc + tx.transaction.bytes)
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use sp_runtime::transaction_validity::TransactionSource;

	#[test]
	fn can_track_heap_size() {
		let mut future = FutureTransactions::default();
		future.import(WaitingTransaction {
			transaction: Transaction {
				data: vec![0u8; 1024],
				bytes: 1,
				hash: 1,
				priority: 1,
				valid_till: 2,
				requires: vec![vec![1], vec![2]],
				provides: vec![vec![3], vec![4]],
				propagate: true,
				source: TransactionSource::External,
			}
			.into(),
			missing_tags: vec![vec![1u8], vec![2u8]].into_iter().collect(),
			imported_at: std::time::Instant::now(),
		});

		// data is at least 1024!
		assert!(parity_util_mem::malloc_size(&future) > 1024);
	}
}
