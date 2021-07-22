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
	cmp,
	collections::{BTreeSet, HashMap, HashSet},
	hash,
	sync::Arc,
};

use log::trace;
use sc_transaction_pool_api::error;
use serde::Serialize;
use sp_runtime::{traits::Member, transaction_validity::TransactionTag as Tag};

use super::{
	base_pool::Transaction,
	future::WaitingTransaction,
	tracked_map::{self, ReadOnlyTrackedMap, TrackedMap},
};

/// An in-pool transaction reference.
///
/// Should be cheap to clone.
#[derive(Debug, parity_util_mem::MallocSizeOf)]
pub struct TransactionRef<Hash, Ex> {
	/// The actual transaction data.
	pub transaction: Arc<Transaction<Hash, Ex>>,
	/// Unique id when transaction was inserted into the pool.
	pub insertion_id: u64,
}

impl<Hash, Ex> Clone for TransactionRef<Hash, Ex> {
	fn clone(&self) -> Self {
		Self { transaction: self.transaction.clone(), insertion_id: self.insertion_id }
	}
}

impl<Hash, Ex> Ord for TransactionRef<Hash, Ex> {
	fn cmp(&self, other: &Self) -> cmp::Ordering {
		self.transaction
			.priority
			.cmp(&other.transaction.priority)
			.then_with(|| other.transaction.valid_till.cmp(&self.transaction.valid_till))
			.then_with(|| other.insertion_id.cmp(&self.insertion_id))
	}
}

impl<Hash, Ex> PartialOrd for TransactionRef<Hash, Ex> {
	fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
		Some(self.cmp(other))
	}
}

impl<Hash, Ex> PartialEq for TransactionRef<Hash, Ex> {
	fn eq(&self, other: &Self) -> bool {
		self.cmp(other) == cmp::Ordering::Equal
	}
}
impl<Hash, Ex> Eq for TransactionRef<Hash, Ex> {}

#[derive(Debug, parity_util_mem::MallocSizeOf)]
pub struct ReadyTx<Hash, Ex> {
	/// A reference to a transaction
	pub transaction: TransactionRef<Hash, Ex>,
	/// A list of transactions that get unlocked by this one
	pub unlocks: Vec<Hash>,
	/// How many required tags are provided inherently
	///
	/// Some transactions might be already pruned from the queue,
	/// so when we compute ready set we may consider this transactions ready earlier.
	pub requires_offset: usize,
}

impl<Hash: Clone, Ex> Clone for ReadyTx<Hash, Ex> {
	fn clone(&self) -> Self {
		Self {
			transaction: self.transaction.clone(),
			unlocks: self.unlocks.clone(),
			requires_offset: self.requires_offset,
		}
	}
}

const HASH_READY: &str = r#"
Every time transaction is imported its hash is placed in `ready` map and tags in `provided_tags`;
Every time transaction is removed from the queue we remove the hash from `ready` map and from `provided_tags`;
Hence every hash retrieved from `provided_tags` is always present in `ready`;
qed
"#;

/// Validated transactions that are block ready with all their dependencies met.
#[derive(Debug, parity_util_mem::MallocSizeOf)]
pub struct ReadyTransactions<Hash: hash::Hash + Eq, Ex> {
	/// Next free insertion id (used to indicate when a transaction was inserted into the pool).
	insertion_id: u64,
	/// tags that are provided by Ready transactions
	/// (only a single transaction can provide a specific tag)
	provided_tags: HashMap<Tag, Hash>,
	/// Transactions that are ready (i.e. don't have any requirements external to the pool)
	ready: TrackedMap<Hash, ReadyTx<Hash, Ex>>,
	/// Best transactions that are ready to be included to the block without any other previous transaction.
	best: BTreeSet<TransactionRef<Hash, Ex>>,
}

impl<Hash, Ex> tracked_map::Size for ReadyTx<Hash, Ex> {
	fn size(&self) -> usize {
		self.transaction.transaction.bytes
	}
}

impl<Hash: hash::Hash + Eq, Ex> Default for ReadyTransactions<Hash, Ex> {
	fn default() -> Self {
		Self {
			insertion_id: Default::default(),
			provided_tags: Default::default(),
			ready: Default::default(),
			best: Default::default(),
		}
	}
}

impl<Hash: hash::Hash + Member + Serialize, Ex> ReadyTransactions<Hash, Ex> {
	/// Borrows a map of tags that are provided by transactions in this queue.
	pub fn provided_tags(&self) -> &HashMap<Tag, Hash> {
		&self.provided_tags
	}

	/// Returns an iterator of ready transactions.
	///
	/// Transactions are returned in order:
	/// 1. First by the dependencies:
	/// 	- never return transaction that requires a tag, which was not provided by one of the previously
	/// returned transactions
	/// 2. Then by priority:
	/// - If there are two transactions with all requirements satisfied the one with higher priority goes first.
	/// 3. Then by the ttl that's left
	/// - transactions that are valid for a shorter time go first
	/// 4. Lastly we sort by the time in the queue
	/// - transactions that are longer in the queue go first
	pub fn get(&self) -> impl Iterator<Item = Arc<Transaction<Hash, Ex>>> {
		BestIterator {
			all: self.ready.clone(),
			best: self.best.clone(),
			awaiting: Default::default(),
		}
	}

	/// Imports transactions to the pool of ready transactions.
	///
	/// The transaction needs to have all tags satisfied (be ready) by transactions
	/// that are in this queue.
	/// Returns transactions that were replaced by the one imported.
	pub fn import(
		&mut self,
		tx: WaitingTransaction<Hash, Ex>,
	) -> error::Result<Vec<Arc<Transaction<Hash, Ex>>>> {
		assert!(
			tx.is_ready(),
			"Only ready transactions can be imported. Missing: {:?}",
			tx.missing_tags
		);
		assert!(
			!self.ready.read().contains_key(&tx.transaction.hash),
			"Transaction is already imported."
		);

		self.insertion_id += 1;
		let insertion_id = self.insertion_id;
		let hash = tx.transaction.hash.clone();
		let transaction = tx.transaction;

		let (replaced, unlocks) = self.replace_previous(&transaction)?;

		let mut goes_to_best = true;
		let mut ready = self.ready.write();
		let mut requires_offset = 0;
		// Add links to transactions that unlock the current one
		for tag in &transaction.requires {
			// Check if the transaction that satisfies the tag is still in the queue.
			if let Some(other) = self.provided_tags.get(tag) {
				let tx = ready.get_mut(other).expect(HASH_READY);
				tx.unlocks.push(hash.clone());
				// this transaction depends on some other, so it doesn't go to best directly.
				goes_to_best = false;
			} else {
				requires_offset += 1;
			}
		}

		// update provided_tags
		// call to replace_previous guarantees that we will be overwriting
		// only entries that have been removed.
		for tag in &transaction.provides {
			self.provided_tags.insert(tag.clone(), hash.clone());
		}

		let transaction = TransactionRef { insertion_id, transaction };

		// insert to best if it doesn't require any other transaction to be included before it
		if goes_to_best {
			self.best.insert(transaction.clone());
		}

		// insert to Ready
		ready.insert(hash, ReadyTx { transaction, unlocks, requires_offset });

		Ok(replaced)
	}

	/// Fold a list of ready transactions to compute a single value.
	pub fn fold<R, F: FnMut(Option<R>, &ReadyTx<Hash, Ex>) -> Option<R>>(
		&mut self,
		f: F,
	) -> Option<R> {
		self.ready.read().values().fold(None, f)
	}

	/// Returns true if given transaction is part of the queue.
	pub fn contains(&self, hash: &Hash) -> bool {
		self.ready.read().contains_key(hash)
	}

	/// Retrieve transaction by hash
	pub fn by_hash(&self, hash: &Hash) -> Option<Arc<Transaction<Hash, Ex>>> {
		self.by_hashes(&[hash.clone()]).into_iter().next().unwrap_or(None)
	}

	/// Retrieve transactions by hash
	pub fn by_hashes(&self, hashes: &[Hash]) -> Vec<Option<Arc<Transaction<Hash, Ex>>>> {
		let ready = self.ready.read();
		hashes
			.iter()
			.map(|hash| ready.get(hash).map(|x| x.transaction.transaction.clone()))
			.collect()
	}

	/// Removes a subtree of transactions from the ready pool.
	///
	/// NOTE removing a transaction will also cause a removal of all transactions that depend on that one
	/// (i.e. the entire subgraph that this transaction is a start of will be removed).
	/// All removed transactions are returned.
	pub fn remove_subtree(&mut self, hashes: &[Hash]) -> Vec<Arc<Transaction<Hash, Ex>>> {
		let to_remove = hashes.to_vec();
		self.remove_subtree_with_tag_filter(to_remove, None)
	}

	/// Removes a subtrees of transactions trees starting from roots given in `to_remove`.
	///
	/// We proceed with a particular branch only if there is at least one provided tag
	/// that is not part of `provides_tag_filter`. I.e. the filter contains tags
	/// that will stay in the pool, so that we can early exit and avoid descending.
	fn remove_subtree_with_tag_filter(
		&mut self,
		mut to_remove: Vec<Hash>,
		provides_tag_filter: Option<HashSet<Tag>>,
	) -> Vec<Arc<Transaction<Hash, Ex>>> {
		let mut removed = vec![];
		let mut ready = self.ready.write();
		while let Some(hash) = to_remove.pop() {
			if let Some(mut tx) = ready.remove(&hash) {
				let invalidated = tx.transaction.transaction.provides.iter().filter(|tag| {
					provides_tag_filter
						.as_ref()
						.map(|filter| !filter.contains(&**tag))
						.unwrap_or(true)
				});

				let mut removed_some_tags = false;
				// remove entries from provided_tags
				for tag in invalidated {
					removed_some_tags = true;
					self.provided_tags.remove(tag);
				}

				// remove from unlocks
				for tag in &tx.transaction.transaction.requires {
					if let Some(hash) = self.provided_tags.get(tag) {
						if let Some(tx) = ready.get_mut(hash) {
							remove_item(&mut tx.unlocks, &hash);
						}
					}
				}

				// remove from best
				self.best.remove(&tx.transaction);

				if removed_some_tags {
					// remove all transactions that the current one unlocks
					to_remove.append(&mut tx.unlocks);
				}

				// add to removed
				trace!(target: "txpool", "[{:?}] Removed as part of the subtree.", hash);
				removed.push(tx.transaction.transaction);
			}
		}

		removed
	}

	/// Removes transactions that provide given tag.
	///
	/// All transactions that lead to a transaction, which provides this tag
	/// are going to be removed from the queue, but no other transactions are touched -
	/// i.e. all other subgraphs starting from given tag are still considered valid & ready.
	pub fn prune_tags(&mut self, tag: Tag) -> Vec<Arc<Transaction<Hash, Ex>>> {
		let mut removed = vec![];
		let mut to_remove = vec![tag];

		while let Some(tag) = to_remove.pop() {
			let res = self
				.provided_tags
				.remove(&tag)
				.and_then(|hash| self.ready.write().remove(&hash));

			if let Some(tx) = res {
				let unlocks = tx.unlocks;

				// Make sure we remove it from best txs
				self.best.remove(&tx.transaction);

				let tx = tx.transaction.transaction;

				// prune previous transactions as well
				{
					let hash = &tx.hash;
					let mut ready = self.ready.write();
					let mut find_previous = |tag| -> Option<Vec<Tag>> {
						let prev_hash = self.provided_tags.get(tag)?;
						let tx2 = ready.get_mut(&prev_hash)?;
						remove_item(&mut tx2.unlocks, hash);
						// We eagerly prune previous transactions as well.
						// But it might not always be good.
						// Possible edge case:
						// - tx provides two tags
						// - the second tag enables some subgraph we don't know of yet
						// - we will prune the transaction
						// - when we learn about the subgraph it will go to future
						// - we will have to wait for re-propagation of that transaction
						// Alternatively the caller may attempt to re-import these transactions.
						if tx2.unlocks.is_empty() {
							Some(tx2.transaction.transaction.provides.clone())
						} else {
							None
						}
					};

					// find previous transactions
					for tag in &tx.requires {
						if let Some(mut tags_to_remove) = find_previous(tag) {
							to_remove.append(&mut tags_to_remove);
						}
					}
				}

				// add the transactions that just got unlocked to `best`
				for hash in unlocks {
					if let Some(tx) = self.ready.write().get_mut(&hash) {
						tx.requires_offset += 1;
						// this transaction is ready
						if tx.requires_offset == tx.transaction.transaction.requires.len() {
							self.best.insert(tx.transaction.clone());
						}
					}
				}

				// we also need to remove all other tags that this transaction provides,
				// but since all the hard work is done, we only clear the provided_tag -> hash
				// mapping.
				let current_tag = &tag;
				for tag in &tx.provides {
					let removed = self.provided_tags.remove(tag);
					assert_eq!(
						removed.as_ref(),
						if current_tag == tag { None } else { Some(&tx.hash) },
						"The pool contains exactly one transaction providing given tag; the removed transaction
						claims to provide that tag, so it has to be mapped to it's hash; qed"
					);
				}

				removed.push(tx);
			}
		}

		removed
	}

	/// Checks if the transaction is providing the same tags as other transactions.
	///
	/// In case that's true it determines if the priority of transactions that
	/// we are about to replace is lower than the priority of the replacement transaction.
	/// We remove/replace old transactions in case they have lower priority.
	///
	/// In case replacement is successful returns a list of removed transactions
	/// and a list of hashes that are still in pool and gets unlocked by the new transaction.
	fn replace_previous(
		&mut self,
		tx: &Transaction<Hash, Ex>,
	) -> error::Result<(Vec<Arc<Transaction<Hash, Ex>>>, Vec<Hash>)> {
		let (to_remove, unlocks) = {
			// check if we are replacing a transaction
			let replace_hashes = tx
				.provides
				.iter()
				.filter_map(|tag| self.provided_tags.get(tag))
				.collect::<HashSet<_>>();

			// early exit if we are not replacing anything.
			if replace_hashes.is_empty() {
				return Ok((vec![], vec![]))
			}

			// now check if collective priority is lower than the replacement transaction.
			let old_priority = {
				let ready = self.ready.read();
				replace_hashes
					.iter()
					.filter_map(|hash| ready.get(hash))
					.fold(0u64, |total, tx| {
						total.saturating_add(tx.transaction.transaction.priority)
					})
			};

			// bail - the transaction has too low priority to replace the old ones
			if old_priority >= tx.priority {
				return Err(error::Error::TooLowPriority { old: old_priority, new: tx.priority })
			}

			// construct a list of unlocked transactions
			let unlocks = {
				let ready = self.ready.read();
				replace_hashes.iter().filter_map(|hash| ready.get(hash)).fold(
					vec![],
					|mut list, tx| {
						list.extend(tx.unlocks.iter().cloned());
						list
					},
				)
			};

			(replace_hashes.into_iter().cloned().collect::<Vec<_>>(), unlocks)
		};

		let new_provides = tx.provides.iter().cloned().collect::<HashSet<_>>();
		let removed = self.remove_subtree_with_tag_filter(to_remove, Some(new_provides));

		Ok((removed, unlocks))
	}

	/// Returns number of transactions in this queue.
	pub fn len(&self) -> usize {
		self.ready.len()
	}

	/// Returns sum of encoding lengths of all transactions in this queue.
	pub fn bytes(&self) -> usize {
		self.ready.bytes()
	}
}

/// Iterator of ready transactions ordered by priority.
pub struct BestIterator<Hash, Ex> {
	all: ReadOnlyTrackedMap<Hash, ReadyTx<Hash, Ex>>,
	awaiting: HashMap<Hash, (usize, TransactionRef<Hash, Ex>)>,
	best: BTreeSet<TransactionRef<Hash, Ex>>,
}

impl<Hash: hash::Hash + Member, Ex> BestIterator<Hash, Ex> {
	/// Depending on number of satisfied requirements insert given ref
	/// either to awaiting set or to best set.
	fn best_or_awaiting(&mut self, satisfied: usize, tx_ref: TransactionRef<Hash, Ex>) {
		if satisfied >= tx_ref.transaction.requires.len() {
			// If we have satisfied all deps insert to best
			self.best.insert(tx_ref);
		} else {
			// otherwise we're still awaiting for some deps
			self.awaiting.insert(tx_ref.transaction.hash.clone(), (satisfied, tx_ref));
		}
	}
}

impl<Hash: hash::Hash + Member, Ex> Iterator for BestIterator<Hash, Ex> {
	type Item = Arc<Transaction<Hash, Ex>>;

	fn next(&mut self) -> Option<Self::Item> {
		loop {
			let best = self.best.iter().next_back()?.clone();
			let best = self.best.take(&best)?;

			let next = self.all.read().get(&best.transaction.hash).cloned();
			let ready = match next {
				Some(ready) => ready,
				// The transaction is not in all, maybe it was removed in the meantime?
				None => continue,
			};

			// Insert transactions that just got unlocked.
			for hash in &ready.unlocks {
				// first check local awaiting transactions
				let res = if let Some((mut satisfied, tx_ref)) = self.awaiting.remove(hash) {
					satisfied += 1;
					Some((satisfied, tx_ref))
				// then get from the pool
				} else {
					self.all
						.read()
						.get(hash)
						.map(|next| (next.requires_offset + 1, next.transaction.clone()))
				};
				if let Some((satisfied, tx_ref)) = res {
					self.best_or_awaiting(satisfied, tx_ref)
				}
			}

			return Some(best.transaction)
		}
	}
}

// See: https://github.com/rust-lang/rust/issues/40062
fn remove_item<T: PartialEq>(vec: &mut Vec<T>, item: &T) {
	if let Some(idx) = vec.iter().position(|i| i == item) {
		vec.swap_remove(idx);
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use sp_runtime::transaction_validity::TransactionSource as Source;

	fn tx(id: u8) -> Transaction<u64, Vec<u8>> {
		Transaction {
			data: vec![id],
			bytes: 1,
			hash: id as u64,
			priority: 1,
			valid_till: 2,
			requires: vec![vec![1], vec![2]],
			provides: vec![vec![3], vec![4]],
			propagate: true,
			source: Source::External,
		}
	}

	fn import<H: hash::Hash + Eq + Member + Serialize, Ex>(
		ready: &mut ReadyTransactions<H, Ex>,
		tx: Transaction<H, Ex>,
	) -> error::Result<Vec<Arc<Transaction<H, Ex>>>> {
		let x = WaitingTransaction::new(tx, ready.provided_tags(), &[]);
		ready.import(x)
	}

	#[test]
	fn should_replace_transaction_that_provides_the_same_tag() {
		// given
		let mut ready = ReadyTransactions::default();
		let mut tx1 = tx(1);
		tx1.requires.clear();
		let mut tx2 = tx(2);
		tx2.requires.clear();
		tx2.provides = vec![vec![3]];
		let mut tx3 = tx(3);
		tx3.requires.clear();
		tx3.provides = vec![vec![4]];

		// when
		import(&mut ready, tx2).unwrap();
		import(&mut ready, tx3).unwrap();
		assert_eq!(ready.get().count(), 2);

		// too low priority
		import(&mut ready, tx1.clone()).unwrap_err();

		tx1.priority = 10;
		import(&mut ready, tx1).unwrap();

		// then
		assert_eq!(ready.get().count(), 1);
	}

	#[test]
	fn should_replace_multiple_transactions_correctly() {
		// given
		let mut ready = ReadyTransactions::default();
		let mut tx0 = tx(0);
		tx0.requires = vec![];
		tx0.provides = vec![vec![0]];
		let mut tx1 = tx(1);
		tx1.requires = vec![];
		tx1.provides = vec![vec![1]];
		let mut tx2 = tx(2);
		tx2.requires = vec![vec![0], vec![1]];
		tx2.provides = vec![vec![2], vec![3]];
		let mut tx3 = tx(3);
		tx3.requires = vec![vec![2]];
		tx3.provides = vec![vec![4]];
		let mut tx4 = tx(4);
		tx4.requires = vec![vec![3]];
		tx4.provides = vec![vec![5]];
		// replacement
		let mut tx2_2 = tx(5);
		tx2_2.requires = vec![vec![0], vec![1]];
		tx2_2.provides = vec![vec![2]];
		tx2_2.priority = 10;

		for tx in vec![tx0, tx1, tx2, tx3, tx4] {
			import(&mut ready, tx).unwrap();
		}
		assert_eq!(ready.get().count(), 5);

		// when
		import(&mut ready, tx2_2).unwrap();

		// then
		assert_eq!(ready.get().count(), 3);
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
		let tx5 = Transaction {
			data: vec![5],
			bytes: 1,
			hash: 5,
			priority: 1,
			valid_till: u64::MAX, // use the max here for testing.
			requires: vec![tx1.provides[0].clone()],
			provides: vec![],
			propagate: true,
			source: Source::External,
		};

		// when
		for tx in vec![tx1, tx2, tx3, tx4, tx5] {
			import(&mut ready, tx).unwrap();
		}

		// then
		assert_eq!(ready.best.len(), 1);

		let mut it = ready.get().map(|tx| tx.data[0]);

		assert_eq!(it.next(), Some(1));
		assert_eq!(it.next(), Some(2));
		assert_eq!(it.next(), Some(3));
		assert_eq!(it.next(), Some(4));
		assert_eq!(it.next(), Some(5));
		assert_eq!(it.next(), None);
	}

	#[test]
	fn can_report_heap_size() {
		let mut ready = ReadyTransactions::default();
		let tx = Transaction {
			data: vec![5],
			bytes: 1,
			hash: 5,
			priority: 1,
			valid_till: u64::MAX, // use the max here for testing.
			requires: vec![],
			provides: vec![],
			propagate: true,
			source: Source::External,
		};
		import(&mut ready, tx).unwrap();

		assert!(parity_util_mem::malloc_size(&ready) > 200);
	}

	#[test]
	fn should_order_refs() {
		let mut id = 1;
		let mut with_priority = |priority, longevity| {
			id += 1;
			let mut tx = tx(id);
			tx.priority = priority;
			tx.valid_till = longevity;
			tx
		};
		// higher priority = better
		assert!(
			TransactionRef { transaction: Arc::new(with_priority(3, 3)), insertion_id: 1 } >
				TransactionRef { transaction: Arc::new(with_priority(2, 3)), insertion_id: 2 }
		);
		// lower validity = better
		assert!(
			TransactionRef { transaction: Arc::new(with_priority(3, 2)), insertion_id: 1 } >
				TransactionRef { transaction: Arc::new(with_priority(3, 3)), insertion_id: 2 }
		);
		// lower insertion_id = better
		assert!(
			TransactionRef { transaction: Arc::new(with_priority(3, 3)), insertion_id: 1 } >
				TransactionRef { transaction: Arc::new(with_priority(3, 3)), insertion_id: 2 }
		);
	}
}
