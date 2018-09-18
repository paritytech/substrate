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
	fmt,
	hash,
};

use primitives::UncheckedExtrinsic;
use sr_primitives::transaction_validity::{
	TransactionTag as Tag,
	TransactionLongevity as Longevity,
	TransactionPriority as Priority,
};

use ready::ReadyTransactions;

pub type BlockNumber = u64;

/// Immutable transaction
#[derive(Debug)]
pub struct Transaction {
	pub ex: UncheckedExtrinsic,
	pub priority: Priority,
	pub longevity: Longevity,
	pub requires: Vec<Tag>,
	pub provides: Vec<Tag>,
}

#[derive(Debug)]
pub struct WaitingTransaction<Hash> {
	pub transaction: Transaction,
	pub missing_tags: HashSet<Tag>,
	pub hash: Hash,
}

impl<Hash> WaitingTransaction<Hash> {
	pub fn new(transaction: Transaction, hash: Hash, provided: &HashMap<Tag, Hash>) -> Self {
		let missing_tags = transaction.requires
			.iter()
			.filter(|tag| !provided.contains_key(&**tag))
			.cloned()
			.collect();

		WaitingTransaction {
			transaction,
			missing_tags,
			hash,
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
	wanted_tags: HashMap<Tag, Vec<Hash>>,
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

impl<Hash: hash::Hash + Eq> FutureTransactions<Hash> {
	pub fn import(&mut self, tx: WaitingTransaction<Hash>) {
		unimplemented!()
	}
}

/// Transaction pool.
///
/// Builds a dependency graph for all transactions in the pool and returns
/// the ones that are currently ready to be executed.
pub struct Pool<Hash: hash::Hash + Eq> {
	future: FutureTransactions<Hash>,
	ready: ReadyTransactions<Hash>,
	insertion_id: u64,
	hasher: Box<Fn(&UncheckedExtrinsic) -> Hash>,
}

impl<Hash: hash::Hash + fmt::Debug + Eq> fmt::Debug for Pool<Hash> {
	fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
		fmt.debug_struct("Pool")
			.field("future", &self.future)
			.field("ready", &self.ready)
			.field("insertion_id", &self.insertion_id)
			.finish()
	}
}

impl<Hash: hash::Hash + Ord + Eq + Clone> Pool<Hash> {
	pub fn new<F>(hasher: F) -> Self
	where
		F: Fn(&UncheckedExtrinsic) -> Hash + 'static,
	{
		Pool {
			future: Default::default(),
			ready: Default::default(),
			insertion_id: Default::default(),
			hasher: Box::new(hasher),
		}
	}

	pub fn import(
		&mut self,
		block_number: BlockNumber,
		ex: UncheckedExtrinsic,
		priority: Priority,
		longevity: Longevity,
		requires: Vec<Tag>,
		provides: Vec<Tag>,
	) {
		let hash = (self.hasher)(&ex);
		let tx = Transaction { ex, priority, longevity, requires, provides };
		let tx = WaitingTransaction::new(tx, hash, self.ready.provided_tags());

		// Tags provided from ready queue satisfy all requirements, so just add to ready.
		if tx.is_ready() {
			self.insertion_id += 1;
			self.ready.import(tx, self.insertion_id, block_number);
			// TODO [ToDr] Check what transactions from future are unlocked.
		} else {
			self.future.import(tx);
		}
	}

	pub fn ready(&self) -> Vec<()> {
		self.ready.get().map(|_| ()).collect()
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	type Hash = u64;

	fn pool() -> Pool<Hash> {
		Pool::new(|ex| ex.0.len() as u64)
	}

	#[test]
	fn should_import_transaction_to_ready() {
		// given
		let mut pool = pool();

		// when
		pool.import(
			1,
			UncheckedExtrinsic(vec![1u8]),
			5u64,
			64u64,
			vec![],
			vec![vec![1]],
		);

		// then
		assert_eq!(pool.ready().len(), 1);
	}
}
