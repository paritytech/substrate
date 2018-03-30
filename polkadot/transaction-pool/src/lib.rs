// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

extern crate transaction_pool;
extern crate polkadot_api;
extern crate polkadot_primitives as primitives;
extern crate substrate_primitives as substrate_primitives;
extern crate substrate_codec as codec;
extern crate ed25519;
extern crate ethereum_types;

#[macro_use]
extern crate error_chain;

use std::collections::HashMap;
use std::cmp::Ordering;
use std::sync::Arc;

use polkadot_api::PolkadotApi;
use primitives::AccountId;
use primitives::transaction::UncheckedTransaction;
use transaction_pool::{Pool, Readiness};
use transaction_pool::scoring::{Change, Choice};

// TODO: make queue generic over hash and sender so we don't need ethereum-types
pub use ethereum_types::{Address as TruncatedAccountId, H256 as TransactionHash};
pub use transaction_pool::{Options, Status, LightStatus, NoopListener, VerifiedTransaction as VerifiedTransactionOps};

/// Truncate an account ID to 160 bits.
pub fn truncate_id(id: &AccountId) -> TruncatedAccountId {
	TruncatedAccountId::from_slice(&id[..20])
}

/// Iterator over pending transactions.
pub type PendingIterator<'a, C> =
	transaction_pool::PendingIterator<'a, VerifiedTransaction, Ready<'a, C>, Scoring, NoopListener>;

error_chain! {
	errors {
		/// Attempted to queue an inherent transaction.
		IsInherent(tx: UncheckedTransaction) {
			description("Inherent transactions cannot be queued."),
			display("Inehrent transactions cannot be queued."),
		}
		/// Attempted to queue a transaction with bad signature.
		BadSignature(tx: UncheckedTransaction) {
			description("Transaction had bad signature."),
			display("Transaction had bad signature."),
		}
		/// Attempted to queue a transaction that is already in the pool.
		AlreadyImported(hash: TransactionHash) {
			description("Transaction is already in the pool."),
			display("Transaction {:?} is already in the pool.", hash),
		}
		/// Import error.
		Import(err: Box<::std::error::Error + Send>) {
			description("Error importing transaction"),
			display("Error importing transaction: {}", err.description()),
		}
	}
}

/// A verified transaction which should be includable and non-inherent.
#[derive(Debug, Clone)]
pub struct VerifiedTransaction {
	inner: UncheckedTransaction,
	hash: TransactionHash,
	address: TruncatedAccountId,
	insertion_id: u64,
	encoded_size: usize,
}

impl VerifiedTransaction {
	/// Attempt to verify a transaction.
	fn create(tx: UncheckedTransaction, insertion_id: u64) -> Result<Self> {
		if tx.is_inherent() {
			bail!(ErrorKind::IsInherent(tx))
		}

		let message = codec::Slicable::encode(&tx);
		if ed25519::verify(&*tx.signature, &message, &tx.transaction.signed[..]) {
			// TODO: make transaction-pool use generic types.
			let hash = substrate_primitives::hashing::blake2_256(&message);
			let address = truncate_id(&tx.transaction.signed);
			Ok(VerifiedTransaction {
				inner: tx,
				hash: hash.into(),
				encoded_size: message.len(),
				address,
				insertion_id,
			})
		} else {
			Err(ErrorKind::BadSignature(tx).into())
		}
	}

	/// Access the underlying transaction.
	pub fn as_transaction(&self) -> &UncheckedTransaction {
		self.as_ref()
	}

	/// Consume the verified transaciton, yielding the unchecked counterpart.
	pub fn into_inner(self) -> UncheckedTransaction {
		self.inner
	}

	/// Get the 256-bit hash of this transaction.
	pub fn hash(&self) -> &TransactionHash {
		&self.hash
	}

	/// Get the truncated account ID of the sender of this transaction.
	pub fn sender(&self) -> &TruncatedAccountId {
		&self.address
	}

	/// Get encoded size of the transaction.
	pub fn encoded_size(&self) -> usize {
		self.encoded_size
	}
}

impl AsRef<UncheckedTransaction> for VerifiedTransaction {
	fn as_ref(&self) -> &UncheckedTransaction {
		&self.inner
	}
}

impl transaction_pool::VerifiedTransaction for VerifiedTransaction {
	fn hash(&self) -> &TransactionHash {
		&self.hash
	}

	fn sender(&self) -> &TruncatedAccountId {
		&self.address
	}

	fn mem_usage(&self) -> usize {
		1 // TODO
	}

	fn insertion_id(&self) -> u64 {
		self.insertion_id
	}
}

/// Scoring implementation for polkadot transactions.
pub struct Scoring;

impl transaction_pool::Scoring<VerifiedTransaction> for Scoring {
	type Score = u64;

	fn compare(&self, old: &VerifiedTransaction, other: &VerifiedTransaction) -> Ordering {
		old.inner.transaction.nonce.cmp(&other.inner.transaction.nonce)
	}

	fn choose(&self, _old: &VerifiedTransaction, _new: &VerifiedTransaction) -> Choice {
		Choice::InsertNew
	}

	fn update_scores(
		&self,
		txs: &[Arc<VerifiedTransaction>],
		scores: &mut [Self::Score],
		_change: Change
	) {
		for i in 0..txs.len() {
			// all the same score since there are no fees.
			// TODO: prioritize things like misbehavior or fishermen reports
			scores[i] = 1;
		}
	}
	fn should_replace(&self, _old: &VerifiedTransaction, _new: &VerifiedTransaction) -> bool {
		false // no fees to determine which is better.
	}
}

/// Readiness evaluator for polkadot transactions.
pub struct Ready<'a, T: 'a + PolkadotApi> {
	at_block: T::CheckedBlockId,
	api_handle: &'a T,
	known_nonces: HashMap<AccountId, ::primitives::TxOrder>,
}

impl<'a, T: 'a + PolkadotApi> Clone for Ready<'a, T> {
	fn clone(&self) -> Self {
		Ready {
			at_block: self.at_block.clone(),
			api_handle: self.api_handle,
			known_nonces: self.known_nonces.clone(),
		}
	}
}

impl<'a, T: 'a + PolkadotApi> Ready<'a, T> {
	/// Create a new readiness evaluator at the given block. Requires that
	/// the ID has already been checked for local corresponding and available state.
	pub fn create(at: T::CheckedBlockId, client: &'a T) -> Self {
		Ready {
			at_block: at,
			api_handle: client,
			known_nonces: HashMap::new(),
		}
	}
}

impl<'a, T: 'a + PolkadotApi> transaction_pool::Ready<VerifiedTransaction> for Ready<'a, T> {
	fn is_ready(&mut self, tx: &VerifiedTransaction) -> Readiness {
		let sender = tx.inner.transaction.signed;

		// TODO: find a way to handle nonce error properly -- will need changes to
		// transaction-pool trait.
		let (api_handle, at_block) = (&self.api_handle, &self.at_block);
		let next_nonce = self.known_nonces.entry(sender)
			.or_insert_with(|| api_handle.nonce(at_block, sender).ok().unwrap_or_else(u64::max_value));

		*next_nonce += 1;

		match tx.inner.transaction.nonce.cmp(&next_nonce) {
			Ordering::Greater => Readiness::Future,
			Ordering::Equal => Readiness::Ready,
			Ordering::Less => Readiness::Stalled,
		}
	}
}

/// The polkadot transaction pool.
///
/// Wraps a `transaction-pool::Pool`.
pub struct TransactionPool {
	inner: transaction_pool::Pool<VerifiedTransaction, Scoring>,
	insertion_index: u64, // TODO: use AtomicU64 when it stabilizes
}

impl TransactionPool {
	/// Create a new transaction pool.
	pub fn new(options: Options) -> Self {
		TransactionPool {
			inner: Pool::new(NoopListener, Scoring, options),
			insertion_index: 0,
		}
	}

	/// Verify and import a transaction into the pool.
	pub fn import(&mut self, tx: UncheckedTransaction) -> Result<Arc<VerifiedTransaction>> {
		let insertion_index = self.insertion_index;
		self.insertion_index += 1;

		let verified = VerifiedTransaction::create(tx, insertion_index)?;

		// TODO: just use a foreign link when the error type is made public.
		let hash = verified.hash.clone();
		self.inner.import(verified)
			.map_err(|e|
				match e {
					// TODO: make error types public in transaction_pool. For now just treat all errors as AlradyImported
					_ => ErrorKind::AlreadyImported(hash),
					// transaction_pool::error::AlreadyImported(h) => ErrorKind::AlreadyImported(h),
					// e => ErrorKind::Import(Box::new(e)),
				})
			.map_err(Into::into)
	}

	/// Clear the pool.
	pub fn clear(&mut self) {
		self.inner.clear();
	}

	/// Remove from the pool.
	pub fn remove(&mut self, hash: &TransactionHash, is_valid: bool) -> Option<Arc<VerifiedTransaction>> {
		self.inner.remove(hash, is_valid)
	}

	/// Cull transactions from the queue.
	pub fn cull<T: PolkadotApi>(&mut self, senders: Option<&[TruncatedAccountId]>, ready: Ready<T>) -> usize {
		self.inner.cull(senders, ready)
	}

	/// Get an iterator of pending transactions.
	pub fn pending<'a, T: 'a + PolkadotApi>(&'a self, ready: Ready<'a, T>) -> PendingIterator<'a, T> {
		self.inner.pending(ready)
	}

	/// Get the full status of the queue (including readiness)
	pub fn status<T: PolkadotApi>(&self, ready: Ready<T>) -> Status {
		self.inner.status(ready)
	}

	/// Returns light status of the pool.
	pub fn light_status(&self) -> LightStatus {
		self.inner.light_status()
	}
}

#[cfg(test)]
mod tests {
}
