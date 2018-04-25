// Copyright 2018 Parity Technologies (UK) Ltd.
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

extern crate ed25519;
extern crate substrate_codec as codec;
extern crate substrate_primitives as substrate_primitives;
extern crate substrate_runtime_primitives as substrate_runtime_primitives;
extern crate polkadot_runtime as runtime;
extern crate polkadot_primitives as primitives;
extern crate polkadot_api;
extern crate transaction_pool;

#[macro_use]
extern crate error_chain;

#[macro_use]
extern crate log;

mod error;

use std::collections::HashMap;
use std::cmp::Ordering;
use std::sync::Arc;

use polkadot_api::PolkadotApi;
use primitives::{Hash, AccountId, Timestamp};
use substrate_primitives::block::{Extrinsic, ExtrinsicHash};
use substrate_primitives::hexdisplay::HexDisplay;
use runtime::{Block, UncheckedExtrinsic, TimestampCall, Call};
use substrate_runtime_primitives::traits::Checkable;
use transaction_pool::{Pool, Readiness};
use transaction_pool::scoring::{Change, Choice};

pub use transaction_pool::{Options, Status, LightStatus, NoopListener, VerifiedTransaction as VerifiedTransactionOps};
pub use error::{Error, ErrorKind, Result};

/// Useful functions for working with Polkadot blocks.
pub struct PolkadotBlock {
	block: Block,
	location: Option<(&'static str, usize)>,
}

impl PolkadotBlock {
	/// Create a new block, checking high-level well-formedness.
	pub fn from(unchecked: Block) -> ::std::result::Result<Self, Block> {
		if unchecked.extrinsics.len() < 1 {
			return Err(unchecked);
		}
		if unchecked.extrinsics[0].is_signed() {
			return Err(unchecked);
		}
		match unchecked.extrinsics[0].extrinsic.function {
			Call::Timestamp(TimestampCall::set(_)) => {},
			_ => return Err(unchecked),
		}

		// any further checks...
		Ok(PolkadotBlock { block: unchecked, location: None })
	}

	/// Create a new block, skipping any high-level well-formedness checks. WARNING: This could
	/// result in internal functions panicking if the block is, in fact, not well-formed.
	pub fn force_from(known_good: Block, file: &'static str, line: usize) -> Self {
		PolkadotBlock { block: known_good, location: Some((file, line)) }
	}

	/// Retrieve the timestamp of a Polkadot block.
	pub fn timestamp(&self) -> Timestamp {
		if let Call::Timestamp(TimestampCall::set(t)) = self.block.extrinsics[0].extrinsic.function {
			t
		} else {
			if let Some((file, line)) = self.location {
				panic!("Invalid block used in `PolkadotBlock::force_from` at {}:{}", file, line);
			} else {
				panic!("Invalid block made it through the PolkadotBlock verification!?");
			}
		}
	}
}

#[macro_export]
macro_rules! assert_polkadot_block {
	($known_good:expr) => ( PolkadotBlock::force_from(known_good, file!(), line!()) )
}

impl ::std::ops::Deref for PolkadotBlock {
	type Target = Block;
	fn deref(&self) -> &Block {
		&self.block
	}
}

impl From<PolkadotBlock> for Block {
	fn from(pd: PolkadotBlock) -> Self {
		pd.block
	}
}

/// Iterator over pending transactions.
pub type PendingIterator<'a, C> =
	transaction_pool::PendingIterator<'a, VerifiedTransaction, Ready<'a, C>, Scoring, NoopListener>;

/// A verified transaction which should be includable and non-inherent.
#[derive(Debug, Clone)]
pub struct VerifiedTransaction {
	inner: <UncheckedExtrinsic as Checkable>::Checked,
	hash: ExtrinsicHash,
	encoded_size: usize,
}

impl VerifiedTransaction {
	/// Attempt to verify a transaction.
	fn create(xt: UncheckedExtrinsic) -> Result<Self> {
		if !xt.is_signed() {
			bail!(ErrorKind::IsInherent(xt))
		}

		let message = codec::Slicable::encode(&xt);
		match xt.check() {
			Ok(xt) => {
				let hash = substrate_primitives::hashing::blake2_256(&message);
				Ok(VerifiedTransaction {
					inner: xt,
					hash: hash.into(),
					encoded_size: message.len(),
				})
			}
			Err(xt) => Err(ErrorKind::BadSignature(xt).into()),
		}
	}

	/// Access the underlying transaction.
	pub fn as_transaction(&self) -> &UncheckedExtrinsic {
		self.as_ref().as_unchecked()
	}

	/// Consume the verified transaciton, yielding the unchecked counterpart.
	pub fn into_inner(self) -> <UncheckedExtrinsic as Checkable>::Checked {
		self.inner
	}

	/// Get the 256-bit hash of this transaction.
	pub fn hash(&self) -> &Hash {
		&self.hash
	}

	/// Get the account ID of the sender of this transaction.
	pub fn sender(&self) -> &AccountId {
		&self.inner.signed
	}

	/// Get encoded size of the transaction.
	pub fn encoded_size(&self) -> usize {
		self.encoded_size
	}
}

impl AsRef< <UncheckedExtrinsic as Checkable>::Checked > for VerifiedTransaction {
	fn as_ref(&self) -> &<UncheckedExtrinsic as Checkable>::Checked {
		&self.inner
	}
}

impl transaction_pool::VerifiedTransaction for VerifiedTransaction {
	type Hash = Hash;
	type Sender = AccountId;

	fn hash(&self) -> &Self::Hash {
		&self.hash
	}

	fn sender(&self) -> &Self::Sender {
		&self.inner.signed
	}

	fn mem_usage(&self) -> usize {
		1 // TODO
	}
}

/// Scoring implementation for polkadot transactions.
#[derive(Debug)]
pub struct Scoring;

impl transaction_pool::Scoring<VerifiedTransaction> for Scoring {
	type Score = u64;
	type Event = ();

	fn compare(&self, old: &VerifiedTransaction, other: &VerifiedTransaction) -> Ordering {
		old.inner.index.cmp(&other.inner.index)
	}

	fn choose(&self, _old: &VerifiedTransaction, _new: &VerifiedTransaction) -> Choice {
		Choice::InsertNew
	}

	fn update_scores(
		&self,
		xts: &[transaction_pool::Transaction<VerifiedTransaction>],
		scores: &mut [Self::Score],
		_change: Change
	) {
		for i in 0..xts.len() {
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
	known_indices: HashMap<AccountId, ::primitives::Index>,
}

impl<'a, T: 'a + PolkadotApi> Clone for Ready<'a, T> {
	fn clone(&self) -> Self {
		Ready {
			at_block: self.at_block.clone(),
			api_handle: self.api_handle,
			known_indices: self.known_indices.clone(),
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
			known_indices: HashMap::new(),
		}
	}
}

impl<'a, T: 'a + PolkadotApi> transaction_pool::Ready<VerifiedTransaction> for Ready<'a, T> {
	fn is_ready(&mut self, xt: &VerifiedTransaction) -> Readiness {
		let sender = xt.inner.signed;
		trace!(target: "transaction-pool", "Checking readiness of {} (from {})", xt.hash, Hash::from(sender));

		// TODO: find a way to handle index error properly -- will need changes to
		// transaction-pool trait.
		let (api_handle, at_block) = (&self.api_handle, &self.at_block);
		let next_index = self.known_indices.entry(sender)
			.or_insert_with(|| api_handle.index(at_block, sender).ok().unwrap_or_else(u64::max_value));

		trace!(target: "transaction-pool", "Next index for sender is {}; xt index is {}", next_index, xt.inner.index);

		match xt.inner.index.cmp(&next_index) {
			Ordering::Greater => Readiness::Future,
			Ordering::Equal => Readiness::Ready,
			Ordering::Less => Readiness::Stale,
		}
	}
}

/// The polkadot transaction pool.
///
/// Wraps a `transaction-pool::Pool`.
pub struct TransactionPool {
	inner: transaction_pool::Pool<VerifiedTransaction, Scoring>,
}

impl TransactionPool {
	/// Create a new transaction pool.
	pub fn new(options: Options) -> Self {
		TransactionPool {
			inner: Pool::new(NoopListener, Scoring, options),
		}
	}

	/// Verify and import a transaction into the pool.
	pub fn import(&mut self, xt: UncheckedExtrinsic) -> Result<Arc<VerifiedTransaction>> {
		let verified = VerifiedTransaction::create(xt)?;

		info!("Extrinsic verified {:?}. Importing...", verified);

		// TODO: just use a foreign link when the error type is made public.
		let hash = verified.hash.clone();
		self.inner.import(verified)
			.map_err(|e|
				match e {
					// TODO: make error types public in transaction_pool. For now just treat all errors as AlreadyImported
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
	pub fn remove(&mut self, hash: &Hash, is_valid: bool) -> Option<Arc<VerifiedTransaction>> {
		self.inner.remove(hash, is_valid)
	}

	/// Cull transactions from the queue.
	pub fn cull<T: PolkadotApi>(&mut self, senders: Option<&[AccountId]>, ready: Ready<T>) -> usize {
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

	/// Submit an extrinsic to the pool.
	pub fn submit_extrinsic(&mut self, xt: Extrinsic) -> Result<ExtrinsicHash> {
		info!("Extrinsic submitted: {}", HexDisplay::from(&xt.0));

		unimplemented!()
		// let xt = xt.using_encoded(|ref mut s| UncheckedExtrinsic::decode(s))
		// 	.ok_or_else(|| ErrorKind::InvalidExtrinsicFormat)?;
        //
		// info!("Correctly formatted: {:?}", xt);
		// self.import(xt)
		// 	.map(|vxt| vxt.extrinsic_hash)
	}
}

#[cfg(test)]
mod tests {
}
