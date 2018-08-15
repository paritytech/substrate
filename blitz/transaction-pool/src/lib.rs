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
extern crate substrate_client as client;
extern crate substrate_codec as codec;
extern crate substrate_extrinsic_pool as extrinsic_pool;
extern crate substrate_primitives;
extern crate substrate_runtime_primitives;
extern crate blitz_runtime as runtime;
extern crate blitz_primitives as primitives;
extern crate blitz_api;
extern crate parking_lot;

#[cfg(test)]
extern crate substrate_keyring;

#[macro_use]
extern crate error_chain;

#[macro_use]
extern crate log;

mod error;

use std::{
	cmp::Ordering,
	collections::HashMap,
	ops::Deref,
	sync::Arc,
};

use codec::{Decode, Encode};
use extrinsic_pool::{
	api::{ExtrinsicPool, EventStream},
	txpool::{self, Readiness, scoring::{Change, Choice}},
	watcher::Watcher,
	Pool,
	Listener,
};
use blitz_api::BlitzApi;
use primitives::{AccountId, BlockId, Hash, Index, UncheckedExtrinsic as FutureProofUncheckedExtrinsic};
use runtime::{Address, UncheckedExtrinsic};
use substrate_runtime_primitives::traits::{Bounded, Checkable, Hash as HashT, BlakeTwo256};

pub use extrinsic_pool::txpool::{Options, Status, LightStatus, VerifiedTransaction as VerifiedTransactionOps};
pub use error::{Error, ErrorKind, Result};

/// Type alias for convenience.
pub type CheckedExtrinsic = <UncheckedExtrinsic as Checkable<fn(Address) -> std::result::Result<AccountId, &'static str>>>::Checked;

/// A verified transaction which should be includable and non-inherent.
#[derive(Clone, Debug)]
pub struct VerifiedTransaction {
	original: UncheckedExtrinsic,
	inner: Option<CheckedExtrinsic>,
	sender: Option<AccountId>,
	hash: Hash,
	encoded_size: usize,
}

impl VerifiedTransaction {
	/// Access the underlying transaction.
	pub fn as_transaction(&self) -> &UncheckedExtrinsic {
		&self.original
	}

	/// Convert to primitive unchecked extrinsic.
	pub fn primitive_extrinsic(&self) -> ::primitives::UncheckedExtrinsic {
		Decode::decode(&mut self.as_transaction().encode().as_slice())
			.expect("UncheckedExtrinsic shares repr with Vec<u8>; qed")
	}

	/// Consume the verified transaction, yielding the checked counterpart.
	pub fn into_inner(self) -> Option<CheckedExtrinsic> {
		self.inner
	}

	/// Get the 256-bit hash of this transaction.
	pub fn hash(&self) -> &Hash {
		&self.hash
	}

	/// Get the account ID of the sender of this transaction.
	pub fn sender(&self) -> Option<AccountId> {
		self.sender
	}

	/// Get the account ID of the sender of this transaction.
	pub fn index(&self) -> Index {
		self.original.extrinsic.index
	}

	/// Get encoded size of the transaction.
	pub fn encoded_size(&self) -> usize {
		self.encoded_size
	}

	/// Returns `true` if the transaction is not yet fully verified.
	pub fn is_fully_verified(&self) -> bool {
		self.inner.is_some()
	}
}

impl txpool::VerifiedTransaction for VerifiedTransaction {
	type Hash = Hash;
	type Sender = Option<AccountId>;

	fn hash(&self) -> &Self::Hash {
		&self.hash
	}

	fn sender(&self) -> &Self::Sender {
		&self.sender
	}

	fn mem_usage(&self) -> usize {
		self.encoded_size // TODO
	}
}

/// Scoring implementation for blitz transactions.
#[derive(Debug)]
pub struct Scoring;

impl txpool::Scoring<VerifiedTransaction> for Scoring {
	type Score = u64;
	type Event = ();

	fn compare(&self, old: &VerifiedTransaction, other: &VerifiedTransaction) -> Ordering {
		old.index().cmp(&other.index())
	}

	fn choose(&self, old: &VerifiedTransaction, new: &VerifiedTransaction) -> Choice {
		if old.is_fully_verified() {
			assert!(new.is_fully_verified(), "Scoring::choose called with transactions from different senders");
			if old.index() == new.index() {
				// TODO [ToDr] Do we allow replacement? If yes then it should be Choice::ReplaceOld
				return Choice::RejectNew;
			}
		}

		// This will keep both transactions, even though they have the same indices.
		// It's fine for not fully verified transactions, we might also allow it for
		// verified transactions but it would mean that only one of the two is actually valid
		// (most likely the first to be included in the block).
		Choice::InsertNew
	}

	fn update_scores(
		&self,
		xts: &[txpool::Transaction<VerifiedTransaction>],
		scores: &mut [Self::Score],
		_change: Change<()>
	) {
		for i in 0..xts.len() {
			if !xts[i].is_fully_verified() {
				scores[i] = 0;
			} else {
				// all the same score since there are no fees.
				// TODO: prioritize things like misbehavior or fishermen reports
				scores[i] = 1;
			}
		}
	}

	fn should_replace(&self, old: &VerifiedTransaction, _new: &VerifiedTransaction) -> bool {
		// Always replace not fully verified transactions.
		!old.is_fully_verified()
	}
}

/// Readiness evaluator for blitz transactions.
pub struct Ready<'a, A: 'a + BlitzApi> {
	at_block: BlockId,
	api: &'a A,
	known_nonces: HashMap<AccountId, ::primitives::Index>,
}

impl<'a, A: 'a + BlitzApi> Ready<'a, A> {
	/// Create a new readiness evaluator at the given block. Requires that
	/// the ID has already been checked for local corresponding and available state.
	fn create(at: BlockId, api: &'a A) -> Self {
		Ready {
			at_block: at,
			api,
			known_nonces: HashMap::new(),
		}
	}
}

impl<'a, T: 'a + BlitzApi> Clone for Ready<'a, T> {
	fn clone(&self) -> Self {
		Ready {
			at_block: self.at_block.clone(),
			api: self.api,
			known_nonces: self.known_nonces.clone(),
		}
	}
}

impl<'a, A: 'a + BlitzApi> txpool::Ready<VerifiedTransaction> for Ready<'a, A>
{
	fn is_ready(&mut self, xt: &VerifiedTransaction) -> Readiness {
		let sender = match xt.sender() {
			Some(sender) => sender,
			None => return Readiness::Future
		};

		trace!(target: "transaction-pool", "Checking readiness of {} (from {})", xt.hash, Hash::from(sender));

		// TODO: find a way to handle index error properly -- will need changes to
		// transaction-pool trait.
		let (api, at_block) = (&self.api, &self.at_block);
		let next_index = self.known_nonces.entry(sender)
			.or_insert_with(|| api.index(at_block, sender).ok().unwrap_or_else(Bounded::max_value));

		trace!(target: "transaction-pool", "Next index for sender is {}; xt index is {}", next_index, xt.original.extrinsic.index);

		let result = match xt.original.extrinsic.index.cmp(&next_index) {
			// TODO: this won't work perfectly since accounts can now be killed, returning the nonce
			// to zero.
			// We should detect if the index was reset and mark all transactions as `Stale` for cull to work correctly.
			// Otherwise those transactions will keep occupying the queue.
			// Perhaps we could mark as stale if `index - state_index` > X?
			Ordering::Greater => Readiness::Future,
			Ordering::Equal => Readiness::Ready,
			// TODO [ToDr] Should mark transactions referrencing too old blockhash as `Stale` as well.
			Ordering::Less => Readiness::Stale,
		};

		// remember to increment `next_index`
		*next_index = next_index.saturating_add(1);

		result
	}
}

pub struct Verifier<'a, A: 'a> {
	api: &'a A,
	at_block: BlockId,
}

impl<'a, A> Verifier<'a, A> where
	A: 'a + BlitzApi,
{
	const NO_ACCOUNT: &'static str = "Account not found.";

	fn lookup(&self, address: Address) -> ::std::result::Result<AccountId, &'static str> {
		// TODO [ToDr] Consider introducing a cache for this.
		match self.api.lookup(&self.at_block, address.clone()) {
			Ok(Some(address)) => Ok(address),
			Ok(None) => Err(Self::NO_ACCOUNT.into()),
			Err(e) => {
				error!("Error looking up address: {:?}: {:?}", address, e);
				Err("API error.")
			},
		}
	}
}

impl<'a, A> txpool::Verifier<UncheckedExtrinsic> for Verifier<'a, A> where
	A: 'a + BlitzApi,
{
	type VerifiedTransaction = VerifiedTransaction;
	type Error = Error;

	fn verify_transaction(&self, uxt: UncheckedExtrinsic) -> Result<Self::VerifiedTransaction> {

		if !uxt.is_signed() {
			bail!(ErrorKind::IsInherent(uxt))
		}

		let encoded = uxt.encode();
		let (encoded_size, hash) = (encoded.len(), BlakeTwo256::hash(&encoded));
		
		debug!(target: "transaction-pool", "Transaction submitted: {}", ::substrate_primitives::hexdisplay::HexDisplay::from(&encoded));

		let inner = match uxt.clone().check_with(|a| self.lookup(a)) {
			Ok(xt) => Some(xt),
			// keep the transaction around in the future pool and attempt to promote it later.
			Err(Self::NO_ACCOUNT) => None,
			Err(e) => bail!(e),
		};
		let sender = inner.as_ref().map(|x| x.signed.clone());

		if encoded_size < 1024 {
			info!(target: "transaction-pool", "Transaction verified: {} => {:?}", hash, uxt);
		} else {
			info!(target: "transaction-pool", "Transaction verified: {} ({} bytes is too large to display)", hash, encoded_size);
		}

		Ok(VerifiedTransaction {
			original: uxt,
			inner,
			sender,
			hash,
			encoded_size
		})
	}
}

/// The blitz transaction pool.
///
/// Wraps a `extrinsic_pool::Pool`.
pub struct TransactionPool<A> {
	inner: Pool<Hash, VerifiedTransaction, Scoring, Error>,
	api: Arc<A>,
}

impl<A> TransactionPool<A> where
	A: BlitzApi,
{
	/// Create a new transaction pool.
	pub fn new(options: Options, api: Arc<A>) -> Self {
		TransactionPool {
			inner: Pool::new(options, Scoring),
			api,
		}
	}

	/// Attempt to directly import `UncheckedExtrinsic` without going through serialization.
	pub fn import_unchecked_extrinsic(&self, block: BlockId, uxt: UncheckedExtrinsic) -> Result<Arc<VerifiedTransaction>> {
		let verifier = Verifier {
			api: &*self.api,
			at_block: block,
		};
		self.inner.submit(verifier, vec![uxt]).map(|mut v| v.swap_remove(0))
	}

	/// Retry to import all semi-verified transactions (unknown account indices)
	pub fn retry_verification(&self, block: BlockId) -> Result<()> {
		let to_reverify = self.inner.remove_sender(None);
		let verifier = Verifier {
			api: &*self.api,
			at_block: block,
		};

		self.inner.submit(verifier, to_reverify.into_iter().map(|tx| tx.original.clone()))?;
		Ok(())
	}

	/// Reverify transaction that has been reported incorrect.
	///
	/// Returns `Ok(None)` in case the hash is missing, `Err(e)` in case of verification error and new transaction
	/// reference otherwise.
	///
	/// TODO [ToDr] That method is currently unused, should be used together with BlockBuilder
	/// when we detect that particular transaction has failed.
	/// In such case we will attempt to remove or re-verify it.
	pub fn reverify_transaction(&self, block: BlockId, hash: Hash) -> Result<Option<Arc<VerifiedTransaction>>> {
		let result = self.inner.remove(&[hash], false).pop().expect("One hash passed; one result received; qed");
		if let Some(tx) = result {
			self.import_unchecked_extrinsic(block, tx.original.clone()).map(Some)
		} else {
			Ok(None)
		}
	}

	/// Cull old transactions from the queue.
	pub fn cull(&self, block: BlockId) -> Result<usize> {
		let ready = Ready::create(block, &*self.api);
		Ok(self.inner.cull(None, ready))
	}

	/// Cull transactions from the queue and then compute the pending set.
	pub fn cull_and_get_pending<F, T>(&self, block: BlockId, f: F) -> Result<T> where
		F: FnOnce(txpool::PendingIterator<VerifiedTransaction, Ready<A>, Scoring, Listener<Hash>>) -> T,
	{
		let ready = Ready::create(block, &*self.api);
		self.inner.cull(None, ready.clone());
		Ok(self.inner.pending(ready, f))
	}

	/// Remove a set of transactions idenitified by hashes.
	pub fn remove(&self, hashes: &[Hash], is_valid: bool) -> Vec<Option<Arc<VerifiedTransaction>>> {
		self.inner.remove(hashes, is_valid)
	}
}

impl<A> Deref for TransactionPool<A> {
	type Target = Pool<Hash, VerifiedTransaction, Scoring, Error>;

	fn deref(&self) -> &Self::Target {
		&self.inner
	}
}

// TODO: more general transaction pool, which can handle more kinds of vec-encoded transactions,
// even when runtime is out of date.
impl<A> ExtrinsicPool<FutureProofUncheckedExtrinsic, BlockId, Hash> for TransactionPool<A> where
	A: Send + Sync + 'static,
	A: BlitzApi,
{
	type Error = Error;

	fn submit(&self, block: BlockId, xts: Vec<FutureProofUncheckedExtrinsic>) -> Result<Vec<Hash>> {
		xts.into_iter()
			.map(|xt| xt.encode())
			.map(|encoded| {
				let decoded = UncheckedExtrinsic::decode(&mut &encoded[..]).ok_or(ErrorKind::InvalidExtrinsicFormat)?;
				let tx = self.import_unchecked_extrinsic(block, decoded)?;
				Ok(*tx.hash())
			})
			.collect()
	}

	fn submit_and_watch(&self, block: BlockId, xt: FutureProofUncheckedExtrinsic) -> Result<Watcher<Hash>> {
		let encoded = xt.encode();
		let decoded = UncheckedExtrinsic::decode(&mut &encoded[..]).ok_or(ErrorKind::InvalidExtrinsicFormat)?;

		let verifier = Verifier {
			api: &*self.api,
			at_block: block,
		};

		self.inner.submit_and_watch(verifier, decoded)
	}

	fn light_status(&self) -> LightStatus {
		self.inner.light_status()
	}

	fn import_notification_stream(&self) -> EventStream {
		self.inner.import_notification_stream()
	}
}
