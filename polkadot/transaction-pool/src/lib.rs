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
extern crate substrate_extrinsic_pool as extrinsic_pool;
extern crate substrate_primitives as substrate_primitives;
extern crate substrate_runtime_primitives;
extern crate polkadot_runtime as runtime;
extern crate polkadot_primitives as primitives;
extern crate polkadot_api;

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

use codec::Slicable;
use extrinsic_pool::{Pool, txpool::{self, Readiness, scoring::{Change, Choice}}};
use polkadot_api::PolkadotApi;
use primitives::parachain::CandidateReceipt;
use primitives::{AccountId, Timestamp, Hash};
use runtime::{Block, UncheckedExtrinsic, TimestampCall, ParachainsCall, Call};
use substrate_primitives::block::{Extrinsic, ExtrinsicHash};
use substrate_primitives::hexdisplay::HexDisplay;
use substrate_runtime_primitives::traits::{Bounded, Checkable};

pub use extrinsic_pool::txpool::{Options, Status, LightStatus, VerifiedTransaction as VerifiedTransactionOps};
pub use error::{Error, ErrorKind, Result};

/// Useful functions for working with Polkadot blocks.
pub struct PolkadotBlock {
	block: Block,
	location: Option<(&'static str, usize)>,
}

impl PolkadotBlock {
	/// Create a new block, checking high-level well-formedness.
	pub fn from(unchecked: Block) -> ::std::result::Result<Self, Block> {
		if unchecked.extrinsics.len() < 2 {
			return Err(unchecked);
		}
		if unchecked.extrinsics[0].is_signed() {
			return Err(unchecked);
		}
		if unchecked.extrinsics[1].is_signed() {
			return Err(unchecked);
		}

		match unchecked.extrinsics[0].extrinsic.function {
			Call::Timestamp(TimestampCall::set(_)) => {},
			_ => return Err(unchecked),
		}

		match unchecked.extrinsics[1].extrinsic.function {
			Call::Parachains(ParachainsCall::set_heads(_)) => {},
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

	/// Retrieve the parachain candidates proposed for this block.
	pub fn parachain_heads(&self) -> &[CandidateReceipt] {
		if let Call::Parachains(ParachainsCall::set_heads(ref t)) = self.block.extrinsics[1].extrinsic.function {
			&t[..]
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

impl txpool::VerifiedTransaction for VerifiedTransaction {
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

impl txpool::Scoring<VerifiedTransaction> for Scoring {
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
		xts: &[txpool::Transaction<VerifiedTransaction>],
		scores: &mut [Self::Score],
		_change: Change<()>
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
	api: &'a T,
	known_indices: HashMap<AccountId, ::primitives::Index>,
}

impl<'a, T: 'a + PolkadotApi> Clone for Ready<'a, T> {
	fn clone(&self) -> Self {
		Ready {
			at_block: self.at_block.clone(),
			api: self.api,
			known_indices: self.known_indices.clone(),
		}
	}
}

impl<'a, T: 'a + PolkadotApi> Ready<'a, T> {
	/// Create a new readiness evaluator at the given block. Requires that
	/// the ID has already been checked for local corresponding and available state.
	pub fn create(at: T::CheckedBlockId, api: &'a T) -> Self {
		Ready {
			at_block: at,
			api,
			known_indices: HashMap::new(),
		}
	}
}

impl<'a, T: 'a + PolkadotApi> txpool::Ready<VerifiedTransaction> for Ready<'a, T> {
	fn is_ready(&mut self, xt: &VerifiedTransaction) -> Readiness {
		let sender = xt.inner.signed;
		trace!(target: "transaction-pool", "Checking readiness of {} (from {})", xt.hash, Hash::from(sender));

		// TODO: find a way to handle index error properly -- will need changes to
		// transaction-pool trait.
		let (api, at_block) = (&self.api, &self.at_block);
		let next_index = self.known_indices.entry(sender)
			.or_insert_with(|| api.index(at_block, sender).ok().unwrap_or_else(Bounded::max_value));

		trace!(target: "transaction-pool", "Next index for sender is {}; xt index is {}", next_index, xt.inner.index);

		let result = match xt.inner.index.cmp(&next_index) {
			Ordering::Greater => Readiness::Future,
			Ordering::Equal => Readiness::Ready,
			Ordering::Less => Readiness::Stale,
		};

		// remember to increment `next_index`
		*next_index = next_index.saturating_add(1);

		result
	}
}

pub struct Verifier;

impl txpool::Verifier<Extrinsic> for Verifier {
	type VerifiedTransaction = VerifiedTransaction;
	type Error = Error;

	fn verify_transaction(&self, xt: Extrinsic) -> Result<Self::VerifiedTransaction> {
		info!("Extrinsic submitted: {}", HexDisplay::from(&xt.0));
		let uxt = xt.using_encoded(|ref mut s| UncheckedExtrinsic::decode(s))
			.ok_or_else(|| ErrorKind::InvalidExtrinsicFormat)?;
		info!("Correctly formatted: {:?}", uxt);
		VerifiedTransaction::create(uxt)
	}
}

/// The polkadot transaction pool.
///
/// Wraps a `extrinsic_pool::Pool`.
pub struct TransactionPool {
	inner: Pool<Verifier, Scoring, Error>,
}

impl TransactionPool {
	/// Create a new transaction pool.
	pub fn new(options: Options) -> Self {
		TransactionPool {
			inner: Pool::new(options, Verifier, Scoring),
		}
	}

	pub fn import_unchecked_extrinsic(&self, uxt: UncheckedExtrinsic) -> Result<Arc<VerifiedTransaction>> {
		Ok(self.inner.import(VerifiedTransaction::create(uxt)?)?)
	}
}

impl Deref for TransactionPool {
	type Target = Pool<Verifier, Scoring, Error>;

	fn deref(&self) -> &Self::Target {
		&self.inner
	}
}

#[cfg(test)]
mod tests {
}

