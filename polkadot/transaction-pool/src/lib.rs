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
extern crate substrate_codec as codec;
extern crate ed25519;

#[macro_use]
extern crate error_chain;

use std::collections::HashMap;
use std::cmp::Ordering;
use std::sync::Arc;

use polkadot_api::PolkadotApi;
use primitives::AccountId;
use primitives::block::Id as BlockId;
use primitives::transaction::UncheckedTransaction;
use transaction_pool::Readiness;
use transaction_pool::scoring::{Change, Choice};

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
	}
}

/// A verified transaction which should be includable and non-inherent.
#[derive(Debug, Clone)]
pub struct VerifiedTransaction(UncheckedTransaction);

impl VerifiedTransaction {
	/// Attempt to verify a transaction.
	pub fn create(tx: UncheckedTransaction) -> Result<Self> {
		if tx.is_inherent() {
			bail!(ErrorKind::IsInherent(tx))
		}

		let message = codec::Slicable::encode(&tx);
		if ed25519::verify(&*tx.signature, &message, &tx.transaction.signed[..]) {
			Ok(VerifiedTransaction(tx))
		} else {
			Err(ErrorKind::BadSignature(tx).into())
		}
	}

	/// Consume the verified transaciton, yielding the unchecked counterpart.
	pub fn into_inner(self) -> UncheckedTransaction {
		self.0
	}
}

/// Scoring implementation for polkadot transactions.
pub struct Scoring;

impl transaction_pool::Scoring<VerifiedTransaction> for Scoring {
    type Score = u64;

    fn compare(&self, old: &VerifiedTransaction, other: &VerifiedTransaction) -> Ordering {
		old.0.transaction.nonce.cmp(&other.0.transaction.nonce)
	}

    fn choose(&self, old: &VerifiedTransaction, new: &VerifiedTransaction) -> Choice {
		if old.0.transaction.nonce == new.0.transaction.nonce {
			Choice::RejectNew // no fees to determine which is better
		} else {
			Choice::InsertNew
		}
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

impl<'a, T: 'a + PolkadotApi> Ready<'a, T> {
	/// Create a new readiness evaluator at the given block.
	pub fn create(at: BlockId, client: &'a T) -> polkadot_api::Result<Self> {
		client.check_id(at).map(|id| Ready {
			at_block: id,
			api_handle: client,
			known_nonces: HashMap::new(),
		})
	}
}

impl<'a, T: 'a + PolkadotApi> transaction_pool::Ready<VerifiedTransaction> for Ready<'a, T> {
	fn is_ready(&mut self, tx: &VerifiedTransaction) -> Readiness {
		let sender = tx.0.transaction.signed;

		// TODO: find a way to handle nonce error properly -- will need changes to
		// transaction-pool trait.
		let (api_handle, at_block) = (&self.api_handle, &self.at_block);
		let next_nonce = self.known_nonces.entry(sender)
			.or_insert_with(|| api_handle.nonce(at_block, sender).ok().unwrap_or_else(u64::max_value));

		*next_nonce += 1;

		match tx.0.transaction.nonce.cmp(&next_nonce) {
			Ordering::Greater => Readiness::Future,
			Ordering::Equal => Readiness::Ready,
			Ordering::Less => Readiness::Stalled,
		}
	}
}

#[cfg(test)]
mod tests {
}
