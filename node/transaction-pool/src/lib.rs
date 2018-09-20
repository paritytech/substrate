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

extern crate substrate_client as client;
extern crate parity_codec as codec;
extern crate substrate_extrinsic_pool as extrinsic_pool;
extern crate substrate_primitives;
extern crate sr_primitives;
extern crate node_runtime as runtime;
extern crate node_primitives as primitives;
extern crate node_api;
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
	sync::Arc,
};

use codec::{Decode, Encode};
use extrinsic_pool::{Readiness, scoring::{Change, Choice}, VerifiedFor, ExtrinsicFor};
use node_api::Api;
use primitives::{AccountId, BlockId, Block, Hash, Index};
use runtime::{UncheckedExtrinsic, RawAddress};
use sr_primitives::traits::{Bounded, Checkable, Hash as HashT, BlakeTwo256};

pub use extrinsic_pool::{Options, Status, LightStatus, VerifiedTransaction as VerifiedTransactionOps};
pub use error::{Error, ErrorKind, Result};

/// Maximal size of a single encoded extrinsic.
const MAX_TRANSACTION_SIZE: usize = 4 * 1024 * 1024;

/// Type alias for the transaction pool.
pub type TransactionPool<A> = extrinsic_pool::Pool<ChainApi<A>>;

/// A verified transaction which should be includable and non-inherent.
#[derive(Clone, Debug)]
pub struct VerifiedTransaction {
	/// Transaction hash.
	pub hash: Hash,
	/// Transaction sender.
	pub sender: AccountId,
	/// Transaction index.
	pub index: Index,
	encoded_size: usize,
}

impl VerifiedTransaction {
	/// Get the 256-bit hash of this transaction.
	pub fn hash(&self) -> &Hash {
		&self.hash
	}

	/// Get the account ID of the sender of this transaction.
	pub fn index(&self) -> Index {
		self.index
	}

	/// Get encoded size of the transaction.
	pub fn encoded_size(&self) -> usize {
		self.encoded_size
	}
}

impl extrinsic_pool::VerifiedTransaction for VerifiedTransaction {
	type Hash = Hash;
	type Sender = AccountId;

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

/// The transaction pool logic.
pub struct ChainApi<A> {
	api: Arc<A>,
}

impl<A> ChainApi<A> where
	A: Api,
{
	/// Create a new instance.
	pub fn new(api: Arc<A>) -> Self {
		ChainApi {
			api,
		}
	}
}


impl<A> extrinsic_pool::ChainApi for ChainApi<A> where
	A: Api + Send + Sync,
{
	type Block = Block;
	type Hash = Hash;
	type Sender = AccountId;
	type VEx = VerifiedTransaction;
	type Ready = HashMap<AccountId, u64>;
	type Error = Error;
	type Score = u64;
	type Event = ();

	fn verify_transaction(&self, _at: &BlockId, xt: &ExtrinsicFor<Self>) -> Result<Self::VEx> {
		let encoded = xt.encode();
		let uxt = UncheckedExtrinsic::decode(&mut encoded.as_slice()).ok_or_else(|| ErrorKind::InvalidExtrinsicFormat)?;
		if !uxt.is_signed() {
			bail!(ErrorKind::IsInherent(uxt))
		}

		let (encoded_size, hash) = (encoded.len(), BlakeTwo256::hash(&encoded));
		if encoded_size > MAX_TRANSACTION_SIZE {
			bail!(ErrorKind::TooLarge(encoded_size, MAX_TRANSACTION_SIZE));
		}

		debug!(target: "transaction-pool", "Transaction submitted: {}", ::substrate_primitives::hexdisplay::HexDisplay::from(&encoded));
		let checked = uxt.clone().check_with(|a| {
			match a {
				RawAddress::Id(id) => Ok(id),
				RawAddress::Index(_) => Err("Index based addresses are not supported".into()),// TODO: Make index addressing optional in substrate
			}
		})?;
		let sender = checked.signed.expect("Only signed extrinsics are allowed at this point");


		if encoded_size < 1024 {
			debug!(target: "transaction-pool", "Transaction verified: {} => {:?}", hash, uxt);
		} else {
			debug!(target: "transaction-pool", "Transaction verified: {} ({} bytes is too large to display)", hash, encoded_size);
		}

		Ok(VerifiedTransaction {
			index: checked.index,
			sender,
			hash,
			encoded_size,
		})
	}

	fn ready(&self) -> Self::Ready {
		HashMap::default()
	}

	fn is_ready(&self, at: &BlockId, known_nonces: &mut Self::Ready, xt: &VerifiedFor<Self>) -> Readiness {
		let sender = xt.verified.sender().clone();
		trace!(target: "transaction-pool", "Checking readiness of {} (from {})", xt.verified.hash, sender);

		// TODO: find a way to handle index error properly -- will need changes to
		// transaction-pool trait.
		let api = &self.api;
		let next_index = known_nonces.entry(sender)
			.or_insert_with(|| api.index(at, sender).ok().unwrap_or_else(Bounded::max_value));

		trace!(target: "transaction-pool", "Next index for sender is {}; xt index is {}", next_index, xt.verified.index);

		let result = match xt.verified.index.cmp(&next_index) {
			// TODO: this won't work perfectly since accounts can now be killed, returning the nonce
			// to zero.
			// We should detect if the index was reset and mark all transactions as `Stale` for cull to work correctly.
			// Otherwise those transactions will keep occupying the queue.
			// Perhaps we could mark as stale if `index - state_index` > X?
			Ordering::Greater => Readiness::Future,
			Ordering::Equal => Readiness::Ready,
			// TODO [ToDr] Should mark transactions referencing too old blockhash as `Stale` as well.
			Ordering::Less => Readiness::Stale,
		};

		// remember to increment `next_index`
		*next_index = next_index.saturating_add(1);

		result
	}

	fn compare(old: &VerifiedFor<Self>, other: &VerifiedFor<Self>) -> Ordering {
		old.verified.index().cmp(&other.verified.index())
	}

	fn choose(old: &VerifiedFor<Self>, new: &VerifiedFor<Self>) -> Choice {
		if old.verified.index() == new.verified.index() {
			return Choice::ReplaceOld;
		}
		Choice::InsertNew
	}

	fn update_scores(
		xts: &[extrinsic_pool::Transaction<VerifiedFor<Self>>],
		scores: &mut [Self::Score],
		_change: Change<()>
	) {
		for i in 0..xts.len() {
			// all the same score since there are no fees.
			// TODO: prioritize things like misbehavior or fishermen reports
			scores[i] = 1;
		}
	}

	fn should_replace(_old: &VerifiedFor<Self>, _new: &VerifiedFor<Self>) -> Choice {
		// Don't allow new transactions if we are reaching the limit.
		Choice::RejectNew
	}
}

