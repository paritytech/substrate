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
extern crate substrate_transaction_pool as transaction_pool;
extern crate substrate_primitives;
extern crate sr_primitives;
extern crate node_runtime as runtime;
extern crate node_primitives as primitives;

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
use client::{Client as SubstrateClient, CallExecutor};
use client::runtime_api::OldTxQueue;
use transaction_pool::{Readiness, scoring::{Change, Choice}, VerifiedFor, ExtrinsicFor};
use primitives::{AccountId, Hash, Index};
use runtime::{Address, UncheckedExtrinsic};
use substrate_primitives::{Blake2Hasher};
use sr_primitives::generic::BlockId;
use sr_primitives::traits::{
	Bounded, Checkable, Block as BlockT, Hash as HashT, Header as HeaderT, BlakeTwo256, Lookup, CurrentHeight,
	BlockNumberToHash
};

pub use transaction_pool::{Options, Status, LightStatus, VerifiedTransaction as VerifiedTransactionOps};
pub use error::{Error, ErrorKind, Result};

/// Maximal size of a single encoded extrinsic.
const MAX_TRANSACTION_SIZE: usize = 4 * 1024 * 1024;

/// Local client abstraction for the transaction-pool.
pub trait Client:
	Send
	+ Sync
	+ CurrentHeight<BlockNumber=<<<Self as Client>::Block as BlockT>::Header as HeaderT>::Number>
	+ BlockNumberToHash<BlockNumber=<<<Self as Client>::Block as BlockT>::Header as HeaderT>::Number, Hash=<<Self as Client>::Block as BlockT>::Hash>
	+ OldTxQueue<<Self as Client>::Block>
{
	/// The block used for this API type.
	type Block: BlockT;
}

impl<B, E, Block> Client for SubstrateClient<B, E, Block> where
	B: client::backend::Backend<Block, Blake2Hasher> + Send + Sync + 'static,
	E: CallExecutor<Block, Blake2Hasher> + Send + Sync + Clone + 'static,
	Block: BlockT,
{
	type Block = Block;
}

/// Type alias for the transaction pool.
pub type TransactionPool<C> = transaction_pool::Pool<ChainApi<C>>;

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

impl transaction_pool::VerifiedTransaction for VerifiedTransaction {
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
pub struct ChainApi<C: Client> {
	api: Arc<C>,
}

impl<C: Client> ChainApi<C> {
	/// Create a new instance.
	pub fn new(api: Arc<C>) -> Self {
		ChainApi {
			api,
		}
	}
}

/// "Chain" context (used for checking transactions) which uses data local to our node/transaction pool.
///
/// This is due for removal when #721 lands
pub struct LocalContext<'a, A: 'a>(&'a Arc<A>);
impl<'a, C: 'a + Client> CurrentHeight for LocalContext<'a, C> {
	type BlockNumber = <C as CurrentHeight>::BlockNumber;
	fn current_height(&self) -> Self::BlockNumber {
		self.0.current_height()
	}
}
impl<'a, C: 'a + Client> BlockNumberToHash for LocalContext<'a, C> {
	type BlockNumber = <C as BlockNumberToHash>::BlockNumber;
	type Hash = <C as BlockNumberToHash>::Hash;
	fn block_number_to_hash(&self, n: Self::BlockNumber) -> Option<Self::Hash> {
		self.0.block_number_to_hash(n)
	}
}
impl<'a, C: 'a + Client> Lookup for LocalContext<'a, C> {
	type Source = Address;
	type Target = AccountId;
	fn lookup(&self, a: Address) -> ::std::result::Result<AccountId, &'static str> {
		self.0.lookup_address(&BlockId::number(self.current_height()), a).unwrap_or(None).ok_or("error with lookup")
	}
}

impl<C: Client> transaction_pool::ChainApi for ChainApi<C> {
	type Block = C::Block;
	type Hash = Hash;
	type Sender = AccountId;
	type VEx = VerifiedTransaction;
	type Ready = HashMap<AccountId, u64>;
	type Error = Error;
	type Score = u64;
	type Event = ();

	fn latest_hash(&self) -> <C::Block as BlockT>::Hash {
		self.api.block_number_to_hash(self.api.current_height()).expect("Latest block number always has a hash; qed")
	}

	fn verify_transaction(&self, _at: &BlockId<Self::Block>, xt: &ExtrinsicFor<Self>) -> Result<Self::VEx> {
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
		let checked = uxt.clone().check(&LocalContext(&self.api))?;
		let (sender, index) = checked.signed.expect("function previously bailed unless uxt.is_signed(); qed");


		if encoded_size < 1024 {
			debug!(target: "transaction-pool", "Transaction verified: {} => {:?}", hash, uxt);
		} else {
			debug!(target: "transaction-pool", "Transaction verified: {} ({} bytes is too large to display)", hash, encoded_size);
		}

		Ok(VerifiedTransaction {
			index,
			sender,
			hash,
			encoded_size,
		})
	}

	fn ready(&self) -> Self::Ready {
		HashMap::default()
	}

	fn is_ready(&self, at: &BlockId<Self::Block>, known_nonces: &mut Self::Ready, xt: &VerifiedFor<Self>) -> Readiness {
		let sender = xt.verified.sender().clone();
		trace!(target: "transaction-pool", "Checking readiness of {} (from {})", xt.verified.hash, sender);

		// TODO: find a way to handle index error properly -- will need changes to
		// transaction-pool trait.
		let api = &self.api;
		let next_index = known_nonces.entry(sender)
			.or_insert_with(|| api.account_nonce(at, sender).ok().unwrap_or_else(Bounded::max_value));

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
		xts: &[transaction_pool::Transaction<VerifiedFor<Self>>],
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
