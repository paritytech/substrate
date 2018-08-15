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
extern crate polkadot_runtime as runtime;
extern crate polkadot_primitives as primitives;
extern crate polkadot_api;
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
	collections::{BTreeMap, HashMap},
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
use polkadot_api::PolkadotApi;
use primitives::{AccountId, BlockId, Hash, Index, UncheckedExtrinsic as FutureProofUncheckedExtrinsic};
use runtime::{Address, UncheckedExtrinsic};
use substrate_primitives::Bytes;
use substrate_runtime_primitives::traits::{Bounded, Checkable, Hash as HashT, BlakeTwo256};

pub use extrinsic_pool::txpool::{Options, Status, LightStatus, VerifiedTransaction as VerifiedTransactionOps};
pub use error::{Error, ErrorKind, Result};

/// Maximal size of a single encoded extrinsic.
///
/// See also polkadot-consensus::MAX_TRANSACTIONS_SIZE
const MAX_TRANSACTION_SIZE: usize = 4 * 1024 * 1024;

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

/// Scoring implementation for polkadot transactions.
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

	fn should_replace(&self, old: &VerifiedTransaction, _new: &VerifiedTransaction) -> Choice {
		// Always replace not fully verified transactions.
		match old.is_fully_verified() {
			true => Choice::RejectNew,
			false => Choice::ReplaceOld
		}
	}
}

/// Readiness evaluator for polkadot transactions.
pub struct Ready<'a, A: 'a + PolkadotApi> {
	at_block: BlockId,
	api: &'a A,
	known_nonces: HashMap<AccountId, ::primitives::Index>,
}

impl<'a, A: 'a + PolkadotApi> Ready<'a, A> {
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

impl<'a, T: 'a + PolkadotApi> Clone for Ready<'a, T> {
	fn clone(&self) -> Self {
		Ready {
			at_block: self.at_block.clone(),
			api: self.api,
			known_nonces: self.known_nonces.clone(),
		}
	}
}

impl<'a, A: 'a + PolkadotApi> txpool::Ready<VerifiedTransaction> for Ready<'a, A>
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
	A: 'a + PolkadotApi,
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
	A: 'a + PolkadotApi,
{
	type VerifiedTransaction = VerifiedTransaction;
	type Error = Error;

	fn verify_transaction(&self, uxt: UncheckedExtrinsic) -> Result<Self::VerifiedTransaction> {
		if !uxt.is_signed() {
			bail!(ErrorKind::IsInherent(uxt))
		}

		let encoded = uxt.encode();
		let encoded_size = encoded.len();

		if encoded_size > MAX_TRANSACTION_SIZE {
			bail!(ErrorKind::TooLarge(encoded_size, MAX_TRANSACTION_SIZE));
		}

		let hash = BlakeTwo256::hash(&encoded);
		debug!(target: "transaction-pool", "Transaction submitted: {}", ::substrate_primitives::hexdisplay::HexDisplay::from(&encoded));

		let inner = match uxt.clone().check_with(|a| self.lookup(a)) {
			Ok(xt) => Some(xt),
			// keep the transaction around in the future pool and attempt to promote it later.
			Err(Self::NO_ACCOUNT) => None,
			Err(e) => bail!(e),
		};
		let sender = inner.as_ref().map(|x| x.signed.clone());

		if encoded_size < 1024 {
			debug!(target: "transaction-pool", "Transaction verified: {} => {:?}", hash, uxt);
		} else {
			debug!(target: "transaction-pool", "Transaction verified: {} ({} bytes is too large to display)", hash, encoded_size);
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

/// The polkadot transaction pool.
///
/// Wraps a `extrinsic_pool::Pool`.
pub struct TransactionPool<A> {
	inner: Pool<Hash, VerifiedTransaction, Scoring, Error>,
	api: Arc<A>,
}

impl<A> TransactionPool<A> where
	A: PolkadotApi,
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
	A: PolkadotApi,
{
	type Error = Error;
	type InPool = BTreeMap<AccountId, Vec<Bytes>>;

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

	fn all(&self) -> Self::InPool {
		self.inner.all(|it| it.fold(Default::default(), |mut map: Self::InPool, tx| {
			// Map with `null` key is not serializable, so we fallback to default accountId.
			map.entry(tx.sender().unwrap_or_default())
				.or_insert_with(Vec::new)
				// use bytes type to make it serialize nicer.
				.push(Bytes(tx.primitive_extrinsic()));
			map
		}))
	}
}

#[cfg(test)]
mod tests {
	use std::sync::{atomic::{self, AtomicBool}, Arc};
	use super::TransactionPool;
	use substrate_keyring::Keyring::{self, *};
	use codec::{Decode, Encode};
	use polkadot_api::{PolkadotApi, BlockBuilder, Result};
	use primitives::{AccountId, AccountIndex, Block, BlockId, Hash, Index, SessionKey,
		UncheckedExtrinsic as FutureProofUncheckedExtrinsic};
	use runtime::{RawAddress, Call, TimestampCall, BareExtrinsic, Extrinsic, UncheckedExtrinsic};
	use primitives::parachain::{DutyRoster, Id as ParaId};
	use substrate_runtime_primitives::{MaybeUnsigned, generic};

	struct TestBlockBuilder;
	impl BlockBuilder for TestBlockBuilder {
		fn push_extrinsic(&mut self, _extrinsic: FutureProofUncheckedExtrinsic) -> Result<()> { unimplemented!() }
		fn bake(self) -> Result<Block> { unimplemented!() }
	}

	fn number_of(at: &BlockId) -> u32 {
		match at {
			generic::BlockId::Number(n) => *n as u32,
			_ => 0,
		}
	}

	#[derive(Default, Clone)]
	struct TestPolkadotApi {
		no_lookup: Arc<AtomicBool>,
	}

	impl TestPolkadotApi {
		fn without_lookup() -> Self {
			TestPolkadotApi {
				no_lookup: Arc::new(AtomicBool::new(true)),
			}
		}

		pub fn enable_lookup(&self) {
			self.no_lookup.store(false, atomic::Ordering::SeqCst);
		}
	}

	impl PolkadotApi for TestPolkadotApi {
		type BlockBuilder = TestBlockBuilder;

		fn session_keys(&self, _at: &BlockId) -> Result<Vec<SessionKey>> { unimplemented!() }
		fn validators(&self, _at: &BlockId) -> Result<Vec<AccountId>> { unimplemented!() }
		fn random_seed(&self, _at: &BlockId) -> Result<Hash> { unimplemented!() }
		fn duty_roster(&self, _at: &BlockId) -> Result<DutyRoster> { unimplemented!() }
		fn timestamp(&self, _at: &BlockId) -> Result<u64> { unimplemented!() }
		fn evaluate_block(&self, _at: &BlockId, _block: Block) -> Result<bool> { unimplemented!() }
		fn active_parachains(&self, _at: &BlockId) -> Result<Vec<ParaId>> { unimplemented!() }
		fn parachain_code(&self, _at: &BlockId, _parachain: ParaId) -> Result<Option<Vec<u8>>> { unimplemented!() }
		fn parachain_head(&self, _at: &BlockId, _parachain: ParaId) -> Result<Option<Vec<u8>>> { unimplemented!() }
		fn build_block(&self, _at: &BlockId, _inherent: ::primitives::InherentData) -> Result<Self::BlockBuilder> { unimplemented!() }
		fn inherent_extrinsics(&self, _at: &BlockId, _inherent: ::primitives::InherentData) -> Result<Vec<Vec<u8>>> { unimplemented!() }

		fn index(&self, _at: &BlockId, _account: AccountId) -> Result<Index> {
			Ok((_account[0] as u32) + number_of(_at))
		}
		fn lookup(&self, _at: &BlockId, _address: RawAddress<AccountId, AccountIndex>) -> Result<Option<AccountId>> {
			match _address {
				RawAddress::Id(i) => Ok(Some(i)),
				RawAddress::Index(_) if self.no_lookup.load(atomic::Ordering::SeqCst) => Ok(None),
				RawAddress::Index(i) => Ok(match (i < 8, i + (number_of(_at) as u64) % 8) {
					(false, _) => None,
					(_, 0) => Some(Alice.to_raw_public().into()),
					(_, 1) => Some(Bob.to_raw_public().into()),
					(_, 2) => Some(Charlie.to_raw_public().into()),
					(_, 3) => Some(Dave.to_raw_public().into()),
					(_, 4) => Some(Eve.to_raw_public().into()),
					(_, 5) => Some(Ferdie.to_raw_public().into()),
					(_, 6) => Some(One.to_raw_public().into()),
					(_, 7) => Some(Two.to_raw_public().into()),
					_ => None,
				}),
			}
		}
	}

	fn uxt(who: Keyring, nonce: Index, use_id: bool) -> UncheckedExtrinsic {
		let sxt = BareExtrinsic {
			signed: who.to_raw_public().into(),
			index: nonce,
			function: Call::Timestamp(TimestampCall::set(0)),
		};
		let sig = sxt.using_encoded(|e| who.sign(e));
		UncheckedExtrinsic::new(Extrinsic {
			signed: if use_id { RawAddress::Id(sxt.signed) } else { RawAddress::Index(
				match who {
					Alice => 0,
					Bob => 1,
					Charlie => 2,
					Dave => 3,
					Eve => 4,
					Ferdie => 5,
					One => 6,
					Two => 7,
				}
			)},
			index: sxt.index,
			function: sxt.function,
		}, MaybeUnsigned(sig.into())).using_encoded(|e| UncheckedExtrinsic::decode(&mut &e[..])).unwrap()
	}

	fn pool(api: &TestPolkadotApi) -> TransactionPool<TestPolkadotApi> {
		TransactionPool::new(Default::default(), Arc::new(api.clone()))
	}

	#[test]
	fn id_submission_should_work() {
		let api = TestPolkadotApi::default();
		let pool = pool(&api);
		pool.import_unchecked_extrinsic(BlockId::number(0), uxt(Alice, 209, true)).unwrap();

		let pending: Vec<_> = pool.cull_and_get_pending(BlockId::number(0), |p| p.map(|a| (a.sender(), a.index())).collect()).unwrap();
		assert_eq!(pending, vec![(Some(Alice.to_raw_public().into()), 209)]);
	}

	#[test]
	fn index_submission_should_work() {
		let api = TestPolkadotApi::default();
		let pool = pool(&api);
		pool.import_unchecked_extrinsic(BlockId::number(0), uxt(Alice, 209, false)).unwrap();

		let pending: Vec<_> = pool.cull_and_get_pending(BlockId::number(0), |p| p.map(|a| (a.sender(), a.index())).collect()).unwrap();
		assert_eq!(pending, vec![(Some(Alice.to_raw_public().into()), 209)]);
	}

	#[test]
	fn multiple_id_submission_should_work() {
		let api = TestPolkadotApi::default();
		let pool = pool(&api);
		pool.import_unchecked_extrinsic(BlockId::number(0), uxt(Alice, 209, true)).unwrap();
		pool.import_unchecked_extrinsic(BlockId::number(0), uxt(Alice, 210, true)).unwrap();

		let pending: Vec<_> = pool.cull_and_get_pending(BlockId::number(0), |p| p.map(|a| (a.sender(), a.index())).collect()).unwrap();
		assert_eq!(pending, vec![(Some(Alice.to_raw_public().into()), 209), (Some(Alice.to_raw_public().into()), 210)]);
	}

	#[test]
	fn multiple_index_submission_should_work() {
		let api = TestPolkadotApi::default();
		let pool = pool(&api);
		pool.import_unchecked_extrinsic(BlockId::number(0), uxt(Alice, 209, false)).unwrap();
		pool.import_unchecked_extrinsic(BlockId::number(0), uxt(Alice, 210, false)).unwrap();

		let pending: Vec<_> = pool.cull_and_get_pending(BlockId::number(0), |p| p.map(|a| (a.sender(), a.index())).collect()).unwrap();
		assert_eq!(pending, vec![(Some(Alice.to_raw_public().into()), 209), (Some(Alice.to_raw_public().into()), 210)]);
	}

	#[test]
	fn id_based_early_nonce_should_be_culled() {
		let api = TestPolkadotApi::default();
		let pool = pool(&api);
		pool.import_unchecked_extrinsic(BlockId::number(0), uxt(Alice, 208, true)).unwrap();

		let pending: Vec<_> = pool.cull_and_get_pending(BlockId::number(0), |p| p.map(|a| (a.sender(), a.index())).collect()).unwrap();
		assert_eq!(pending, vec![]);
	}

	#[test]
	fn index_based_early_nonce_should_be_culled() {
		let api = TestPolkadotApi::default();
		let pool = pool(&api);
		pool.import_unchecked_extrinsic(BlockId::number(0), uxt(Alice, 208, false)).unwrap();

		let pending: Vec<_> = pool.cull_and_get_pending(BlockId::number(0), |p| p.map(|a| (a.sender(), a.index())).collect()).unwrap();
		assert_eq!(pending, vec![]);
	}

	#[test]
	fn id_based_late_nonce_should_be_queued() {
		let api = TestPolkadotApi::default();
		let pool = pool(&api);

		pool.import_unchecked_extrinsic(BlockId::number(0), uxt(Alice, 210, true)).unwrap();
		let pending: Vec<_> = pool.cull_and_get_pending(BlockId::number(0), |p| p.map(|a| (a.sender(), a.index())).collect()).unwrap();
		assert_eq!(pending, vec![]);

		pool.import_unchecked_extrinsic(BlockId::number(0), uxt(Alice, 209, true)).unwrap();
		let pending: Vec<_> = pool.cull_and_get_pending(BlockId::number(0), |p| p.map(|a| (a.sender(), a.index())).collect()).unwrap();
		assert_eq!(pending, vec![(Some(Alice.to_raw_public().into()), 209), (Some(Alice.to_raw_public().into()), 210)]);
	}

	#[test]
	fn index_based_late_nonce_should_be_queued() {
		let api = TestPolkadotApi::default();
		let pool = pool(&api);

		pool.import_unchecked_extrinsic(BlockId::number(0), uxt(Alice, 210, false)).unwrap();
		let pending: Vec<_> = pool.cull_and_get_pending(BlockId::number(0), |p| p.map(|a| (a.sender(), a.index())).collect()).unwrap();
		assert_eq!(pending, vec![]);

		pool.import_unchecked_extrinsic(BlockId::number(0), uxt(Alice, 209, false)).unwrap();
		let pending: Vec<_> = pool.cull_and_get_pending(BlockId::number(0), |p| p.map(|a| (a.sender(), a.index())).collect()).unwrap();
		assert_eq!(pending, vec![(Some(Alice.to_raw_public().into()), 209), (Some(Alice.to_raw_public().into()), 210)]);
	}

	#[test]
	fn index_then_id_submission_should_make_progress() {
		let api = TestPolkadotApi::without_lookup();
		let pool = pool(&api);
		pool.import_unchecked_extrinsic(BlockId::number(0), uxt(Alice, 209, false)).unwrap();
		pool.import_unchecked_extrinsic(BlockId::number(0), uxt(Alice, 210, true)).unwrap();

		let pending: Vec<_> = pool.cull_and_get_pending(BlockId::number(0), |p| p.map(|a| (a.sender(), a.index())).collect()).unwrap();
		assert_eq!(pending, vec![]);

		api.enable_lookup();
		pool.retry_verification(BlockId::number(0)).unwrap();

		let pending: Vec<_> = pool.cull_and_get_pending(BlockId::number(0), |p| p.map(|a| (a.sender(), a.index())).collect()).unwrap();
		assert_eq!(pending, vec![
			(Some(Alice.to_raw_public().into()), 209),
			(Some(Alice.to_raw_public().into()), 210)
		]);
	}

	#[test]
	fn retrying_verification_might_not_change_anything() {
		let api = TestPolkadotApi::without_lookup();
		let pool = pool(&api);
		pool.import_unchecked_extrinsic(BlockId::number(0), uxt(Alice, 209, false)).unwrap();
		pool.import_unchecked_extrinsic(BlockId::number(0), uxt(Alice, 210, true)).unwrap();

		let pending: Vec<_> = pool.cull_and_get_pending(BlockId::number(0), |p| p.map(|a| (a.sender(), a.index())).collect()).unwrap();
		assert_eq!(pending, vec![]);

		pool.retry_verification(BlockId::number(1)).unwrap();

		let pending: Vec<_> = pool.cull_and_get_pending(BlockId::number(0), |p| p.map(|a| (a.sender(), a.index())).collect()).unwrap();
		assert_eq!(pending, vec![]);
	}

	#[test]
	fn id_then_index_submission_should_make_progress() {
		let api = TestPolkadotApi::without_lookup();
		let pool = pool(&api);
		pool.import_unchecked_extrinsic(BlockId::number(0), uxt(Alice, 209, true)).unwrap();
		pool.import_unchecked_extrinsic(BlockId::number(0), uxt(Alice, 210, false)).unwrap();

		let pending: Vec<_> = pool.cull_and_get_pending(BlockId::number(0), |p| p.map(|a| (a.sender(), a.index())).collect()).unwrap();
		assert_eq!(pending, vec![
			(Some(Alice.to_raw_public().into()), 209)
		]);

		// when
		api.enable_lookup();
		pool.retry_verification(BlockId::number(0)).unwrap();

		let pending: Vec<_> = pool.cull_and_get_pending(BlockId::number(0), |p| p.map(|a| (a.sender(), a.index())).collect()).unwrap();
		assert_eq!(pending, vec![
			(Some(Alice.to_raw_public().into()), 209),
			(Some(Alice.to_raw_public().into()), 210)
		]);
	}

	#[test]
	fn index_change_should_result_in_second_tx_culled_or_future() {
		let api = TestPolkadotApi::default();
		let pool = pool(&api);
		let block = BlockId::number(0);
		pool.import_unchecked_extrinsic(block, uxt(Alice, 209, false)).unwrap();
		let hash = *pool.import_unchecked_extrinsic(block, uxt(Alice, 210, false)).unwrap().hash();

		let pending: Vec<_> = pool.cull_and_get_pending(block, |p| p.map(|a| (a.sender(), a.index())).collect()).unwrap();
		assert_eq!(pending, vec![
			(Some(Alice.to_raw_public().into()), 209),
			(Some(Alice.to_raw_public().into()), 210)
		]);

		// first xt is mined, but that has a side-effect of switching index 0 from Alice to Bob.
		// second xt now invalid signature, so it fails.

		// there is no way of reporting this back to the queue right now (TODO). this should cause
		// the queue to flush all information regarding the sender index/account.

		// after this, a re-evaluation of the second's readiness should result in it being thrown
		// out (or maybe placed in future queue).
		let err = pool.reverify_transaction(BlockId::number(1), hash).unwrap_err();
		match *err.kind() {
			::error::ErrorKind::Msg(ref m) if m == "bad signature in extrinsic" => {},
			ref e => assert!(false, "The transaction should be rejected with BadSignature error, got: {:?}", e),
		}

		let pending: Vec<_> = pool.cull_and_get_pending(BlockId::number(1), |p| p.map(|a| (a.sender(), a.index())).collect()).unwrap();
		assert_eq!(pending, vec![]);

	}
}
