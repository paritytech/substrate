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
	collections::{hash_map::Entry, HashMap},
	ops::Deref,
	sync::Arc,
	result
};
use parking_lot::Mutex;

use codec::Slicable;
use extrinsic_pool::{Pool, txpool::{self, Readiness, scoring::{Change, Choice}}};
use extrinsic_pool::api::ExtrinsicPool;
use polkadot_api::PolkadotApi;
use primitives::{AccountId, AccountIndex, Hash, Index, UncheckedExtrinsic as FutureProofUncheckedExtrinsic};
use runtime::{Address, RawAddress, UncheckedExtrinsic};
use substrate_runtime_primitives::traits::{Bounded, Checkable, Hashing, BlakeTwo256};

pub use extrinsic_pool::txpool::{Options, Status, LightStatus, VerifiedTransaction as VerifiedTransactionOps};
pub use error::{Error, ErrorKind, Result};

/// Type alias for convenience.
pub type CheckedExtrinsic = <UncheckedExtrinsic as Checkable>::Checked;

/// A verified transaction which should be includable and non-inherent.
#[derive(Debug)]
pub struct VerifiedTransaction {
	original: UncheckedExtrinsic,
	// `create()` will leave this as `Some` only if the `Address` is an `AccountId`, otherwise a
	// call to `polish` is needed.
	inner: Mutex<Option<CheckedExtrinsic>>,
	hash: Hash,
	encoded_size: usize,
}

impl Clone for VerifiedTransaction {
	fn clone(&self) -> Self {
		VerifiedTransaction {
			original: self.original.clone(),
			inner: Mutex::new(self.inner.lock().clone()),
			hash: self.hash.clone(),
			encoded_size: self.encoded_size.clone(),
		}
	}
}

impl VerifiedTransaction {
	/// Attempt to verify a transaction.
	fn create(original: UncheckedExtrinsic) -> Result<Self> {
		if !original.is_signed() {
			bail!(ErrorKind::IsInherent(original))
		}
		const UNAVAILABLE_MESSAGE: &'static str = "chain state not available";
		let (encoded_size, hash) = original.using_encoded(|e| (e.len(), BlakeTwo256::hash(e)));
		let lookup = |a| match a {
			RawAddress::Id(i) => Ok(i),
			_ => Err(UNAVAILABLE_MESSAGE),
		};
		let inner = Mutex::new(match original.clone().check(lookup) {
			Ok(xt) => Some(xt),
			Err(e) if e == UNAVAILABLE_MESSAGE => None,
			Err(e) => bail!(ErrorKind::BadSignature(e)),
		});
		Ok(VerifiedTransaction { original, inner, hash, encoded_size })
	}

	/// If this transaction isn't really verified, verify it and morph it into a really verified
	/// transaction.
	pub fn polish<F>(&self, lookup: F) -> Result<()> where
	 	F: FnOnce(Address) -> result::Result<AccountId, &'static str> + Send + Sync
	{
		let inner: result::Result<CheckedExtrinsic, Error> = self.original
			.clone()
			.check(lookup)
			.map_err(|e| ErrorKind::BadSignature(e).into());
		*self.inner.lock() = Some(inner?);
		Ok(())
	}

	/// Is this transaction *really* verified?
	pub fn is_really_verified(&self) -> bool {
		self.inner.lock().is_some()
	}

	/// Access the underlying transaction.
	pub fn as_transaction(&self) -> &UncheckedExtrinsic {
		&self.original
	}

	/// Convert to primitive unchecked extrinsic.
	pub fn primitive_extrinsic(&self) -> ::primitives::UncheckedExtrinsic {
		Slicable::decode(&mut self.as_transaction().encode().as_slice())
			.expect("UncheckedExtrinsic shares repr with Vec<u8>; qed")
	}

	/// Consume the verified transaciton, yielding the unchecked counterpart.
	pub fn into_inner(self) -> Result<CheckedExtrinsic> {
		self.inner.lock().clone().ok_or_else(|| ErrorKind::NotReady.into())
	}

	/// Get the 256-bit hash of this transaction.
	pub fn hash(&self) -> &Hash {
		&self.hash
	}

	/// Get the account ID of the sender of this transaction.
	pub fn sender(&self) -> Result<AccountId> {
		self.inner.lock().as_ref().map(|i| i.signed.clone()).ok_or_else(|| ErrorKind::NotReady.into())
	}

	/// Get the account ID of the sender of this transaction.
	pub fn index(&self) -> Index {
		self.original.extrinsic.index
	}

	/// Get encoded size of the transaction.
	pub fn encoded_size(&self) -> usize {
		self.encoded_size
	}
}

impl txpool::VerifiedTransaction for VerifiedTransaction {
	type Hash = Hash;
	type Sender = Address;

	fn hash(&self) -> &Self::Hash {
		&self.hash
	}

	fn sender(&self) -> &Self::Sender {
		self.original.sender()
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
		old.index().cmp(&other.index())
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
	known_nonces: HashMap<AccountId, (::primitives::Index, bool)>,
	known_indexes: HashMap<AccountIndex, AccountId>,
}

impl<'a, T: 'a + PolkadotApi> Ready<'a, T> {
	/// Create a new readiness evaluator at the given block. Requires that
	/// the ID has already been checked for local corresponding and available state.
	pub fn create(at: T::CheckedBlockId, api: &'a T) -> Self {
		Ready {
			at_block: at,
			api,
			known_nonces: HashMap::new(),
			known_indexes: HashMap::new(),
		}
	}
}

impl<'a, T: 'a + PolkadotApi> Clone for Ready<'a, T> {
	fn clone(&self) -> Self {
		Ready {
			at_block: self.at_block.clone(),
			api: self.api,
			known_nonces: self.known_nonces.clone(),
			known_indexes: self.known_indexes.clone(),
		}
	}
}

impl<'a, T: 'a + PolkadotApi> txpool::Ready<VerifiedTransaction> for Ready<'a, T>
{
	fn is_ready(&mut self, xt: &VerifiedTransaction) -> Readiness {
		if !xt.is_really_verified() {
			let id = match xt.original.extrinsic.signed.clone() {
				RawAddress::Id(id) => id.clone(),	// should never happen, since we're not verified.
				RawAddress::Index(i) => match self.known_indexes.entry(i) {
					Entry::Occupied(e) => e.get().clone(),
					Entry::Vacant(e) => {
						let (api, at_block) = (&self.api, &self.at_block);
						if let Some(id) = api.lookup(at_block, RawAddress::Index(i))
							.ok()
							.and_then(|o| o)
						{
							e.insert(id.clone());
							id
						} else {
							// Invalid index.
							// return stale in order to get the pool to throw it away.
							return Readiness::Stale
						}
					}
				},
			};
			if VerifiedTransaction::polish(xt, move |_| Ok(id)).is_err() {
				// Invalid signature.
				// return stale in order to get the pool to throw it away.
				return Readiness::Stale
			}
		}

		// guaranteed to be properly verified at this point.

		let sender = xt.sender().expect("only way to get here is `is_really_verified` or successful `polish`; either guarantees `is_really_verified`; `sender` is `Ok` if `is_really_verified`; qed");
		trace!(target: "transaction-pool", "Checking readiness of {} (from {})", xt.hash, Hash::from(sender));

		let is_index_sender = match xt.original.extrinsic.signed { RawAddress::Index(_) => false, _ => true };

		// TODO: find a way to handle index error properly -- will need changes to
		// transaction-pool trait.
		let (api, at_block) = (&self.api, &self.at_block);
		let get_nonce = || api.index(at_block, sender).ok().unwrap_or_else(Bounded::max_value);
		let (next_nonce, was_index_sender) = self.known_nonces.entry(sender).or_insert_with(|| (get_nonce(), is_index_sender));

		trace!(target: "transaction-pool", "Next index for sender is {}; xt index is {}", next_nonce, xt.original.extrinsic.index);

		if *was_index_sender == is_index_sender || get_nonce() == *next_nonce {
			match xt.original.extrinsic.index.cmp(&next_nonce) {
				Ordering::Greater => Readiness::Future,
				Ordering::Less => Readiness::Stale,
				Ordering::Equal => {
					// remember to increment `next_nonce`
					// TODO: this won't work perfectly since accounts can now be killed, returning the nonce
					// to zero.
					*next_nonce = next_nonce.saturating_add(1);
					Readiness::Ready
				}
			}
		} else {
			// ignore for now.
			Readiness::Future
		}
	}
}

pub struct Verifier;

impl txpool::Verifier<UncheckedExtrinsic> for Verifier {
	type VerifiedTransaction = VerifiedTransaction;
	type Error = Error;

	fn verify_transaction(&self, uxt: UncheckedExtrinsic) -> Result<Self::VerifiedTransaction> {
		info!("Extrinsic Submitted: {:?}", uxt);
		VerifiedTransaction::create(uxt)
	}
}

/// The polkadot transaction pool.
///
/// Wraps a `extrinsic_pool::Pool`.
pub struct TransactionPool {
	inner: Pool<UncheckedExtrinsic, Hash, Verifier, Scoring, Error>,
}

impl TransactionPool {
	/// Create a new transaction pool.
	pub fn new(options: Options) -> Self {
		TransactionPool {
			inner: Pool::new(options, Verifier, Scoring),
		}
	}

	// TODO: remove. This is pointless - just use `submit()` directly.
	pub fn import_unchecked_extrinsic(&self, uxt: UncheckedExtrinsic) -> Result<Arc<VerifiedTransaction>> {
		self.inner.submit(vec![uxt]).map(|mut v| v.swap_remove(0))
	}
}

impl Deref for TransactionPool {
	type Target = Pool<UncheckedExtrinsic, Hash, Verifier, Scoring, Error>;

	fn deref(&self) -> &Self::Target {
		&self.inner
	}
}

impl ExtrinsicPool<FutureProofUncheckedExtrinsic, Hash> for TransactionPool {
	type Error = Error;

	fn submit(&self, xts: Vec<FutureProofUncheckedExtrinsic>) -> Result<Vec<Hash>> {
		// TODO: more general transaction pool, which can handle more kinds of vec-encoded transactions,
		// even when runtime is out of date.
		xts.into_iter()
			.map(|xt| xt.encode())
			.map(|encoded| UncheckedExtrinsic::decode(&mut &encoded[..]))
			.map(|maybe_decoded| maybe_decoded.ok_or_else(|| ErrorKind::InvalidExtrinsicFormat.into()))
			.map(|x| x.and_then(|x| self.import_unchecked_extrinsic(x)))
			.map(|x| x.map(|x| x.hash().clone()))
			.collect()
	}
}

#[cfg(test)]
mod tests {
	use super::{TransactionPool, Ready};
	use substrate_keyring::Keyring::{self, *};
	use codec::Slicable;
	use polkadot_api::{PolkadotApi, BlockBuilder, CheckedBlockId, Result};
	use primitives::{AccountId, AccountIndex, Block, BlockId, Hash, Index, SessionKey, Timestamp,
		UncheckedExtrinsic as FutureProofUncheckedExtrinsic};
	use runtime::{RawAddress, Call, TimestampCall, BareExtrinsic, Extrinsic, UncheckedExtrinsic};
	use primitives::parachain::{CandidateReceipt, DutyRoster, Id as ParaId};
	use substrate_runtime_primitives::{MaybeUnsigned, generic};

	struct TestBlockBuilder;
	impl BlockBuilder for TestBlockBuilder {
		fn push_extrinsic(&mut self, _extrinsic: FutureProofUncheckedExtrinsic) -> Result<()> { unimplemented!() }
		fn bake(self) -> Result<Block> { unimplemented!() }
	}

	#[derive(Clone)]
	struct TestCheckedBlockId(pub BlockId);
	impl CheckedBlockId for TestCheckedBlockId {
		fn block_id(&self) -> &BlockId { &self.0 }
	}

	fn number_of(at: &TestCheckedBlockId) -> u32 {
		match at.0 {
			generic::BlockId::Number(n) => n as u32,
			_ => 0,
		}
	}

	#[derive(Clone)]
	struct TestPolkadotApi;
	impl PolkadotApi for TestPolkadotApi {
		type CheckedBlockId = TestCheckedBlockId;
		type BlockBuilder = TestBlockBuilder;

		fn check_id(&self, id: BlockId) -> Result<TestCheckedBlockId> { Ok(TestCheckedBlockId(id)) }
		fn session_keys(&self, _at: &TestCheckedBlockId) -> Result<Vec<SessionKey>> { unimplemented!() }
		fn validators(&self, _at: &TestCheckedBlockId) -> Result<Vec<AccountId>> { unimplemented!() }
		fn random_seed(&self, _at: &TestCheckedBlockId) -> Result<Hash> { unimplemented!() }
		fn duty_roster(&self, _at: &TestCheckedBlockId) -> Result<DutyRoster> { unimplemented!() }
		fn timestamp(&self, _at: &TestCheckedBlockId) -> Result<u64> { unimplemented!() }
		fn evaluate_block(&self, _at: &TestCheckedBlockId, _block: Block) -> Result<bool> { unimplemented!() }
		fn active_parachains(&self, _at: &TestCheckedBlockId) -> Result<Vec<ParaId>> { unimplemented!() }
		fn parachain_code(&self, _at: &TestCheckedBlockId, _parachain: ParaId) -> Result<Option<Vec<u8>>> { unimplemented!() }
		fn parachain_head(&self, _at: &TestCheckedBlockId, _parachain: ParaId) -> Result<Option<Vec<u8>>> { unimplemented!() }
		fn build_block(&self, _at: &TestCheckedBlockId, _timestamp: Timestamp, _new_heads: Vec<CandidateReceipt>) -> Result<Self::BlockBuilder> { unimplemented!() }
		fn inherent_extrinsics(&self, _at: &TestCheckedBlockId, _timestamp: Timestamp, _new_heads: Vec<CandidateReceipt>) -> Result<Vec<Vec<u8>>> { unimplemented!() }

		fn index(&self, _at: &TestCheckedBlockId, _account: AccountId) -> Result<Index> {
			Ok((_account[0] as u32) + number_of(_at))
		}
		fn lookup(&self, _at: &TestCheckedBlockId, _address: RawAddress<AccountId, AccountIndex>) -> Result<Option<AccountId>> {
			match _address {
				RawAddress::Id(i) => Ok(Some(i)),
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

	#[test]
	fn id_submission_should_work() {
		let pool = TransactionPool::new(Default::default());
		pool.submit(vec![uxt(Alice, 209, true)]).unwrap();

		let ready = Ready::create(TestPolkadotApi.check_id(BlockId::number(0)).unwrap(), &TestPolkadotApi);
		let pending: Vec<_> = pool.cull_and_get_pending(ready, |p| p.map(|a| (a.sender().ok(), a.index())).collect());
		assert_eq!(pending, vec![(Some(Alice.to_raw_public().into()), 209)]);
	}

	#[test]
	fn index_submission_should_work() {
		let pool = TransactionPool::new(Default::default());
		pool.submit(vec![uxt(Alice, 209, false)]).unwrap();

		let ready = Ready::create(TestPolkadotApi.check_id(BlockId::number(0)).unwrap(), &TestPolkadotApi);
		let pending: Vec<_> = pool.cull_and_get_pending(ready, |p| p.map(|a| (a.sender().ok(), a.index())).collect());
		assert_eq!(pending, vec![(Some(Alice.to_raw_public().into()), 209)]);
	}

	#[test]
	fn multiple_id_submission_should_work() {
		let pool = TransactionPool::new(Default::default());
		pool.submit(vec![uxt(Alice, 209, true)]).unwrap();
		pool.submit(vec![uxt(Alice, 210, true)]).unwrap();

		let ready = Ready::create(TestPolkadotApi.check_id(BlockId::number(0)).unwrap(), &TestPolkadotApi);
		let pending: Vec<_> = pool.cull_and_get_pending(ready, |p| p.map(|a| (a.sender().ok(), a.index())).collect());
		assert_eq!(pending, vec![(Some(Alice.to_raw_public().into()), 209), (Some(Alice.to_raw_public().into()), 210)]);
	}

	#[test]
	fn multiple_index_submission_should_work() {
		let pool = TransactionPool::new(Default::default());
		pool.submit(vec![uxt(Alice, 209, false)]).unwrap();
		pool.submit(vec![uxt(Alice, 210, false)]).unwrap();

		let ready = Ready::create(TestPolkadotApi.check_id(BlockId::number(0)).unwrap(), &TestPolkadotApi);
		let pending: Vec<_> = pool.cull_and_get_pending(ready, |p| p.map(|a| (a.sender().ok(), a.index())).collect());
		assert_eq!(pending, vec![(Some(Alice.to_raw_public().into()), 209), (Some(Alice.to_raw_public().into()), 210)]);
	}

	#[test]
	fn id_based_early_nonce_should_be_culled() {
		let pool = TransactionPool::new(Default::default());
		pool.submit(vec![uxt(Alice, 208, true)]).unwrap();

		let ready = Ready::create(TestPolkadotApi.check_id(BlockId::number(0)).unwrap(), &TestPolkadotApi);
		let pending: Vec<_> = pool.cull_and_get_pending(ready, |p| p.map(|a| (a.sender().ok(), a.index())).collect());
		assert_eq!(pending, vec![]);
	}

	#[test]
	fn index_based_early_nonce_should_be_culled() {
		let pool = TransactionPool::new(Default::default());
		pool.submit(vec![uxt(Alice, 208, false)]).unwrap();

		let ready = Ready::create(TestPolkadotApi.check_id(BlockId::number(0)).unwrap(), &TestPolkadotApi);
		let pending: Vec<_> = pool.cull_and_get_pending(ready, |p| p.map(|a| (a.sender().ok(), a.index())).collect());
		assert_eq!(pending, vec![]);
	}

	#[test]
	fn id_based_late_nonce_should_be_queued() {
		let pool = TransactionPool::new(Default::default());
		let ready = || Ready::create(TestPolkadotApi.check_id(BlockId::number(0)).unwrap(), &TestPolkadotApi);

		pool.submit(vec![uxt(Alice, 210, true)]).unwrap();
		let pending: Vec<_> = pool.cull_and_get_pending(ready(), |p| p.map(|a| (a.sender().ok(), a.index())).collect());
		assert_eq!(pending, vec![]);

		pool.submit(vec![uxt(Alice, 209, true)]).unwrap();
		let pending: Vec<_> = pool.cull_and_get_pending(ready(), |p| p.map(|a| (a.sender().ok(), a.index())).collect());
		assert_eq!(pending, vec![(Some(Alice.to_raw_public().into()), 209), (Some(Alice.to_raw_public().into()), 210)]);
	}

	#[test]
	fn index_based_late_nonce_should_be_queued() {
		let pool = TransactionPool::new(Default::default());
		let ready = || Ready::create(TestPolkadotApi.check_id(BlockId::number(0)).unwrap(), &TestPolkadotApi);

		pool.submit(vec![uxt(Alice, 210, false)]).unwrap();
		let pending: Vec<_> = pool.cull_and_get_pending(ready(), |p| p.map(|a| (a.sender().ok(), a.index())).collect());
		assert_eq!(pending, vec![]);

		pool.submit(vec![uxt(Alice, 209, false)]).unwrap();
		let pending: Vec<_> = pool.cull_and_get_pending(ready(), |p| p.map(|a| (a.sender().ok(), a.index())).collect());
		assert_eq!(pending, vec![(Some(Alice.to_raw_public().into()), 209), (Some(Alice.to_raw_public().into()), 210)]);
	}

	#[test]
	fn index_then_id_submission_should_make_progress() {
		let pool = TransactionPool::new(Default::default());
		pool.submit(vec![uxt(Alice, 209, false)]).unwrap();
		pool.submit(vec![uxt(Alice, 210, true)]).unwrap();

		let ready = Ready::create(TestPolkadotApi.check_id(BlockId::number(0)).unwrap(), &TestPolkadotApi);
		let pending: Vec<_> = pool.cull_and_get_pending(ready, |p| p.map(|a| (a.sender().ok(), a.index())).collect());
		assert_eq!(pending, vec![
			(Some(Alice.to_raw_public().into()), 209)
		]);
	}

	#[test]
	fn id_then_index_submission_should_make_progress() {
		let pool = TransactionPool::new(Default::default());
		pool.submit(vec![uxt(Alice, 209, true)]).unwrap();
		pool.submit(vec![uxt(Alice, 210, false)]).unwrap();

		let ready = Ready::create(TestPolkadotApi.check_id(BlockId::number(0)).unwrap(), &TestPolkadotApi);
		let pending: Vec<_> = pool.cull_and_get_pending(ready, |p| p.map(|a| (a.sender().ok(), a.index())).collect());
		assert_eq!(pending, vec![
			(Some(Alice.to_raw_public().into()), 209)
		]);
	}

	#[test]
	fn index_change_should_result_in_second_tx_culled_or_future() {
		let pool = TransactionPool::new(Default::default());
		pool.submit(vec![uxt(Alice, 209, false)]).unwrap();
		pool.submit(vec![uxt(Alice, 210, false)]).unwrap();

		let ready = Ready::create(TestPolkadotApi.check_id(BlockId::number(0)).unwrap(), &TestPolkadotApi);
		let pending: Vec<_> = pool.cull_and_get_pending(ready, |p| p.map(|a| (a.sender().ok(), a.index())).collect());
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
/*
		// TODO: uncomment once the new queue design is in.
		let ready = Ready::create(TestPolkadotApi.check_id(BlockId::number(1)).unwrap(), &TestPolkadotApi);
		let pending: Vec<_> = pool.cull_and_get_pending(ready, |p| p.map(|a| (a.sender().ok(), a.index())).collect());
		assert_eq!(pending, vec![]);
*/
	}
}
