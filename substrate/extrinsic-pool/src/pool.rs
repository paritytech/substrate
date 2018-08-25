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
	collections::{BTreeMap, HashMap},
	fmt,
	sync::Arc,
	time,
};
use futures::sync::mpsc;
use parking_lot::{Mutex, RwLock};
use serde::{Serialize, de::DeserializeOwned};
use txpool::{self, Scoring, Readiness};

use error::IntoPoolError;
use listener::Listener;
use rotator::PoolRotator;
use watcher::Watcher;

use runtime_primitives::{generic::BlockId, traits::Block as BlockT};

/// Modification notification event stream type;
pub type EventStream = mpsc::UnboundedReceiver<()>;

/// Extrinsic hash type for a pool.
pub type ExHash<A> = <A as ChainApi>::Hash;
/// Extrinsic type for a pool.
pub type ExtrinsicFor<A> = <<A as ChainApi>::Block as BlockT>::Extrinsic;
/// Verified extrinsic data for `ChainApi`.
pub type VerifiedFor<A> = Verified<ExtrinsicFor<A>, <A as ChainApi>::VEx>;
/// A collection of all extrinsics.
pub type AllExtrinsics<A> = BTreeMap<<<A as ChainApi>::VEx as txpool::VerifiedTransaction>::Sender, Vec<ExtrinsicFor<A>>>;

/// Verified extrinsic struct. Wraps original extrinsic and verification info.
#[derive(Debug)]
pub struct Verified<Ex, VEx> {
	/// Original extrinsic.
	pub original: Ex,
	/// Verification data.
	pub verified: VEx,
	/// Pool deadline, after it's reached we remove the extrinsic from the pool.
	pub valid_till: time::Instant,
}

impl<Ex, VEx> txpool::VerifiedTransaction for Verified<Ex, VEx>
where
	Ex: fmt::Debug,
	VEx: txpool::VerifiedTransaction,
{
	type Hash = <VEx as txpool::VerifiedTransaction>::Hash;
	type Sender = <VEx as txpool::VerifiedTransaction>::Sender;

	fn hash(&self) -> &Self::Hash {
		self.verified.hash()
	}

	fn sender(&self) -> &Self::Sender {
		self.verified.sender()
	}

	fn mem_usage(&self) -> usize {
		// TODO: add `original` mem usage.
		self.verified.mem_usage()
	}
}

/// Concrete extrinsic validation and query logic.
pub trait ChainApi: Send + Sync {
	/// Block type.
	type Block: BlockT;
	/// Extrinsic hash type.
	type Hash: ::std::hash::Hash + Eq + Copy + fmt::Debug + fmt::LowerHex + Serialize + DeserializeOwned + ::std::str::FromStr + Send + Sync + Default + 'static;
	/// Extrinsic sender type.
	type Sender: ::std::hash::Hash + fmt::Debug + Serialize + DeserializeOwned + Eq + Clone + Send + Sync + Ord + Default;
	/// Unchecked extrinsic type.
	/// Verified extrinsic type.
	type VEx: txpool::VerifiedTransaction<Hash=Self::Hash, Sender=Self::Sender> + Send + Sync + Clone;
	/// Readiness evaluator
	type Ready;
	/// Error type.
	type Error: From<txpool::Error> + IntoPoolError;
	/// Score type.
	type Score: ::std::cmp::Ord + Clone + Default + fmt::Debug + Send + Send + Sync;
	/// Custom scoring update event type.
	type Event: ::std::fmt::Debug;
	/// Verify extrinsic at given block.
	fn verify_transaction(&self, at: &BlockId<Self::Block>, uxt: &ExtrinsicFor<Self>) -> Result<Self::VEx, Self::Error>;

	/// Create new readiness evaluator.
	fn ready(&self) -> Self::Ready;

	/// Check readiness for verified extrinsic at given block.
	fn is_ready(&self, at: &BlockId<Self::Block>, context: &mut Self::Ready, xt: &VerifiedFor<Self>) -> Readiness;

	/// Decides on ordering of `T`s from a particular sender.
	fn compare(old: &VerifiedFor<Self>, other: &VerifiedFor<Self>) -> ::std::cmp::Ordering;

	/// Decides how to deal with two transactions from a sender that seem to occupy the same slot in the queue.
	fn choose(old: &VerifiedFor<Self>, new: &VerifiedFor<Self>) -> txpool::scoring::Choice;

	/// Updates the transaction scores given a list of transactions and a change to previous scoring.
	/// NOTE: you can safely assume that both slices have the same length.
	/// (i.e. score at index `i` represents transaction at the same index)
	fn update_scores(xts: &[txpool::Transaction<VerifiedFor<Self>>], scores: &mut [Self::Score], change: txpool::scoring::Change<Self::Event>);

	/// Decides if `new` should push out `old` transaction from the pool.
	///
	/// NOTE returning `InsertNew` here can lead to some transactions being accepted above pool limits.
	fn should_replace(old: &VerifiedFor<Self>, new: &VerifiedFor<Self>) -> txpool::scoring::Choice;
}

pub struct Ready<'a, 'b, B: 'a + ChainApi> {
	api: &'a B,
	at: &'b BlockId<B::Block>,
	context: B::Ready,
	rotator: &'a PoolRotator<B::Hash>,
	now: time::Instant,
}

impl<'a, 'b, B: ChainApi> txpool::Ready<VerifiedFor<B>> for Ready<'a, 'b, B> {
	fn is_ready(&mut self, xt: &VerifiedFor<B>) -> Readiness {
		if self.rotator.ban_if_stale(&self.now, xt) {
			debug!(target: "extrinsic-pool", "[{:?}] Banning as stale.", txpool::VerifiedTransaction::hash(xt));
			return Readiness::Stale;
		}

		self.api.is_ready(self.at, &mut self.context, xt)
	}
}

pub struct ScoringAdapter<T>(::std::marker::PhantomData<T>);

impl<T> ::std::fmt::Debug for ScoringAdapter<T> {
	fn fmt(&self, _f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
		Ok(())
	}
}

impl<T: ChainApi> Scoring<VerifiedFor<T>> for ScoringAdapter<T> {
	type Score = <T as ChainApi>::Score;
	type Event = <T as ChainApi>::Event;

	fn compare(&self, old: &VerifiedFor<T>, other: &VerifiedFor<T>) -> ::std::cmp::Ordering {
		T::compare(old, other)
	}

	fn choose(&self, old: &VerifiedFor<T>, new: &VerifiedFor<T>) -> txpool::scoring::Choice {
		T::choose(old, new)
	}

	fn update_scores(&self, xts: &[txpool::Transaction<VerifiedFor<T>>], scores: &mut [Self::Score], change: txpool::scoring::Change<Self::Event>) {
		T::update_scores(xts, scores, change)
	}

	fn should_replace(&self, old: &VerifiedFor<T>, new: &VerifiedFor<T>) -> txpool::scoring::Choice {
		T::should_replace(old, new)
	}
}

/// Maximum time the transaction will be kept in the pool.
///
/// Transactions that don't get included within the limit are removed from the pool.
const POOL_TIME: time::Duration = time::Duration::from_secs(60 * 5);

/// Extrinsics pool.
pub struct Pool<B: ChainApi> {
	api: B,
	pool: RwLock<txpool::Pool<
		VerifiedFor<B>,
		ScoringAdapter<B>,
		Listener<B::Hash>,
	>>,
	import_notification_sinks: Mutex<Vec<mpsc::UnboundedSender<()>>>,
	rotator: PoolRotator<B::Hash>,
}

impl<B: ChainApi> Pool<B> {
	/// Create a new transaction pool.
	pub fn new(options: txpool::Options, api: B) -> Self {
		Pool {
			pool: RwLock::new(txpool::Pool::new(Listener::default(), ScoringAdapter::<B>(Default::default()), options)),
			import_notification_sinks: Default::default(),
			api,
			rotator: Default::default(),
		}
	}

	/// Imports a pre-verified extrinsic to the pool.
	pub fn import(&self, xt: VerifiedFor<B>) -> Result<Arc<VerifiedFor<B>>, B::Error> {
		let result = self.pool.write().import(xt)?;

		self.import_notification_sinks.lock()
			.retain(|sink| sink.unbounded_send(()).is_ok());

		Ok(result)
	}

	/// Return an event stream of transactions imported to the pool.
	pub fn import_notification_stream(&self) -> EventStream {
		let (sink, stream) = mpsc::unbounded();
		self.import_notification_sinks.lock().push(sink);
		stream
	}

	/// Invoked when extrinsics are broadcasted.
	pub fn on_broadcasted(&self, propagated: HashMap<B::Hash, Vec<String>>) {
		for (hash, peers) in propagated.into_iter() {
			self.pool.write().listener_mut().broadcasted(&hash, peers);
		}
	}

	/// Imports a bunch of unverified extrinsics to the pool
	pub fn submit_at<T>(&self, at: &BlockId<B::Block>, xts: T) -> Result<Vec<Arc<VerifiedFor<B>>>, B::Error> where
		T: IntoIterator<Item=ExtrinsicFor<B>>
	{
		xts
			.into_iter()
			.map(|xt| {
				match self.api.verify_transaction(at, &xt) {
					Ok(ref verified) if self.rotator.is_banned(txpool::VerifiedTransaction::hash(verified)) => {
						return (Err(txpool::Error::from("Temporarily Banned".to_owned()).into()), xt)
					},
					result => (result, xt),
				}
			})
			.map(|(v, xt)| {
				let xt = Verified {
					original: xt,
					verified: v?,
					valid_till: time::Instant::now() + POOL_TIME,
				};
				Ok(self.pool.write().import(xt)?)
			})
			.collect()
	}

	/// Imports one unverified extrinsic to the pool
	pub fn submit_one(&self, at: &BlockId<B::Block>, xt: ExtrinsicFor<B>) -> Result<Arc<VerifiedFor<B>>, B::Error>  {
		Ok(self.submit_at(at, ::std::iter::once(xt))?.pop().expect("One extrinsic passed; one result returned; qed"))
	}

	/// Import a single extrinsic and starts to watch their progress in the pool.
	pub fn submit_and_watch(&self, at: &BlockId<B::Block>, xt: ExtrinsicFor<B>) -> Result<Watcher<B::Hash>, B::Error> {
		let xt = self.submit_at(at, Some(xt))?.pop().expect("One extrinsic passed; one result returned; qed");
		Ok(self.pool.write().listener_mut().create_watcher(xt))
	}

	/// Remove from the pool.
	pub fn remove(&self, hashes: &[B::Hash], is_valid: bool) -> Vec<Option<Arc<VerifiedFor<B>>>> {
		let mut pool = self.pool.write();
		let mut results = Vec::with_capacity(hashes.len());
		for hash in hashes {
			results.push(pool.remove(hash, is_valid));
		}
		results
	}

	/// Cull transactions from the queue.
	pub fn cull_from(
		&self,
		at: &BlockId<B::Block>,
		senders: Option<&[<B::VEx as txpool::VerifiedTransaction>::Sender]>,
	) -> usize
	{
		self.rotator.clear_timeouts(&time::Instant::now());
		let ready = self.ready(at);
		self.pool.write().cull(senders, ready)
	}

	/// Cull old transactions from the queue.
	pub fn cull(&self, at: &BlockId<B::Block>) -> Result<usize, B::Error> {
		Ok(self.cull_from(at, None))
	}

	/// Cull transactions from the queue and then compute the pending set.
	pub fn cull_and_get_pending<F, T>(&self, at: &BlockId<B::Block>, f: F) -> Result<T, B::Error> where
		F: FnOnce(txpool::PendingIterator<VerifiedFor<B>, Ready<B>, ScoringAdapter<B>, Listener<B::Hash>>) -> T,
	{
		self.cull_from(at, None);
		Ok(self.pending(at, f))
	}

	/// Get the full status of the queue (including readiness)
	pub fn status<R: txpool::Ready<VerifiedFor<B>>>(&self, ready: R) -> txpool::Status {
		self.pool.read().status(ready)
	}

	/// Returns light status of the pool.
	pub fn light_status(&self) -> txpool::LightStatus {
		self.pool.read().light_status()
	}

	/// Removes all transactions from given sender
	pub fn remove_sender(&self, sender: <B::VEx as txpool::VerifiedTransaction>::Sender) -> Vec<Arc<VerifiedFor<B>>> {
		let mut pool = self.pool.write();
		let pending = pool.pending_from_sender(|_: &VerifiedFor<B>| txpool::Readiness::Ready, &sender).collect();
		// remove all transactions from this sender
		pool.cull(Some(&[sender]), |_: &VerifiedFor<B>| txpool::Readiness::Stale);
		pending
	}

	/// Retrieve the pending set. Be careful to not leak the pool `ReadGuard` to prevent deadlocks.
	pub fn pending<F, T>(&self, at: &BlockId<B::Block>, f: F) -> T where
		F: FnOnce(txpool::PendingIterator<VerifiedFor<B>, Ready<B>, ScoringAdapter<B>, Listener<B::Hash>>) -> T,
	{
		let ready = self.ready(at);
		f(self.pool.read().pending(ready))
	}

	/// Retry to import all verified transactions from given sender.
	pub fn retry_verification(&self, at: &BlockId<B::Block>, sender: <B::VEx as txpool::VerifiedTransaction>::Sender) -> Result<(), B::Error> {
		let to_reverify = self.remove_sender(sender);
		self.submit_at(at, to_reverify.into_iter().map(|ex| Arc::try_unwrap(ex).expect("Removed items have no references").original))?;
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
	pub fn reverify_transaction(&self, at: &BlockId<B::Block>, hash: B::Hash) -> Result<Option<Arc<VerifiedFor<B>>>, B::Error> {
		let result = self.remove(&[hash], false).pop().expect("One hash passed; one result received; qed");
		if let Some(ex) = result {
			self.submit_one(at, Arc::try_unwrap(ex).expect("Removed items have no references").original).map(Some)
		} else {
			Ok(None)
		}
	}

	/// Retrieve all transactions in the pool grouped by sender.
	pub fn all(&self) -> AllExtrinsics<B> {
		use txpool::VerifiedTransaction;
		let pool = self.pool.read();
		let all = pool.unordered_pending(AlwaysReady);
		all.fold(Default::default(), |mut map: AllExtrinsics<B>, tx| {
			// Map with `null` key is not serializable, so we fallback to default accountId.
			map.entry(tx.verified.sender().clone())
				.or_insert_with(Vec::new)
				// use bytes type to make it serialize nicer.
				.push(tx.original.clone());
			map
		})
	}

	fn ready<'a, 'b>(&'a self, at: &'b BlockId<B::Block>) -> Ready<'a, 'b, B> {
		Ready {
			api: &self.api,
			rotator: &self.rotator,
			context: self.api.ready(),
			at,
			now: time::Instant::now(),
		}
	}
}

 /// A Readiness implementation that returns `Ready` for all transactions.
pub struct AlwaysReady;
impl<VEx> txpool::Ready<VEx> for AlwaysReady {
	fn is_ready(&mut self, _tx: &VEx) -> txpool::Readiness {
		txpool::Readiness::Ready
	}
}

#[cfg(test)]
pub mod tests {
	use txpool;
	use super::{VerifiedFor, ExtrinsicFor};
	use std::collections::HashMap;
	use std::cmp::Ordering;
	use {Pool, ChainApi, scoring, Readiness};
	use keyring::Keyring::{self, *};
	use codec::Encode;
	use test_client::runtime::{AccountId, Block, Hash, Index, Extrinsic, Transfer};
	use runtime_primitives::{generic, traits::{Hash as HashT, BlindCheckable, BlakeTwo256}};
	use VerifiedTransaction as VerifiedExtrinsic;

	type BlockId = generic::BlockId<Block>;

	#[derive(Clone, Debug)]
	pub struct VerifiedTransaction {
		pub hash: Hash,
		pub sender: AccountId,
		pub nonce: u64,
	}

	impl txpool::VerifiedTransaction for VerifiedTransaction {
		type Hash = Hash;
		type Sender = AccountId;

		fn hash(&self) -> &Self::Hash {
			&self.hash
		}

		fn sender(&self) -> &Self::Sender {
			&self.sender
		}

		fn mem_usage(&self) -> usize {
			256
		}
	}

	struct TestApi;

	impl TestApi {
		fn default() -> Self {
			TestApi
		}
	}

	impl ChainApi for TestApi {
		type Block = Block;
		type Hash = Hash;
		type Sender = AccountId;
		type Error = txpool::Error;
		type VEx = VerifiedTransaction;
		type Ready = HashMap<AccountId, u64>;
		type Score = u64;
		type Event = ();

		fn verify_transaction(&self, _at: &BlockId, uxt: &ExtrinsicFor<Self>) -> Result<Self::VEx, Self::Error> {
			let hash = BlakeTwo256::hash(&uxt.encode());
			let xt = uxt.clone().check()?;
			Ok(VerifiedTransaction {
				hash,
				sender: xt.transfer.from,
				nonce: xt.transfer.nonce,
			})
		}

		fn is_ready(&self, at: &BlockId, nonce_cache: &mut Self::Ready, xt: &VerifiedFor<Self>) -> Readiness {
			let sender = xt.verified.sender;
			let next_index = nonce_cache.entry(sender)
				.or_insert_with(|| index(at, sender));

			let result = match xt.original.transfer.nonce.cmp(&next_index) {
				Ordering::Greater => Readiness::Future,
				Ordering::Equal => Readiness::Ready,
				Ordering::Less => Readiness::Stale,
			};

			// remember to increment `next_index`
			*next_index = next_index.saturating_add(1);

			result
		}

		fn ready(&self) -> Self::Ready {
			HashMap::default()
		}

		fn compare(old: &VerifiedFor<Self>, other: &VerifiedFor<Self>) -> Ordering {
			old.original.transfer.nonce.cmp(&other.original.transfer.nonce)
		}

		fn choose(old: &VerifiedFor<Self>, new: &VerifiedFor<Self>) -> scoring::Choice {
			assert!(new.verified.sender == old.verified.sender, "Scoring::choose called with transactions from different senders");
			if old.original.transfer.nonce == new.original.transfer.nonce {
				return scoring::Choice::RejectNew;
			}
			scoring::Choice::InsertNew
		}

		fn update_scores(
			xts: &[txpool::Transaction<VerifiedFor<Self>>],
			scores: &mut [Self::Score],
			_change: scoring::Change<()>
		) {
			for i in 0..xts.len() {
				scores[i] = xts[i].original.transfer.amount;
			}
		}

		fn should_replace(_old: &VerifiedFor<Self>, _new: &VerifiedFor<Self>) -> scoring::Choice {
			scoring::Choice::InsertNew
		}
	}

	fn index(at: &BlockId, _account: AccountId) -> u64 {
		(_account[0] as u64) + number_of(at)
	}

	fn number_of(at: &BlockId) -> u64 {
		match at {
			generic::BlockId::Number(n) => *n as u64,
			_ => 0,
		}
	}

	fn uxt(who: Keyring, nonce: Index) -> Extrinsic {
		let transfer = Transfer {
			from: who.to_raw_public().into(),
			to: AccountId::default(),
			nonce,
			amount: 1,
		};
		let signature = transfer.using_encoded(|e| who.sign(e));
		Extrinsic {
			transfer,
			signature: signature.into(),
		}
	}

	fn pool() -> Pool<TestApi> {
		Pool::new(Default::default(), TestApi::default())
	}

	#[test]
	fn submission_should_work() {
		let pool = pool();
		assert_eq!(209, index(&BlockId::number(0), Alice.to_raw_public().into()));
		pool.submit_one(&BlockId::number(0), uxt(Alice, 209)).unwrap();

		let pending: Vec<_> = pool.cull_and_get_pending(&BlockId::number(0), |p| p.map(|a| (*a.sender(), a.original.transfer.nonce)).collect()).unwrap();
		assert_eq!(pending, vec![(Alice.to_raw_public().into(), 209)]);
	}

	#[test]
	fn multiple_submission_should_work() {
		let pool = pool();
		pool.submit_one(&BlockId::number(0), uxt(Alice, 209)).unwrap();
		pool.submit_one(&BlockId::number(0), uxt(Alice, 210)).unwrap();

		let pending: Vec<_> = pool.cull_and_get_pending(&BlockId::number(0), |p| p.map(|a| (*a.sender(), a.original.transfer.nonce)).collect()).unwrap();
		assert_eq!(pending, vec![(Alice.to_raw_public().into(), 209), (Alice.to_raw_public().into(), 210)]);
	}

	#[test]
	fn early_nonce_should_be_culled() {
		let pool = pool();
		pool.submit_one(&BlockId::number(0), uxt(Alice, 208)).unwrap();

		let pending: Vec<_> = pool.cull_and_get_pending(&BlockId::number(0), |p| p.map(|a| (*a.sender(), a.original.transfer.nonce)).collect()).unwrap();
		assert_eq!(pending, vec![]);
	}

	#[test]
	fn late_nonce_should_be_queued() {
		let pool = pool();

		pool.submit_one(&BlockId::number(0), uxt(Alice, 210)).unwrap();
		let pending: Vec<_> = pool.cull_and_get_pending(&BlockId::number(0), |p| p.map(|a| (*a.sender(), a.original.transfer.nonce)).collect()).unwrap();
		assert_eq!(pending, vec![]);

		pool.submit_one(&BlockId::number(0), uxt(Alice, 209)).unwrap();
		let pending: Vec<_> = pool.cull_and_get_pending(&BlockId::number(0), |p| p.map(|a| (*a.sender(), a.original.transfer.nonce)).collect()).unwrap();
		assert_eq!(pending, vec![(Alice.to_raw_public().into(), 209), (Alice.to_raw_public().into(), 210)]);
	}

	#[test]
	fn retrying_verification_might_not_change_anything() {
		let pool = pool();
		pool.submit_one(&BlockId::number(0), uxt(Alice, 209)).unwrap();
		pool.submit_one(&BlockId::number(0), uxt(Alice, 210)).unwrap();

		let pending: Vec<_> = pool.cull_and_get_pending(&BlockId::number(0), |p| p.map(|a| (*a.sender(), a.original.transfer.nonce)).collect()).unwrap();
		assert_eq!(pending, vec![(Alice.to_raw_public().into(), 209), (Alice.to_raw_public().into(), 210)]);

		pool.retry_verification(&BlockId::number(1), Alice.to_raw_public().into()).unwrap();

		let pending: Vec<_> = pool.cull_and_get_pending(&BlockId::number(0), |p| p.map(|a| (*a.sender(), a.original.transfer.nonce)).collect()).unwrap();
		assert_eq!(pending, vec![(Alice.to_raw_public().into(), 209), (Alice.to_raw_public().into(), 210)]);
	}
}
