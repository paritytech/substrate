// Copyright 2018-2019 Parity Technologies (UK) Ltd.
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
	collections::{HashSet, HashMap},
	hash,
	sync::Arc,
	time,
};

use crate::base_pool as base;
use crate::error;
use crate::listener::Listener;
use crate::rotator::PoolRotator;
use crate::watcher::Watcher;
use serde::Serialize;
use log::debug;

use futures::{
	Future, FutureExt,
	channel::mpsc,
	future::{Either, ready, join_all},
};
use parking_lot::{Mutex, RwLock};
use sr_primitives::{
	generic::BlockId,
	traits::{self, SaturatedConversion},
	transaction_validity::{TransactionValidity, TransactionTag as Tag, TransactionValidityError},
};

pub use crate::base_pool::Limit;

/// Modification notification event stream type;
pub type EventStream = mpsc::UnboundedReceiver<()>;

/// Extrinsic hash type for a pool.
pub type ExHash<A> = <A as ChainApi>::Hash;
/// Block hash type for a pool.
pub type BlockHash<A> = <<A as ChainApi>::Block as traits::Block>::Hash;
/// Extrinsic type for a pool.
pub type ExtrinsicFor<A> = <<A as ChainApi>::Block as traits::Block>::Extrinsic;
/// Block number type for the ChainApi
pub type NumberFor<A> = traits::NumberFor<<A as ChainApi>::Block>;
/// A type of transaction stored in the pool
pub type TransactionFor<A> = Arc<base::Transaction<ExHash<A>, ExtrinsicFor<A>>>;

/// Concrete extrinsic validation and query logic.
pub trait ChainApi: Send + Sync {
	/// Block type.
	type Block: traits::Block;
	/// Transaction Hash type
	type Hash: hash::Hash + Eq + traits::Member + Serialize;
	/// Error type.
	type Error: From<error::Error> + error::IntoPoolError;
	/// Validate transaction future.
	type ValidationFuture: Future<Output=Result<TransactionValidity, Self::Error>> + Send;

	/// Verify extrinsic at given block.
	fn validate_transaction(
		&self,
		at: &BlockId<Self::Block>,
		uxt: ExtrinsicFor<Self>,
	) -> Self::ValidationFuture;

	/// Returns a block number given the block id.
	fn block_id_to_number(&self, at: &BlockId<Self::Block>) -> Result<Option<NumberFor<Self>>, Self::Error>;

	/// Returns a block hash given the block id.
	fn block_id_to_hash(&self, at: &BlockId<Self::Block>) -> Result<Option<BlockHash<Self>>, Self::Error>;

	/// Returns hash and encoding length of the extrinsic.
	fn hash_and_length(&self, uxt: &ExtrinsicFor<Self>) -> (Self::Hash, usize);
}

/// Pool configuration options.
#[derive(Debug, Clone)]
pub struct Options {
	/// Ready queue limits.
	pub ready: Limit,
	/// Future queue limits.
	pub future: Limit,
}

impl Default for Options {
	fn default() -> Self {
		Options {
			ready: Limit {
				count: 512,
				total_bytes: 10 * 1024 * 1024,
			},
			future: Limit {
				count: 128,
				total_bytes: 1 * 1024 * 1024,
			},
		}
	}
}

/// Extrinsics pool.
pub struct Pool<B: ChainApi> {
	data: SharedPoolData<B>,
}

/// Extrinsics pool shared data.
struct SharedPoolData<B: ChainApi>(Arc<PoolData<B>>);

/// Extrinsics pool data.
struct PoolData<B: ChainApi> {
	api: B,
	options: Options,
	listener: RwLock<Listener<ExHash<B>, BlockHash<B>>>,
	pool: RwLock<base::BasePool<
		ExHash<B>,
		ExtrinsicFor<B>,
	>>,
	import_notification_sinks: Mutex<Vec<mpsc::UnboundedSender<()>>>,
	rotator: PoolRotator<ExHash<B>>,
}

impl<B: ChainApi> Pool<B> {
	/// Imports a bunch of unverified extrinsics to the pool
	pub fn submit_at<T>(&self, at: &BlockId<B::Block>, xts: T, force: bool)
		-> Result<impl Future<Output=Vec<Result<ExHash<B>, B::Error>>>, B::Error>
	where
		T: IntoIterator<Item=ExtrinsicFor<B>>
	{
		self.data.submit_at(at, xts, force)
	}

	/// Imports one unverified extrinsic to the pool
	pub fn submit_one(
		&self,
		at: &BlockId<B::Block>,
		xt: ExtrinsicFor<B>,
	) -> impl Future<Output=Result<ExHash<B>, B::Error>> {
		match self.submit_at(at, std::iter::once(xt), false) {
			Ok(import_future) => Either::Left(import_future
				.map(|mut import_result| import_result
					.pop()
					.expect("One extrinsic passed; one result returned; qed")
				)
			),
			Err(error) => Either::Right(ready(Err(error))),
		}
	}

	/// Import a single extrinsic and starts to watch their progress in the pool.
	pub fn submit_and_watch(
		&self,
		at: &BlockId<B::Block>,
		xt: ExtrinsicFor<B>,
	) -> impl Future<Output=Result<Watcher<ExHash<B>, BlockHash<B>>, B::Error>> {
		let hash = self.data.0.api.hash_and_length(&xt).0;
		let watcher = self.data.0.listener.write().create_watcher(hash);
		self.submit_one(at, xt).map(move |r| r.map(|_| watcher))
	}

	/// Prunes ready transactions.
	///
	/// Used to clear the pool from transactions that were part of recently imported block.
	/// To perform pruning we need the tags that each extrinsic provides and to avoid calling
	/// into runtime too often we first lookup all extrinsics that are in the pool and get
	/// their provided tags from there. Otherwise we query the runtime at the `parent` block.
	pub fn prune(
		&self,
		at: &BlockId<B::Block>,
		parent: &BlockId<B::Block>,
		extrinsics: &[ExtrinsicFor<B>],
	) -> impl Future<Output=Result<(), B::Error>> {
		// Get details of all extrinsics that are already in the pool
		let hashes = extrinsics.iter()
			.map(|extrinsic| self.data.0.api.hash_and_length(extrinsic).0)
			.collect::<Vec<_>>();
		let in_pool = self.data.0.pool.read().by_hash(&hashes);

		// Zip the ones from the pool with the full list (we get pairs `(Extrinsic, Option<TransactionDetails>)`)
		let all = extrinsics.iter().zip(in_pool.iter());

		// Prepare future that collect tags for all extrinsics
		let future_tags = join_all(all
			.map(|(extrinsic, existing_in_pool)|
				match *existing_in_pool {
					// reuse the tags for extrinsics that were found in the pool
					Some(ref transaction) => Either::Left(
						ready(transaction.provides.clone())
					),
					// if it's not found in the pool query the runtime at parent block
					// to get validity info and tags that the extrinsic provides.
					None => Either::Right(self.data.0.api.validate_transaction(parent, extrinsic.clone())
						.then(|validity| ready(match validity {
							Ok(Ok(validity)) => validity.provides,
							// silently ignore invalid extrinsics,
							// cause they might just be inherent
							_ => Vec::new(),
						}))),
				}
			));

		// Prune all transactions that provide collected tags
		let data = self.data.clone();
		let at_clone = at.clone();
		future_tags.then(move |tags|
			data.prune_tags(
				&at_clone,
				tags.into_iter().flat_map(|t| t),
				in_pool.into_iter().filter_map(|x| x).map(|x| x.hash.clone()),
			)
		)
	}

	/// Prunes ready transactions that provide given list of tags.
	///
	/// Given tags are assumed to be always provided now, so all transactions
	/// in the Future Queue that require that particular tag (and have other
	/// requirements satisfied) are promoted to Ready Queue.
	///
	/// Moreover for each provided tag we remove transactions in the pool that:
	/// 1. Provide that tag directly
	/// 2. Are a dependency of pruned transaction.
	///
	/// By removing predecessor transactions as well we might actually end up
	/// pruning too much, so all removed transactions are reverified against
	/// the runtime (`validate_transaction`) to make sure they are invalid.
	///
	/// However we avoid revalidating transactions that are contained within
	/// the second parameter of `known_imported_hashes`. These transactions
	/// (if pruned) are not revalidated and become temporarily banned to
	/// prevent importing them in the (near) future.
	pub fn prune_tags(
		&self,
		at: &BlockId<B::Block>,
		tags: impl IntoIterator<Item=Tag>,
		known_imported_hashes: impl IntoIterator<Item=ExHash<B>> + Clone,
	) -> impl Future<Output=Result<(), B::Error>> {
		self.data.prune_tags(at, tags, known_imported_hashes)
	}

	/// Removes stale transactions from the pool.
	///
	/// Stale transactions are transaction beyond their longevity period.
	/// Note this function does not remove transactions that are already included in the chain.
	/// See `prune_tags` if you want this.
	pub fn clear_stale(&self, at: &BlockId<B::Block>) -> Result<(), B::Error> {
		self.data.clear_stale(at)
	}

	/// Create a new transaction pool.
	pub fn new(options: Options, api: B) -> Self {
		Pool {
			data: SharedPoolData(Arc::new(PoolData {
				api,
				options,
				listener: Default::default(),
				pool: Default::default(),
				import_notification_sinks: Default::default(),
				rotator: Default::default(),
			})),
		}
	}

	/// Return an event stream of transactions imported to the pool.
	pub fn import_notification_stream(&self) -> EventStream {
		let (sink, stream) = mpsc::unbounded();
		self.data.0.import_notification_sinks.lock().push(sink);
		stream
	}

	/// Invoked when extrinsics are broadcasted.
	pub fn on_broadcasted(&self, propagated: HashMap<ExHash<B>, Vec<String>>) {
		let mut listener = self.data.0.listener.write();
		for (hash, peers) in propagated.into_iter() {
			listener.broadcasted(&hash, peers);
		}
	}

	/// Remove from the pool.
	pub fn remove_invalid(&self, hashes: &[ExHash<B>]) -> Vec<TransactionFor<B>> {
		self.data.remove_invalid(hashes)
	}

	/// Get an iterator for ready transactions ordered by priority
	pub fn ready(&self) -> impl Iterator<Item=TransactionFor<B>> {
		self.data.0.pool.read().ready()
	}

	/// Returns pool status.
	pub fn status(&self) -> base::Status {
		self.data.0.pool.read().status()
	}

	/// Returns transaction hash
	pub fn hash_of(&self, xt: &ExtrinsicFor<B>) -> ExHash<B> {
		self.data.0.api.hash_and_length(xt).0
	}
}

impl<B: ChainApi> Clone for SharedPoolData<B> {
	fn clone(&self) -> Self {
		Self(self.0.clone())
	}
}

impl<B: ChainApi> SharedPoolData<B> {
	/// Imports a bunch of unverified extrinsics to the pool
	pub fn submit_at<T>(&self, at: &BlockId<B::Block>, xts: T, force: bool)
		-> Result<impl Future<Output=Vec<Result<ExHash<B>, B::Error>>>, B::Error>
	where
		T: IntoIterator<Item=ExtrinsicFor<B>>
	{
		let block_number = self.0.api.block_id_to_number(at)?
			.ok_or_else(|| error::Error::InvalidBlockId(format!("{:?}", at)).into())?;

		// for each xt, prepare a validation future
		let validation_futures = xts.into_iter().map(move |xt| {
			let (hash, bytes) = self.0.api.hash_and_length(&xt);
			if !force && self.0.rotator.is_banned(&hash) {
				return Either::Left(ready(Err(error::Error::TemporarilyBanned.into())))
			}

			let self_clone = self.clone();
			Either::Right(self.0.api.validate_transaction(at, xt.clone())
				.then(move |validation_result| ready(validation_result.and_then(|validity|
					match validity {
						Ok(validity) => if validity.provides.is_empty() {
							Err(error::Error::NoTagsProvided.into())
						} else {
							Ok(base::Transaction {
								data: xt,
								bytes,
								hash,
								priority: validity.priority,
								requires: validity.requires,
								provides: validity.provides,
								propagate: validity.propagate,
								valid_till: block_number
									.saturated_into::<u64>()
									.saturating_add(validity.longevity),
							})
						},
						Err(TransactionValidityError::Invalid(e)) => {
							Err(error::Error::InvalidTransaction(e).into())
						},
						Err(TransactionValidityError::Unknown(e)) => {
							self_clone.0.listener.write().invalid(&hash);
							Err(error::Error::UnknownTransaction(e).into())
						},
					}
				)))
			)
		});

		// make single validation future that waits all until all extrinsics are validated
		let validation_future = join_all(validation_futures);

		// and then import all successfully validated extrinsics at once + enforce limits
		let self_clone = self.clone();
		let import_future = validation_future
			.then(move |validation_results| ready({
				let import_results = validation_results
					.into_iter()
					.map(|validation_result| {
						let imported = self_clone.0.pool.write().import(validation_result?)?;

						if let base::Imported::Ready { .. } = imported {
							self_clone.0.import_notification_sinks
								.lock()
								.retain(|sink| sink.unbounded_send(()).is_ok());
						}

						let mut listener = self_clone.0.listener.write();
						fire_events(&mut *listener, &imported);
						Ok(imported.hash().clone())
					})
					.collect::<Vec<_>>();

				let removed = self_clone.enforce_limits();

				import_results.into_iter().map(|res| match res {
					Ok(ref hash) if removed.contains(hash) => Err(error::Error::ImmediatelyDropped.into()),
					other => other,
				}).collect::<Vec<Result<ExHash<B>, B::Error>>>()
			}));

		Ok(import_future)
	}

	/// Remove extrinsics that ary beyond pool limits.
	fn enforce_limits(&self) -> HashSet<ExHash<B>> {
		let status = self.0.pool.read().status();
		let ready_limit = &self.0.options.ready;
		let future_limit = &self.0.options.future;

		debug!(target: "txpool", "Pool Status: {:?}", status);

		if ready_limit.is_exceeded(status.ready, status.ready_bytes)
			|| future_limit.is_exceeded(status.future, status.future_bytes) {
			// clean up the pool
			let removed = {
				let mut pool = self.0.pool.write();
				let removed = pool.enforce_limits(ready_limit, future_limit)
					.into_iter().map(|x| x.hash.clone()).collect::<HashSet<_>>();
				// ban all removed transactions
				self.0.rotator.ban(&std::time::Instant::now(), removed.iter().map(|x| x.clone()));
				removed
			};
			// run notifications
			let mut listener = self.0.listener.write();
			for h in &removed {
				listener.dropped(h, None);
			}

			removed
		} else {
			Default::default()
		}
	}


	/// Prunes ready transactions that provide given list of tags.
	fn prune_tags(
		&self,
		at: &BlockId<B::Block>,
		tags: impl IntoIterator<Item=Tag>,
		known_imported_hashes: impl IntoIterator<Item=ExHash<B>> + Clone,
	) -> impl Future<Output=Result<(), B::Error>> {
		// Perform tag-based pruning in the base pool
		let status = self.0.pool.write().prune_tags(tags);
		// Notify event listeners of all transactions
		// that were promoted to `Ready` or were dropped.
		{
			let mut listener = self.0.listener.write();
			for promoted in &status.promoted {
				fire_events(&mut *listener, promoted);
			}
			for f in &status.failed {
				listener.dropped(f, None);
			}
		}
		// make sure that we don't revalidate extrinsics that were part of the recently
		// imported block. This is especially important for UTXO-like chains cause the
		// inputs are pruned so such transaction would go to future again.
		self.0.rotator.ban(&std::time::Instant::now(), known_imported_hashes.clone().into_iter());

		// try to re-submit pruned transactions since some of them might be still valid.
		// note that `known_imported_hashes` will be rejected here due to temporary ban.
		let hashes = status.pruned.iter().map(|tx| tx.hash.clone()).collect::<Vec<_>>();
		let results_future = self.submit_at(at, status.pruned.into_iter().map(|tx| tx.data.clone()), false);
		let results_future = match results_future {
			Ok(results_future) => results_future,
			Err(err) => return Either::Left(ready(Err(err))),
		};

		// Collect the hashes of transactions that now became invalid (meaning that they are successfully pruned).
		let hashes_future = results_future.then(move |results| ready(results
			.into_iter()
			.enumerate()
			.filter_map(move |(idx, r)| match r.map_err(error::IntoPoolError::into_pool_error) {
				Err(Ok(error::Error::InvalidTransaction(_))) => Some(hashes[idx].clone()),
				_ => None,
			})
		));

		// Fire `pruned` notifications for collected hashes and make sure to include
		// `known_imported_hashes` since they were just imported as part of the block.
		let self_clone = self.clone();
		let at_clone = at.clone();
		let hashes_future = hashes_future.then(move |hashes| {
			let notify = || {
				let hashes = hashes.chain(known_imported_hashes.into_iter());

				let header_hash = self_clone.0.api.block_id_to_hash(&at_clone)?
					.ok_or_else(|| error::Error::InvalidBlockId(format!("{:?}", at_clone)).into())?;
				let mut listener = self_clone.0.listener.write();
				for h in hashes {
					listener.pruned(header_hash, &h);
				}

				Ok(())
			};

			ready(notify())
		});

		// perform regular cleanup of old transactions in the pool
		// and update temporary bans.
		let self_clone = self.clone();
		let at_clone = at.clone();
		Either::Right(hashes_future.then(move |r| ready(match r {
			Ok(()) => self_clone.clear_stale(&at_clone),
			Err(err) => Err(err),
		})))
	}

	/// Removes stale transactions from the pool.
	fn clear_stale(&self, at: &BlockId<B::Block>) -> Result<(), B::Error> {
		let block_number = self.0.api.block_id_to_number(at)?
			.ok_or_else(|| error::Error::InvalidBlockId(format!("{:?}", at)).into())?
			.saturated_into::<u64>();
		let now = time::Instant::now();
		let to_remove = {
			self.0.pool.read().ready()
				.filter(|tx| self.0.rotator.ban_if_stale(&now, block_number, &tx))
				.map(|tx| tx.hash.clone())
				.collect::<Vec<_>>()
		};
		let futures_to_remove: Vec<ExHash<B>> = {
			let p = self.0.pool.read();
			let mut hashes = Vec::new();
			for tx in p.futures() {
				if self.0.rotator.ban_if_stale(&now, block_number, &tx) {
					hashes.push(tx.hash.clone());
				}
			}
			hashes
		};
		// removing old transactions
		self.remove_invalid(&to_remove);
		self.remove_invalid(&futures_to_remove);
		// clear banned transactions timeouts
		self.0.rotator.clear_timeouts(&now);

		Ok(())
	}

	/// Remove from the pool.
	fn remove_invalid(&self, hashes: &[ExHash<B>]) -> Vec<TransactionFor<B>> {
		// temporarily ban invalid transactions
		debug!(target: "txpool", "Banning invalid transactions: {:?}", hashes);
		self.0.rotator.ban(&time::Instant::now(), hashes.iter().cloned());

		let invalid = self.0.pool.write().remove_invalid(hashes);

		let mut listener = self.0.listener.write();
		for tx in &invalid {
			listener.invalid(&tx.hash);
		}

		invalid
	}
}

fn fire_events<H, H2, Ex>(
	listener: &mut Listener<H, H2>,
	imported: &base::Imported<H, Ex>,
) where
	H: hash::Hash + Eq + traits::Member + Serialize,
	H2: Clone,
{
	match *imported {
		base::Imported::Ready { ref promoted, ref failed, ref removed, ref hash } => {
			listener.ready(hash, None);
			for f in failed {
				listener.invalid(f);
			}
			for r in removed {
				listener.dropped(&r.hash, Some(hash));
			}
			for p in promoted {
				listener.ready(p, None);
			}
		},
		base::Imported::Future { ref hash } => {
			listener.future(hash)
		},
	}
}

#[cfg(test)]
mod tests {
	use futures::executor::block_on;
	use super::*;
	use sr_primitives::transaction_validity::{ValidTransaction, InvalidTransaction};
	use codec::Encode;
	use test_runtime::{Block, Extrinsic, Transfer, H256, AccountId};
	use assert_matches::assert_matches;
	use crate::watcher;

	const INVALID_NONCE: u64 = 254;

	#[derive(Debug, Default)]
	struct TestApi {
		delay: Mutex<Option<std::sync::mpsc::Receiver<()>>>,
	}

	impl ChainApi for TestApi {
		type Block = Block;
		type Hash = u64;
		type Error = error::Error;
		type ValidationFuture = futures::future::Ready<error::Result<TransactionValidity>>;

		/// Verify extrinsic at given block.
		fn validate_transaction(
			&self,
			at: &BlockId<Self::Block>,
			uxt: ExtrinsicFor<Self>,
		) -> Self::ValidationFuture {
			let block_number = self.block_id_to_number(at).unwrap().unwrap();
			let nonce = uxt.transfer().nonce;

			// This is used to control the test flow.
			if nonce > 0 {
				let opt = self.delay.lock().take();
				if let Some(delay) = opt {
					if delay.recv().is_err() {
						println!("Error waiting for delay!");
					}
				}
			}

			futures::future::ready(if nonce < block_number {
				Ok(InvalidTransaction::Stale.into())
			} else {
				Ok(Ok(ValidTransaction {
					priority: 4,
					requires: if nonce > block_number { vec![vec![nonce as u8 - 1]] } else { vec![] },
					provides: if nonce == INVALID_NONCE { vec![] } else { vec![vec![nonce as u8]] },
					longevity: 3,
					propagate: true,
				}))
			})
		}

		/// Returns a block number given the block id.
		fn block_id_to_number(&self, at: &BlockId<Self::Block>) -> Result<Option<NumberFor<Self>>, Self::Error> {
			Ok(match at {
				BlockId::Number(num) => Some(*num),
				BlockId::Hash(_) => None,
			})
		}

		/// Returns a block hash given the block id.
		fn block_id_to_hash(&self, at: &BlockId<Self::Block>) -> Result<Option<BlockHash<Self>>, Self::Error> {
			Ok(match at {
				BlockId::Number(num) => Some(H256::from_low_u64_be(*num)).into(),
				BlockId::Hash(_) => None,
			})
		}

		/// Hash the extrinsic.
		fn hash_and_length(&self, uxt: &ExtrinsicFor<Self>) -> (Self::Hash, usize) {
			let len = uxt.encode().len();
			(
				(H256::from(uxt.transfer().from.clone()).to_low_u64_be() << 5) + uxt.transfer().nonce,
				len
			)
		}
	}

	fn uxt(transfer: Transfer) -> Extrinsic {
		Extrinsic::Transfer(transfer, Default::default())
	}

	fn pool() -> Pool<TestApi> {
		Pool::new(Default::default(), TestApi::default())
	}


	#[test]
	fn should_validate_and_import_transaction() {
		// given
		let pool = pool();

		// when
		let hash = block_on(pool.submit_one(&BlockId::Number(0), uxt(Transfer {
			from: AccountId::from_h256(H256::from_low_u64_be(1)),
			to: AccountId::from_h256(H256::from_low_u64_be(2)),
			amount: 5,
			nonce: 0,
		}))).unwrap();

		// then
		assert_eq!(pool.ready().map(|v| v.hash).collect::<Vec<_>>(), vec![hash]);
	}

	#[test]
	fn should_reject_if_temporarily_banned() {
		// given
		let pool = pool();
		let uxt = uxt(Transfer {
			from: AccountId::from_h256(H256::from_low_u64_be(1)),
			to: AccountId::from_h256(H256::from_low_u64_be(2)),
			amount: 5,
			nonce: 0,
		});

		// when
		pool.data.0.rotator.ban(&time::Instant::now(), vec![pool.hash_of(&uxt)]);
		let res = block_on(pool.submit_one(&BlockId::Number(0), uxt));
		assert_eq!(pool.status().ready, 0);
		assert_eq!(pool.status().future, 0);

		// then
		assert_matches!(res.unwrap_err(), error::Error::TemporarilyBanned);
	}

	#[test]
	fn should_notify_about_pool_events() {
		let stream = {
			// given
			let pool = pool();
			let stream = pool.import_notification_stream();

			// when
			let _hash = block_on(pool.submit_one(&BlockId::Number(0), uxt(Transfer {
				from: AccountId::from_h256(H256::from_low_u64_be(1)),
				to: AccountId::from_h256(H256::from_low_u64_be(2)),
				amount: 5,
				nonce: 0,
			}))).unwrap();
			let _hash = block_on(pool.submit_one(&BlockId::Number(0), uxt(Transfer {
				from: AccountId::from_h256(H256::from_low_u64_be(1)),
				to: AccountId::from_h256(H256::from_low_u64_be(2)),
				amount: 5,
				nonce: 1,
			}))).unwrap();
			// future doesn't count
			let _hash = block_on(pool.submit_one(&BlockId::Number(0), uxt(Transfer {
				from: AccountId::from_h256(H256::from_low_u64_be(1)),
				to: AccountId::from_h256(H256::from_low_u64_be(2)),
				amount: 5,
				nonce: 3,
			}))).unwrap();

			assert_eq!(pool.status().ready, 2);
			assert_eq!(pool.status().future, 1);
			stream
		};

		// then
		let mut it = futures::executor::block_on_stream(stream);
		assert_eq!(it.next(), Some(()));
		assert_eq!(it.next(), Some(()));
		assert_eq!(it.next(), None);
	}

	#[test]
	fn should_clear_stale_transactions() {
		// given
		let pool = pool();
		let hash1 = block_on(pool.submit_one(&BlockId::Number(0), uxt(Transfer {
			from: AccountId::from_h256(H256::from_low_u64_be(1)),
			to: AccountId::from_h256(H256::from_low_u64_be(2)),
			amount: 5,
			nonce: 0,
		}))).unwrap();
		let hash2 = block_on(pool.submit_one(&BlockId::Number(0), uxt(Transfer {
			from: AccountId::from_h256(H256::from_low_u64_be(1)),
			to: AccountId::from_h256(H256::from_low_u64_be(2)),
			amount: 5,
			nonce: 1,
		}))).unwrap();
		let hash3 = block_on(pool.submit_one(&BlockId::Number(0), uxt(Transfer {
			from: AccountId::from_h256(H256::from_low_u64_be(1)),
			to: AccountId::from_h256(H256::from_low_u64_be(2)),
			amount: 5,
			nonce: 3,
		}))).unwrap();

		// when
		pool.clear_stale(&BlockId::Number(5)).unwrap();

		// then
		assert_eq!(pool.ready().count(), 0);
		assert_eq!(pool.status().future, 0);
		assert_eq!(pool.status().ready, 0);
		// make sure they are temporarily banned as well
		assert!(pool.data.0.rotator.is_banned(&hash1));
		assert!(pool.data.0.rotator.is_banned(&hash2));
		assert!(pool.data.0.rotator.is_banned(&hash3));
	}

	#[test]
	fn should_ban_mined_transactions() {
		// given
		let pool = pool();
		let hash1 = block_on(pool.submit_one(&BlockId::Number(0), uxt(Transfer {
			from: AccountId::from_h256(H256::from_low_u64_be(1)),
			to: AccountId::from_h256(H256::from_low_u64_be(2)),
			amount: 5,
			nonce: 0,
		}))).unwrap();

		// when
		block_on(pool.prune_tags(&BlockId::Number(1), vec![vec![0]], vec![hash1.clone()])).unwrap();

		// then
		assert!(pool.data.0.rotator.is_banned(&hash1));
	}

	#[test]
	fn should_limit_futures() {
		// given
		let limit = Limit {
			count: 100,
			total_bytes: 200,
		};
		let pool = Pool::new(Options {
			ready: limit.clone(),
			future: limit.clone(),
		}, TestApi::default());

		let hash1 = block_on(pool.submit_one(&BlockId::Number(0), uxt(Transfer {
			from: AccountId::from_h256(H256::from_low_u64_be(1)),
			to: AccountId::from_h256(H256::from_low_u64_be(2)),
			amount: 5,
			nonce: 1,
		}))).unwrap();
		assert_eq!(pool.status().future, 1);

		// when
		let hash2 = block_on(pool.submit_one(&BlockId::Number(0), uxt(Transfer {
			from: AccountId::from_h256(H256::from_low_u64_be(2)),
			to: AccountId::from_h256(H256::from_low_u64_be(2)),
			amount: 5,
			nonce: 10,
		}))).unwrap();

		// then
		assert_eq!(pool.status().future, 1);
		assert!(pool.data.0.rotator.is_banned(&hash1));
		assert!(!pool.data.0.rotator.is_banned(&hash2));
	}

	#[test]
	fn should_error_if_reject_immediately() {
		// given
		let limit = Limit {
			count: 100,
			total_bytes: 10,
		};
		let pool = Pool::new(Options {
			ready: limit.clone(),
			future: limit.clone(),
		}, TestApi::default());

		// when
		block_on(pool.submit_one(&BlockId::Number(0), uxt(Transfer {
			from: AccountId::from_h256(H256::from_low_u64_be(1)),
			to: AccountId::from_h256(H256::from_low_u64_be(2)),
			amount: 5,
			nonce: 1,
		}))).unwrap_err();

		// then
		assert_eq!(pool.status().ready, 0);
		assert_eq!(pool.status().future, 0);
	}

	#[test]
	fn should_reject_transactions_with_no_provides() {
		// given
		let pool = pool();

		// when
		let err = block_on(pool.submit_one(&BlockId::Number(0), uxt(Transfer {
			from: AccountId::from_h256(H256::from_low_u64_be(1)),
			to: AccountId::from_h256(H256::from_low_u64_be(2)),
			amount: 5,
			nonce: INVALID_NONCE,
		}))).unwrap_err();

		// then
		assert_eq!(pool.status().ready, 0);
		assert_eq!(pool.status().future, 0);
		assert_matches!(err, error::Error::NoTagsProvided);
	}

	mod listener {
		use super::*;

		#[test]
		fn should_trigger_ready_and_finalized() {
			// given
			let pool = pool();
			let watcher = block_on(pool.submit_and_watch(&BlockId::Number(0), uxt(Transfer {
				from: AccountId::from_h256(H256::from_low_u64_be(1)),
				to: AccountId::from_h256(H256::from_low_u64_be(2)),
				amount: 5,
				nonce: 0,
			}))).unwrap();
			assert_eq!(pool.status().ready, 1);
			assert_eq!(pool.status().future, 0);

			// when
			block_on(pool.prune_tags(&BlockId::Number(2), vec![vec![0u8]], vec![])).unwrap();
			assert_eq!(pool.status().ready, 0);
			assert_eq!(pool.status().future, 0);

			// then
			let mut stream = futures::executor::block_on_stream(watcher.into_stream());
			assert_eq!(stream.next(), Some(watcher::Status::Ready));
			assert_eq!(stream.next(), Some(watcher::Status::Finalized(H256::from_low_u64_be(2).into())));
			assert_eq!(stream.next(), None);
		}

		#[test]
		fn should_trigger_ready_and_finalized_when_pruning_via_hash() {
			// given
			let pool = pool();
			let watcher = block_on(pool.submit_and_watch(&BlockId::Number(0), uxt(Transfer {
				from: AccountId::from_h256(H256::from_low_u64_be(1)),
				to: AccountId::from_h256(H256::from_low_u64_be(2)),
				amount: 5,
				nonce: 0,
			}))).unwrap();
			assert_eq!(pool.status().ready, 1);
			assert_eq!(pool.status().future, 0);

			// when
			block_on(pool.prune_tags(&BlockId::Number(2), vec![vec![0u8]], vec![2u64])).unwrap();
			assert_eq!(pool.status().ready, 0);
			assert_eq!(pool.status().future, 0);

			// then
			let mut stream = futures::executor::block_on_stream(watcher.into_stream());
			assert_eq!(stream.next(), Some(watcher::Status::Ready));
			assert_eq!(stream.next(), Some(watcher::Status::Finalized(H256::from_low_u64_be(2).into())));
			assert_eq!(stream.next(), None);
		}

		#[test]
		fn should_trigger_future_and_ready_after_promoted() {
			// given
			let pool = pool();
			let watcher = block_on(pool.submit_and_watch(&BlockId::Number(0), uxt(Transfer {
				from: AccountId::from_h256(H256::from_low_u64_be(1)),
				to: AccountId::from_h256(H256::from_low_u64_be(2)),
				amount: 5,
				nonce: 1,
			}))).unwrap();
			assert_eq!(pool.status().ready, 0);
			assert_eq!(pool.status().future, 1);

			// when
			block_on(pool.submit_one(&BlockId::Number(0), uxt(Transfer {
				from: AccountId::from_h256(H256::from_low_u64_be(1)),
				to: AccountId::from_h256(H256::from_low_u64_be(2)),
				amount: 5,
				nonce: 0,
			}))).unwrap();
			assert_eq!(pool.status().ready, 2);

			// then
			let mut stream = futures::executor::block_on_stream(watcher.into_stream());
			assert_eq!(stream.next(), Some(watcher::Status::Future));
			assert_eq!(stream.next(), Some(watcher::Status::Ready));
		}

		#[test]
		fn should_trigger_invalid_and_ban() {
			// given
			let pool = pool();
			let uxt = uxt(Transfer {
				from: AccountId::from_h256(H256::from_low_u64_be(1)),
				to: AccountId::from_h256(H256::from_low_u64_be(2)),
				amount: 5,
				nonce: 0,
			});
			let watcher = block_on(pool.submit_and_watch(&BlockId::Number(0), uxt)).unwrap();
			assert_eq!(pool.status().ready, 1);

			// when
			pool.remove_invalid(&[*watcher.hash()]);


			// then
			let mut stream = futures::executor::block_on_stream(watcher.into_stream());
			assert_eq!(stream.next(), Some(watcher::Status::Ready));
			assert_eq!(stream.next(), Some(watcher::Status::Invalid));
			assert_eq!(stream.next(), None);
		}

		#[test]
		fn should_trigger_broadcasted() {
			// given
			let pool = pool();
			let uxt = uxt(Transfer {
				from: AccountId::from_h256(H256::from_low_u64_be(1)),
				to: AccountId::from_h256(H256::from_low_u64_be(2)),
				amount: 5,
				nonce: 0,
			});
			let watcher = block_on(pool.submit_and_watch(&BlockId::Number(0), uxt)).unwrap();
			assert_eq!(pool.status().ready, 1);

			// when
			let mut map = HashMap::new();
			let peers = vec!["a".into(), "b".into(), "c".into()];
			map.insert(*watcher.hash(), peers.clone());
			pool.on_broadcasted(map);


			// then
			let mut stream = futures::executor::block_on_stream(watcher.into_stream());
			assert_eq!(stream.next(), Some(watcher::Status::Ready));
			assert_eq!(stream.next(), Some(watcher::Status::Broadcast(peers)));
		}

		#[test]
		fn should_trigger_dropped() {
			// given
			let limit = Limit {
				count: 1,
				total_bytes: 1000,
			};
			let pool = Pool::new(Options {
				ready: limit.clone(),
				future: limit.clone(),
			}, TestApi::default());

			let xt = uxt(Transfer {
				from: AccountId::from_h256(H256::from_low_u64_be(1)),
				to: AccountId::from_h256(H256::from_low_u64_be(2)),
				amount: 5,
				nonce: 0,
			});
			let watcher = block_on(pool.submit_and_watch(&BlockId::Number(0), xt)).unwrap();
			assert_eq!(pool.status().ready, 1);

			// when
			let xt = uxt(Transfer {
				from: AccountId::from_h256(H256::from_low_u64_be(2)),
				to: AccountId::from_h256(H256::from_low_u64_be(1)),
				amount: 4,
				nonce: 1,
			});
			block_on(pool.submit_one(&BlockId::Number(1), xt)).unwrap();
			assert_eq!(pool.status().ready, 1);

			// then
			let mut stream = futures::executor::block_on_stream(watcher.into_stream());
			assert_eq!(stream.next(), Some(watcher::Status::Ready));
			assert_eq!(stream.next(), Some(watcher::Status::Dropped));
		}

		#[test]
		fn should_handle_pruning_in_the_middle_of_import() {
			let _ = env_logger::try_init();
			// given
			let (ready, is_ready) = std::sync::mpsc::sync_channel(0);
			let (tx, rx) = std::sync::mpsc::sync_channel(1);
			let mut api = TestApi::default();
			api.delay = Mutex::new(rx.into());
			let pool = Arc::new(Pool::new(Default::default(), api));

			// when
			let xt = uxt(Transfer {
				from: AccountId::from_h256(H256::from_low_u64_be(1)),
				to: AccountId::from_h256(H256::from_low_u64_be(2)),
				amount: 5,
				nonce: 1,
			});

			// This transaction should go to future, since we use `nonce: 1`
			let pool2 = pool.clone();
			std::thread::spawn(move || {
				block_on(pool2.submit_one(&BlockId::Number(0), xt)).unwrap();
				ready.send(()).unwrap();
			});

			// But now before the previous one is imported we import
			// the one that it depends on.
			let xt = uxt(Transfer {
				from: AccountId::from_h256(H256::from_low_u64_be(1)),
				to: AccountId::from_h256(H256::from_low_u64_be(2)),
				amount: 4,
				nonce: 0,
			});
			// The tag the above transaction provides (TestApi is using just nonce as u8)
			let provides = vec![0_u8];
			block_on(pool.submit_one(&BlockId::Number(0), xt)).unwrap();
			assert_eq!(pool.status().ready, 1);

			// Now block import happens before the second transaction is able to finish verification.
			block_on(pool.prune_tags(&BlockId::Number(1), vec![provides], vec![])).unwrap();
			assert_eq!(pool.status().ready, 0);


			// so when we release the verification of the previous one it will have
			// something in `requires`, but should go to ready directly, since the previous transaction was imported
			// correctly.
			tx.send(()).unwrap();

			// then
			is_ready.recv().unwrap(); // wait for finish
			assert_eq!(pool.status().ready, 1);
			assert_eq!(pool.status().future, 0);
		}
	}
}
