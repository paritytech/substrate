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
use error_chain::bail;
use log::debug;

use futures::sync::mpsc;
use parking_lot::{Mutex, RwLock};
use sr_primitives::{
	generic::BlockId,
	traits::{self, As},
	transaction_validity::{TransactionValidity, TransactionTag as Tag},
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

	/// Verify extrinsic at given block.
	fn validate_transaction(&self, at: &BlockId<Self::Block>, uxt: ExtrinsicFor<Self>) -> Result<TransactionValidity, Self::Error>;

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
	pub fn submit_at<T>(&self, at: &BlockId<B::Block>, xts: T) -> Result<Vec<Result<ExHash<B>, B::Error>>, B::Error> where
		T: IntoIterator<Item=ExtrinsicFor<B>>
	{
		let block_number = self.api.block_id_to_number(at)?
			.ok_or_else(|| error::ErrorKind::Msg(format!("Invalid block id: {:?}", at)).into())?;

		let results = xts
			.into_iter()
			.map(|xt| -> Result<_, B::Error> {
				let (hash, bytes) = self.api.hash_and_length(&xt);
				if self.rotator.is_banned(&hash) {
					bail!(error::Error::from(error::ErrorKind::TemporarilyBanned))
				}

				match self.api.validate_transaction(at, xt.clone())? {
					TransactionValidity::Valid { priority, requires, provides, longevity } => {
						Ok(base::Transaction {
							data: xt,
							bytes,
							hash,
							priority,
							requires,
							provides,
							valid_till: block_number.as_().saturating_add(longevity),
						})
					},
					TransactionValidity::Invalid(e) => {
						bail!(error::Error::from(error::ErrorKind::InvalidTransaction(e)))
					},
					TransactionValidity::Unknown(e) => {
						self.listener.write().invalid(&hash);
						bail!(error::Error::from(error::ErrorKind::UnknownTransactionValidity(e)))
					},
				}
			})
			.map(|tx| {
				let imported = self.pool.write().import(tx?)?;

				if let base::Imported::Ready { .. } = imported {
					self.import_notification_sinks.lock().retain(|sink| sink.unbounded_send(()).is_ok());
				}

				let mut listener = self.listener.write();
				fire_events(&mut *listener, &imported);
				Ok(imported.hash().clone())
			})
			.collect::<Vec<_>>();

		let removed = self.enforce_limits();

		Ok(results.into_iter().map(|res| match res {
			Ok(ref hash) if removed.contains(hash) => Err(error::Error::from(error::ErrorKind::ImmediatelyDropped).into()),
			other => other,
		}).collect())
	}

	fn enforce_limits(&self) -> HashSet<ExHash<B>> {
		let status = self.pool.read().status();
		let ready_limit = &self.options.ready;
		let future_limit = &self.options.future;

		debug!(target: "txpool", "Pool Status: {:?}", status);

		if ready_limit.is_exceeded(status.ready, status.ready_bytes)
			|| future_limit.is_exceeded(status.future, status.future_bytes) {
			// clean up the pool
			let removed = {
				let mut pool = self.pool.write();
				let removed = pool.enforce_limits(ready_limit, future_limit)
					.into_iter().map(|x| x.hash.clone()).collect::<HashSet<_>>();
				// ban all removed transactions
				self.rotator.ban(&std::time::Instant::now(), removed.iter().map(|x| x.clone()));
				removed
			};
			// run notifications
			let mut listener = self.listener.write();
			for h in &removed {
				listener.dropped(h, None);
			}

			removed
		} else {
			Default::default()
		}
	}

	/// Imports one unverified extrinsic to the pool
	pub fn submit_one(&self, at: &BlockId<B::Block>, xt: ExtrinsicFor<B>) -> Result<ExHash<B>, B::Error> {
		Ok(self.submit_at(at, ::std::iter::once(xt))?.pop().expect("One extrinsic passed; one result returned; qed")?)
	}

	/// Import a single extrinsic and starts to watch their progress in the pool.
	pub fn submit_and_watch(&self, at: &BlockId<B::Block>, xt: ExtrinsicFor<B>) -> Result<Watcher<ExHash<B>, BlockHash<B>>, B::Error> {
		let hash = self.api.hash_and_length(&xt).0;
		let watcher = self.listener.write().create_watcher(hash);
		self.submit_one(at, xt)?;
		Ok(watcher)
	}

	/// Prunes ready transactions.
	///
	/// Used to clear the pool from transactions that were part of recently imported block.
	/// To perform pruning we need the tags that each extrinsic provides and to avoid calling
	/// into runtime too often we first lookup all extrinsics that are in the pool and get
	/// their provided tags from there. Otherwise we query the runtime at the `parent` block.
	pub fn prune(&self, at: &BlockId<B::Block>, parent: &BlockId<B::Block>, extrinsics: &[ExtrinsicFor<B>]) -> Result<(), B::Error> {
		let mut tags = Vec::with_capacity(extrinsics.len());
		// Get details of all extrinsics that are already in the pool
		let hashes = extrinsics.iter().map(|extrinsic| self.api.hash_and_length(extrinsic).0).collect::<Vec<_>>();
		let in_pool = self.pool.read().by_hash(&hashes);
		{
			// Zip the ones from the pool with the full list (we get pairs `(Extrinsic, Option<TransactionDetails>)`)
			let all = extrinsics.iter().zip(in_pool.iter());

			for (extrinsic, existing_in_pool) in all {
				match *existing_in_pool {
					// reuse the tags for extrinsis that were found in the pool
					Some(ref transaction) => {
						tags.extend(transaction.provides.iter().cloned());
					},
					// if it's not found in the pool query the runtime at parent block
					// to get validity info and tags that the extrinsic provides.
					None => {
						let validity = self.api.validate_transaction(parent, extrinsic.clone());
						match validity {
							Ok(TransactionValidity::Valid { mut provides, .. }) => {
								tags.append(&mut provides);
							},
							// silently ignore invalid extrinsics,
							// cause they might just be inherent
							_ => {}
						}
					},
				}
			}
		}

		self.prune_tags(at, tags, in_pool.into_iter().filter_map(|x| x).map(|x| x.hash.clone()))?;

		Ok(())
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
	) -> Result<(), B::Error> {
		// Perform tag-based pruning in the base pool
		let status = self.pool.write().prune_tags(tags);
		// Notify event listeners of all transactions
		// that were promoted to `Ready` or were dropped.
		{
			let mut listener = self.listener.write();
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
		self.rotator.ban(&std::time::Instant::now(), known_imported_hashes.clone().into_iter());

		// try to re-submit pruned transactions since some of them might be still valid.
		// note that `known_imported_hashes` will be rejected here due to temporary ban.
		let hashes = status.pruned.iter().map(|tx| tx.hash.clone()).collect::<Vec<_>>();
		let results = self.submit_at(at, status.pruned.into_iter().map(|tx| tx.data.clone()))?;

		// Collect the hashes of transactions that now became invalid (meaning that they are succesfully pruned).
		let hashes = results.into_iter().enumerate().filter_map(|(idx, r)| match r.map_err(error::IntoPoolError::into_pool_error) {
			Err(Ok(err)) => match err.kind() {
				error::ErrorKind::InvalidTransaction(_) => Some(hashes[idx].clone()),
				_ => None,
			},
			_ => None,
		});
		// Fire `pruned` notifications for collected hashes and make sure to include
		// `known_imported_hashes` since they were just imported as part of the block.
		let hashes = hashes.chain(known_imported_hashes.into_iter());
		{
			let header_hash = self.api.block_id_to_hash(at)?
				.ok_or_else(|| error::ErrorKind::Msg(format!("Invalid block id: {:?}", at)).into())?;
			let mut listener = self.listener.write();
			for h in hashes {
				listener.pruned(header_hash, &h);
			}
		}
		// perform regular cleanup of old transactions in the pool
		// and update temporary bans.
		self.clear_stale(at)?;
		Ok(())
	}

	/// Removes stale transactions from the pool.
	///
	/// Stale transactions are transaction beyond their longevity period.
	/// Note this function does not remove transactions that are already included in the chain.
	/// See `prune_tags` if you want this.
	pub fn clear_stale(&self, at: &BlockId<B::Block>) -> Result<(), B::Error> {
		let block_number = self.api.block_id_to_number(at)?
				.ok_or_else(|| error::ErrorKind::Msg(format!("Invalid block id: {:?}", at)).into())?
				.as_();
		let now = time::Instant::now();
		let to_remove = {
			self.ready()
				.filter(|tx| self.rotator.ban_if_stale(&now, block_number, &tx))
				.map(|tx| tx.hash.clone())
				.collect::<Vec<_>>()
		};
		let futures_to_remove: Vec<ExHash<B>> = {
			let p = self.pool.read();
			let mut hashes = Vec::new();
			for tx in p.futures() {
				if self.rotator.ban_if_stale(&now, block_number, &tx) {
					hashes.push(tx.hash.clone());
				}
			}
			hashes
		};
		// removing old transactions
		self.remove_invalid(&to_remove);
		self.remove_invalid(&futures_to_remove);
		// clear banned transactions timeouts
		self.rotator.clear_timeouts(&now);

		Ok(())
	}

	/// Create a new transaction pool.
	pub fn new(options: Options, api: B) -> Self {
		Pool {
			api,
			options,
			listener: Default::default(),
			pool: Default::default(),
			import_notification_sinks: Default::default(),
			rotator: Default::default(),
		}
	}

	/// Return an event stream of transactions imported to the pool.
	pub fn import_notification_stream(&self) -> EventStream {
		let (sink, stream) = mpsc::unbounded();
		self.import_notification_sinks.lock().push(sink);
		stream
	}

	/// Invoked when extrinsics are broadcasted.
	pub fn on_broadcasted(&self, propagated: HashMap<ExHash<B>, Vec<String>>) {
		let mut listener = self.listener.write();
		for (hash, peers) in propagated.into_iter() {
			listener.broadcasted(&hash, peers);
		}
	}

	/// Remove from the pool.
	pub fn remove_invalid(&self, hashes: &[ExHash<B>]) -> Vec<TransactionFor<B>> {
		// temporarily ban invalid transactions
		debug!(target: "txpool", "Banning invalid transactions: {:?}", hashes);
		self.rotator.ban(&time::Instant::now(), hashes.iter().cloned());

		let invalid = self.pool.write().remove_invalid(hashes);

		let mut listener = self.listener.write();
		for tx in &invalid {
			listener.invalid(&tx.hash);
		}

		invalid
	}

	/// Get an iterator for ready transactions ordered by priority
	pub fn ready(&self) -> impl Iterator<Item=TransactionFor<B>> {
		self.pool.read().ready()
	}

	/// Returns pool status.
	pub fn status(&self) -> base::Status {
		self.pool.read().status()
	}

	/// Returns transaction hash
	#[cfg(test)]
	fn hash_of(&self, xt: &ExtrinsicFor<B>) -> ExHash<B> {
		self.api.hash_and_length(xt).0
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
	use super::*;
	use futures::Stream;
	use parity_codec::Encode;
	use test_runtime::{Block, Extrinsic, Transfer, H256, AccountId};
	use assert_matches::assert_matches;
	use crate::watcher;

	#[derive(Debug, Default)]
	struct TestApi {
		delay: Mutex<Option<std::sync::mpsc::Receiver<()>>>,
	}

	impl ChainApi for TestApi {
		type Block = Block;
		type Hash = u64;
		type Error = error::Error;

		/// Verify extrinsic at given block.
		fn validate_transaction(&self, at: &BlockId<Self::Block>, uxt: ExtrinsicFor<Self>) -> Result<TransactionValidity, Self::Error> {

			let block_number = self.block_id_to_number(at)?.unwrap();
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

			if nonce < block_number {
				Ok(TransactionValidity::Invalid(0))
			} else {
				Ok(TransactionValidity::Valid {
					priority: 4,
					requires: if nonce > block_number { vec![vec![nonce as u8 - 1]] } else { vec![] },
					provides: vec![vec![nonce as u8]],
					longevity: 3,
				})
			}
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
		let hash = pool.submit_one(&BlockId::Number(0), uxt(Transfer {
			from: AccountId::from_h256(H256::from_low_u64_be(1)),
			to: AccountId::from_h256(H256::from_low_u64_be(2)),
			amount: 5,
			nonce: 0,
		})).unwrap();

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
		pool.rotator.ban(&time::Instant::now(), vec![pool.hash_of(&uxt)]);
		let res = pool.submit_one(&BlockId::Number(0), uxt);
		assert_eq!(pool.status().ready, 0);
		assert_eq!(pool.status().future, 0);

		// then
		assert_matches!(res.unwrap_err().kind(), error::ErrorKind::TemporarilyBanned);
	}

	#[test]
	fn should_notify_about_pool_events() {
		let stream = {
			// given
			let pool = pool();
			let stream = pool.import_notification_stream();

			// when
			let _hash = pool.submit_one(&BlockId::Number(0), uxt(Transfer {
				from: AccountId::from_h256(H256::from_low_u64_be(1)),
				to: AccountId::from_h256(H256::from_low_u64_be(2)),
				amount: 5,
				nonce: 0,
			})).unwrap();
			let _hash = pool.submit_one(&BlockId::Number(0), uxt(Transfer {
				from: AccountId::from_h256(H256::from_low_u64_be(1)),
				to: AccountId::from_h256(H256::from_low_u64_be(2)),
				amount: 5,
				nonce: 1,
			})).unwrap();
			// future doesn't count
			let _hash = pool.submit_one(&BlockId::Number(0), uxt(Transfer {
				from: AccountId::from_h256(H256::from_low_u64_be(1)),
				to: AccountId::from_h256(H256::from_low_u64_be(2)),
				amount: 5,
				nonce: 3,
			})).unwrap();

			assert_eq!(pool.status().ready, 2);
			assert_eq!(pool.status().future, 1);
			stream
		};

		// then
		let mut it = stream.wait();
		assert_eq!(it.next(), Some(Ok(())));
		assert_eq!(it.next(), Some(Ok(())));
		assert_eq!(it.next(), None);
	}

	#[test]
	fn should_clear_stale_transactions() {
		// given
		let pool = pool();
		let hash1 = pool.submit_one(&BlockId::Number(0), uxt(Transfer {
			from: AccountId::from_h256(H256::from_low_u64_be(1)),
			to: AccountId::from_h256(H256::from_low_u64_be(2)),
			amount: 5,
			nonce: 0,
		})).unwrap();
		let hash2 = pool.submit_one(&BlockId::Number(0), uxt(Transfer {
			from: AccountId::from_h256(H256::from_low_u64_be(1)),
			to: AccountId::from_h256(H256::from_low_u64_be(2)),
			amount: 5,
			nonce: 1,
		})).unwrap();
		let hash3 = pool.submit_one(&BlockId::Number(0), uxt(Transfer {
			from: AccountId::from_h256(H256::from_low_u64_be(1)),
			to: AccountId::from_h256(H256::from_low_u64_be(2)),
			amount: 5,
			nonce: 3,
		})).unwrap();

		// when
		pool.clear_stale(&BlockId::Number(5)).unwrap();

		// then
		assert_eq!(pool.ready().count(), 0);
		assert_eq!(pool.status().future, 0);
		assert_eq!(pool.status().ready, 0);
		// make sure they are temporarily banned as well
		assert!(pool.rotator.is_banned(&hash1));
		assert!(pool.rotator.is_banned(&hash2));
		assert!(pool.rotator.is_banned(&hash3));
	}

	#[test]
	fn should_ban_mined_transactions() {
		// given
		let pool = pool();
		let hash1 = pool.submit_one(&BlockId::Number(0), uxt(Transfer {
			from: AccountId::from_h256(H256::from_low_u64_be(1)),
			to: AccountId::from_h256(H256::from_low_u64_be(2)),
			amount: 5,
			nonce: 0,
		})).unwrap();

		// when
		pool.prune_tags(&BlockId::Number(1), vec![vec![0]], vec![hash1.clone()]).unwrap();

		// then
		assert!(pool.rotator.is_banned(&hash1));
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

		let hash1 = pool.submit_one(&BlockId::Number(0), uxt(Transfer {
			from: AccountId::from_h256(H256::from_low_u64_be(1)),
			to: AccountId::from_h256(H256::from_low_u64_be(2)),
			amount: 5,
			nonce: 1,
		})).unwrap();
		assert_eq!(pool.status().future, 1);

		// when
		let hash2 = pool.submit_one(&BlockId::Number(0), uxt(Transfer {
			from: AccountId::from_h256(H256::from_low_u64_be(2)),
			to: AccountId::from_h256(H256::from_low_u64_be(2)),
			amount: 5,
			nonce: 10,
		})).unwrap();

		// then
		assert_eq!(pool.status().future, 1);
		assert!(pool.rotator.is_banned(&hash1));
		assert!(!pool.rotator.is_banned(&hash2));
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
		pool.submit_one(&BlockId::Number(0), uxt(Transfer {
			from: AccountId::from_h256(H256::from_low_u64_be(1)),
			to: AccountId::from_h256(H256::from_low_u64_be(2)),
			amount: 5,
			nonce: 1,
		})).unwrap_err();

		// then
		assert_eq!(pool.status().ready, 0);
		assert_eq!(pool.status().future, 0);
	}


	mod listener {
		use super::*;

		#[test]
		fn should_trigger_ready_and_finalized() {
			// given
			let pool = pool();
			let watcher = pool.submit_and_watch(&BlockId::Number(0), uxt(Transfer {
				from: AccountId::from_h256(H256::from_low_u64_be(1)),
				to: AccountId::from_h256(H256::from_low_u64_be(2)),
				amount: 5,
				nonce: 0,
			})).unwrap();
			assert_eq!(pool.status().ready, 1);
			assert_eq!(pool.status().future, 0);

			// when
			pool.prune_tags(&BlockId::Number(2), vec![vec![0u8]], vec![]).unwrap();
			assert_eq!(pool.status().ready, 0);
			assert_eq!(pool.status().future, 0);

			// then
			let mut stream = watcher.into_stream().wait();
			assert_eq!(stream.next(), Some(Ok(watcher::Status::Ready)));
			assert_eq!(stream.next(), Some(Ok(watcher::Status::Finalized(H256::from_low_u64_be(2).into()))));
			assert_eq!(stream.next(), None);
		}

		#[test]
		fn should_trigger_ready_and_finalized_when_pruning_via_hash() {
			// given
			let pool = pool();
			let watcher = pool.submit_and_watch(&BlockId::Number(0), uxt(Transfer {
				from: AccountId::from_h256(H256::from_low_u64_be(1)),
				to: AccountId::from_h256(H256::from_low_u64_be(2)),
				amount: 5,
				nonce: 0,
			})).unwrap();
			assert_eq!(pool.status().ready, 1);
			assert_eq!(pool.status().future, 0);

			// when
			pool.prune_tags(&BlockId::Number(2), vec![vec![0u8]], vec![2u64]).unwrap();
			assert_eq!(pool.status().ready, 0);
			assert_eq!(pool.status().future, 0);

			// then
			let mut stream = watcher.into_stream().wait();
			assert_eq!(stream.next(), Some(Ok(watcher::Status::Ready)));
			assert_eq!(stream.next(), Some(Ok(watcher::Status::Finalized(H256::from_low_u64_be(2).into()))));
			assert_eq!(stream.next(), None);
		}

		#[test]
		fn should_trigger_future_and_ready_after_promoted() {
			// given
			let pool = pool();
			let watcher = pool.submit_and_watch(&BlockId::Number(0), uxt(Transfer {
				from: AccountId::from_h256(H256::from_low_u64_be(1)),
				to: AccountId::from_h256(H256::from_low_u64_be(2)),
				amount: 5,
				nonce: 1,
			})).unwrap();
			assert_eq!(pool.status().ready, 0);
			assert_eq!(pool.status().future, 1);

			// when
			pool.submit_one(&BlockId::Number(0), uxt(Transfer {
				from: AccountId::from_h256(H256::from_low_u64_be(1)),
				to: AccountId::from_h256(H256::from_low_u64_be(2)),
				amount: 5,
				nonce: 0,
			})).unwrap();
			assert_eq!(pool.status().ready, 2);

			// then
			let mut stream = watcher.into_stream().wait();
			assert_eq!(stream.next(), Some(Ok(watcher::Status::Future)));
			assert_eq!(stream.next(), Some(Ok(watcher::Status::Ready)));
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
			let watcher = pool.submit_and_watch(&BlockId::Number(0), uxt).unwrap();
			assert_eq!(pool.status().ready, 1);

			// when
			pool.remove_invalid(&[*watcher.hash()]);


			// then
			let mut stream = watcher.into_stream().wait();
			assert_eq!(stream.next(), Some(Ok(watcher::Status::Ready)));
			assert_eq!(stream.next(), Some(Ok(watcher::Status::Invalid)));
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
			let watcher = pool.submit_and_watch(&BlockId::Number(0), uxt).unwrap();
			assert_eq!(pool.status().ready, 1);

			// when
			let mut map = HashMap::new();
			let peers = vec!["a".into(), "b".into(), "c".into()];
			map.insert(*watcher.hash(), peers.clone());
			pool.on_broadcasted(map);


			// then
			let mut stream = watcher.into_stream().wait();
			assert_eq!(stream.next(), Some(Ok(watcher::Status::Ready)));
			assert_eq!(stream.next(), Some(Ok(watcher::Status::Broadcast(peers))));
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
			let watcher = pool.submit_and_watch(&BlockId::Number(0), xt).unwrap();
			assert_eq!(pool.status().ready, 1);

			// when
			let xt = uxt(Transfer {
				from: AccountId::from_h256(H256::from_low_u64_be(2)),
				to: AccountId::from_h256(H256::from_low_u64_be(1)),
				amount: 4,
				nonce: 1,
			});
			pool.submit_one(&BlockId::Number(1), xt).unwrap();
			assert_eq!(pool.status().ready, 1);

			// then
			let mut stream = watcher.into_stream().wait();
			assert_eq!(stream.next(), Some(Ok(watcher::Status::Ready)));
			assert_eq!(stream.next(), Some(Ok(watcher::Status::Dropped)));
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
				pool2.submit_one(&BlockId::Number(0), xt).unwrap();
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
			pool.submit_one(&BlockId::Number(0), xt).unwrap();
			assert_eq!(pool.status().ready, 1);

			// Now block import happens before the second transaction is able to finish verification.
			pool.prune_tags(&BlockId::Number(1), vec![provides], vec![]).unwrap();
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
