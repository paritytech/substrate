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
	collections::HashMap,
	hash,
	sync::Arc,
	time,
};

use base_pool as base;
use error;
use listener::Listener;
use rotator::PoolRotator;
use watcher::Watcher;

use futures::sync::mpsc;
use parking_lot::{Mutex, RwLock};
use sr_primitives::{
	generic::BlockId,
	traits::{self, As},
	transaction_validity::{TransactionValidity, TransactionTag as Tag},
};

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
	/// Hash type
	type Hash: hash::Hash + Eq + traits::Member;
	/// Error type.
	type Error: From<error::Error> + error::IntoPoolError;

	/// Verify extrinsic at given block.
	fn validate_transaction(&self, at: &BlockId<Self::Block>, uxt: &ExtrinsicFor<Self>) -> Result<TransactionValidity, Self::Error>;

	/// Returns a block number given the block id.
	fn block_id_to_number(&self, at: &BlockId<Self::Block>) -> Result<Option<NumberFor<Self>>, Self::Error>;

	/// Returns a block hash given the block id.
	fn block_id_to_hash(&self, at: &BlockId<Self::Block>) -> Result<Option<BlockHash<Self>>, Self::Error>;

	/// Hash the extrinsic.
	fn hash(&self, uxt: &ExtrinsicFor<Self>) -> Self::Hash;
}

/// Pool configuration options.
#[derive(Debug, Clone, Default)]
pub struct Options;

/// Extrinsics pool.
pub struct Pool<B: ChainApi> {
	api: B,
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

		Ok(xts
			.into_iter()
			.map(|xt| -> Result<_, B::Error> {
				let hash = self.api.hash(&xt);
				if self.rotator.is_banned(&hash) {
					bail!(error::Error::from(error::ErrorKind::TemporarilyBanned))
				}

				match self.api.validate_transaction(at, &xt)? {
					TransactionValidity::Valid(priority, requires, provides, longevity) => {
						Ok(base::Transaction {
							data:  xt,
							hash,
							priority,
							requires,
							provides,
							valid_till: block_number.as_().saturating_add(longevity),
						})
					},
					TransactionValidity::Invalid => {
						bail!(error::Error::from(error::ErrorKind::InvalidTransaction))
					},
					TransactionValidity::Unknown => {
						self.listener.write().invalid(&hash);
						bail!(error::Error::from(error::ErrorKind::UnknownTransactionValidity))
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
			.collect())
	}

	/// Imports one unverified extrinsic to the pool
	pub fn submit_one(&self, at: &BlockId<B::Block>, xt: ExtrinsicFor<B>) -> Result<ExHash<B>, B::Error> {
		Ok(self.submit_at(at, ::std::iter::once(xt))?.pop().expect("One extrinsic passed; one result returned; qed")?)
	}

	/// Import a single extrinsic and starts to watch their progress in the pool.
	pub fn submit_and_watch(&self, at: &BlockId<B::Block>, xt: ExtrinsicFor<B>) -> Result<Watcher<ExHash<B>, BlockHash<B>>, B::Error> {
		let hash = self.api.hash(&xt);
		let watcher = self.listener.write().create_watcher(hash);
		self.submit_one(at, xt)?;
		Ok(watcher)
	}

	/// Prunes ready transactions that provide given list of tags.
	pub fn prune_tags(&self, at: &BlockId<B::Block>, tags: impl IntoIterator<Item=Tag>) -> Result<(), B::Error> {
		let status = self.pool.write().prune_tags(tags);
		{
			let mut listener = self.listener.write();
			for promoted in &status.promoted {
				fire_events(&mut *listener, promoted);
			}
			for f in &status.failed {
				listener.dropped(f, None);
			}
		}
		// try to re-submit pruned transactions since some of them might be still valid.
		let hashes = status.pruned.iter().map(|tx| tx.hash.clone()).collect::<Vec<_>>();
		let results = self.submit_at(at, status.pruned.into_iter().map(|tx| tx.data.clone()))?;
		// Fire mined event for transactions that became invalid.
		let hashes = results.into_iter().enumerate().filter_map(|(idx, r)| match r.map_err(error::IntoPoolError::into_pool_error) {
			Err(Ok(err)) => match err.kind() {
				error::ErrorKind::InvalidTransaction => Some(hashes[idx].clone()),
				_ => None,
			},
			_ => None,
		});
		{
			let header_hash = self.api.block_id_to_hash(at)?
				.ok_or_else(|| error::ErrorKind::Msg(format!("Invalid block id: {:?}", at)).into())?;
			let mut listener = self.listener.write();
			for h in hashes {
				listener.pruned(header_hash, &h)
			}
		}
		// clear old transactions
		self.clear_stale(at)?;
		Ok(())
	}

	/// Removes stale transactions from the pool.
	///
	/// Stale transactions are transaction beyond their longevity period.
	/// Note this function does not remove transactions that are already included in the chain.
	/// See `prune_tags` ifyou want this.
	pub fn clear_stale(&self, at: &BlockId<B::Block>) -> Result<(), B::Error> {
		let block_number = self.api.block_id_to_number(at)?
				.ok_or_else(|| error::ErrorKind::Msg(format!("Invalid block id: {:?}", at)).into())?
				.as_();
		let now = time::Instant::now();
		let to_remove = self.ready(|pending| pending
			.filter(|tx| self.rotator.ban_if_stale(&now, block_number, &tx))
			.map(|tx| tx.hash.clone())
			.collect::<Vec<_>>()
		);
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
}

impl<B: ChainApi> Pool<B> {
	/// Create a new transaction pool.
	/// TODO [ToDr] Options
	pub fn new(_options: Options, api: B) -> Self {
		Pool {
			api,
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
		self.rotator.ban(&time::Instant::now(), hashes);

		let invalid = self.pool.write().remove_invalid(hashes);

		let mut listener = self.listener.write();
		for tx in &invalid {
			listener.invalid(&tx.hash);
		}

		invalid
	}

	/// Get ready transactions ordered by priority
	pub fn ready<F, X>(&self, f: F) -> X where
		F: FnOnce(&mut Iterator<Item=TransactionFor<B>>) -> X,
	{
		let pool = self.pool.read();
		let mut ready = pool.ready();
		f(&mut ready)
	}

	/// Returns all transactions in the pool.
	///
	/// Be careful with large limit values, as querying the entire pool might be time consuming.
	pub fn all(&self, limit: usize) -> Vec<ExtrinsicFor<B>> {
		self.ready(|it| it.take(limit).map(|ex| ex.data.clone()).collect())
	}

	/// Returns pool status.
	pub fn status(&self) -> base::Status {
		self.pool.read().status()
	}

	/// Returns transaction hash
	pub fn hash_of(&self, xt: &ExtrinsicFor<B>) -> ExHash<B> {
		self.api.hash(xt)
	}
}

fn fire_events<H, H2, Ex>(
	listener: &mut Listener<H, H2>,
	imported: &base::Imported<H, Ex>,
) where
	H: hash::Hash + Eq + traits::Member,
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
	use test_runtime::{Block, Extrinsic, Transfer};

	#[derive(Debug, Default)]
	struct TestApi;

	impl ChainApi for TestApi {
		type Block = Block;
		type Hash = u64;
		type Error = error::Error;

		/// Verify extrinsic at given block.
		fn validate_transaction(&self, at: &BlockId<Self::Block>, uxt: &ExtrinsicFor<Self>) -> Result<TransactionValidity, Self::Error> {
			let block_number = self.block_id_to_number(at)?.unwrap();
			let nonce = uxt.transfer.nonce;

			if nonce < block_number {
				Ok(TransactionValidity::Invalid)
			} else {
				Ok(TransactionValidity::Valid(
					4,
					if nonce > block_number { vec![vec![nonce as u8 - 1]] } else { vec![] },
					vec![vec![nonce as u8]],
					3,
				))
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
				BlockId::Number(num) => Some((*num).into()),
				BlockId::Hash(_) => None,
			})
		}

		/// Hash the extrinsic.
		fn hash(&self, uxt: &ExtrinsicFor<Self>) -> Self::Hash {
			(uxt.transfer.from.low_u64() << 5) + uxt.transfer.nonce
		}
	}

	fn uxt(transfer: Transfer) -> Extrinsic {
		Extrinsic {
			transfer,
			signature: Default::default(),
		}
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
			from: 1.into(),
			to: 2.into(),
			amount: 5,
			nonce: 0,
		})).unwrap();

		// then
		assert_eq!(pool.ready(|pending| pending.map(|tx| tx.hash.clone()).collect::<Vec<_>>()), vec![hash]);
	}

	#[test]
	fn should_reject_if_temporarily_banned() {
		// given
		let pool = pool();
		let uxt = uxt(Transfer {
			from: 1.into(),
			to: 2.into(),
			amount: 5,
			nonce: 0,
		});

		// when
		pool.rotator.ban(&time::Instant::now(), &[pool.hash_of(&uxt)]);
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
				from: 1.into(),
				to: 2.into(),
				amount: 5,
				nonce: 0,
			})).unwrap();
			let _hash = pool.submit_one(&BlockId::Number(0), uxt(Transfer {
				from: 1.into(),
				to: 2.into(),
				amount: 5,
				nonce: 1,
			})).unwrap();
			// future doesn't count
			let _hash = pool.submit_one(&BlockId::Number(0), uxt(Transfer {
				from: 1.into(),
				to: 2.into(),
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
			from: 1.into(),
			to: 2.into(),
			amount: 5,
			nonce: 0,
		})).unwrap();
		let hash2 = pool.submit_one(&BlockId::Number(0), uxt(Transfer {
			from: 1.into(),
			to: 2.into(),
			amount: 5,
			nonce: 1,
		})).unwrap();
		let hash3 = pool.submit_one(&BlockId::Number(0), uxt(Transfer {
			from: 1.into(),
			to: 2.into(),
			amount: 5,
			nonce: 3,
		})).unwrap();

		// when
		pool.clear_stale(&BlockId::Number(5)).unwrap();

		// then
		assert_eq!(pool.all(3).len(), 0);
		assert_eq!(pool.status().future, 0);
		assert_eq!(pool.status().ready, 0);
		// make sure they are temporarily banned as well
		assert!(pool.rotator.is_banned(&hash1));
		assert!(pool.rotator.is_banned(&hash2));
		assert!(pool.rotator.is_banned(&hash3));
	}

	mod listener {
		use super::*;

		#[test]
		fn should_trigger_ready_and_finalised() {
			// given
			let pool = pool();
			let watcher = pool.submit_and_watch(&BlockId::Number(0), uxt(Transfer {
				from: 1.into(),
				to: 2.into(),
				amount: 5,
				nonce: 0,
			})).unwrap();
			assert_eq!(pool.status().ready, 1);
			assert_eq!(pool.status().future, 0);

			// when
			pool.prune_tags(&BlockId::Number(2), vec![vec![0u8]]).unwrap();
			assert_eq!(pool.status().ready, 0);
			assert_eq!(pool.status().future, 0);

			// then
			let mut stream = watcher.into_stream().wait();
			assert_eq!(stream.next(), Some(Ok(::watcher::Status::Ready)));
			assert_eq!(stream.next(), Some(Ok(::watcher::Status::Finalised(2.into()))));
			assert_eq!(stream.next(), None);
		}

		#[test]
		fn should_trigger_future_and_ready_after_promoted() {
			// given
			let pool = pool();
			let watcher = pool.submit_and_watch(&BlockId::Number(0), uxt(Transfer {
				from: 1.into(),
				to: 2.into(),
				amount: 5,
				nonce: 1,
			})).unwrap();
			assert_eq!(pool.status().ready, 0);
			assert_eq!(pool.status().future, 1);

			// when
			pool.submit_one(&BlockId::Number(0), uxt(Transfer {
				from: 1.into(),
				to: 2.into(),
				amount: 5,
				nonce: 0,
			})).unwrap();
			assert_eq!(pool.status().ready, 2);

			// then
			let mut stream = watcher.into_stream().wait();
			assert_eq!(stream.next(), Some(Ok(::watcher::Status::Future)));
			assert_eq!(stream.next(), Some(Ok(::watcher::Status::Ready)));
		}

		#[test]
		fn should_trigger_invalid_and_ban() {
			// given
			let pool = pool();
			let uxt = uxt(Transfer {
				from: 1.into(),
				to: 2.into(),
				amount: 5,
				nonce: 0,
			});
			let watcher = pool.submit_and_watch(&BlockId::Number(0), uxt).unwrap();
			assert_eq!(pool.status().ready, 1);

			// when
			pool.remove_invalid(&[*watcher.hash()]);


			// then
			let mut stream = watcher.into_stream().wait();
			assert_eq!(stream.next(), Some(Ok(::watcher::Status::Ready)));
			assert_eq!(stream.next(), Some(Ok(::watcher::Status::Invalid)));
			assert_eq!(stream.next(), None);
		}

		#[test]
		fn should_trigger_broadcasted() {
			// given
			let pool = pool();
			let uxt = uxt(Transfer {
				from: 1.into(),
				to: 2.into(),
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
			assert_eq!(stream.next(), Some(Ok(::watcher::Status::Ready)));
			assert_eq!(stream.next(), Some(Ok(::watcher::Status::Broadcast(peers))));
		}
	}
}
