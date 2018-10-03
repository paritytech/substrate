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
	traits,
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
pub type TransactionFor<A> = Arc<base::Transaction<ExHash<A>, TxData<ExtrinsicFor<A>>>>;

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

	/// Hash the extrinsic.
	fn hash(&self, uxt: &ExtrinsicFor<Self>) -> Self::Hash;
}

/// Maximum time the transaction will be kept in the pool.
///
/// Transactions that don't get included within the limit are removed from the pool.
const POOL_TIME: time::Duration = time::Duration::from_secs(60 * 5);

/// Additional transaction data
#[derive(Debug, Serialize, Deserialize)]
pub struct TxData<Ex> {
	/// Raw data stored by the user.
	pub raw: Ex,
	/// Transaction validity deadline.
	/// TODO [ToDr] Should we use longevity instead?
	#[serde(skip)]
	pub valid_till: Option<time::Instant>,
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
		TxData<ExtrinsicFor<B>>,
	>>,
	import_notification_sinks: Mutex<Vec<mpsc::UnboundedSender<()>>>,
	rotator: PoolRotator<ExHash<B>>,
}

impl<B: ChainApi> Pool<B> where
	NumberFor<B>: Into<base::BlockNumber>,
{

	/// Imports a bunch of unverified extrinsics to the pool
	pub fn submit_at<T>(&self, at: &BlockId<B::Block>, xts: T) -> Result<Vec<ExHash<B>>, B::Error> where
		T: IntoIterator<Item=ExtrinsicFor<B>>
	{
		let block_number = self.api.block_id_to_number(at)?
			.ok_or_else(|| error::ErrorKind::Msg(format!("Invalid block id: {:?}", at)).into())?;
		xts
			.into_iter()
			.map(|xt| -> Result<_, B::Error> {
				let hash = self.api.hash(&xt);
				if self.rotator.is_banned(&hash) {
					let kind: error::ErrorKind = "Temporarily Banned".into();
					return Err(kind.into())?;
				}

				match self.api.validate_transaction(at, &xt)? {
					TransactionValidity::Valid(priority, requires, provides, longevity) => {
						Ok(base::Transaction {
							data: TxData {
								raw: xt,
								valid_till: Some(time::Instant::now() + POOL_TIME),
							},
							hash,
							priority,
							requires,
							provides,
							longevity,
						})
					},
					TransactionValidity::Invalid => {
						unimplemented!()
					},
					TransactionValidity::Unknown => {
						unimplemented!()
					},
				}
			})
			.map(|tx| {
				let imported = self.pool.write().import(block_number.into(), tx?)?;

				self.import_notification_sinks.lock().retain(|sink| sink.unbounded_send(()).is_ok());

				// TODO [ToDr] notify listener

				Ok(imported.hash().clone())
			})
			.collect()
	}

	/// Imports one unverified extrinsic to the pool
	pub fn submit_one(&self, at: &BlockId<B::Block>, xt: ExtrinsicFor<B>) -> Result<ExHash<B>, B::Error> {
		Ok(self.submit_at(at, ::std::iter::once(xt))?.pop().expect("One extrinsic passed; one result returned; qed"))
	}

	/// Import a single extrinsic and starts to watch their progress in the pool.
	pub fn submit_and_watch(&self, at: &BlockId<B::Block>, xt: ExtrinsicFor<B>) -> Result<Watcher<ExHash<B>, BlockHash<B>>, B::Error> {
		let xt = self.submit_at(at, Some(xt))?.pop().expect("One extrinsic passed; one result returned; qed");
		Ok(self.listener.write().create_watcher(xt))
	}

	/// Prunes ready transactions that provide given list of tags.
	pub fn prune_tags(&self, at: &BlockId<B::Block>, tags: impl IntoIterator<Item=Tag>) -> Result<(), B::Error> {
		let block_number = self.api.block_id_to_number(at)?
			.ok_or_else(|| error::ErrorKind::Msg(format!("Invalid block id: {:?}", at)).into())?;

		let status = self.pool.write().prune_tags(block_number.into(), tags);
		// try to re-submit pruned transactions since some of them might be still valid.
		self.submit_at(at, status.pruned.into_iter().map(|tx| tx.data.raw.clone()))?;
		// TODO [ToDr] Fire events for promoted / failed
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

		self.pool.write().remove_invalid(hashes)
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
	pub fn all(&self, limit: usize) -> Vec<TransactionFor<B>> {
		self.ready(|it| it.take(limit).collect())
	}
}

#[cfg(test)]
mod tests {
	#[test]
	fn should_have_some_basic_tests() {
		assert_eq!(true, false);
	}
}
