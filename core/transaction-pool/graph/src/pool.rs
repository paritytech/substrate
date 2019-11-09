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
	hash,
	collections::HashMap,
	sync::Arc,
};

use crate::base_pool as base;
use crate::error;
use crate::watcher::Watcher;
use serde::Serialize;

use futures::{
	Future, FutureExt,
	channel::mpsc,
	future::{Either, ready, join_all},
};
use sr_primitives::{
	generic::BlockId,
	traits::{self, SaturatedConversion},
	transaction_validity::{TransactionValidity, TransactionTag as Tag, TransactionValidityError},
};
use crate::validated_pool::{ValidatedPool, ValidatedTransaction};

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
/// A type of validated transaction stored in the pool.
pub type ValidatedTransactionFor<A> = ValidatedTransaction<
	ExHash<A>,
	ExtrinsicFor<A>,
	<A as ChainApi>::Error,
>;

/// Concrete extrinsic validation and query logic.
pub trait ChainApi: Send + Sync {
	/// Block type.
	type Block: traits::Block;
	/// Transaction Hash type
	type Hash: hash::Hash + Eq + traits::Member + Serialize;
	/// Error type.
	type Error: From<error::Error> + error::IntoPoolError;
	/// Validate transaction future.
	type ValidationFuture: Future<Output=Result<TransactionValidity, Self::Error>> + Send + Unpin;

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
	pub ready: base::Limit,
	/// Future queue limits.
	pub future: base::Limit,
}

impl Default for Options {
	fn default() -> Self {
		Options {
			ready: base::Limit {
				count: 512,
				total_bytes: 10 * 1024 * 1024,
			},
			future: base::Limit {
				count: 128,
				total_bytes: 1 * 1024 * 1024,
			},
		}
	}
}

/// Extrinsics pool that performs validation.
pub struct Pool<B: ChainApi> {
	validated_pool: Arc<ValidatedPool<B>>,
}

impl<B: ChainApi> Pool<B> {
	/// Create a new transaction pool.
	pub fn new(options: Options, api: B) -> Self {
		Pool {
			validated_pool: Arc::new(ValidatedPool::new(options, api)),
		}
	}

	/// Imports a bunch of unverified extrinsics to the pool
	pub fn submit_at<T>(&self, at: &BlockId<B::Block>, xts: T, force: bool)
		-> impl Future<Output=Result<Vec<Result<ExHash<B>, B::Error>>, B::Error>>
	where
		T: IntoIterator<Item=ExtrinsicFor<B>>
	{
		let validated_pool = self.validated_pool.clone();
		self.verify(at, xts, force)
			.map(move |validated_transactions| validated_transactions
				.map(|validated_transactions| validated_pool.submit(validated_transactions)))
	}

	/// Imports one unverified extrinsic to the pool
	pub fn submit_one(
		&self,
		at: &BlockId<B::Block>,
		xt: ExtrinsicFor<B>,
	) -> impl Future<Output=Result<ExHash<B>, B::Error>> {
		self.submit_at(at, std::iter::once(xt), false)
			.map(|import_result| import_result.and_then(|mut import_result| import_result
				.pop()
				.expect("One extrinsic passed; one result returned; qed")
			))
	}

	/// Import a single extrinsic and starts to watch their progress in the pool.
	pub fn submit_and_watch(
		&self,
		at: &BlockId<B::Block>,
		xt: ExtrinsicFor<B>,
	) -> impl Future<Output=Result<Watcher<ExHash<B>, BlockHash<B>>, B::Error>> {
		let block_number = match self.resolve_block_number(at) {
			Ok(block_number) => block_number,
			Err(err) => return Either::Left(ready(Err(err)))
		};

		let validated_pool = self.validated_pool.clone();
		Either::Right(
			self.verify_one(at, block_number, xt, false)
				.map(move |validated_transactions| validated_pool.submit_and_watch(validated_transactions))
		)
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
		let (in_pool_hashes, in_pool_tags) = self.validated_pool.extrinsics_tags(extrinsics);

		// Zip the ones from the pool with the full list (we get pairs `(Extrinsic, Option<Vec<Tag>>)`)
		let all = extrinsics.iter().zip(in_pool_tags.into_iter());

		// Prepare future that collect tags for all extrinsics
		let future_tags = join_all(all
			.map(|(extrinsic, in_pool_tags)|
				match in_pool_tags {
					// reuse the tags for extrinsics that were found in the pool
					Some(tags) => Either::Left(
						ready(tags)
					),
					// if it's not found in the pool query the runtime at parent block
					// to get validity info and tags that the extrinsic provides.
					None => Either::Right(self.validated_pool.api().validate_transaction(parent, extrinsic.clone())
						.then(|validity| ready(match validity {
							Ok(Ok(validity)) => validity.provides,
							// silently ignore invalid extrinsics,
							// cause they might just be inherent
							_ => Vec::new(),
						}))),
				}
			));

		// Prune transactions by tags
		let at = at.clone();
		let self_clone = self.clone();
		future_tags.then(move |tags| self_clone.prune_tags(
			&at,
			tags.into_iter().flat_map(|tags| tags),
			in_pool_hashes,
		))
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
	/// Returns transactions that have been removed from the pool and must be reverified
	/// before reinserting to the pool.
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
		log::trace!(target: "txpool", "Pruning at {:?}", at);
		// Prune all transactions that provide given tags
		let prune_status = match self.validated_pool.prune_tags(tags) {
			Ok(prune_status) => prune_status,
			Err(e) => return Either::Left(ready(Err(e))),
		};

		// Make sure that we don't revalidate extrinsics that were part of the recently
		// imported block. This is especially important for UTXO-like chains cause the
		// inputs are pruned so such transaction would go to future again.
		self.validated_pool.ban(&std::time::Instant::now(), known_imported_hashes.clone().into_iter());

		// Try to re-validate pruned transactions since some of them might be still valid.
		// note that `known_imported_hashes` will be rejected here due to temporary ban.
		let pruned_hashes = prune_status.pruned.iter().map(|tx| tx.hash.clone()).collect::<Vec<_>>();
		let pruned_transactions = prune_status.pruned.into_iter().map(|tx| tx.data.clone());
		let reverify_future = self.verify(at, pruned_transactions, false);

		log::trace!(target: "txpool", "Prunning at {:?}. Resubmitting transactions.", at);
		// And finally - submit reverified transactions back to the pool
		let at = at.clone();
		let validated_pool = self.validated_pool.clone();
		Either::Right(reverify_future.then(move |reverified_transactions|
			ready(reverified_transactions.and_then(|reverified_transactions|
				validated_pool.resubmit_pruned(
					&at,
					known_imported_hashes,
					pruned_hashes,
					reverified_transactions,
				))
			)))
	}

	/// Return an event stream of transactions imported to the pool.
	pub fn import_notification_stream(&self) -> EventStream {
		self.validated_pool.import_notification_stream()
	}

	/// Invoked when extrinsics are broadcasted.
	pub fn on_broadcasted(&self, propagated: HashMap<ExHash<B>, Vec<String>>) {
		self.validated_pool.on_broadcasted(propagated)
	}

	/// Remove from the pool.
	pub fn remove_invalid(&self, hashes: &[ExHash<B>]) -> Vec<TransactionFor<B>> {
		self.validated_pool.remove_invalid(hashes)
	}

	/// Get an iterator for ready transactions ordered by priority
	pub fn ready(&self) -> impl Iterator<Item=TransactionFor<B>> {
		self.validated_pool.ready()
	}

	/// Returns pool status.
	pub fn status(&self) -> base::Status {
		self.validated_pool.status()
	}

	/// Returns transaction hash
	pub fn hash_of(&self, xt: &ExtrinsicFor<B>) -> ExHash<B> {
		self.validated_pool.api().hash_and_length(xt).0
	}

	/// Resolves block number by id.
	fn resolve_block_number(&self, at: &BlockId<B::Block>) -> Result<NumberFor<B>, B::Error> {
		self.validated_pool.api().block_id_to_number(at)
			.and_then(|number| number.ok_or_else(||
				error::Error::InvalidBlockId(format!("{:?}", at)).into()))
	}

	/// Returns future that validates a bunch of transactions at given block.
	fn verify(
		&self,
		at: &BlockId<B::Block>,
		xts: impl IntoIterator<Item=ExtrinsicFor<B>>,
		force: bool,
	) -> impl Future<Output=Result<Vec<ValidatedTransactionFor<B>>, B::Error>> {
		// we need a block number to compute tx validity
		let block_number = match self.resolve_block_number(at) {
			Ok(block_number) => block_number,
			Err(err) => return Either::Left(ready(Err(err))),
		};

		// for each xt, prepare a validation future
		let validation_futures = xts.into_iter().map(move |xt|
			self.verify_one(at, block_number, xt, force)
		);

		// make single validation future that waits all until all extrinsics are validated
		Either::Right(join_all(validation_futures).then(|x| ready(Ok(x))))
	}

	/// Returns future that validates single transaction at given block.
	fn verify_one(
		&self,
		block_id: &BlockId<B::Block>,
		block_number: NumberFor<B>,
		xt: ExtrinsicFor<B>,
		force: bool,
	) -> impl Future<Output=ValidatedTransactionFor<B>> {
		let (hash, bytes) = self.validated_pool.api().hash_and_length(&xt);
		if !force && self.validated_pool.is_banned(&hash) {
			return Either::Left(ready(ValidatedTransaction::Invalid(hash, error::Error::TemporarilyBanned.into())))
		}

		Either::Right(self.validated_pool.api().validate_transaction(block_id, xt.clone())
			.then(move |validation_result| ready(match validation_result {
				Ok(validity) => match validity {
					Ok(validity) => if validity.provides.is_empty() {
						ValidatedTransaction::Invalid(hash, error::Error::NoTagsProvided.into())
					} else {
						ValidatedTransaction::Valid(base::Transaction {
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
					Err(TransactionValidityError::Invalid(e)) =>
						ValidatedTransaction::Invalid(hash, error::Error::InvalidTransaction(e).into()),
					Err(TransactionValidityError::Unknown(e)) =>
						ValidatedTransaction::Unknown(hash, error::Error::UnknownTransaction(e).into()),
				},
				Err(e) => ValidatedTransaction::Invalid(hash, e),
			})))
	}
}

impl<B: ChainApi> Clone for Pool<B> {
	fn clone(&self) -> Self {
		Self {
			validated_pool: self.validated_pool.clone(),
		}
	}
}

#[cfg(test)]
mod tests {
	use std::{
		collections::HashMap,
		time::Instant,
	};
	use parking_lot::Mutex;
	use futures::executor::block_on;
	use super::*;
	use sr_primitives::transaction_validity::{ValidTransaction, InvalidTransaction};
	use codec::Encode;
	use test_runtime::{Block, Extrinsic, Transfer, H256, AccountId};
	use assert_matches::assert_matches;
	use crate::base_pool::Limit;
	use crate::watcher;

	const INVALID_NONCE: u64 = 254;

	#[derive(Clone, Debug, Default)]
	struct TestApi {
		delay: Arc<Mutex<Option<std::sync::mpsc::Receiver<()>>>>,
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
		pool.validated_pool.rotator().ban(&Instant::now(), vec![pool.hash_of(&uxt)]);
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
		pool.validated_pool.clear_stale(&BlockId::Number(5)).unwrap();

		// then
		assert_eq!(pool.ready().count(), 0);
		assert_eq!(pool.status().future, 0);
		assert_eq!(pool.status().ready, 0);
		// make sure they are temporarily banned as well
		assert!(pool.validated_pool.rotator().is_banned(&hash1));
		assert!(pool.validated_pool.rotator().is_banned(&hash2));
		assert!(pool.validated_pool.rotator().is_banned(&hash3));
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
		assert!(pool.validated_pool.rotator().is_banned(&hash1));
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
		assert!(pool.validated_pool.rotator().is_banned(&hash1));
		assert!(!pool.validated_pool.rotator().is_banned(&hash2));
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
			pool.validated_pool.remove_invalid(&[*watcher.hash()]);


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
			api.delay = Arc::new(Mutex::new(rx.into()));
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

