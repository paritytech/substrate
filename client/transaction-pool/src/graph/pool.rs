// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

use std::{collections::HashMap, sync::Arc, time::Duration};

use crate::LOG_TARGET;
use futures::{channel::mpsc::Receiver, Future};
use sc_transaction_pool_api::error;
use sp_blockchain::TreeRoute;
use sp_runtime::{
	generic::BlockId,
	traits::{self, Block as BlockT, SaturatedConversion},
	transaction_validity::{
		TransactionSource, TransactionTag as Tag, TransactionValidity, TransactionValidityError,
	},
};
use std::time::Instant;

use super::{
	base_pool as base,
	validated_pool::{IsValidator, ValidatedPool, ValidatedTransaction},
	watcher::Watcher,
};

/// Modification notification event stream type;
pub type EventStream<H> = Receiver<H>;

/// Block hash type for a pool.
pub type BlockHash<A> = <<A as ChainApi>::Block as traits::Block>::Hash;
/// Extrinsic hash type for a pool.
pub type ExtrinsicHash<A> = <<A as ChainApi>::Block as traits::Block>::Hash;
/// Extrinsic type for a pool.
pub type ExtrinsicFor<A> = <<A as ChainApi>::Block as traits::Block>::Extrinsic;
/// Block number type for the ChainApi
pub type NumberFor<A> = traits::NumberFor<<A as ChainApi>::Block>;
/// A type of transaction stored in the pool
pub type TransactionFor<A> = Arc<base::Transaction<ExtrinsicHash<A>, ExtrinsicFor<A>>>;
/// A type of validated transaction stored in the pool.
pub type ValidatedTransactionFor<A> =
	ValidatedTransaction<ExtrinsicHash<A>, ExtrinsicFor<A>, <A as ChainApi>::Error>;

/// Concrete extrinsic validation and query logic.
pub trait ChainApi: Send + Sync {
	/// Block type.
	type Block: BlockT;
	/// Error type.
	type Error: From<error::Error> + error::IntoPoolError;
	/// Validate transaction future.
	type ValidationFuture: Future<Output = Result<TransactionValidity, Self::Error>> + Send + Unpin;
	/// Body future (since block body might be remote)
	type BodyFuture: Future<Output = Result<Option<Vec<<Self::Block as traits::Block>::Extrinsic>>, Self::Error>>
		+ Unpin
		+ Send
		+ 'static;

	/// Verify extrinsic at given block.
	fn validate_transaction(
		&self,
		at: &BlockId<Self::Block>,
		source: TransactionSource,
		uxt: ExtrinsicFor<Self>,
	) -> Self::ValidationFuture;

	/// Returns a block number given the block id.
	fn block_id_to_number(
		&self,
		at: &BlockId<Self::Block>,
	) -> Result<Option<NumberFor<Self>>, Self::Error>;

	/// Returns a block hash given the block id.
	fn block_id_to_hash(
		&self,
		at: &BlockId<Self::Block>,
	) -> Result<Option<<Self::Block as BlockT>::Hash>, Self::Error>;

	/// Returns hash and encoding length of the extrinsic.
	fn hash_and_length(&self, uxt: &ExtrinsicFor<Self>) -> (ExtrinsicHash<Self>, usize);

	/// Returns a block body given the block.
	fn block_body(&self, at: <Self::Block as BlockT>::Hash) -> Self::BodyFuture;

	/// Returns a block header given the block id.
	fn block_header(
		&self,
		at: <Self::Block as BlockT>::Hash,
	) -> Result<Option<<Self::Block as BlockT>::Header>, Self::Error>;

	/// Compute a tree-route between two blocks. See [`TreeRoute`] for more details.
	fn tree_route(
		&self,
		from: <Self::Block as BlockT>::Hash,
		to: <Self::Block as BlockT>::Hash,
	) -> Result<TreeRoute<Self::Block>, Self::Error>;
}

/// Pool configuration options.
#[derive(Debug, Clone)]
pub struct Options {
	/// Ready queue limits.
	pub ready: base::Limit,
	/// Future queue limits.
	pub future: base::Limit,
	/// Reject future transactions.
	pub reject_future_transactions: bool,
	/// How long the extrinsic is banned for.
	pub ban_time: Duration,
}

impl Default for Options {
	fn default() -> Self {
		Self {
			ready: base::Limit { count: 8192, total_bytes: 20 * 1024 * 1024 },
			future: base::Limit { count: 512, total_bytes: 1 * 1024 * 1024 },
			reject_future_transactions: false,
			ban_time: Duration::from_secs(60 * 30),
		}
	}
}

/// Should we check that the transaction is banned
/// in the pool, before we verify it?
#[derive(Copy, Clone)]
enum CheckBannedBeforeVerify {
	Yes,
	No,
}

/// Extrinsics pool that performs validation.
pub struct Pool<B: ChainApi> {
	validated_pool: Arc<ValidatedPool<B>>,
}

impl<B: ChainApi> Pool<B> {
	/// Create a new transaction pool.
	pub fn new(options: Options, is_validator: IsValidator, api: Arc<B>) -> Self {
		Self { validated_pool: Arc::new(ValidatedPool::new(options, is_validator, api)) }
	}

	/// Imports a bunch of unverified extrinsics to the pool
	pub async fn submit_at(
		&self,
		at: &BlockId<B::Block>,
		source: TransactionSource,
		xts: impl IntoIterator<Item = ExtrinsicFor<B>>,
	) -> Result<Vec<Result<ExtrinsicHash<B>, B::Error>>, B::Error> {
		let xts = xts.into_iter().map(|xt| (source, xt));
		let validated_transactions = self.verify(at, xts, CheckBannedBeforeVerify::Yes).await?;
		Ok(self.validated_pool.submit(validated_transactions.into_values()))
	}

	/// Resubmit the given extrinsics to the pool.
	///
	/// This does not check if a transaction is banned, before we verify it again.
	pub async fn resubmit_at(
		&self,
		at: &BlockId<B::Block>,
		source: TransactionSource,
		xts: impl IntoIterator<Item = ExtrinsicFor<B>>,
	) -> Result<Vec<Result<ExtrinsicHash<B>, B::Error>>, B::Error> {
		let xts = xts.into_iter().map(|xt| (source, xt));
		let validated_transactions = self.verify(at, xts, CheckBannedBeforeVerify::No).await?;
		Ok(self.validated_pool.submit(validated_transactions.into_values()))
	}

	/// Imports one unverified extrinsic to the pool
	pub async fn submit_one(
		&self,
		at: &BlockId<B::Block>,
		source: TransactionSource,
		xt: ExtrinsicFor<B>,
	) -> Result<ExtrinsicHash<B>, B::Error> {
		let res = self.submit_at(at, source, std::iter::once(xt)).await?.pop();
		res.expect("One extrinsic passed; one result returned; qed")
	}

	/// Import a single extrinsic and starts to watch its progress in the pool.
	pub async fn submit_and_watch(
		&self,
		at: &BlockId<B::Block>,
		source: TransactionSource,
		xt: ExtrinsicFor<B>,
	) -> Result<Watcher<ExtrinsicHash<B>, ExtrinsicHash<B>>, B::Error> {
		let block_number = self.resolve_block_number(at)?;
		let (_, tx) = self
			.verify_one(at, block_number, source, xt, CheckBannedBeforeVerify::Yes)
			.await;
		self.validated_pool.submit_and_watch(tx)
	}

	/// Resubmit some transaction that were validated elsewhere.
	pub fn resubmit(
		&self,
		revalidated_transactions: HashMap<ExtrinsicHash<B>, ValidatedTransactionFor<B>>,
	) {
		let now = Instant::now();
		self.validated_pool.resubmit(revalidated_transactions);
		log::debug!(
			target: LOG_TARGET,
			"Resubmitted. Took {} ms. Status: {:?}",
			now.elapsed().as_millis(),
			self.validated_pool.status()
		);
	}

	/// Prunes known ready transactions.
	///
	/// Used to clear the pool from transactions that were part of recently imported block.
	/// The main difference from the `prune` is that we do not revalidate any transactions
	/// and ignore unknown passed hashes.
	pub fn prune_known(
		&self,
		at: &BlockId<B::Block>,
		hashes: &[ExtrinsicHash<B>],
	) -> Result<(), B::Error> {
		// Get details of all extrinsics that are already in the pool
		let in_pool_tags =
			self.validated_pool.extrinsics_tags(hashes).into_iter().flatten().flatten();

		// Prune all transactions that provide given tags
		let prune_status = self.validated_pool.prune_tags(in_pool_tags)?;
		let pruned_transactions =
			hashes.iter().cloned().chain(prune_status.pruned.iter().map(|tx| tx.hash));
		self.validated_pool.fire_pruned(at, pruned_transactions)
	}

	/// Prunes ready transactions.
	///
	/// Used to clear the pool from transactions that were part of recently imported block.
	/// To perform pruning we need the tags that each extrinsic provides and to avoid calling
	/// into runtime too often we first lookup all extrinsics that are in the pool and get
	/// their provided tags from there. Otherwise we query the runtime at the `parent` block.
	pub async fn prune(
		&self,
		at: &BlockId<B::Block>,
		parent: &BlockId<B::Block>,
		extrinsics: &[ExtrinsicFor<B>],
	) -> Result<(), B::Error> {
		log::debug!(
			target: LOG_TARGET,
			"Starting pruning of block {:?} (extrinsics: {})",
			at,
			extrinsics.len()
		);
		// Get details of all extrinsics that are already in the pool
		let in_pool_hashes =
			extrinsics.iter().map(|extrinsic| self.hash_of(extrinsic)).collect::<Vec<_>>();
		let in_pool_tags = self.validated_pool.extrinsics_tags(&in_pool_hashes);

		// Zip the ones from the pool with the full list (we get pairs `(Extrinsic,
		// Option<Vec<Tag>>)`)
		let all = extrinsics.iter().zip(in_pool_tags.into_iter());

		let mut future_tags = Vec::new();
		for (extrinsic, in_pool_tags) in all {
			match in_pool_tags {
				// reuse the tags for extrinsics that were found in the pool
				Some(tags) => future_tags.extend(tags),
				// if it's not found in the pool query the runtime at parent block
				// to get validity info and tags that the extrinsic provides.
				None => {
					// Avoid validating block txs if the pool is empty
					if !self.validated_pool.status().is_empty() {
						let validity = self
							.validated_pool
							.api()
							.validate_transaction(
								parent,
								TransactionSource::InBlock,
								extrinsic.clone(),
							)
							.await;

						if let Ok(Ok(validity)) = validity {
							future_tags.extend(validity.provides);
						}
					} else {
						log::trace!(
							target: LOG_TARGET,
							"txpool is empty, skipping validation for block {at:?}",
						);
					}
				},
			}
		}

		self.prune_tags(at, future_tags, in_pool_hashes).await
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
	pub async fn prune_tags(
		&self,
		at: &BlockId<B::Block>,
		tags: impl IntoIterator<Item = Tag>,
		known_imported_hashes: impl IntoIterator<Item = ExtrinsicHash<B>> + Clone,
	) -> Result<(), B::Error> {
		log::debug!(target: LOG_TARGET, "Pruning at {:?}", at);
		// Prune all transactions that provide given tags
		let prune_status = self.validated_pool.prune_tags(tags)?;

		// Make sure that we don't revalidate extrinsics that were part of the recently
		// imported block. This is especially important for UTXO-like chains cause the
		// inputs are pruned so such transaction would go to future again.
		self.validated_pool
			.ban(&Instant::now(), known_imported_hashes.clone().into_iter());

		// Try to re-validate pruned transactions since some of them might be still valid.
		// note that `known_imported_hashes` will be rejected here due to temporary ban.
		let pruned_hashes = prune_status.pruned.iter().map(|tx| tx.hash).collect::<Vec<_>>();
		let pruned_transactions =
			prune_status.pruned.into_iter().map(|tx| (tx.source, tx.data.clone()));

		let reverified_transactions =
			self.verify(at, pruned_transactions, CheckBannedBeforeVerify::Yes).await?;

		log::trace!(target: LOG_TARGET, "Pruning at {:?}. Resubmitting transactions.", at);
		// And finally - submit reverified transactions back to the pool

		self.validated_pool.resubmit_pruned(
			at,
			known_imported_hashes,
			pruned_hashes,
			reverified_transactions.into_values().collect(),
		)
	}

	/// Returns transaction hash
	pub fn hash_of(&self, xt: &ExtrinsicFor<B>) -> ExtrinsicHash<B> {
		self.validated_pool.api().hash_and_length(xt).0
	}

	/// Resolves block number by id.
	fn resolve_block_number(&self, at: &BlockId<B::Block>) -> Result<NumberFor<B>, B::Error> {
		self.validated_pool.api().block_id_to_number(at).and_then(|number| {
			number.ok_or_else(|| error::Error::InvalidBlockId(format!("{:?}", at)).into())
		})
	}

	/// Returns future that validates a bunch of transactions at given block.
	async fn verify(
		&self,
		at: &BlockId<B::Block>,
		xts: impl IntoIterator<Item = (TransactionSource, ExtrinsicFor<B>)>,
		check: CheckBannedBeforeVerify,
	) -> Result<HashMap<ExtrinsicHash<B>, ValidatedTransactionFor<B>>, B::Error> {
		// we need a block number to compute tx validity
		let block_number = self.resolve_block_number(at)?;

		let res = futures::future::join_all(
			xts.into_iter()
				.map(|(source, xt)| self.verify_one(at, block_number, source, xt, check)),
		)
		.await
		.into_iter()
		.collect::<HashMap<_, _>>();

		Ok(res)
	}

	/// Returns future that validates single transaction at given block.
	async fn verify_one(
		&self,
		block_id: &BlockId<B::Block>,
		block_number: NumberFor<B>,
		source: TransactionSource,
		xt: ExtrinsicFor<B>,
		check: CheckBannedBeforeVerify,
	) -> (ExtrinsicHash<B>, ValidatedTransactionFor<B>) {
		let (hash, bytes) = self.validated_pool.api().hash_and_length(&xt);

		let ignore_banned = matches!(check, CheckBannedBeforeVerify::No);
		if let Err(err) = self.validated_pool.check_is_known(&hash, ignore_banned) {
			return (hash, ValidatedTransaction::Invalid(hash, err))
		}

		let validation_result = self
			.validated_pool
			.api()
			.validate_transaction(block_id, source, xt.clone())
			.await;

		let status = match validation_result {
			Ok(status) => status,
			Err(e) => return (hash, ValidatedTransaction::Invalid(hash, e)),
		};

		let validity = match status {
			Ok(validity) =>
				if validity.provides.is_empty() {
					ValidatedTransaction::Invalid(hash, error::Error::NoTagsProvided.into())
				} else {
					ValidatedTransaction::valid_at(
						block_number.saturated_into::<u64>(),
						hash,
						source,
						xt,
						bytes,
						validity,
					)
				},
			Err(TransactionValidityError::Invalid(e)) =>
				ValidatedTransaction::Invalid(hash, error::Error::InvalidTransaction(e).into()),
			Err(TransactionValidityError::Unknown(e)) =>
				ValidatedTransaction::Unknown(hash, error::Error::UnknownTransaction(e).into()),
		};

		(hash, validity)
	}

	/// get a reference to the underlying validated pool.
	pub fn validated_pool(&self) -> &ValidatedPool<B> {
		&self.validated_pool
	}
}

impl<B: ChainApi> Clone for Pool<B> {
	fn clone(&self) -> Self {
		Self { validated_pool: self.validated_pool.clone() }
	}
}

#[cfg(test)]
mod tests {
	use super::{super::base_pool::Limit, *};
	use crate::tests::{pool, uxt, TestApi, INVALID_NONCE};
	use assert_matches::assert_matches;
	use futures::executor::block_on;
	use parking_lot::Mutex;
	use sc_transaction_pool_api::TransactionStatus;
	use sp_runtime::transaction_validity::TransactionSource;
	use std::{collections::HashMap, time::Instant};
	use substrate_test_runtime::{AccountId, Extrinsic, Transfer, H256};

	const SOURCE: TransactionSource = TransactionSource::External;

	#[test]
	fn should_validate_and_import_transaction() {
		// given
		let pool = pool();

		// when
		let hash = block_on(pool.submit_one(
			&BlockId::Number(0),
			SOURCE,
			uxt(Transfer {
				from: AccountId::from_h256(H256::from_low_u64_be(1)),
				to: AccountId::from_h256(H256::from_low_u64_be(2)),
				amount: 5,
				nonce: 0,
			}),
		))
		.unwrap();

		// then
		assert_eq!(pool.validated_pool().ready().map(|v| v.hash).collect::<Vec<_>>(), vec![hash]);
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
		pool.validated_pool.ban(&Instant::now(), vec![pool.hash_of(&uxt)]);
		let res = block_on(pool.submit_one(&BlockId::Number(0), SOURCE, uxt));
		assert_eq!(pool.validated_pool().status().ready, 0);
		assert_eq!(pool.validated_pool().status().future, 0);

		// then
		assert_matches!(res.unwrap_err(), error::Error::TemporarilyBanned);
	}

	#[test]
	fn should_reject_unactionable_transactions() {
		// given
		let pool = Pool::new(
			Default::default(),
			// the node does not author blocks
			false.into(),
			TestApi::default().into(),
		);

		// after validation `IncludeData` will be set to non-propagable
		let uxt = Extrinsic::IncludeData(vec![42]);

		// when
		let res = block_on(pool.submit_one(&BlockId::Number(0), SOURCE, uxt));

		// then
		assert_matches!(res.unwrap_err(), error::Error::Unactionable);
	}

	#[test]
	fn should_notify_about_pool_events() {
		let (stream, hash0, hash1) = {
			// given
			let pool = pool();
			let stream = pool.validated_pool().import_notification_stream();

			// when
			let hash0 = block_on(pool.submit_one(
				&BlockId::Number(0),
				SOURCE,
				uxt(Transfer {
					from: AccountId::from_h256(H256::from_low_u64_be(1)),
					to: AccountId::from_h256(H256::from_low_u64_be(2)),
					amount: 5,
					nonce: 0,
				}),
			))
			.unwrap();
			let hash1 = block_on(pool.submit_one(
				&BlockId::Number(0),
				SOURCE,
				uxt(Transfer {
					from: AccountId::from_h256(H256::from_low_u64_be(1)),
					to: AccountId::from_h256(H256::from_low_u64_be(2)),
					amount: 5,
					nonce: 1,
				}),
			))
			.unwrap();
			// future doesn't count
			let _hash = block_on(pool.submit_one(
				&BlockId::Number(0),
				SOURCE,
				uxt(Transfer {
					from: AccountId::from_h256(H256::from_low_u64_be(1)),
					to: AccountId::from_h256(H256::from_low_u64_be(2)),
					amount: 5,
					nonce: 3,
				}),
			))
			.unwrap();

			assert_eq!(pool.validated_pool().status().ready, 2);
			assert_eq!(pool.validated_pool().status().future, 1);

			(stream, hash0, hash1)
		};

		// then
		let mut it = futures::executor::block_on_stream(stream);
		assert_eq!(it.next(), Some(hash0));
		assert_eq!(it.next(), Some(hash1));
		assert_eq!(it.next(), None);
	}

	#[test]
	fn should_clear_stale_transactions() {
		// given
		let pool = pool();
		let hash1 = block_on(pool.submit_one(
			&BlockId::Number(0),
			SOURCE,
			uxt(Transfer {
				from: AccountId::from_h256(H256::from_low_u64_be(1)),
				to: AccountId::from_h256(H256::from_low_u64_be(2)),
				amount: 5,
				nonce: 0,
			}),
		))
		.unwrap();
		let hash2 = block_on(pool.submit_one(
			&BlockId::Number(0),
			SOURCE,
			uxt(Transfer {
				from: AccountId::from_h256(H256::from_low_u64_be(1)),
				to: AccountId::from_h256(H256::from_low_u64_be(2)),
				amount: 5,
				nonce: 1,
			}),
		))
		.unwrap();
		let hash3 = block_on(pool.submit_one(
			&BlockId::Number(0),
			SOURCE,
			uxt(Transfer {
				from: AccountId::from_h256(H256::from_low_u64_be(1)),
				to: AccountId::from_h256(H256::from_low_u64_be(2)),
				amount: 5,
				nonce: 3,
			}),
		))
		.unwrap();

		// when
		pool.validated_pool.clear_stale(&BlockId::Number(5)).unwrap();

		// then
		assert_eq!(pool.validated_pool().ready().count(), 0);
		assert_eq!(pool.validated_pool().status().future, 0);
		assert_eq!(pool.validated_pool().status().ready, 0);
		// make sure they are temporarily banned as well
		assert!(pool.validated_pool.is_banned(&hash1));
		assert!(pool.validated_pool.is_banned(&hash2));
		assert!(pool.validated_pool.is_banned(&hash3));
	}

	#[test]
	fn should_ban_mined_transactions() {
		// given
		let pool = pool();
		let hash1 = block_on(pool.submit_one(
			&BlockId::Number(0),
			SOURCE,
			uxt(Transfer {
				from: AccountId::from_h256(H256::from_low_u64_be(1)),
				to: AccountId::from_h256(H256::from_low_u64_be(2)),
				amount: 5,
				nonce: 0,
			}),
		))
		.unwrap();

		// when
		block_on(pool.prune_tags(&BlockId::Number(1), vec![vec![0]], vec![hash1])).unwrap();

		// then
		assert!(pool.validated_pool.is_banned(&hash1));
	}

	#[test]
	fn should_limit_futures() {
		// given
		let limit = Limit { count: 100, total_bytes: 200 };

		let options = Options { ready: limit.clone(), future: limit.clone(), ..Default::default() };

		let pool = Pool::new(options, true.into(), TestApi::default().into());

		let hash1 = block_on(pool.submit_one(
			&BlockId::Number(0),
			SOURCE,
			uxt(Transfer {
				from: AccountId::from_h256(H256::from_low_u64_be(1)),
				to: AccountId::from_h256(H256::from_low_u64_be(2)),
				amount: 5,
				nonce: 1,
			}),
		))
		.unwrap();
		assert_eq!(pool.validated_pool().status().future, 1);

		// when
		let hash2 = block_on(pool.submit_one(
			&BlockId::Number(0),
			SOURCE,
			uxt(Transfer {
				from: AccountId::from_h256(H256::from_low_u64_be(2)),
				to: AccountId::from_h256(H256::from_low_u64_be(2)),
				amount: 5,
				nonce: 10,
			}),
		))
		.unwrap();

		// then
		assert_eq!(pool.validated_pool().status().future, 1);
		assert!(pool.validated_pool.is_banned(&hash1));
		assert!(!pool.validated_pool.is_banned(&hash2));
	}

	#[test]
	fn should_error_if_reject_immediately() {
		// given
		let limit = Limit { count: 100, total_bytes: 10 };

		let options = Options { ready: limit.clone(), future: limit.clone(), ..Default::default() };

		let pool = Pool::new(options, true.into(), TestApi::default().into());

		// when
		block_on(pool.submit_one(
			&BlockId::Number(0),
			SOURCE,
			uxt(Transfer {
				from: AccountId::from_h256(H256::from_low_u64_be(1)),
				to: AccountId::from_h256(H256::from_low_u64_be(2)),
				amount: 5,
				nonce: 1,
			}),
		))
		.unwrap_err();

		// then
		assert_eq!(pool.validated_pool().status().ready, 0);
		assert_eq!(pool.validated_pool().status().future, 0);
	}

	#[test]
	fn should_reject_transactions_with_no_provides() {
		// given
		let pool = pool();

		// when
		let err = block_on(pool.submit_one(
			&BlockId::Number(0),
			SOURCE,
			uxt(Transfer {
				from: AccountId::from_h256(H256::from_low_u64_be(1)),
				to: AccountId::from_h256(H256::from_low_u64_be(2)),
				amount: 5,
				nonce: INVALID_NONCE,
			}),
		))
		.unwrap_err();

		// then
		assert_eq!(pool.validated_pool().status().ready, 0);
		assert_eq!(pool.validated_pool().status().future, 0);
		assert_matches!(err, error::Error::NoTagsProvided);
	}

	mod listener {
		use super::*;

		#[test]
		fn should_trigger_ready_and_finalized() {
			// given
			let pool = pool();
			let watcher = block_on(pool.submit_and_watch(
				&BlockId::Number(0),
				SOURCE,
				uxt(Transfer {
					from: AccountId::from_h256(H256::from_low_u64_be(1)),
					to: AccountId::from_h256(H256::from_low_u64_be(2)),
					amount: 5,
					nonce: 0,
				}),
			))
			.unwrap();
			assert_eq!(pool.validated_pool().status().ready, 1);
			assert_eq!(pool.validated_pool().status().future, 0);

			// when
			block_on(pool.prune_tags(&BlockId::Number(2), vec![vec![0u8]], vec![])).unwrap();
			assert_eq!(pool.validated_pool().status().ready, 0);
			assert_eq!(pool.validated_pool().status().future, 0);

			// then
			let mut stream = futures::executor::block_on_stream(watcher.into_stream());
			assert_eq!(stream.next(), Some(TransactionStatus::Ready));
			assert_eq!(
				stream.next(),
				Some(TransactionStatus::InBlock((H256::from_low_u64_be(2).into(), 0))),
			);
		}

		#[test]
		fn should_trigger_ready_and_finalized_when_pruning_via_hash() {
			// given
			let pool = pool();
			let watcher = block_on(pool.submit_and_watch(
				&BlockId::Number(0),
				SOURCE,
				uxt(Transfer {
					from: AccountId::from_h256(H256::from_low_u64_be(1)),
					to: AccountId::from_h256(H256::from_low_u64_be(2)),
					amount: 5,
					nonce: 0,
				}),
			))
			.unwrap();
			assert_eq!(pool.validated_pool().status().ready, 1);
			assert_eq!(pool.validated_pool().status().future, 0);

			// when
			block_on(pool.prune_tags(&BlockId::Number(2), vec![vec![0u8]], vec![*watcher.hash()]))
				.unwrap();
			assert_eq!(pool.validated_pool().status().ready, 0);
			assert_eq!(pool.validated_pool().status().future, 0);

			// then
			let mut stream = futures::executor::block_on_stream(watcher.into_stream());
			assert_eq!(stream.next(), Some(TransactionStatus::Ready));
			assert_eq!(
				stream.next(),
				Some(TransactionStatus::InBlock((H256::from_low_u64_be(2).into(), 0))),
			);
		}

		#[test]
		fn should_trigger_future_and_ready_after_promoted() {
			// given
			let pool = pool();
			let watcher = block_on(pool.submit_and_watch(
				&BlockId::Number(0),
				SOURCE,
				uxt(Transfer {
					from: AccountId::from_h256(H256::from_low_u64_be(1)),
					to: AccountId::from_h256(H256::from_low_u64_be(2)),
					amount: 5,
					nonce: 1,
				}),
			))
			.unwrap();
			assert_eq!(pool.validated_pool().status().ready, 0);
			assert_eq!(pool.validated_pool().status().future, 1);

			// when
			block_on(pool.submit_one(
				&BlockId::Number(0),
				SOURCE,
				uxt(Transfer {
					from: AccountId::from_h256(H256::from_low_u64_be(1)),
					to: AccountId::from_h256(H256::from_low_u64_be(2)),
					amount: 5,
					nonce: 0,
				}),
			))
			.unwrap();
			assert_eq!(pool.validated_pool().status().ready, 2);

			// then
			let mut stream = futures::executor::block_on_stream(watcher.into_stream());
			assert_eq!(stream.next(), Some(TransactionStatus::Future));
			assert_eq!(stream.next(), Some(TransactionStatus::Ready));
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
			let watcher =
				block_on(pool.submit_and_watch(&BlockId::Number(0), SOURCE, uxt)).unwrap();
			assert_eq!(pool.validated_pool().status().ready, 1);

			// when
			pool.validated_pool.remove_invalid(&[*watcher.hash()]);

			// then
			let mut stream = futures::executor::block_on_stream(watcher.into_stream());
			assert_eq!(stream.next(), Some(TransactionStatus::Ready));
			assert_eq!(stream.next(), Some(TransactionStatus::Invalid));
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
			let watcher =
				block_on(pool.submit_and_watch(&BlockId::Number(0), SOURCE, uxt)).unwrap();
			assert_eq!(pool.validated_pool().status().ready, 1);

			// when
			let mut map = HashMap::new();
			let peers = vec!["a".into(), "b".into(), "c".into()];
			map.insert(*watcher.hash(), peers.clone());
			pool.validated_pool().on_broadcasted(map);

			// then
			let mut stream = futures::executor::block_on_stream(watcher.into_stream());
			assert_eq!(stream.next(), Some(TransactionStatus::Ready));
			assert_eq!(stream.next(), Some(TransactionStatus::Broadcast(peers)));
		}

		#[test]
		fn should_trigger_dropped_older() {
			// given
			let limit = Limit { count: 1, total_bytes: 1000 };
			let options =
				Options { ready: limit.clone(), future: limit.clone(), ..Default::default() };

			let pool = Pool::new(options, true.into(), TestApi::default().into());

			let xt = uxt(Transfer {
				from: AccountId::from_h256(H256::from_low_u64_be(1)),
				to: AccountId::from_h256(H256::from_low_u64_be(2)),
				amount: 5,
				nonce: 0,
			});
			let watcher = block_on(pool.submit_and_watch(&BlockId::Number(0), SOURCE, xt)).unwrap();
			assert_eq!(pool.validated_pool().status().ready, 1);

			// when
			let xt = uxt(Transfer {
				from: AccountId::from_h256(H256::from_low_u64_be(2)),
				to: AccountId::from_h256(H256::from_low_u64_be(1)),
				amount: 4,
				nonce: 1,
			});
			block_on(pool.submit_one(&BlockId::Number(1), SOURCE, xt)).unwrap();
			assert_eq!(pool.validated_pool().status().ready, 1);

			// then
			let mut stream = futures::executor::block_on_stream(watcher.into_stream());
			assert_eq!(stream.next(), Some(TransactionStatus::Ready));
			assert_eq!(stream.next(), Some(TransactionStatus::Dropped));
		}

		#[test]
		fn should_trigger_dropped_lower_priority() {
			{
				// given
				let limit = Limit { count: 1, total_bytes: 1000 };
				let options =
					Options { ready: limit.clone(), future: limit.clone(), ..Default::default() };

				let pool = Pool::new(options, true.into(), TestApi::default().into());

				let xt = Extrinsic::IncludeData(Vec::new());
				block_on(pool.submit_one(&BlockId::Number(0), SOURCE, xt)).unwrap();
				assert_eq!(pool.validated_pool().status().ready, 1);

				// then
				let xt = uxt(Transfer {
					from: AccountId::from_h256(H256::from_low_u64_be(2)),
					to: AccountId::from_h256(H256::from_low_u64_be(1)),
					amount: 4,
					nonce: 1,
				});
				let result = block_on(pool.submit_one(&BlockId::Number(1), SOURCE, xt));
				assert!(matches!(
					result,
					Err(sc_transaction_pool_api::error::Error::ImmediatelyDropped)
				));
			}
			{
				// given
				let limit = Limit { count: 2, total_bytes: 1000 };
				let options =
					Options { ready: limit.clone(), future: limit.clone(), ..Default::default() };

				let pool = Pool::new(options, true.into(), TestApi::default().into());

				let xt = Extrinsic::IncludeData(Vec::new());
				block_on(pool.submit_and_watch(&BlockId::Number(0), SOURCE, xt)).unwrap();
				assert_eq!(pool.validated_pool().status().ready, 1);

				let xt = uxt(Transfer {
					from: AccountId::from_h256(H256::from_low_u64_be(1)),
					to: AccountId::from_h256(H256::from_low_u64_be(2)),
					amount: 5,
					nonce: 0,
				});
				let watcher =
					block_on(pool.submit_and_watch(&BlockId::Number(0), SOURCE, xt)).unwrap();
				assert_eq!(pool.validated_pool().status().ready, 2);

				// when
				let xt = Extrinsic::Store(Vec::new());
				block_on(pool.submit_one(&BlockId::Number(1), SOURCE, xt)).unwrap();
				assert_eq!(pool.validated_pool().status().ready, 2);

				// then
				let mut stream = futures::executor::block_on_stream(watcher.into_stream());
				assert_eq!(stream.next(), Some(TransactionStatus::Ready));
				assert_eq!(stream.next(), Some(TransactionStatus::Dropped));
			}
		}

		#[test]
		fn should_handle_pruning_in_the_middle_of_import() {
			// given
			let (ready, is_ready) = std::sync::mpsc::sync_channel(0);
			let (tx, rx) = std::sync::mpsc::sync_channel(1);
			let mut api = TestApi::default();
			api.delay = Arc::new(Mutex::new(rx.into()));
			let pool = Arc::new(Pool::new(Default::default(), true.into(), api.into()));

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
				block_on(pool2.submit_one(&BlockId::Number(0), SOURCE, xt)).unwrap();
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
			block_on(pool.submit_one(&BlockId::Number(0), SOURCE, xt)).unwrap();
			assert_eq!(pool.validated_pool().status().ready, 1);

			// Now block import happens before the second transaction is able to finish
			// verification.
			block_on(pool.prune_tags(&BlockId::Number(1), vec![provides], vec![])).unwrap();
			assert_eq!(pool.validated_pool().status().ready, 0);

			// so when we release the verification of the previous one it will have
			// something in `requires`, but should go to ready directly, since the previous
			// transaction was imported correctly.
			tx.send(()).unwrap();

			// then
			is_ready.recv().unwrap(); // wait for finish
			assert_eq!(pool.validated_pool().status().ready, 1);
			assert_eq!(pool.validated_pool().status().future, 0);
		}
	}
}
