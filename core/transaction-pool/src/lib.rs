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

// tag::description[]
//! Substrate transaction pool.
// end::description[]

#![warn(missing_docs)]
#![warn(unused_extern_crates)]

extern crate substrate_transaction_graph as txpool;

#[cfg(test)]
pub mod tests {
	use super::*;
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
		type Error = txpool::error::Error;
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

	#[test]
	fn should_ban_invalid_transactions() {
		let pool = pool();
		let uxt = uxt(Alice, 209);
		let hash = *pool.submit_one(&BlockId::number(0), uxt.clone()).unwrap().hash();
		pool.remove(&[hash], true);
		pool.submit_one(&BlockId::number(0), uxt.clone()).unwrap();

		// when
		pool.remove(&[hash], false);
		let pending: Vec<AccountId> = pool.cull_and_get_pending(&BlockId::number(0), |p| p.map(|a| *a.sender()).collect()).unwrap();
		assert_eq!(pending, vec![]);

		// then
		pool.submit_one(&BlockId::number(0), uxt.clone()).unwrap_err();
	}
}
