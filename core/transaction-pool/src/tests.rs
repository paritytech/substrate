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


use super::*;

use parity_codec::Encode;
use txpool::{self, Pool};
use test_client::{runtime::{AccountId, Block, Hash, Index, Extrinsic, Transfer}, AccountKeyring::{self, *}};
use sr_primitives::{
	generic::{self, BlockId},
	traits::{Hash as HashT, BlakeTwo256},
	transaction_validity::TransactionValidity,
};

struct TestApi;

impl TestApi {
	fn default() -> Self {
		TestApi
	}
}

impl txpool::ChainApi for TestApi {
	type Block = Block;
	type Hash = Hash;
	type Error = error::Error;

	fn validate_transaction(&self, at: &BlockId<Self::Block>, uxt: txpool::ExtrinsicFor<Self>) -> error::Result<TransactionValidity> {
		let expected = index(at);
		let requires = if expected == uxt.transfer().nonce {
			vec![]
		} else {
			vec![vec![uxt.transfer().nonce as u8 - 1]]
		};
		let provides = vec![vec![uxt.transfer().nonce as u8]];

		Ok(TransactionValidity::Valid {
			priority: 1,
			requires,
			provides,
			longevity: 64,
		})
	}

	fn block_id_to_number(&self, at: &BlockId<Self::Block>) -> error::Result<Option<txpool::NumberFor<Self>>> {
		Ok(Some(number_of(at)))
	}

	fn block_id_to_hash(&self, at: &BlockId<Self::Block>) -> error::Result<Option<txpool::BlockHash<Self>>> {
		Ok(match at {
			generic::BlockId::Hash(x) => Some(x.clone()),
			_ => Some(Default::default()),
		})
	}

	fn hash_and_length(&self, ex: &txpool::ExtrinsicFor<Self>) -> (Self::Hash, usize) {
		let encoded = ex.encode();
		(BlakeTwo256::hash(&encoded), encoded.len())
	}

}

fn index(at: &BlockId<Block>) -> u64 {
	209 + number_of(at)
}

fn number_of(at: &BlockId<Block>) -> u64 {
	match at {
		generic::BlockId::Number(n) => *n as u64,
		_ => 0,
	}
}

fn uxt(who: AccountKeyring, nonce: Index) -> Extrinsic {
	let transfer = Transfer {
		from: who.into(),
		to: AccountId::default(),
		nonce,
		amount: 1,
	};
	let signature = transfer.using_encoded(|e| who.sign(e));
	Extrinsic::Transfer(transfer, signature.into())
}

fn pool() -> Pool<TestApi> {
	Pool::new(Default::default(), TestApi::default())
}

#[test]
fn submission_should_work() {
	let pool = pool();
	assert_eq!(209, index(&BlockId::number(0)));
	pool.submit_one(&BlockId::number(0), uxt(Alice, 209)).unwrap();

	let pending: Vec<_> = pool.ready().map(|a| a.data.transfer().nonce).collect();
	assert_eq!(pending, vec![209]);
}

#[test]
fn multiple_submission_should_work() {
	let pool = pool();
	pool.submit_one(&BlockId::number(0), uxt(Alice, 209)).unwrap();
	pool.submit_one(&BlockId::number(0), uxt(Alice, 210)).unwrap();

	let pending: Vec<_> = pool.ready().map(|a| a.data.transfer().nonce).collect();
	assert_eq!(pending, vec![209, 210]);
}

#[test]
fn early_nonce_should_be_culled() {
	let pool = pool();
	pool.submit_one(&BlockId::number(0), uxt(Alice, 208)).unwrap();

	let pending: Vec<_> = pool.ready().map(|a| a.data.transfer().nonce).collect();
	assert_eq!(pending, Vec::<Index>::new());
}

#[test]
fn late_nonce_should_be_queued() {
	let pool = pool();

	pool.submit_one(&BlockId::number(0), uxt(Alice, 210)).unwrap();
	let pending: Vec<_> = pool.ready().map(|a| a.data.transfer().nonce).collect();
	assert_eq!(pending, Vec::<Index>::new());

	pool.submit_one(&BlockId::number(0), uxt(Alice, 209)).unwrap();
	let pending: Vec<_> = pool.ready().map(|a| a.data.transfer().nonce).collect();
	assert_eq!(pending, vec![209, 210]);
}

#[test]
fn prune_tags_should_work() {
	let pool = pool();
	pool.submit_one(&BlockId::number(0), uxt(Alice, 209)).unwrap();
	pool.submit_one(&BlockId::number(0), uxt(Alice, 210)).unwrap();

	let pending: Vec<_> = pool.ready().map(|a| a.data.transfer().nonce).collect();
	assert_eq!(pending, vec![209, 210]);

	pool.prune_tags(&BlockId::number(1), vec![vec![209]], vec![]).unwrap();

	let pending: Vec<_> = pool.ready().map(|a| a.data.transfer().nonce).collect();
	assert_eq!(pending, vec![210]);
}

#[test]
fn should_ban_invalid_transactions() {
	let pool = pool();
	let uxt = uxt(Alice, 209);
	let hash = pool.submit_one(&BlockId::number(0), uxt.clone()).unwrap();
	pool.remove_invalid(&[hash]);
	pool.submit_one(&BlockId::number(0), uxt.clone()).unwrap_err();

	// when
	let pending: Vec<_> = pool.ready().map(|a| a.data.transfer().nonce).collect();
	assert_eq!(pending, Vec::<Index>::new());

	// then
	pool.submit_one(&BlockId::number(0), uxt.clone()).unwrap_err();
}
