// Copyright 2018-2020 Parity Technologies (UK) Ltd.
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

use codec::Encode;
use futures::executor::block_on;
use sc_transaction_graph::{self, Pool};
use substrate_test_runtime_client::{runtime::{AccountId, Block, Hash, Index, Extrinsic, Transfer}, AccountKeyring::{self, *}};
use sp_runtime::{
	generic::{self, BlockId},
	traits::{Hash as HashT, BlakeTwo256},
	transaction_validity::{TransactionValidity, ValidTransaction},
};

struct TestApi {
	pub modifier: Box<dyn Fn(&mut ValidTransaction) + Send + Sync>,
}

impl TestApi {
	fn default() -> Self {
		TestApi {
			modifier: Box::new(|_| {}),
		}
	}
}

impl sc_transaction_graph::ChainApi for TestApi {
	type Block = Block;
	type Hash = Hash;
	type Error = error::Error;
	type ValidationFuture = futures::future::Ready<error::Result<TransactionValidity>>;

	fn validate_transaction(
		&self,
		at: &BlockId<Self::Block>,
		uxt: sc_transaction_graph::ExtrinsicFor<Self>,
	) -> Self::ValidationFuture {
		let expected = index(at);
		let requires = if expected == uxt.transfer().nonce {
			vec![]
		} else {
			vec![vec![uxt.transfer().nonce as u8 - 1]]
		};
		let provides = vec![vec![uxt.transfer().nonce as u8]];

		let mut validity = ValidTransaction {
			priority: 1,
			requires,
			provides,
			longevity: 64,
			propagate: true,
		};

		(self.modifier)(&mut validity);

		futures::future::ready(Ok(
			Ok(validity)
		))
	}

	fn block_id_to_number(&self, at: &BlockId<Self::Block>) -> error::Result<Option<sc_transaction_graph::NumberFor<Self>>> {
		Ok(Some(number_of(at)))
	}

	fn block_id_to_hash(&self, at: &BlockId<Self::Block>) -> error::Result<Option<sc_transaction_graph::BlockHash<Self>>> {
		Ok(match at {
			generic::BlockId::Hash(x) => Some(x.clone()),
			_ => Some(Default::default()),
		})
	}

	fn hash_and_length(&self, ex: &sc_transaction_graph::ExtrinsicFor<Self>) -> (Self::Hash, usize) {
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
	block_on(pool.submit_one(&BlockId::number(0), uxt(Alice, 209))).unwrap();

	let pending: Vec<_> = pool.ready().map(|a| a.data.transfer().nonce).collect();
	assert_eq!(pending, vec![209]);
}

#[test]
fn multiple_submission_should_work() {
	let pool = pool();
	block_on(pool.submit_one(&BlockId::number(0), uxt(Alice, 209))).unwrap();
	block_on(pool.submit_one(&BlockId::number(0), uxt(Alice, 210))).unwrap();

	let pending: Vec<_> = pool.ready().map(|a| a.data.transfer().nonce).collect();
	assert_eq!(pending, vec![209, 210]);
}

#[test]
fn early_nonce_should_be_culled() {
	let pool = pool();
	block_on(pool.submit_one(&BlockId::number(0), uxt(Alice, 208))).unwrap();

	let pending: Vec<_> = pool.ready().map(|a| a.data.transfer().nonce).collect();
	assert_eq!(pending, Vec::<Index>::new());
}

#[test]
fn late_nonce_should_be_queued() {
	let pool = pool();

	block_on(pool.submit_one(&BlockId::number(0), uxt(Alice, 210))).unwrap();
	let pending: Vec<_> = pool.ready().map(|a| a.data.transfer().nonce).collect();
	assert_eq!(pending, Vec::<Index>::new());

	block_on(pool.submit_one(&BlockId::number(0), uxt(Alice, 209))).unwrap();
	let pending: Vec<_> = pool.ready().map(|a| a.data.transfer().nonce).collect();
	assert_eq!(pending, vec![209, 210]);
}

#[test]
fn prune_tags_should_work() {
	let pool = pool();
	block_on(pool.submit_one(&BlockId::number(0), uxt(Alice, 209))).unwrap();
	block_on(pool.submit_one(&BlockId::number(0), uxt(Alice, 210))).unwrap();

	let pending: Vec<_> = pool.ready().map(|a| a.data.transfer().nonce).collect();
	assert_eq!(pending, vec![209, 210]);

	block_on(pool.prune_tags(&BlockId::number(1), vec![vec![209]], vec![])).unwrap();

	let pending: Vec<_> = pool.ready().map(|a| a.data.transfer().nonce).collect();
	assert_eq!(pending, vec![210]);
}

#[test]
fn should_ban_invalid_transactions() {
	let pool = pool();
	let uxt = uxt(Alice, 209);
	let hash = block_on(pool.submit_one(&BlockId::number(0), uxt.clone())).unwrap();
	pool.remove_invalid(&[hash]);
	block_on(pool.submit_one(&BlockId::number(0), uxt.clone())).unwrap_err();

	// when
	let pending: Vec<_> = pool.ready().map(|a| a.data.transfer().nonce).collect();
	assert_eq!(pending, Vec::<Index>::new());

	// then
	block_on(pool.submit_one(&BlockId::number(0), uxt.clone())).unwrap_err();
}

#[test]
fn should_correctly_prune_transactions_providing_more_than_one_tag() {
	let mut api = TestApi::default();
	api.modifier = Box::new(|v: &mut ValidTransaction| {
		v.provides.push(vec![155]);
	});
	let pool = Pool::new(Default::default(), api);
	let xt = uxt(Alice, 209);
	block_on(pool.submit_one(&BlockId::number(0), xt.clone())).expect("1. Imported");
	assert_eq!(pool.status().ready, 1);

	// remove the transaction that just got imported.
	block_on(pool.prune_tags(&BlockId::number(1), vec![vec![209]], vec![])).expect("1. Pruned");
	assert_eq!(pool.status().ready, 0);
	// it's re-imported to future
	assert_eq!(pool.status().future, 1);

	// so now let's insert another transaction that also provides the 155
	let xt = uxt(Alice, 211);
	block_on(pool.submit_one(&BlockId::number(2), xt.clone())).expect("2. Imported");
	assert_eq!(pool.status().ready, 1);
	assert_eq!(pool.status().future, 1);
	let pending: Vec<_> = pool.ready().map(|a| a.data.transfer().nonce).collect();
	assert_eq!(pending, vec![211]);

	// prune it and make sure the pool is empty
	block_on(pool.prune_tags(&BlockId::number(3), vec![vec![155]], vec![])).expect("2. Pruned");
	assert_eq!(pool.status().ready, 0);
	assert_eq!(pool.status().future, 2);
}
