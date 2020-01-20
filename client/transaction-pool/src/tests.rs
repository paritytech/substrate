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

use crate::{BasicPool, MaintainedTransactionPool};
use codec::Encode;
use futures::executor::block_on;
use parking_lot::RwLock;
use sc_transaction_graph::{self, ExHash, Pool};
use sp_runtime::{
	generic::{self, BlockId},
	traits::{BlakeTwo256, Hash as HashT},
	transaction_validity::{TransactionValidity, ValidTransaction, TransactionValidityError, InvalidTransaction},
};
use std::collections::HashSet;
use substrate_test_runtime_client::{
	runtime::{AccountId, Block, BlockNumber, Extrinsic, Hash, Header, Index, Transfer},
	AccountKeyring::{self, *},
};

struct TestApi {
	pub modifier: RwLock<Box<dyn Fn(&mut ValidTransaction) + Send + Sync>>,
	pub chain_block_by_number: RwLock<HashMap<BlockNumber, Vec<Extrinsic>>>,
	pub chain_headers_by_number: RwLock<HashMap<BlockNumber, Header>>,
	pub invalid_hashes: RwLock<HashSet<ExHash<Self>>>,
	pub validation_requests: RwLock<Vec<Extrinsic>>,
}

impl TestApi {
	fn default() -> Self {
		TestApi {
			modifier: RwLock::new(Box::new(|_| {})),
			chain_block_by_number: RwLock::new(HashMap::new()),
			invalid_hashes: RwLock::new(HashSet::new()),
			chain_headers_by_number: RwLock::new(HashMap::new()),
			validation_requests: RwLock::new(Default::default()),
		}
	}

	fn push_block(&self, block_number: BlockNumber, xts: Vec<Extrinsic>) {
		self.chain_block_by_number.write().insert(block_number, xts);
		self.chain_headers_by_number.write().insert(block_number, Header {
			number: block_number,
			digest: Default::default(),
			extrinsics_root:  Default::default(),
			parent_hash: Default::default(),
			state_root: Default::default(),
		});
	}
}

impl sc_transaction_graph::ChainApi for TestApi {
	type Block = Block;
	type Hash = Hash;
	type Error = error::Error;
	type ValidationFuture = futures::future::Ready<error::Result<TransactionValidity>>;
	type BodyFuture = futures::future::Ready<error::Result<Option<Vec<Extrinsic>>>>;

	fn validate_transaction(
		&self,
		at: &BlockId<Self::Block>,
		uxt: sc_transaction_graph::ExtrinsicFor<Self>,
	) -> Self::ValidationFuture {

		self.validation_requests.write().push(uxt.clone());

		let expected = index(at);
		let requires = if expected == uxt.transfer().nonce {
			vec![]
		} else {
			vec![vec![uxt.transfer().nonce as u8 - 1]]
		};
		let provides = vec![vec![uxt.transfer().nonce as u8]];

		if self.invalid_hashes.read().contains(&self.hash_and_length(&uxt).0) {
			return futures::future::ready(Ok(
				Err(TransactionValidityError::Invalid(InvalidTransaction::Custom(0)))
			))
		}

		let mut validity = ValidTransaction {
			priority: 1,
			requires,
			provides,
			longevity: 64,
			propagate: true,
		};

		(self.modifier.read())(&mut validity);

		futures::future::ready(Ok(Ok(validity)))
	}

	fn block_id_to_number(
		&self,
		at: &BlockId<Self::Block>,
	) -> error::Result<Option<sc_transaction_graph::NumberFor<Self>>> {
		Ok(Some(number_of(at)))
	}

	fn block_id_to_hash(
		&self,
		at: &BlockId<Self::Block>,
	) -> error::Result<Option<sc_transaction_graph::BlockHash<Self>>> {
		Ok(match at {
			generic::BlockId::Hash(x) => Some(x.clone()),
			_ => Some(Default::default()),
		})
	}

	fn hash_and_length(
		&self,
		ex: &sc_transaction_graph::ExtrinsicFor<Self>,
	) -> (Self::Hash, usize) {
		let encoded = ex.encode();
		(BlakeTwo256::hash(&encoded), encoded.len())
	}

	fn block_body(&self, id: &BlockId<Self::Block>) -> Self::BodyFuture {
		futures::future::ready(Ok(if let BlockId::Number(num) = id {
			self.chain_block_by_number.read().get(num).cloned()
		} else {
			None
		}))
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
	Pool::new(Default::default(), TestApi::default().into())
}

fn maintained_pool() -> BasicPool<TestApi, Block> {
	BasicPool::new(Default::default(), TestApi::default())
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
	let api = TestApi::default();
	*api.modifier.write() = Box::new(|v: &mut ValidTransaction| {
		v.provides.push(vec![155]);
	});
	let pool = Pool::new(Default::default(), Arc::new(api));
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

#[test]
fn should_prune_old_during_maintenance() {
	let xt = uxt(Alice, 209);

	let pool = maintained_pool();

	block_on(pool.submit_one(&BlockId::number(0), xt.clone())).expect("1. Imported");
	assert_eq!(pool.status().ready, 1);

	pool.api.push_block(1, vec![xt.clone()]);

	block_on(pool.maintain(&BlockId::number(1), &[]));
	assert_eq!(pool.status().ready, 0);
}


#[test]
fn should_revalidate_during_maintenance() {
	let xt1 = uxt(Alice, 209);
	let xt2 = uxt(Alice, 210);

	let pool = maintained_pool();
	block_on(pool.submit_one(&BlockId::number(0), xt1.clone())).expect("1. Imported");
	block_on(pool.submit_one(&BlockId::number(0), xt2.clone())).expect("2. Imported");
	assert_eq!(pool.status().ready, 2);
	assert_eq!(pool.api.validation_requests.read().len(), 2);

	pool.api.push_block(1, vec![xt1.clone()]);

	block_on(pool.maintain(&BlockId::number(1), &[]));
	assert_eq!(pool.status().ready, 1);
	// test that pool revalidated transaction that left ready and not included in the block
	assert_eq!(pool.api.validation_requests.read().len(), 3);
}
