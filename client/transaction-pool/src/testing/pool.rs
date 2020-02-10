// Copyright 2020 Parity Technologies (UK) Ltd.
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

use crate::*;
use sc_transaction_graph::{self, Pool};
use sp_transaction_pool::TransactionStatus;
use futures::executor::block_on;
use sp_runtime::{
	generic::BlockId,
	transaction_validity::ValidTransaction,
};
use substrate_test_runtime_client::{
	runtime::{Block, Hash, Index, Extrinsic},
	AccountKeyring::*,
};
use substrate_test_runtime_transaction_pool::{TestApi, uxt};

fn pool() -> Pool<TestApi> {
	Pool::new(Default::default(), TestApi::with_alice_nonce(209).into())
}

fn maintained_pool() -> (BasicPool<TestApi, Block>, futures::executor::ThreadPool) {
	let (pool, background_task) = BasicPool::new(Default::default(), std::sync::Arc::new(TestApi::with_alice_nonce(209)));

	let thread_pool = futures::executor::ThreadPool::new().unwrap();
	thread_pool.spawn_ok(background_task);
	(pool, thread_pool)
}

#[test]
fn submission_should_work() {
	let pool = pool();
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
	let hash209 = block_on(pool.submit_one(&BlockId::number(0), uxt(Alice, 209))).unwrap();
	block_on(pool.submit_one(&BlockId::number(0), uxt(Alice, 210))).unwrap();

	let pending: Vec<_> = pool.ready().map(|a| a.data.transfer().nonce).collect();
	assert_eq!(pending, vec![209, 210]);

	block_on(
		pool.prune_tags(
			&BlockId::number(1),
			vec![vec![209]],
			vec![hash209],
		)
	).expect("Prune tags");

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
	let api = Arc::new(TestApi::with_alice_nonce(209));
	api.set_valid_modifier(Box::new(|v: &mut ValidTransaction| {
		v.provides.push(vec![155]);
	}));
	let pool = Pool::new(Default::default(), api.clone());
	let xt = uxt(Alice, 209);
	block_on(pool.submit_one(&BlockId::number(0), xt.clone())).expect("1. Imported");
	assert_eq!(pool.status().ready, 1);

	// remove the transaction that just got imported.
	api.increment_nonce(Alice.into());
	block_on(pool.prune_tags(&BlockId::number(1), vec![vec![209]], vec![])).expect("1. Pruned");
	assert_eq!(pool.status().ready, 0);
	// it's re-imported to future
	assert_eq!(pool.status().future, 1);

	// so now let's insert another transaction that also provides the 155
	api.increment_nonce(Alice.into());
	let xt = uxt(Alice, 211);
	block_on(pool.submit_one(&BlockId::number(2), xt.clone())).expect("2. Imported");
	assert_eq!(pool.status().ready, 1);
	assert_eq!(pool.status().future, 1);
	let pending: Vec<_> = pool.ready().map(|a| a.data.transfer().nonce).collect();
	assert_eq!(pending, vec![211]);

	// prune it and make sure the pool is empty
	api.increment_nonce(Alice.into());
	block_on(pool.prune_tags(&BlockId::number(3), vec![vec![155]], vec![])).expect("2. Pruned");
	assert_eq!(pool.status().ready, 0);
	assert_eq!(pool.status().future, 2);
}

#[test]
fn should_prune_old_during_maintenance() {
	let xt = uxt(Alice, 209);

	let (pool, _guard) = maintained_pool();

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

	let (pool, _guard) = maintained_pool();
	block_on(pool.submit_one(&BlockId::number(0), xt1.clone())).expect("1. Imported");
	block_on(pool.submit_one(&BlockId::number(0), xt2.clone())).expect("2. Imported");
	assert_eq!(pool.status().ready, 2);
	assert_eq!(pool.api.validation_requests().len(), 2);

	pool.api.push_block(1, vec![xt1.clone()]);

	block_on(pool.maintain(&BlockId::number(1), &[]));

	// maintaince is in background
	block_on(futures_timer::Delay::new(std::time::Duration::from_millis(10)));

	assert_eq!(pool.status().ready, 1);
	// test that pool revalidated transaction that left ready and not included in the block
	assert_eq!(pool.api.validation_requests().len(), 3);
}

#[test]
fn should_resubmit_from_retracted_during_maintaince() {
	let xt = uxt(Alice, 209);
	let retracted_hash = Hash::random();

	let (pool, _guard) = maintained_pool();

	block_on(pool.submit_one(&BlockId::number(0), xt.clone())).expect("1. Imported");
	assert_eq!(pool.status().ready, 1);

	pool.api.push_block(1, vec![]);
	pool.api.push_fork_block(retracted_hash, vec![xt.clone()]);

	block_on(pool.maintain(&BlockId::number(1), &[retracted_hash]));
	assert_eq!(pool.status().ready, 1);
}

#[test]
fn should_not_retain_invalid_hashes_from_retracted() {
	let xt = uxt(Alice, 209);
	let retracted_hash = Hash::random();

	let (pool, _guard) = maintained_pool();

	block_on(pool.submit_one(&BlockId::number(0), xt.clone())).expect("1. Imported");
	assert_eq!(pool.status().ready, 1);

	pool.api.push_block(1, vec![]);
	pool.api.push_fork_block(retracted_hash, vec![xt.clone()]);
	pool.api.add_invalid(&xt);

	block_on(pool.maintain(&BlockId::number(1), &[retracted_hash]));

	// maintenance is in background
	block_on(futures_timer::Delay::new(std::time::Duration::from_millis(10)));

	assert_eq!(pool.status().ready, 0);
}

#[test]
fn should_push_watchers_during_maintaince() {
	fn alice_uxt(nonce: u64) -> Extrinsic {
		uxt(Alice, 209 + nonce)
	}

	// given
	let (pool, _guard) = maintained_pool();

	let tx0 = alice_uxt(0);
	let watcher0 = block_on(pool.submit_and_watch(&BlockId::Number(0), tx0.clone())).unwrap();
	let tx1 = alice_uxt(1);
	let watcher1 = block_on(pool.submit_and_watch(&BlockId::Number(0), tx1.clone())).unwrap();
	let tx2 = alice_uxt(2);
	let watcher2 = block_on(pool.submit_and_watch(&BlockId::Number(0), tx2.clone())).unwrap();
	let tx3 = alice_uxt(3);
	let watcher3 = block_on(pool.submit_and_watch(&BlockId::Number(0), tx3.clone())).unwrap();
	let tx4 = alice_uxt(4);
	let watcher4 = block_on(pool.submit_and_watch(&BlockId::Number(0), tx4.clone())).unwrap();
	assert_eq!(pool.status().ready, 5);

	// when
	pool.api.add_invalid(&tx3);
	pool.api.add_invalid(&tx4);
	block_on(pool.maintain(&BlockId::Number(0), &[]));

	// revalidation is in background
	block_on(futures_timer::Delay::new(std::time::Duration::from_millis(10)));

	// then
	// hash3 is now invalid
	// hash4 is now invalid

	assert_eq!(pool.status().ready, 3);
	assert_eq!(
		futures::executor::block_on_stream(watcher3).collect::<Vec<_>>(),
		vec![TransactionStatus::Ready, TransactionStatus::Invalid],
	);
	assert_eq!(
		futures::executor::block_on_stream(watcher4).collect::<Vec<_>>(),
		vec![TransactionStatus::Ready, TransactionStatus::Invalid],
	);

	// when
	pool.api.push_block(1, vec![tx0, tx1, tx2]);
	block_on(pool.maintain(&BlockId::Number(1), &[]));

	// then
	// events for hash0 are: Ready, InBlock
	// events for hash1 are: Ready, InBlock
	// events for hash2 are: Ready, InBlock
	assert_eq!(
		futures::executor::block_on_stream(watcher0).collect::<Vec<_>>(),
		vec![TransactionStatus::Ready, TransactionStatus::InBlock(Hash::zero())],
	);
	assert_eq!(
		futures::executor::block_on_stream(watcher1).collect::<Vec<_>>(),
		vec![TransactionStatus::Ready, TransactionStatus::InBlock(Hash::zero())],
	);
	assert_eq!(
		futures::executor::block_on_stream(watcher2).collect::<Vec<_>>(),
		vec![TransactionStatus::Ready, TransactionStatus::InBlock(Hash::zero())],
	);
}

#[test]
fn can_track_heap_size() {
	let (pool, _guard) = maintained_pool();
	block_on(pool.submit_one(&BlockId::number(0), uxt(Alice, 209))).expect("1. Imported");
	block_on(pool.submit_one(&BlockId::number(0), uxt(Alice, 210))).expect("1. Imported");
	block_on(pool.submit_one(&BlockId::number(0), uxt(Alice, 211))).expect("1. Imported");
	block_on(pool.submit_one(&BlockId::number(0), uxt(Alice, 212))).expect("1. Imported");

	assert!(parity_util_mem::malloc_size(&pool) > 3000);
}
