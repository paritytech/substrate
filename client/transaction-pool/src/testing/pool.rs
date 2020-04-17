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
use sp_transaction_pool::TransactionStatus;
use futures::executor::block_on;
use txpool::{self, Pool};
use sp_runtime::{
	generic::BlockId,
	transaction_validity::{ValidTransaction, TransactionSource, InvalidTransaction},
};
use substrate_test_runtime_client::{
	runtime::{Block, Hash, Index, Header, Extrinsic, Transfer},
	AccountKeyring::*,
};
use substrate_test_runtime_transaction_pool::{TestApi, uxt};
use futures::{prelude::*, task::Poll};
use codec::Encode;

fn pool() -> Pool<TestApi> {
	Pool::new(Default::default(), TestApi::with_alice_nonce(209).into())
}

fn maintained_pool() -> (
	BasicPool<TestApi, Block>,
	futures::executor::ThreadPool,
	intervalier::BackSignalControl,
) {
	let (pool, background_task, notifier) = BasicPool::new_test(
		std::sync::Arc::new(TestApi::with_alice_nonce(209))
	);

	let thread_pool = futures::executor::ThreadPool::new().unwrap();
	thread_pool.spawn_ok(background_task);
	(pool, thread_pool, notifier)
}

fn header(number: u64) -> Header {
	Header {
		number,
		digest: Default::default(),
		extrinsics_root:  Default::default(),
		parent_hash: Default::default(),
		state_root: Default::default(),
	}
}

const SOURCE: TransactionSource = TransactionSource::External;

#[test]
fn submission_should_work() {
	let pool = pool();
	block_on(pool.submit_one(&BlockId::number(0), SOURCE, uxt(Alice, 209))).unwrap();

	let pending: Vec<_> = pool.validated_pool().ready().map(|a| a.data.transfer().nonce).collect();
	assert_eq!(pending, vec![209]);
}

#[test]
fn multiple_submission_should_work() {
	let pool = pool();
	block_on(pool.submit_one(&BlockId::number(0), SOURCE, uxt(Alice, 209))).unwrap();
	block_on(pool.submit_one(&BlockId::number(0), SOURCE, uxt(Alice, 210))).unwrap();

	let pending: Vec<_> = pool.validated_pool().ready().map(|a| a.data.transfer().nonce).collect();
	assert_eq!(pending, vec![209, 210]);
}

#[test]
fn early_nonce_should_be_culled() {
	let pool = pool();
	block_on(pool.submit_one(&BlockId::number(0), SOURCE, uxt(Alice, 208))).unwrap();

	let pending: Vec<_> = pool.validated_pool().ready().map(|a| a.data.transfer().nonce).collect();
	assert_eq!(pending, Vec::<Index>::new());
}

#[test]
fn late_nonce_should_be_queued() {
	let pool = pool();

	block_on(pool.submit_one(&BlockId::number(0), SOURCE, uxt(Alice, 210))).unwrap();
	let pending: Vec<_> = pool.validated_pool().ready().map(|a| a.data.transfer().nonce).collect();
	assert_eq!(pending, Vec::<Index>::new());

	block_on(pool.submit_one(&BlockId::number(0), SOURCE, uxt(Alice, 209))).unwrap();
	let pending: Vec<_> = pool.validated_pool().ready().map(|a| a.data.transfer().nonce).collect();
	assert_eq!(pending, vec![209, 210]);
}

#[test]
fn prune_tags_should_work() {
	let pool = pool();
	let hash209 = block_on(pool.submit_one(&BlockId::number(0), SOURCE, uxt(Alice, 209))).unwrap();
	block_on(pool.submit_one(&BlockId::number(0), SOURCE, uxt(Alice, 210))).unwrap();

	let pending: Vec<_> = pool.validated_pool().ready().map(|a| a.data.transfer().nonce).collect();
	assert_eq!(pending, vec![209, 210]);

	block_on(
		pool.prune_tags(
			&BlockId::number(1),
			vec![vec![209]],
			vec![hash209],
		)
	).expect("Prune tags");

	let pending: Vec<_> = pool.validated_pool().ready().map(|a| a.data.transfer().nonce).collect();
	assert_eq!(pending, vec![210]);
}

#[test]
fn should_ban_invalid_transactions() {
	let pool = pool();
	let uxt = uxt(Alice, 209);
	let hash = block_on(pool.submit_one(&BlockId::number(0), SOURCE, uxt.clone())).unwrap();
	pool.validated_pool().remove_invalid(&[hash]);
	block_on(pool.submit_one(&BlockId::number(0), SOURCE, uxt.clone())).unwrap_err();

	// when
	let pending: Vec<_> = pool.validated_pool().ready().map(|a| a.data.transfer().nonce).collect();
	assert_eq!(pending, Vec::<Index>::new());

	// then
	block_on(pool.submit_one(&BlockId::number(0), SOURCE, uxt.clone())).unwrap_err();
}

#[test]
fn should_correctly_prune_transactions_providing_more_than_one_tag() {
	let api = Arc::new(TestApi::with_alice_nonce(209));
	api.set_valid_modifier(Box::new(|v: &mut ValidTransaction| {
		v.provides.push(vec![155]);
	}));
	let pool = Pool::new(Default::default(), api.clone());
	let xt = uxt(Alice, 209);
	block_on(pool.submit_one(&BlockId::number(0), SOURCE, xt.clone())).expect("1. Imported");
	assert_eq!(pool.validated_pool().status().ready, 1);

	// remove the transaction that just got imported.
	api.increment_nonce(Alice.into());
	block_on(pool.prune_tags(&BlockId::number(1), vec![vec![209]], vec![])).expect("1. Pruned");
	assert_eq!(pool.validated_pool().status().ready, 0);
	// it's re-imported to future
	assert_eq!(pool.validated_pool().status().future, 1);

	// so now let's insert another transaction that also provides the 155
	api.increment_nonce(Alice.into());
	let xt = uxt(Alice, 211);
	block_on(pool.submit_one(&BlockId::number(2), SOURCE, xt.clone())).expect("2. Imported");
	assert_eq!(pool.validated_pool().status().ready, 1);
	assert_eq!(pool.validated_pool().status().future, 1);
	let pending: Vec<_> = pool.validated_pool().ready().map(|a| a.data.transfer().nonce).collect();
	assert_eq!(pending, vec![211]);

	// prune it and make sure the pool is empty
	api.increment_nonce(Alice.into());
	block_on(pool.prune_tags(&BlockId::number(3), vec![vec![155]], vec![])).expect("2. Pruned");
	assert_eq!(pool.validated_pool().status().ready, 0);
	assert_eq!(pool.validated_pool().status().future, 2);
}

fn block_event(id: u64) -> ChainEvent<Block> {
	ChainEvent::NewBlock {
		id: BlockId::number(id),
		is_new_best: true,
		retracted: vec![],
		header: header(id),
	}
}

fn block_event_with_retracted(id: u64, retracted: Vec<Hash>) -> ChainEvent<Block> {
	ChainEvent::NewBlock {
		id: BlockId::number(id),
		is_new_best: true,
		retracted: retracted,
		header: header(id),
	}
}


#[test]
fn should_prune_old_during_maintenance() {
	let xt = uxt(Alice, 209);

	let (pool, _guard, _notifier) = maintained_pool();

	block_on(pool.submit_one(&BlockId::number(0), SOURCE, xt.clone())).expect("1. Imported");
	assert_eq!(pool.status().ready, 1);

	pool.api.push_block(1, vec![xt.clone()]);

	block_on(pool.maintain(block_event(1)));
	assert_eq!(pool.status().ready, 0);
}

#[test]
fn should_revalidate_during_maintenance() {
	let xt1 = uxt(Alice, 209);
	let xt2 = uxt(Alice, 210);

	let (pool, _guard, mut notifier) = maintained_pool();
	block_on(pool.submit_one(&BlockId::number(0), SOURCE, xt1.clone())).expect("1. Imported");
	block_on(pool.submit_one(&BlockId::number(0), SOURCE, xt2.clone())).expect("2. Imported");
	assert_eq!(pool.status().ready, 2);
	assert_eq!(pool.api.validation_requests().len(), 2);

	pool.api.push_block(1, vec![xt1.clone()]);

	block_on(pool.maintain(block_event(1)));
	assert_eq!(pool.status().ready, 1);
	block_on(notifier.next());

	// test that pool revalidated transaction that left ready and not included in the block
	assert_eq!(pool.api.validation_requests().len(), 3);
}

#[test]
fn should_resubmit_from_retracted_during_maintenance() {
	let xt = uxt(Alice, 209);
	let retracted_hash = Hash::random();

	let (pool, _guard, _notifier) = maintained_pool();

	block_on(pool.submit_one(&BlockId::number(0), SOURCE, xt.clone())).expect("1. Imported");
	assert_eq!(pool.status().ready, 1);

	pool.api.push_block(1, vec![]);
	pool.api.push_fork_block(retracted_hash, vec![xt.clone()]);

	let event = block_event_with_retracted(1, vec![retracted_hash]);

	block_on(pool.maintain(event));
	assert_eq!(pool.status().ready, 1);
}

#[test]
fn should_not_retain_invalid_hashes_from_retracted() {
	let xt = uxt(Alice, 209);
	let retracted_hash = Hash::random();

	let (pool, _guard, mut notifier) = maintained_pool();

	block_on(pool.submit_one(&BlockId::number(0), SOURCE, xt.clone())).expect("1. Imported");
	assert_eq!(pool.status().ready, 1);

	pool.api.push_block(1, vec![]);
	pool.api.push_fork_block(retracted_hash, vec![xt.clone()]);
	pool.api.add_invalid(&xt);

	let event = block_event_with_retracted(1, vec![retracted_hash]);

	block_on(pool.maintain(event));
	block_on(notifier.next());

	assert_eq!(pool.status().ready, 0);
}

#[test]
fn should_revalidate_transaction_multiple_times() {
	let xt = uxt(Alice, 209);

	let (pool, _guard, mut notifier) = maintained_pool();

	block_on(pool.submit_one(&BlockId::number(0), SOURCE, xt.clone())).expect("1. Imported");
	assert_eq!(pool.status().ready, 1);

	pool.api.push_block(1, vec![xt.clone()]);

	block_on(pool.maintain(block_event(1)));

	block_on(pool.submit_one(&BlockId::number(0), SOURCE, xt.clone())).expect("1. Imported");
	assert_eq!(pool.status().ready, 1);

	pool.api.push_block(2, vec![]);
	pool.api.add_invalid(&xt);

	block_on(pool.maintain(block_event(2)));
	block_on(notifier.next());

	assert_eq!(pool.status().ready, 0);
}

#[test]
fn should_revalidate_across_many_blocks() {
	let xt1 = uxt(Alice, 209);
	let xt2 = uxt(Alice, 210);
	let xt3 = uxt(Alice, 211);

	let (pool, _guard, mut notifier) = maintained_pool();

	block_on(pool.submit_one(&BlockId::number(1), SOURCE, xt1.clone())).expect("1. Imported");
	block_on(pool.submit_one(&BlockId::number(1), SOURCE, xt2.clone())).expect("1. Imported");
	assert_eq!(pool.status().ready, 2);

	pool.api.push_block(1, vec![]);
	block_on(pool.maintain(block_event(1)));
	block_on(notifier.next());

	block_on(pool.submit_one(&BlockId::number(2), SOURCE, xt3.clone())).expect("1. Imported");
	assert_eq!(pool.status().ready, 3);

	pool.api.push_block(2, vec![xt1.clone()]);
	block_on(pool.maintain(block_event(2)));
	block_on(notifier.next());

	assert_eq!(pool.status().ready, 2);
	// xt1 and xt2 validated twice, then xt3 once, then xt2 and xt3 again
	assert_eq!(pool.api.validation_requests().len(), 7);
}


#[test]
fn should_push_watchers_during_maintaince() {
	fn alice_uxt(nonce: u64) -> Extrinsic {
		uxt(Alice, 209 + nonce)
	}

	// given
	let (pool, _guard, mut notifier) = maintained_pool();

	let tx0 = alice_uxt(0);
	let watcher0 = block_on(
		pool.submit_and_watch(&BlockId::Number(0), SOURCE, tx0.clone())
	).unwrap();
	let tx1 = alice_uxt(1);
	let watcher1 = block_on(
		pool.submit_and_watch(&BlockId::Number(0), SOURCE, tx1.clone())
	).unwrap();
	let tx2 = alice_uxt(2);
	let watcher2 = block_on(
		pool.submit_and_watch(&BlockId::Number(0), SOURCE, tx2.clone())
	).unwrap();
	let tx3 = alice_uxt(3);
	let watcher3 = block_on(
		pool.submit_and_watch(&BlockId::Number(0), SOURCE, tx3.clone())
	).unwrap();
	let tx4 = alice_uxt(4);
	let watcher4 = block_on(
		pool.submit_and_watch(&BlockId::Number(0), SOURCE, tx4.clone())
	).unwrap();
	assert_eq!(pool.status().ready, 5);

	// when
	pool.api.add_invalid(&tx3);
	pool.api.add_invalid(&tx4);

	// clear timer events if any
	block_on(pool.maintain(block_event(0)));
	block_on(notifier.next());

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
	let header_hash = pool.api.push_block(1, vec![tx0, tx1, tx2]).hash();
	block_on(pool.maintain(block_event(1)));

	let event = ChainEvent::Finalized { hash: header_hash.clone() };
	block_on(pool.maintain(event));

	// then
	// events for hash0 are: Ready, InBlock
	// events for hash1 are: Ready, InBlock
	// events for hash2 are: Ready, InBlock
	assert_eq!(
		futures::executor::block_on_stream(watcher0).collect::<Vec<_>>(),
		vec![TransactionStatus::Ready, TransactionStatus::InBlock(header_hash.clone()), TransactionStatus::Finalized(header_hash.clone())],
	);
	assert_eq!(
		futures::executor::block_on_stream(watcher1).collect::<Vec<_>>(),
		vec![TransactionStatus::Ready, TransactionStatus::InBlock(header_hash.clone()), TransactionStatus::Finalized(header_hash.clone())],
	);
	assert_eq!(
		futures::executor::block_on_stream(watcher2).collect::<Vec<_>>(),
		vec![TransactionStatus::Ready, TransactionStatus::InBlock(header_hash.clone()), TransactionStatus::Finalized(header_hash.clone())],
	);
}

#[test]
fn can_track_heap_size() {
	let (pool, _guard, _notifier) = maintained_pool();
	block_on(pool.submit_one(&BlockId::number(0), SOURCE, uxt(Alice, 209))).expect("1. Imported");
	block_on(pool.submit_one(&BlockId::number(0), SOURCE, uxt(Alice, 210))).expect("1. Imported");
	block_on(pool.submit_one(&BlockId::number(0), SOURCE, uxt(Alice, 211))).expect("1. Imported");
	block_on(pool.submit_one(&BlockId::number(0), SOURCE, uxt(Alice, 212))).expect("1. Imported");

	assert!(parity_util_mem::malloc_size(&pool) > 3000);
}

#[test]
fn finalization() {
	let xt = uxt(Alice, 209);
	let api = TestApi::with_alice_nonce(209);
	api.push_block(1, vec![]);
	let (pool, _background, _) = BasicPool::new_test(api.into());
	let watcher = block_on(
		pool.submit_and_watch(&BlockId::number(1), SOURCE, xt.clone())
	).expect("1. Imported");
	pool.api.push_block(2, vec![xt.clone()]);

	let header = pool.api.chain().read().header_by_number.get(&2).cloned().unwrap();
	let event = ChainEvent::NewBlock {
		id: BlockId::Hash(header.hash()),
		is_new_best: true,
		header: header.clone(),
		retracted: vec![]
	};
	block_on(pool.maintain(event));

	let event = ChainEvent::Finalized { hash: header.hash() };
	block_on(pool.maintain(event));

	let mut stream = futures::executor::block_on_stream(watcher);
	assert_eq!(stream.next(), Some(TransactionStatus::Ready));
	assert_eq!(stream.next(), Some(TransactionStatus::InBlock(header.hash())));
	assert_eq!(stream.next(), Some(TransactionStatus::Finalized(header.hash())));
	assert_eq!(stream.next(), None);
}

#[test]
fn fork_aware_finalization() {
	let api = TestApi::empty();
	// starting block A1 (last finalized.)
	api.push_block(1, vec![]);

	let (pool, _background, _) = BasicPool::new_test(api.into());
	let mut canon_watchers = vec![];

	let from_alice = uxt(Alice, 1);
	let from_dave = uxt(Dave, 2);
	let from_bob = uxt(Bob, 1);
	let from_charlie = uxt(Charlie, 1);
	pool.api.increment_nonce(Alice.into());
	pool.api.increment_nonce(Dave.into());
	pool.api.increment_nonce(Charlie.into());
	pool.api.increment_nonce(Bob.into());

	let from_dave_watcher;
	let from_bob_watcher;
	let b1;
	let d1;
	let c2;
	let d2;


	// block B1
	{
		let watcher = block_on(
			pool.submit_and_watch(&BlockId::number(1), SOURCE, from_alice.clone())
		).expect("1. Imported");
		let header = pool.api.push_block(2, vec![from_alice.clone()]);
		canon_watchers.push((watcher, header.hash()));
		assert_eq!(pool.status().ready, 1);

		let event = ChainEvent::NewBlock {
			id: BlockId::Number(2),
			is_new_best: true,
			header: header.clone(),
			retracted: vec![],
		};
		b1 = header.hash();
		block_on(pool.maintain(event));
		assert_eq!(pool.status().ready, 0);
		let event = ChainEvent::Finalized { hash: b1 };
		block_on(pool.maintain(event));
	}

	// block C2
	{
		let header = pool.api.push_fork_block_with_parent(b1, vec![from_dave.clone()]);
		from_dave_watcher = block_on(
			pool.submit_and_watch(&BlockId::number(1), SOURCE, from_dave.clone())
		).expect("1. Imported");
		assert_eq!(pool.status().ready, 1);
		let event = ChainEvent::NewBlock {
			id: BlockId::Hash(header.hash()),
			is_new_best: true,
			header: header.clone(),
			retracted: vec![]
		};
		c2 = header.hash();
		block_on(pool.maintain(event));
		assert_eq!(pool.status().ready, 0);
	}

	// block D2
	{
		from_bob_watcher = block_on(
			pool.submit_and_watch(&BlockId::number(1), SOURCE, from_bob.clone())
		).expect("1. Imported");
		assert_eq!(pool.status().ready, 1);
		let header = pool.api.push_fork_block_with_parent(c2, vec![from_bob.clone()]);

		let event = ChainEvent::NewBlock {
			id: BlockId::Hash(header.hash()),
			is_new_best: true,
			header: header.clone(),
			retracted: vec![]
		};
		d2 = header.hash();
		block_on(pool.maintain(event));
		assert_eq!(pool.status().ready, 0);
	}

	// block C1
	{
		let watcher = block_on(
			pool.submit_and_watch(&BlockId::number(1), SOURCE, from_charlie.clone())
		).expect("1.Imported");
		assert_eq!(pool.status().ready, 1);
		let header = pool.api.push_block(3, vec![from_charlie.clone()]);

		canon_watchers.push((watcher, header.hash()));
		let event = ChainEvent::NewBlock {
			id: BlockId::Number(3),
			is_new_best: true,
			header: header.clone(),
			retracted: vec![c2, d2],
		};
		block_on(pool.maintain(event));
		assert_eq!(pool.status().ready, 2);
		let event = ChainEvent::Finalized { hash: header.hash() };
		block_on(pool.maintain(event));
	}

	// block D1
	{
		let xt = uxt(Eve, 0);
		let w = block_on(
			pool.submit_and_watch(&BlockId::number(1), SOURCE, xt.clone())
		).expect("1. Imported");
		assert_eq!(pool.status().ready, 3);
		let header = pool.api.push_block(4, vec![xt.clone()]);
		canon_watchers.push((w, header.hash()));

		let event = ChainEvent::NewBlock {
			id: BlockId::Hash(header.hash()),
			is_new_best: true,
			header: header.clone(),
			retracted: vec![]
		};
		d1 = header.hash();
		block_on(pool.maintain(event));
		assert_eq!(pool.status().ready, 2);
		let event = ChainEvent::Finalized { hash: d1 };
		block_on(pool.maintain(event));
	}

	let e1;

	// block e1
	{
		let header = pool.api.push_block(5, vec![from_dave, from_bob]);
		e1 = header.hash();
		let event = ChainEvent::NewBlock {
			id: BlockId::Hash(header.hash()),
			is_new_best: true,
			header: header.clone(),
			retracted: vec![]
		};
		block_on(pool.maintain(event));
		assert_eq!(pool.status().ready, 0);
		block_on(pool.maintain(ChainEvent::Finalized { hash: e1 }));
	}


	for (canon_watcher, h) in canon_watchers {
		let mut stream = futures::executor::block_on_stream(canon_watcher);
		assert_eq!(stream.next(), Some(TransactionStatus::Ready));
		assert_eq!(stream.next(), Some(TransactionStatus::InBlock(h.clone())));
		assert_eq!(stream.next(), Some(TransactionStatus::Finalized(h)));
		assert_eq!(stream.next(), None);
	}


	{
		let mut stream= futures::executor::block_on_stream(from_dave_watcher);
		assert_eq!(stream.next(), Some(TransactionStatus::Ready));
		assert_eq!(stream.next(), Some(TransactionStatus::InBlock(c2.clone())));
		assert_eq!(stream.next(), Some(TransactionStatus::Retracted(c2)));
		assert_eq!(stream.next(), Some(TransactionStatus::Ready));
		assert_eq!(stream.next(), Some(TransactionStatus::InBlock(e1)));
		assert_eq!(stream.next(), Some(TransactionStatus::Finalized(e1.clone())));
		assert_eq!(stream.next(), None);
	}

	{
		let mut stream= futures::executor::block_on_stream(from_bob_watcher);
		assert_eq!(stream.next(), Some(TransactionStatus::Ready));
		assert_eq!(stream.next(), Some(TransactionStatus::InBlock(d2.clone())));
		assert_eq!(stream.next(), Some(TransactionStatus::Retracted(d2)));
		assert_eq!(stream.next(), Some(TransactionStatus::Ready));
		assert_eq!(stream.next(), Some(TransactionStatus::InBlock(e1)));
		assert_eq!(stream.next(), Some(TransactionStatus::Finalized(e1.clone())));
		assert_eq!(stream.next(), None);
	}
}

#[test]
fn ready_set_should_not_resolve_before_block_update() {
	let (pool, _guard, _notifier) = maintained_pool();
	let xt1 = uxt(Alice, 209);
	block_on(pool.submit_one(&BlockId::number(1), SOURCE, xt1.clone())).expect("1. Imported");

	assert!(pool.ready_at(1).now_or_never().is_none());
}

#[test]
fn ready_set_should_resolve_after_block_update() {
	let (pool, _guard, _notifier) = maintained_pool();
	pool.api.push_block(1, vec![]);

	let xt1 = uxt(Alice, 209);

	block_on(pool.submit_one(&BlockId::number(1), SOURCE, xt1.clone())).expect("1. Imported");
	block_on(pool.maintain(block_event(1)));

	assert!(pool.ready_at(1).now_or_never().is_some());
}

#[test]
fn ready_set_should_eventually_resolve_when_block_update_arrives() {
	let (pool, _guard, _notifier) = maintained_pool();
	pool.api.push_block(1, vec![]);

	let xt1 = uxt(Alice, 209);

	block_on(pool.submit_one(&BlockId::number(1), SOURCE, xt1.clone())).expect("1. Imported");

	let noop_waker = futures::task::noop_waker();
	let mut context = futures::task::Context::from_waker(&noop_waker);

	let mut ready_set_future = pool.ready_at(1);
	if let Poll::Ready(_) = ready_set_future.poll_unpin(&mut context) {
		panic!("Ready set should not be ready before block update!");
	}

	block_on(pool.maintain(block_event(1)));

	match ready_set_future.poll_unpin(&mut context)  {
		Poll::Pending => {
			panic!("Ready set should become ready after block update!");
		},
		Poll::Ready(iterator) => {
			let data = iterator.collect::<Vec<_>>();
			assert_eq!(data.len(), 1);
		}
	}
}

#[test]
fn should_not_accept_old_signatures() {
	use std::convert::TryFrom;

	let client = Arc::new(substrate_test_runtime_client::new());
	let pool = Arc::new(
		BasicPool::new_test(Arc::new(FullChainApi::new(client))).0
	);

	let transfer = Transfer {
		from: Alice.into(),
		to: Bob.into(),
		nonce: 0,
		amount: 1,
	};
	let _bytes: sp_core::sr25519::Signature = transfer.using_encoded(|e| Alice.sign(e)).into();

	// generated with schnorrkel 0.1.1 from `_bytes`
	let old_singature = sp_core::sr25519::Signature::try_from(&hex::decode(
		"c427eb672e8c441c86d31f1a81b22b43102058e9ce237cabe9897ea5099ffd426cd1c6a1f4f2869c3df57901d36bedcb295657adb3a4355add86ed234eb83108"
	).expect("hex invalid")[..]).expect("signature construction failed");

	let xt = Extrinsic::Transfer { transfer, signature: old_singature, exhaust_resources_when_not_first: false };

	assert_matches::assert_matches!(
		block_on(pool.submit_one(&BlockId::number(0), SOURCE, xt.clone())),
		Err(error::Error::Pool(
			sp_transaction_pool::error::Error::InvalidTransaction(InvalidTransaction::BadProof)
		)),
		"Should be invalid transaction with bad proof",
	);
}
