// Copyright 2017 Parity Technologies (UK) Ltd.
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

use std::{sync::Arc, result::Result};
use codec::Encode;
use extrinsic_pool::{VerifiedTransaction, scoring, Transaction, ChainApi, Error as PoolError,
	Readiness, ExtrinsicFor, VerifiedFor};
use test_client::runtime::{Block, Extrinsic, Transfer};
use test_client;
use tokio::runtime;
use runtime_primitives::generic::BlockId;

#[derive(Clone, Debug)]
pub struct Verified
{
	sender: u64, 
	hash: u64,
}

impl VerifiedTransaction for Verified {
	type Hash = u64;
	type Sender = u64;

	fn hash(&self) -> &Self::Hash { &self.hash }
	fn sender(&self) -> &Self::Sender { &self.sender }
	fn mem_usage(&self) -> usize { 256 }
}

struct TestApi;

impl ChainApi for TestApi {
	type Block = Block;
	type Hash = u64;
	type Sender = u64;
	type Error = PoolError;
	type VEx = Verified;
	type Score = u64;
	type Event = ();
	type Ready = ();

	fn verify_transaction(&self, _at: &BlockId<Block>, uxt: &ExtrinsicFor<Self>) -> Result<Self::VEx, Self::Error> {
		Ok(Verified {
			sender: uxt.transfer.from[31] as u64,
			hash:  uxt.transfer.nonce,
		}) 
	}

	fn is_ready(&self, _at: &BlockId<Block>, _c: &mut Self::Ready, _xt: &VerifiedFor<Self>) -> Readiness {
		Readiness::Ready
	}
	
	fn ready(&self) -> Self::Ready { }

	fn compare(old: &VerifiedFor<Self>, other: &VerifiedFor<Self>) -> ::std::cmp::Ordering {
		old.verified.hash().cmp(&other.verified.hash())
	}

	fn choose(_old: &VerifiedFor<Self>, _new: &VerifiedFor<Self>) -> scoring::Choice {
		scoring::Choice::ReplaceOld
	}

	fn update_scores(xts: &[Transaction<VerifiedFor<Self>>], scores: &mut [Self::Score], _change: scoring::Change<()>) {
		for i in 0..xts.len() {
			scores[i] = xts[i].verified.sender
		}
	}

	fn should_replace(_old: &VerifiedFor<Self>, _new: &VerifiedFor<Self>) -> scoring::Choice {
		scoring::Choice::ReplaceOld
	}
}

type DummyTxPool = Pool<TestApi>;

fn uxt(sender: u64, hash: u64) -> Extrinsic {
	Extrinsic {
		signature: Default::default(),
		transfer: Transfer {
			amount: Default::default(),
			nonce: hash,
			from: From::from(sender),
			to: Default::default(),
		}
	}
}

#[test]
fn submit_transaction_should_not_cause_error() {
	let runtime = runtime::Runtime::new().unwrap();
	let p = Author {
		client: Arc::new(test_client::new()),
		pool: Arc::new(DummyTxPool::new(Default::default(), TestApi)),
		subscriptions: Subscriptions::new(runtime.executor()),
	};

	assert_matches!(
		AuthorApi::submit_extrinsic(&p, uxt(5, 1).encode().into()),
		Ok(1)
	);
	assert!(
		AuthorApi::submit_extrinsic(&p, uxt(5, 1).encode().into()).is_err()
	);
}

#[test]
fn submit_rich_transaction_should_not_cause_error() {
	let runtime = runtime::Runtime::new().unwrap();
	let p = Author {
		client: Arc::new(test_client::new()),
		pool: Arc::new(DummyTxPool::new(Default::default(), TestApi)),
		subscriptions: Subscriptions::new(runtime.executor()),
	};

	assert_matches!(
		AuthorApi::submit_rich_extrinsic(&p, uxt(5, 0)),
		Ok(0)
	);
	assert!(
		AuthorApi::submit_rich_extrinsic(&p, uxt(5, 0)).is_err()
	);
}

#[test]
fn should_watch_extrinsic() {
	//given
	let mut runtime = runtime::Runtime::new().unwrap();
	let pool = Arc::new(DummyTxPool::new(Default::default(), TestApi));
	let p = Author {
		client: Arc::new(test_client::new()),
		pool: pool.clone(),
		subscriptions: Subscriptions::new(runtime.executor()),
	};
	let (subscriber, id_rx, data) = ::jsonrpc_macros::pubsub::Subscriber::new_test("test");

	// when
	p.watch_extrinsic(Default::default(), subscriber, uxt(5, 5).encode().into());

	// then
	assert_eq!(runtime.block_on(id_rx), Ok(Ok(0.into())));
	// check notifications
	AuthorApi::submit_rich_extrinsic(&p, uxt(5, 1)).unwrap();
	assert_eq!(
		runtime.block_on(data.into_future()).unwrap().0,
		Some(r#"{"jsonrpc":"2.0","method":"test","params":{"result":{"usurped":1},"subscription":0}}"#.into())
	);
}

#[test]
fn should_return_pending_extrinsics() {
	let runtime = runtime::Runtime::new().unwrap();
	let pool = Arc::new(DummyTxPool::new(Default::default(), TestApi));
	let p = Author {
		client: Arc::new(test_client::new()),
		pool: pool.clone(),
		subscriptions: Subscriptions::new(runtime.executor()),
	};
	let ex = uxt(5, 1);
	AuthorApi::submit_rich_extrinsic(&p, ex.clone()).unwrap();
 	assert_matches!(
		p.pending_extrinsics(),
		Ok(ref expected) if expected.get(&5) == Some(&vec![ex])
	);
}
