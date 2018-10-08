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

use std::sync::Arc;
use codec::Encode;
use transaction_pool::{
	txpool::Pool,
	ChainApi,
};
use primitives::H256;
use test_client::runtime::{Extrinsic, Transfer};
use test_client;
use tokio::runtime;

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
	let client = Arc::new(test_client::new());
	let p = Author {
		client: client.clone(),
		pool: Arc::new(Pool::new(Default::default(), ChainApi::new(client))),
		subscriptions: Subscriptions::new(runtime.executor()),
	};
	let h: H256 = 1.into();

	assert_matches!(
		AuthorApi::submit_extrinsic(&p, uxt(5, 1).encode().into()),
		Ok(h2) if h == h2
	);
	assert!(
		AuthorApi::submit_extrinsic(&p, uxt(5, 1).encode().into()).is_err()
	);
}

#[test]
fn submit_rich_transaction_should_not_cause_error() {
	let runtime = runtime::Runtime::new().unwrap();
	let client = Arc::new(test_client::new());
	let p = Author {
		client: client.clone(),
		pool: Arc::new(Pool::new(Default::default(), ChainApi::new(client.clone()))),
		subscriptions: Subscriptions::new(runtime.executor()),
	};
	let h: H256 = 0.into();

	assert_matches!(
		AuthorApi::submit_rich_extrinsic(&p, uxt(5, 0)),
		Ok(h2) if h == h2
	);
	assert!(
		AuthorApi::submit_rich_extrinsic(&p, uxt(5, 0)).is_err()
	);
}

#[test]
fn should_watch_extrinsic() {
	//given
	let mut runtime = runtime::Runtime::new().unwrap();
	let client = Arc::new(test_client::new());
	let pool = Arc::new(Pool::new(Default::default(), ChainApi::new(client.clone())));
	let p = Author {
		client,
		pool: pool.clone(),
		subscriptions: Subscriptions::new(runtime.executor()),
	};
	let (subscriber, id_rx, data) = ::jsonrpc_macros::pubsub::Subscriber::new_test("test");

	// when
	p.watch_extrinsic(Default::default(), subscriber, uxt(5, 5).encode().into());

	// then
	assert_eq!(runtime.block_on(id_rx), Ok(Ok(1.into())));
	// check notifications
	AuthorApi::submit_rich_extrinsic(&p, uxt(5, 1)).unwrap();
	assert_eq!(
		runtime.block_on(data.into_future()).unwrap().0,
		Some(r#"{"jsonrpc":"2.0","method":"test","params":{"result":{"usurped":1},"subscription":1}}"#.into())
	);
}

#[test]
fn should_return_pending_extrinsics() {
	let runtime = runtime::Runtime::new().unwrap();
	let client = Arc::new(test_client::new());
	let pool = Arc::new(Pool::new(Default::default(), ChainApi::new(client.clone())));
	let p = Author {
		client,
		pool: pool.clone(),
		subscriptions: Subscriptions::new(runtime.executor()),
	};
	let ex = uxt(5, 1);
	AuthorApi::submit_rich_extrinsic(&p, ex.clone()).unwrap();
 	assert_matches!(
		p.pending_extrinsics(),
		Ok(ref expected) if expected == &vec![ex]
	);
}
