// Copyright 2017-2018 Parity Technologies (UK) Ltd.
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
use test_client::keyring::Keyring;
use test_client::runtime::{Extrinsic, Transfer};
use test_client;
use tokio::runtime;

fn uxt(sender: Keyring, nonce: u64) -> Extrinsic {
	let tx = Transfer {
		amount: Default::default(),
		nonce,
		from: sender.to_raw_public().into(),
		to: Default::default(),
	};
	let signature = Keyring::from_raw_public(tx.from.to_fixed_bytes()).unwrap().sign(&tx.encode()).into();
	Extrinsic { transfer: tx, signature }
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
	let h: H256 = hex!("e10ad66bce51ef3e2a1167934ce3740d2d8c703810f9b314e89f2e783f75e826").into();

	assert_matches!(
		AuthorApi::submit_extrinsic(&p, uxt(Keyring::Alice, 1).encode().into()),
		Ok(h2) if h == h2
	);
	assert!(
		AuthorApi::submit_extrinsic(&p, uxt(Keyring::Alice, 1).encode().into()).is_err()
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
	let h: H256 = hex!("fccc48291473c53746cd267cf848449edd7711ee6511fba96919d5f9f4859e4f").into();

	assert_matches!(
		AuthorApi::submit_extrinsic(&p, uxt(Keyring::Alice, 0).encode().into()),
		Ok(h2) if h == h2
	);
	assert!(
		AuthorApi::submit_extrinsic(&p, uxt(Keyring::Alice, 0).encode().into()).is_err()
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
	p.watch_extrinsic(Default::default(), subscriber, uxt(Keyring::Alice, 0).encode().into());

	// then
	assert_eq!(runtime.block_on(id_rx), Ok(Ok(1.into())));
	// check notifications
	let replacement = {
		let tx = Transfer {
			amount: 5,
			nonce: 0,
			from: Keyring::Alice.to_raw_public().into(),
			to: Default::default(),
		};
		let signature = Keyring::from_raw_public(tx.from.to_fixed_bytes()).unwrap().sign(&tx.encode()).into();
		Extrinsic { transfer: tx, signature }
	};
	AuthorApi::submit_extrinsic(&p, replacement.encode().into()).unwrap();
	let (res, data) = runtime.block_on(data.into_future()).unwrap();
	assert_eq!(
		res,
		Some(r#"{"jsonrpc":"2.0","method":"test","params":{"result":"ready","subscription":1}}"#.into())
	);
	assert_eq!(
		runtime.block_on(data.into_future()).unwrap().0,
		Some(r#"{"jsonrpc":"2.0","method":"test","params":{"result":{"usurped":"0xed454dcee51431679c2559403187a56567fded1fc50b6ae3aada87c1d412df5c"},"subscription":1}}"#.into())
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
	let ex = uxt(Keyring::Alice, 0);
	AuthorApi::submit_extrinsic(&p, ex.encode().into()).unwrap();
 	assert_matches!(
		p.pending_extrinsics(),
		Ok(ref expected) if *expected == vec![Bytes(ex.encode())]
	);
}
