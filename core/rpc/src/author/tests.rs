// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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
use assert_matches::assert_matches;
use parity_codec::Encode;
use transaction_pool::{
	txpool::Pool,
	ChainApi,
};
use primitives::{H256, blake2_256, hexdisplay::HexDisplay};
use test_client::{self, AccountKeyring, runtime::{Extrinsic, Transfer}};
use tokio::runtime;

fn uxt(sender: AccountKeyring, nonce: u64) -> Extrinsic {
	let tx = Transfer {
		amount: Default::default(),
		nonce,
		from: sender.into(),
		to: Default::default(),
	};
	tx.into_signed_tx()
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
	let xt = uxt(AccountKeyring::Alice, 1).encode();
	let h: H256 = blake2_256(&xt).into();

	assert_matches!(
		AuthorApi::submit_extrinsic(&p, xt.clone().into()),
		Ok(h2) if h == h2
	);
	assert!(
		AuthorApi::submit_extrinsic(&p, xt.into()).is_err()
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
	let xt = uxt(AccountKeyring::Alice, 0).encode();
	let h: H256 = blake2_256(&xt).into();

	assert_matches!(
		AuthorApi::submit_extrinsic(&p, xt.clone().into()),
		Ok(h2) if h == h2
	);
	assert!(
		AuthorApi::submit_extrinsic(&p, xt.into()).is_err()
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
	let (subscriber, id_rx, data) = ::jsonrpc_pubsub::typed::Subscriber::new_test("test");

	// when
	p.watch_extrinsic(Default::default(), subscriber, uxt(AccountKeyring::Alice, 0).encode().into());

	// then
	assert_eq!(runtime.block_on(id_rx), Ok(Ok(1.into())));
	// check notifications
	let replacement = {
		let tx = Transfer {
			amount: 5,
			nonce: 0,
			from: AccountKeyring::Alice.into(),
			to: Default::default(),
		};
		tx.into_signed_tx()
	};
	AuthorApi::submit_extrinsic(&p, replacement.encode().into()).unwrap();
	let (res, data) = runtime.block_on(data.into_future()).unwrap();
	assert_eq!(
		res,
		Some(r#"{"jsonrpc":"2.0","method":"test","params":{"result":"ready","subscription":1}}"#.into())
	);
	let h = blake2_256(&replacement.encode());
	assert_eq!(
		runtime.block_on(data.into_future()).unwrap().0,
		Some(format!(r#"{{"jsonrpc":"2.0","method":"test","params":{{"result":{{"usurped":"0x{}"}},"subscription":1}}}}"#, HexDisplay::from(&h)))
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
	let ex = uxt(AccountKeyring::Alice, 0);
	AuthorApi::submit_extrinsic(&p, ex.encode().into()).unwrap();
 	assert_matches!(
		p.pending_extrinsics(),
		Ok(ref expected) if *expected == vec![Bytes(ex.encode())]
	);
}
