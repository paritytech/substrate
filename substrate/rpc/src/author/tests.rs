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

use std::{fmt, sync::Arc, result::Result};
use codec::Encode;
use extrinsic_pool::{api, txpool, watcher::{self, Watcher}};
use parking_lot::Mutex;
use test_client;
use tokio::runtime;

type Extrinsic = u64;
type Hash = u64;

#[derive(Default)]
struct DummyTxPool {
	submitted: Mutex<Vec<Extrinsic>>,
	sender: Mutex<Option<watcher::Sender<u64>>>,
}

#[derive(Debug)]
struct Error;
impl api::Error for Error {}
impl ::std::error::Error for Error {
	fn description(&self) -> &str { "Error" }
}
impl fmt::Display for Error {
	fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
		fmt::Debug::fmt(self, fmt)
	}
}

impl<BlockHash> api::ExtrinsicPool<Extrinsic, BlockHash, u64> for DummyTxPool {
	type Error = Error;
	type InPool = Vec<u8>;

	/// Submit extrinsic for inclusion in block.
	fn submit(&self, _block: BlockHash, xt: Vec<Extrinsic>) -> Result<Vec<Hash>, Self::Error> {
		let mut submitted = self.submitted.lock();
		if submitted.len() < 1 {
			let hashes = xt.iter().map(|_xt| 1).collect();
			submitted.extend(xt);
			Ok(hashes)
		} else {
			Err(Error)
		}
	}

	fn submit_and_watch(&self, _block: BlockHash, xt: Extrinsic) -> Result<Watcher<u64>, Self::Error> {
		let mut submitted = self.submitted.lock();
		if submitted.len() < 1 {
			submitted.push(xt);
			let mut sender = watcher::Sender::default();
			let watcher = sender.new_watcher();
			*self.sender.lock() = Some(sender);
			Ok(watcher)
		} else {
			Err(Error)
		}
	}

	fn light_status(&self) -> txpool::LightStatus {
		unreachable!()
	}

	fn import_notification_stream(&self) -> api::EventStream {
		unreachable!()
	}

	fn all(&self) -> Self::InPool {
		vec![1, 2, 3, 4, 5]
	}
}

#[test]
fn submit_transaction_should_not_cause_error() {
	let runtime = runtime::Runtime::new().unwrap();
	let p = Author {
		client: Arc::new(test_client::new()),
		pool: Arc::new(DummyTxPool::default()),
		subscriptions: Subscriptions::new(runtime.executor()),
	};

	assert_matches!(
		AuthorApi::submit_extrinsic(&p, u64::encode(&5).into()),
		Ok(1)
	);
	assert!(
		AuthorApi::submit_extrinsic(&p, u64::encode(&5).into()).is_err()
	);
}

#[test]
fn submit_rich_transaction_should_not_cause_error() {
	let runtime = runtime::Runtime::new().unwrap();
	let p = Author {
		client: Arc::new(test_client::new()),
		pool: Arc::new(DummyTxPool::default()),
		subscriptions: Subscriptions::new(runtime.executor()),
	};

	assert_matches!(
		AuthorApi::submit_rich_extrinsic(&p, 5),
		Ok(1)
	);
	assert!(
		AuthorApi::submit_rich_extrinsic(&p, 5).is_err()
	);
}

#[test]
fn should_watch_extrinsic() {
	//given
	let mut runtime = runtime::Runtime::new().unwrap();
	let pool = Arc::new(DummyTxPool::default());
	let p = Author {
		client: Arc::new(test_client::new()),
		pool: pool.clone(),
		subscriptions: Subscriptions::new(runtime.executor()),
	};
	let (subscriber, id_rx, data) = ::jsonrpc_macros::pubsub::Subscriber::new_test("test");

	// when
	p.watch_extrinsic(Default::default(), subscriber, u64::encode(&5).into());

	// then
	assert_eq!(runtime.block_on(id_rx), Ok(Ok(0.into())));

	// check notifications
	pool.sender.lock().as_mut().unwrap().usurped(5);

	assert_eq!(
		runtime.block_on(data.into_future()).unwrap().0,
		Some(r#"{"jsonrpc":"2.0","method":"test","params":{"result":{"usurped":5},"subscription":0}}"#.into())
	);
}

#[test]
fn should_return_pending_extrinsics() {
	let runtime = runtime::Runtime::new().unwrap();
	let p = Author {
		client: Arc::new(test_client::new()),
		pool: Arc::new(DummyTxPool::default()),
		subscriptions: Subscriptions::new(runtime.executor()),
	};

	assert_matches!(
		p.pending_extrinsics(),
		Ok(ref expected) if expected == &[1u8, 2, 3, 4, 5]
	);
}
