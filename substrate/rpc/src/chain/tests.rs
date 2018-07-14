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
use jsonrpc_macros::pubsub;
use client::BlockOrigin;
use test_client::{self, TestClient};
use test_client::runtime::Header;

#[ignore]
#[test]
fn should_return_header() {
	let core = ::tokio::runtime::Runtime::new().unwrap();
	let remote = core.executor();

	let client = Chain {
		client: Arc::new(test_client::new()),
		subscriptions: Subscriptions::new(remote),
	};
	assert_matches!(
		client.header(client.client.genesis_hash()),
		Ok(Some(ref x)) if x == &Header {
			parent_hash: 0.into(),
			number: 0,
			state_root: "17dccc74bd9200b7ce5a2f6a1bf379f1cdcf91bca3d19c3d17e1478b8d404703".into(),
			extrinsics_root: "56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421".into(),
			digest: Default::default(),
		}
	);

	assert_matches!(
		client.header(5.into()),
		Ok(None)
	);
}

#[ignore]
#[test]
fn should_notify_about_latest_block() {
	let mut core = ::tokio::runtime::Runtime::new().unwrap();
	let remote = core.executor();
	let (subscriber, id, transport) = pubsub::Subscriber::new_test("test");

	{
		let api = Chain {
			client: Arc::new(test_client::new()),
			subscriptions: Subscriptions::new(remote),
		};

		api.subscribe_new_head(Default::default(), subscriber);

		// assert id assigned
		assert_eq!(core.block_on(id), Ok(Ok(SubscriptionId::Number(0))));

		let builder = api.client.new_block().unwrap();
		api.client.justify_and_import(BlockOrigin::Own, builder.bake().unwrap()).unwrap();
	}

	// assert notification send to transport
	let (notification, next) = core.block_on(transport.into_future()).unwrap();
	assert_eq!(notification, Some(
		r#"{"jsonrpc":"2.0","method":"test","params":{"result":{"digest":{"logs":[]},"extrinsicsRoot":"0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421","number":1,"parentHash":"0x50fb1e7f32e8ad17f553846f4338861e17eb95132e7c3b433e0429ffab2f8f13","stateRoot":"0x17dccc74bd9200b7ce5a2f6a1bf379f1cdcf91bca3d19c3d17e1478b8d404703"},"subscription":0}}"#.to_owned()
	));
	// no more notifications on this channel
	assert_eq!(core.block_on(next.into_future()).unwrap().0, None);
}
