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

#[test]
fn should_return_header() {
	let core = ::tokio_core::reactor::Core::new().unwrap();
	let remote = core.remote();

	let client = Chain {
		client: Arc::new(test_client::new()),
		subscriptions: Subscriptions::new(remote),
	};
	assert_matches!(
		client.header(client.client.genesis_hash()),
		Ok(Some(ref x)) if x == &Header {
			parent_hash: 0.into(),
			number: 0,
			state_root: "0d7ce1cafdb5ff10d3445ec13cd1412bb1232179cb16e5cceb878aba8c28fa50".into(),
			extrinsics_root: "56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421".into(),
			digest: Default::default(),
		}
	);

	assert_matches!(
		client.header(5.into()),
		Ok(None)
	);
}

#[test]
fn should_notify_about_latest_block() {
	let mut core = ::tokio_core::reactor::Core::new().unwrap();
	let remote = core.remote();
	let (subscriber, id, transport) = pubsub::Subscriber::new_test("test");

	{
		let api = Chain {
			client: Arc::new(test_client::new()),
			subscriptions: Subscriptions::new(remote),
		};

		api.subscribe_new_head(Default::default(), subscriber);

		// assert id assigned
		assert_eq!(core.run(id), Ok(Ok(SubscriptionId::Number(0))));

		let builder = api.client.new_block().unwrap();
		api.client.justify_and_import(BlockOrigin::Own, builder.bake().unwrap()).unwrap();
	}

	// assert notification send to transport
	let (notification, next) = core.run(transport.into_future()).unwrap();
	assert_eq!(notification, Some(
		r#"{"jsonrpc":"2.0","method":"test","params":{"result":{"digest":{"logs":[]},"extrinsicsRoot":"0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421","number":1,"parentHash":"0x27a851b5c445924dc632cdad76c6eb292e75f4992972d36384e429b41c057fdb","stateRoot":"0x643016ad98f8d9f15ef06c5bfaf98a934873684d60729dc3ba738ebe0f6bbb19"},"subscription":0}}"#.to_owned()
	));
	// no more notifications on this channel
	assert_eq!(core.run(next.into_future()).unwrap().0, None);
}
