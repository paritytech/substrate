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
use jsonrpc_macros::pubsub;
use test_client::{self, TestClient};
use test_client::runtime::{Block, Header};
use consensus::BlockOrigin;

#[test]
fn should_return_header() {
	let core = ::tokio::runtime::Runtime::new().unwrap();
	let remote = core.executor();

	let client = Chain {
		client: Arc::new(test_client::new()),
		subscriptions: Subscriptions::new(remote),
	};

	assert_matches!(
		client.header(Some(client.client.genesis_hash()).into()),
		Ok(Some(ref x)) if x == &Header {
			parent_hash: 0.into(),
			number: 0,
			state_root: x.state_root.clone(),
			extrinsics_root: "03170a2e7597b7b7e3d84c05391d139a62b157e78786d8c082f29dcf4c111314".parse().unwrap(),
			digest: Default::default(),
		}
	);

	assert_matches!(
		client.header(None.into()),
		Ok(Some(ref x)) if x == &Header {
			parent_hash: 0.into(),
			number: 0,
			state_root: x.state_root.clone(),
			extrinsics_root: "03170a2e7597b7b7e3d84c05391d139a62b157e78786d8c082f29dcf4c111314".parse().unwrap(),
			digest: Default::default(),
		}
	);

	assert_matches!(
		client.header(Some(5.into()).into()),
		Ok(None)
	);
}

#[test]
fn should_return_a_block() {
	let core = ::tokio::runtime::Runtime::new().unwrap();
	let remote = core.executor();

	let api = Chain {
		client: Arc::new(test_client::new()),
		subscriptions: Subscriptions::new(remote),
	};

	let block = api.client.new_block().unwrap().bake().unwrap();
	let block_hash = block.hash();
	api.client.import(BlockOrigin::Own, block).unwrap();

	// Genesis block is not justified
	assert_matches!(
		api.block(Some(api.client.genesis_hash()).into()),
		Ok(Some(SignedBlock { justification: None, .. }))
	);

	assert_matches!(
		api.block(Some(block_hash).into()),
		Ok(Some(ref x)) if x.block == Block {
			header: Header {
				parent_hash: api.client.genesis_hash(),
				number: 1,
				state_root: x.block.header.state_root.clone(),
				extrinsics_root: "03170a2e7597b7b7e3d84c05391d139a62b157e78786d8c082f29dcf4c111314".parse().unwrap(),
				digest: Default::default(),
			},
			extrinsics: vec![],
		}
	);

	assert_matches!(
		api.block(None.into()),
		Ok(Some(ref x)) if x.block == Block {
			header: Header {
				parent_hash: api.client.genesis_hash(),
				number: 1,
				state_root: x.block.header.state_root.clone(),
				extrinsics_root: "03170a2e7597b7b7e3d84c05391d139a62b157e78786d8c082f29dcf4c111314".parse().unwrap(),
				digest: Default::default(),
			},
			extrinsics: vec![],
		}
	);

	assert_matches!(
		api.block(Some(5.into()).into()),
		Ok(None)
	);
}

#[test]
fn should_return_block_hash() {
	let core = ::tokio::runtime::Runtime::new().unwrap();
	let remote = core.executor();

	let client = Chain {
		client: Arc::new(test_client::new()),
		subscriptions: Subscriptions::new(remote),
	};

	assert_matches!(
		client.block_hash(None.into()),
		Ok(Some(ref x)) if x == &client.client.genesis_hash()
	);


	assert_matches!(
		client.block_hash(Some(0u64).into()),
		Ok(Some(ref x)) if x == &client.client.genesis_hash()
	);

	assert_matches!(
		client.block_hash(Some(1u64).into()),
		Ok(None)
	);

	let block = client.client.new_block().unwrap().bake().unwrap();
	client.client.import(BlockOrigin::Own, block.clone()).unwrap();

	assert_matches!(
		client.block_hash(Some(0u64).into()),
		Ok(Some(ref x)) if x == &client.client.genesis_hash()
	);
	assert_matches!(
		client.block_hash(Some(1u64).into()),
		Ok(Some(ref x)) if x == &block.hash()
	);
}


#[test]
fn should_return_finalised_hash() {
	let core = ::tokio::runtime::Runtime::new().unwrap();
	let remote = core.executor();

	let client = Chain {
		client: Arc::new(test_client::new()),
		subscriptions: Subscriptions::new(remote),
	};

	assert_matches!(
		client.finalised_head(),
		Ok(ref x) if x == &client.client.genesis_hash()
	);

	// import new block
	let builder = client.client.new_block().unwrap();
	client.client.import(BlockOrigin::Own, builder.bake().unwrap()).unwrap();
	// no finalisation yet
	assert_matches!(
		client.finalised_head(),
		Ok(ref x) if x == &client.client.genesis_hash()
	);

	// finalise
	client.client.finalize_block(BlockId::number(1), None, true).unwrap();
	assert_matches!(
		client.finalised_head(),
		Ok(ref x) if x == &client.client.block_hash(1).unwrap().unwrap()
	);
}

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
		assert_eq!(core.block_on(id), Ok(Ok(SubscriptionId::Number(1))));

		let builder = api.client.new_block().unwrap();
		api.client.import(BlockOrigin::Own, builder.bake().unwrap()).unwrap();
	}

	// assert initial head sent.
	let (notification, next) = core.block_on(transport.into_future()).unwrap();
	assert!(notification.is_some());
	// assert notification sent to transport
	let (notification, next) = core.block_on(next.into_future()).unwrap();
	assert!(notification.is_some());
	// no more notifications on this channel
	assert_eq!(core.block_on(next.into_future()).unwrap().0, None);
}

#[test]
fn should_notify_about_finalised_block() {
	let mut core = ::tokio::runtime::Runtime::new().unwrap();
	let remote = core.executor();
	let (subscriber, id, transport) = pubsub::Subscriber::new_test("test");

	{
		let api = Chain {
			client: Arc::new(test_client::new()),
			subscriptions: Subscriptions::new(remote),
		};

		api.subscribe_finalised_heads(Default::default(), subscriber);

		// assert id assigned
		assert_eq!(core.block_on(id), Ok(Ok(SubscriptionId::Number(1))));

		let builder = api.client.new_block().unwrap();
		api.client.import(BlockOrigin::Own, builder.bake().unwrap()).unwrap();
		api.client.finalize_block(BlockId::number(1), None, true).unwrap();
	}

	// assert initial head sent.
	let (notification, next) = core.block_on(transport.into_future()).unwrap();
	assert!(notification.is_some());
	// assert notification sent to transport
	let (notification, next) = core.block_on(next.into_future()).unwrap();
	assert!(notification.is_some());
	// no more notifications on this channel
	assert_eq!(core.block_on(next.into_future()).unwrap().0, None);
}
