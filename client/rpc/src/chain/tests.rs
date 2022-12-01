// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

use super::*;
use crate::testing::{test_executor, timeout_secs};
use assert_matches::assert_matches;
use jsonrpsee::types::EmptyParams;
use sc_block_builder::BlockBuilderProvider;
use sp_consensus::BlockOrigin;
use sp_rpc::list::ListOrValue;
use substrate_test_runtime_client::{
	prelude::*,
	runtime::{Block, Header, H256},
};

#[tokio::test]
async fn should_return_header() {
	let client = Arc::new(substrate_test_runtime_client::new());
	let api = new_full(client.clone(), test_executor()).into_rpc();

	let res: Header =
		api.call("chain_getHeader", [H256::from(client.genesis_hash())]).await.unwrap();
	assert_eq!(
		res,
		Header {
			parent_hash: H256::from_low_u64_be(0),
			number: 0,
			state_root: res.state_root,
			extrinsics_root: "03170a2e7597b7b7e3d84c05391d139a62b157e78786d8c082f29dcf4c111314"
				.parse()
				.unwrap(),
			digest: Default::default(),
		}
	);

	let res: Header = api.call("chain_getHeader", EmptyParams::new()).await.unwrap();
	assert_eq!(
		res,
		Header {
			parent_hash: H256::from_low_u64_be(0),
			number: 0,
			state_root: res.state_root,
			extrinsics_root: "03170a2e7597b7b7e3d84c05391d139a62b157e78786d8c082f29dcf4c111314"
				.parse()
				.unwrap(),
			digest: Default::default(),
		}
	);

	assert_matches!(
		api.call::<_, Option<Header>>("chain_getHeader", [H256::from_low_u64_be(5)])
			.await
			.unwrap(),
		None
	);
}

#[tokio::test]
async fn should_return_a_block() {
	let mut client = Arc::new(substrate_test_runtime_client::new());
	let api = new_full(client.clone(), test_executor()).into_rpc();

	let block = client.new_block(Default::default()).unwrap().build().unwrap().block;
	let block_hash = block.hash();
	client.import(BlockOrigin::Own, block).await.unwrap();

	let res: SignedBlock<Block> =
		api.call("chain_getBlock", [H256::from(client.genesis_hash())]).await.unwrap();

	// Genesis block is not justified
	assert!(res.justifications.is_none());

	let res: SignedBlock<Block> =
		api.call("chain_getBlock", [H256::from(block_hash)]).await.unwrap();
	assert_eq!(
		res.block,
		Block {
			header: Header {
				parent_hash: client.genesis_hash(),
				number: 1,
				state_root: res.block.header.state_root,
				extrinsics_root: "03170a2e7597b7b7e3d84c05391d139a62b157e78786d8c082f29dcf4c111314"
					.parse()
					.unwrap(),
				digest: Default::default(),
			},
			extrinsics: vec![],
		}
	);

	let res: SignedBlock<Block> = api.call("chain_getBlock", Vec::<H256>::new()).await.unwrap();
	assert_eq!(
		res.block,
		Block {
			header: Header {
				parent_hash: client.genesis_hash(),
				number: 1,
				state_root: res.block.header.state_root,
				extrinsics_root: "03170a2e7597b7b7e3d84c05391d139a62b157e78786d8c082f29dcf4c111314"
					.parse()
					.unwrap(),
				digest: Default::default(),
			},
			extrinsics: vec![],
		}
	);

	assert_matches!(
		api.call::<_, Option<Header>>("chain_getBlock", [H256::from_low_u64_be(5)])
			.await
			.unwrap(),
		None
	);
}

#[tokio::test]
async fn should_return_block_hash() {
	let mut client = Arc::new(substrate_test_runtime_client::new());
	let api = new_full(client.clone(), test_executor()).into_rpc();

	let res: ListOrValue<Option<H256>> =
		api.call("chain_getBlockHash", EmptyParams::new()).await.unwrap();

	assert_matches!(
		res,
		ListOrValue::Value(Some(ref x)) if x == &client.genesis_hash()
	);

	let res: ListOrValue<Option<H256>> =
		api.call("chain_getBlockHash", [ListOrValue::from(0_u64)]).await.unwrap();
	assert_matches!(
		res,
		ListOrValue::Value(Some(ref x)) if x == &client.genesis_hash()
	);

	let res: Option<ListOrValue<Option<H256>>> =
		api.call("chain_getBlockHash", [ListOrValue::from(1_u64)]).await.unwrap();
	assert_matches!(res, None);

	let block = client.new_block(Default::default()).unwrap().build().unwrap().block;
	client.import(BlockOrigin::Own, block.clone()).await.unwrap();

	let res: ListOrValue<Option<H256>> =
		api.call("chain_getBlockHash", [ListOrValue::from(0_u64)]).await.unwrap();
	assert_matches!(
		res,
		ListOrValue::Value(Some(ref x)) if x == &client.genesis_hash()
	);

	let res: ListOrValue<Option<H256>> =
		api.call("chain_getBlockHash", [ListOrValue::from(1_u64)]).await.unwrap();
	assert_matches!(
		res,
		ListOrValue::Value(Some(ref x)) if x == &block.hash()
	);

	let res: ListOrValue<Option<H256>> = api
		.call("chain_getBlockHash", [ListOrValue::Value(sp_core::U256::from(1_u64))])
		.await
		.unwrap();
	assert_matches!(
		res,
		ListOrValue::Value(Some(ref x)) if x == &block.hash()
	);

	let res: ListOrValue<Option<H256>> = api
		.call("chain_getBlockHash", [ListOrValue::List(vec![0_u64, 1_u64, 2_u64])])
		.await
		.unwrap();
	assert_matches!(
		res,
		ListOrValue::List(list) if list == &[client.genesis_hash().into(), block.hash().into(), None]
	);
}

#[tokio::test]
async fn should_return_finalized_hash() {
	let mut client = Arc::new(substrate_test_runtime_client::new());
	let api = new_full(client.clone(), test_executor()).into_rpc();

	let res: H256 = api.call("chain_getFinalizedHead", EmptyParams::new()).await.unwrap();
	assert_eq!(res, client.genesis_hash());

	// import new block
	let block = client.new_block(Default::default()).unwrap().build().unwrap().block;
	let block_hash = block.hash();
	client.import(BlockOrigin::Own, block).await.unwrap();

	// no finalization yet
	let res: H256 = api.call("chain_getFinalizedHead", EmptyParams::new()).await.unwrap();
	assert_eq!(res, client.genesis_hash());

	// finalize
	client.finalize_block(block_hash, None).unwrap();
	let res: H256 = api.call("chain_getFinalizedHead", EmptyParams::new()).await.unwrap();
	assert_eq!(res, block_hash);
}

#[tokio::test]
async fn should_notify_about_latest_block() {
	test_head_subscription("chain_subscribeAllHeads").await;
}

#[tokio::test]
async fn should_notify_about_best_block() {
	test_head_subscription("chain_subscribeNewHeads").await;
}

#[tokio::test]
async fn should_notify_about_finalized_block() {
	test_head_subscription("chain_subscribeFinalizedHeads").await;
}

async fn test_head_subscription(method: &str) {
	let mut client = Arc::new(substrate_test_runtime_client::new());

	let mut sub = {
		let api = new_full(client.clone(), test_executor()).into_rpc();
		let sub = api.subscribe(method, EmptyParams::new()).await.unwrap();
		let block = client.new_block(Default::default()).unwrap().build().unwrap().block;
		let block_hash = block.hash();
		client.import(BlockOrigin::Own, block).await.unwrap();
		client.finalize_block(block_hash, None).unwrap();
		sub
	};

	assert_matches!(timeout_secs(10, sub.next::<Header>()).await, Ok(Some(_)));
	assert_matches!(timeout_secs(10, sub.next::<Header>()).await, Ok(Some(_)));

	sub.close();
	assert_matches!(timeout_secs(10, sub.next::<Header>()).await, Ok(None));
}
