// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

use crate::service::tests::TestNetworkBuilder;

use futures::prelude::*;
use libp2p::PeerId;
use sc_block_builder::BlockBuilderProvider;
use sc_client_api::HeaderBackend;
use sc_consensus::JustificationSyncLink;
use sc_network_common::{
	service::NetworkSyncForkRequest,
	sync::{SyncState, SyncStatus},
};
use sc_network_sync::{mock::MockChainSync, service::mock::MockChainSyncInterface};
use sp_core::H256;
use sp_runtime::{
	generic::BlockId,
	traits::{Block as BlockT, Header as _},
};
use std::{iter, sync::Arc, task::Poll};
use substrate_test_runtime_client::{TestClientBuilder, TestClientBuilderExt as _};

fn set_default_expecations_no_peers(
	chain_sync: &mut MockChainSync<substrate_test_runtime_client::runtime::Block>,
) {
	chain_sync.expect_block_requests().returning(|| Box::new(iter::empty()));
	chain_sync.expect_state_request().returning(|| None);
	chain_sync.expect_justification_requests().returning(|| Box::new(iter::empty()));
	chain_sync.expect_warp_sync_request().returning(|| None);
	chain_sync.expect_poll().returning(|_| Poll::Pending);
	chain_sync.expect_status().returning(|| SyncStatus {
		state: SyncState::Idle,
		best_seen_block: None,
		num_peers: 0u32,
		queued_blocks: 0u32,
		state_sync: None,
		warp_sync: None,
	});
}

#[async_std::test]
async fn normal_network_poll_no_peers() {
	// build `ChainSync` and set default expectations for it
	let mut chain_sync =
		Box::new(MockChainSync::<substrate_test_runtime_client::runtime::Block>::new());
	set_default_expecations_no_peers(&mut chain_sync);

	// build `ChainSyncInterface` provider and set no expecations for it (i.e., it cannot be
	// called)
	let chain_sync_service =
		Box::new(MockChainSyncInterface::<substrate_test_runtime_client::runtime::Block>::new());

	let mut network = TestNetworkBuilder::new()
		.with_chain_sync((chain_sync, chain_sync_service))
		.build();

	// poll the network once
	futures::future::poll_fn(|cx| {
		let _ = network.network().poll_unpin(cx);
		Poll::Ready(())
	})
	.await;
}

#[async_std::test]
async fn request_justification() {
	// build `ChainSyncInterface` provider and set no expecations for it (i.e., it cannot be
	// called)
	let chain_sync_service =
		Box::new(MockChainSyncInterface::<substrate_test_runtime_client::runtime::Block>::new());

	// build `ChainSync` and verify that call to `request_justification()` is made
	let mut chain_sync =
		Box::new(MockChainSync::<substrate_test_runtime_client::runtime::Block>::new());

	let hash = H256::random();
	let number = 1337u64;

	chain_sync
		.expect_request_justification()
		.withf(move |in_hash, in_number| &hash == in_hash && &number == in_number)
		.once()
		.returning(|_, _| ());

	set_default_expecations_no_peers(&mut chain_sync);
	let mut network = TestNetworkBuilder::new()
		.with_chain_sync((chain_sync, chain_sync_service))
		.build();

	// send "request justifiction" message and poll the network
	network.service().request_justification(&hash, number);

	futures::future::poll_fn(|cx| {
		let _ = network.network().poll_unpin(cx);
		Poll::Ready(())
	})
	.await;
}

#[async_std::test]
async fn clear_justification_requests() {
	// build `ChainSyncInterface` provider and set no expecations for it (i.e., it cannot be
	// called)
	let chain_sync_service =
		Box::new(MockChainSyncInterface::<substrate_test_runtime_client::runtime::Block>::new());

	// build `ChainSync` and verify that call to `clear_justification_requests()` is made
	let mut chain_sync =
		Box::new(MockChainSync::<substrate_test_runtime_client::runtime::Block>::new());

	chain_sync.expect_clear_justification_requests().once().returning(|| ());

	set_default_expecations_no_peers(&mut chain_sync);
	let mut network = TestNetworkBuilder::new()
		.with_chain_sync((chain_sync, chain_sync_service))
		.build();

	// send "request justifiction" message and poll the network
	network.service().clear_justification_requests();

	futures::future::poll_fn(|cx| {
		let _ = network.network().poll_unpin(cx);
		Poll::Ready(())
	})
	.await;
}

#[async_std::test]
async fn set_sync_fork_request() {
	// build `ChainSync` and set default expectations for it
	let mut chain_sync =
		Box::new(MockChainSync::<substrate_test_runtime_client::runtime::Block>::new());
	set_default_expecations_no_peers(&mut chain_sync);

	// build `ChainSyncInterface` provider and verify that the `set_sync_fork_request()`
	// call is delegated to `ChainSyncInterface` (which eventually forwards it to `ChainSync`)
	let mut chain_sync_service =
		MockChainSyncInterface::<substrate_test_runtime_client::runtime::Block>::new();

	let hash = H256::random();
	let number = 1337u64;
	let peers = (0..3).map(|_| PeerId::random()).collect::<Vec<_>>();
	let copy_peers = peers.clone();

	chain_sync_service
		.expect_set_sync_fork_request()
		.withf(move |in_peers, in_hash, in_number| {
			&peers == in_peers && &hash == in_hash && &number == in_number
		})
		.once()
		.returning(|_, _, _| ());

	let mut network = TestNetworkBuilder::new()
		.with_chain_sync((chain_sync, Box::new(chain_sync_service)))
		.build();

	// send "set sync fork request" message and poll the network
	network.service().set_sync_fork_request(copy_peers, hash, number);

	futures::future::poll_fn(|cx| {
		let _ = network.network().poll_unpin(cx);
		Poll::Ready(())
	})
	.await;
}

#[async_std::test]
async fn on_block_finalized() {
	let client = Arc::new(TestClientBuilder::with_default_backend().build_with_longest_chain().0);
	// build `ChainSyncInterface` provider and set no expecations for it (i.e., it cannot be
	// called)
	let chain_sync_service =
		Box::new(MockChainSyncInterface::<substrate_test_runtime_client::runtime::Block>::new());

	// build `ChainSync` and verify that call to `on_block_finalized()` is made
	let mut chain_sync =
		Box::new(MockChainSync::<substrate_test_runtime_client::runtime::Block>::new());

	let at = client.header(&BlockId::Hash(client.info().best_hash)).unwrap().unwrap().hash();
	let block = client
		.new_block_at(&BlockId::Hash(at), Default::default(), false)
		.unwrap()
		.build()
		.unwrap()
		.block;
	let header = block.header.clone();
	let block_number = *header.number();
	let hash = block.hash();

	chain_sync
		.expect_on_block_finalized()
		.withf(move |in_hash, in_number| &hash == in_hash && &block_number == in_number)
		.once()
		.returning(|_, _| ());

	set_default_expecations_no_peers(&mut chain_sync);
	let mut network = TestNetworkBuilder::new()
		.with_client(client)
		.with_chain_sync((chain_sync, chain_sync_service))
		.build();

	// send "set sync fork request" message and poll the network
	network.network().on_block_finalized(hash, header);

	futures::future::poll_fn(|cx| {
		let _ = network.network().poll_unpin(cx);
		Poll::Ready(())
	})
	.await;
}
