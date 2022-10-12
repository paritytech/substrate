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

use crate::{config, NetworkWorker};

use futures::prelude::*;
use libp2p::PeerId;
use sc_block_builder::BlockBuilderProvider;
use sc_client_api::{BlockBackend, HeaderBackend};
use sc_consensus::JustificationSyncLink;
use sc_network_common::{
	config::{
		NonDefaultSetConfig, NonReservedPeerMode, NotificationHandshake, ProtocolId, SetConfig,
		TransportConfig,
	},
	protocol::role::Roles,
	service::NetworkSyncForkRequest,
	sync::{message::BlockAnnouncesHandshake, ChainSync as ChainSyncT, SyncState, SyncStatus},
};
use sc_network_light::light_client_requests::handler::LightClientRequestHandler;
use sc_network_sync::{
	block_request_handler::BlockRequestHandler, mock::MockChainSync,
	state_request_handler::StateRequestHandler,
};
use sp_core::H256;
use sp_runtime::{
	generic::BlockId,
	traits::{Block as BlockT, Header as _, Zero},
};
use std::{iter, sync::Arc, task::Poll};
use substrate_test_runtime_client::{TestClientBuilder, TestClientBuilderExt as _};

type TestNetworkWorker = NetworkWorker<
	substrate_test_runtime_client::runtime::Block,
	substrate_test_runtime_client::runtime::Hash,
	substrate_test_runtime_client::TestClient,
>;

const BLOCK_ANNOUNCE_PROTO_NAME: &str = "/block-announces";
const PROTOCOL_NAME: &str = "/foo";

fn make_network(
	chain_sync: Box<dyn ChainSyncT<substrate_test_runtime_client::runtime::Block>>,
	client: Arc<substrate_test_runtime_client::TestClient>,
) -> (TestNetworkWorker, Arc<substrate_test_runtime_client::TestClient>) {
	let network_config = config::NetworkConfiguration {
		extra_sets: vec![NonDefaultSetConfig {
			notifications_protocol: PROTOCOL_NAME.into(),
			fallback_names: Vec::new(),
			max_notification_size: 1024 * 1024,
			handshake: None,
			set_config: Default::default(),
		}],
		listen_addresses: vec![config::build_multiaddr![Memory(rand::random::<u64>())]],
		transport: TransportConfig::MemoryOnly,
		..config::NetworkConfiguration::new_local()
	};

	#[derive(Clone)]
	struct PassThroughVerifier(bool);

	#[async_trait::async_trait]
	impl<B: BlockT> sc_consensus::Verifier<B> for PassThroughVerifier {
		async fn verify(
			&mut self,
			mut block: sc_consensus::BlockImportParams<B, ()>,
		) -> Result<
			(
				sc_consensus::BlockImportParams<B, ()>,
				Option<Vec<(sp_blockchain::well_known_cache_keys::Id, Vec<u8>)>>,
			),
			String,
		> {
			let maybe_keys = block
				.header
				.digest()
				.log(|l| {
					l.try_as_raw(sp_runtime::generic::OpaqueDigestItemId::Consensus(b"aura"))
						.or_else(|| {
							l.try_as_raw(sp_runtime::generic::OpaqueDigestItemId::Consensus(
								b"babe",
							))
						})
				})
				.map(|blob| {
					vec![(sp_blockchain::well_known_cache_keys::AUTHORITIES, blob.to_vec())]
				});

			block.finalized = self.0;
			block.fork_choice = Some(sc_consensus::ForkChoiceStrategy::LongestChain);
			Ok((block, maybe_keys))
		}
	}

	let import_queue = Box::new(sc_consensus::BasicQueue::new(
		PassThroughVerifier(false),
		Box::new(client.clone()),
		None,
		&sp_core::testing::TaskExecutor::new(),
		None,
	));

	let protocol_id = ProtocolId::from("/test-protocol-name");

	let fork_id = Some(String::from("test-fork-id"));

	let block_request_protocol_config = {
		let (handler, protocol_config) =
			BlockRequestHandler::new(&protocol_id, None, client.clone(), 50);
		async_std::task::spawn(handler.run().boxed());
		protocol_config
	};

	let state_request_protocol_config = {
		let (handler, protocol_config) =
			StateRequestHandler::new(&protocol_id, None, client.clone(), 50);
		async_std::task::spawn(handler.run().boxed());
		protocol_config
	};

	let light_client_request_protocol_config = {
		let (handler, protocol_config) =
			LightClientRequestHandler::new(&protocol_id, None, client.clone());
		async_std::task::spawn(handler.run().boxed());
		protocol_config
	};

	let block_announce_config = NonDefaultSetConfig {
		notifications_protocol: BLOCK_ANNOUNCE_PROTO_NAME.into(),
		fallback_names: vec![],
		max_notification_size: 1024 * 1024,
		handshake: Some(NotificationHandshake::new(BlockAnnouncesHandshake::<
			substrate_test_runtime_client::runtime::Block,
		>::build(
			Roles::from(&config::Role::Full),
			client.info().best_number,
			client.info().best_hash,
			client
				.block_hash(Zero::zero())
				.ok()
				.flatten()
				.expect("Genesis block exists; qed"),
		))),
		set_config: SetConfig {
			in_peers: 0,
			out_peers: 0,
			reserved_nodes: Vec::new(),
			non_reserved_mode: NonReservedPeerMode::Deny,
		},
	};

	let worker = NetworkWorker::new(config::Params {
		block_announce_config,
		role: config::Role::Full,
		executor: None,
		network_config,
		chain: client.clone(),
		protocol_id,
		fork_id,
		import_queue,
		chain_sync,
		metrics_registry: None,
		block_request_protocol_config,
		state_request_protocol_config,
		light_client_request_protocol_config,
		warp_sync_protocol_config: None,
		request_response_protocol_configs: Vec::new(),
	})
	.unwrap();

	(worker, client)
}

fn set_default_expecations_no_peers(
	chain_sync: &mut MockChainSync<substrate_test_runtime_client::runtime::Block>,
) {
	chain_sync.expect_block_requests().returning(|| Box::new(iter::empty()));
	chain_sync.expect_state_request().returning(|| None);
	chain_sync.expect_justification_requests().returning(|| Box::new(iter::empty()));
	chain_sync.expect_warp_sync_request().returning(|| None);
	chain_sync.expect_poll_block_announce_validation().returning(|_| Poll::Pending);
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
	let client = Arc::new(TestClientBuilder::with_default_backend().build_with_longest_chain().0);
	let mut chain_sync =
		Box::new(MockChainSync::<substrate_test_runtime_client::runtime::Block>::new());
	set_default_expecations_no_peers(&mut chain_sync);

	let (mut network, _) = make_network(chain_sync, client);

	// poll the network once
	futures::future::poll_fn(|cx| {
		let _ = network.poll_unpin(cx);
		Poll::Ready(())
	})
	.await;
}

#[async_std::test]
async fn request_justification() {
	let client = Arc::new(TestClientBuilder::with_default_backend().build_with_longest_chain().0);
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
	let (mut network, _) = make_network(chain_sync, client);

	// send "request justifiction" message and poll the network
	network.service().request_justification(&hash, number);

	futures::future::poll_fn(|cx| {
		let _ = network.poll_unpin(cx);
		Poll::Ready(())
	})
	.await;
}

#[async_std::test]
async fn clear_justification_requests(&mut self) {
	let client = Arc::new(TestClientBuilder::with_default_backend().build_with_longest_chain().0);
	let mut chain_sync =
		Box::new(MockChainSync::<substrate_test_runtime_client::runtime::Block>::new());

	chain_sync.expect_clear_justification_requests().once().returning(|| ());

	set_default_expecations_no_peers(&mut chain_sync);
	let (mut network, _) = make_network(chain_sync, client);

	// send "request justifiction" message and poll the network
	network.service().clear_justification_requests();

	futures::future::poll_fn(|cx| {
		let _ = network.poll_unpin(cx);
		Poll::Ready(())
	})
	.await;
}

#[async_std::test]
async fn set_sync_fork_request() {
	let client = Arc::new(TestClientBuilder::with_default_backend().build_with_longest_chain().0);
	let mut chain_sync =
		Box::new(MockChainSync::<substrate_test_runtime_client::runtime::Block>::new());

	let hash = H256::random();
	let number = 1337u64;
	let peers = (0..3).map(|_| PeerId::random()).collect::<Vec<_>>();
	let copy_peers = peers.clone();

	chain_sync
		.expect_set_sync_fork_request()
		.withf(move |in_peers, in_hash, in_number| {
			&peers == in_peers && &hash == in_hash && &number == in_number
		})
		.once()
		.returning(|_, _, _| ());

	set_default_expecations_no_peers(&mut chain_sync);
	let (mut network, _) = make_network(chain_sync, client);

	// send "set sync fork request" message and poll the network
	network.service().set_sync_fork_request(copy_peers, hash, number);

	futures::future::poll_fn(|cx| {
		let _ = network.poll_unpin(cx);
		Poll::Ready(())
	})
	.await;
}

#[async_std::test]
async fn on_block_finalized() {
	let client = Arc::new(TestClientBuilder::with_default_backend().build_with_longest_chain().0);
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
	let (mut network, _) = make_network(chain_sync, client);

	// send "set sync fork request" message and poll the network
	network.on_block_finalized(hash, header);

	futures::future::poll_fn(|cx| {
		let _ = network.poll_unpin(cx);
		Poll::Ready(())
	})
	.await;
}
