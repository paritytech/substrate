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

use client::{backend::Backend, blockchain::HeaderBackend};
use crate::config::Roles;
use crate::message;
use consensus::BlockOrigin;
use std::collections::HashSet;
use super::*;

fn test_ancestor_search_when_common_is(n: usize) {
	let _ = ::env_logger::try_init();
	let mut net = TestNet::new(3);

	net.peer(0).push_blocks(n, false);
	net.peer(1).push_blocks(n, false);
	net.peer(2).push_blocks(n, false);

	net.peer(0).push_blocks(10, true);
	net.peer(1).push_blocks(100, false);
	net.peer(2).push_blocks(100, false);

	net.sync();
	assert!(net.peer(0).client.as_in_memory_backend().blockchain()
		.canon_equals_to(net.peer(1).client.as_in_memory_backend().blockchain()));
}

#[test]
fn sync_peers_works() {
	let _ = ::env_logger::try_init();
	let mut net = TestNet::new(3);
	net.sync();
	for peer in 0..3 {
		// Assert peers is up to date.
		assert_eq!(net.peer(peer).num_peers(), 2);
		// And then disconnect.
		for other in 0..3 {
			if other != peer {
				net.peer(peer).on_disconnect(net.peer(other));
			}
		}
	}
	net.sync();
	// Now peers are disconnected.
	for peer in 0..3 {
		assert_eq!(net.peer(peer).num_peers(), 0);
	}
}

#[test]
fn sync_cycle_from_offline_to_syncing_to_offline() {
	let _ = ::env_logger::try_init();
	let mut net = TestNet::new(3);
	for peer in 0..3 {
		// Offline, and not major syncing.
		assert!(net.peer(peer).is_offline());
		assert!(!net.peer(peer).is_major_syncing());
	}

	// Generate blocks.
	net.peer(2).push_blocks(100, false);
	net.start();
	for peer in 0..3 {
		// Online
		assert!(!net.peer(peer).is_offline());
		if peer < 2 {
			// Major syncing.
			assert!(net.peer(peer).is_major_syncing());
		}
	}
	net.sync();
	for peer in 0..3 {
		// All done syncing.
		assert!(!net.peer(peer).is_major_syncing());
	}

	// Now disconnect them all.
	for peer in 0..3 {
		for other in 0..3 {
			if other != peer {
				net.peer(peer).on_disconnect(net.peer(other));
			}
		}
		net.sync();
		assert!(net.peer(peer).is_offline());
		assert!(!net.peer(peer).is_major_syncing());
	}
}

#[test]
fn syncing_node_not_major_syncing_when_disconnected() {
	let _ = ::env_logger::try_init();
	let mut net = TestNet::new(3);

	// Generate blocks.
	net.peer(2).push_blocks(100, false);
	net.start();
	net.sync_step();

	// Peer 1 is major-syncing.
	assert!(net.peer(1).is_major_syncing());

	// Disconnect peer 1 form everyone else.
	net.peer(1).on_disconnect(net.peer(0));
	net.peer(1).on_disconnect(net.peer(2));

	// Peer 1 is not major-syncing.
	net.sync();
	assert!(!net.peer(1).is_major_syncing());
}

#[test]
fn sync_from_two_peers_works() {
	let _ = ::env_logger::try_init();
	let mut net = TestNet::new(3);
	net.peer(1).push_blocks(100, false);
	net.peer(2).push_blocks(100, false);
	net.sync();
	assert!(net.peer(0).client.as_in_memory_backend().blockchain()
		.equals_to(net.peer(1).client.as_in_memory_backend().blockchain()));
	assert!(!net.peer(0).is_major_syncing());
}

#[test]
fn sync_from_two_peers_with_ancestry_search_works() {
	let _ = ::env_logger::try_init();
	let mut net = TestNet::new(3);
	net.peer(0).push_blocks(10, true);
	net.peer(1).push_blocks(100, false);
	net.peer(2).push_blocks(100, false);
	net.sync();
	assert!(net.peer(0).client.as_in_memory_backend().blockchain()
		.canon_equals_to(net.peer(1).client.as_in_memory_backend().blockchain()));
}

#[test]
fn ancestry_search_works_when_backoff_is_one() {
	let _ = ::env_logger::try_init();
	let mut net = TestNet::new(3);

	net.peer(0).push_blocks(1, false);
	net.peer(1).push_blocks(2, false);
	net.peer(2).push_blocks(2, false);

	net.sync();
	assert!(net.peer(0).client.as_in_memory_backend().blockchain()
		.canon_equals_to(net.peer(1).client.as_in_memory_backend().blockchain()));
}

#[test]
fn ancestry_search_works_when_ancestor_is_genesis() {
	let _ = ::env_logger::try_init();
	let mut net = TestNet::new(3);

	net.peer(0).push_blocks(13, true);
	net.peer(1).push_blocks(100, false);
	net.peer(2).push_blocks(100, false);

	net.sync();
	assert!(net.peer(0).client.as_in_memory_backend().blockchain()
		.canon_equals_to(net.peer(1).client.as_in_memory_backend().blockchain()));
}

#[test]
fn ancestry_search_works_when_common_is_one() {
	test_ancestor_search_when_common_is(1);
}

#[test]
fn ancestry_search_works_when_common_is_two() {
	test_ancestor_search_when_common_is(2);
}

#[test]
fn ancestry_search_works_when_common_is_hundred() {
	test_ancestor_search_when_common_is(100);
}

#[test]
fn sync_long_chain_works() {
	let mut net = TestNet::new(2);
	net.peer(1).push_blocks(500, false);
	net.sync();
	assert!(net.peer(0).client.as_in_memory_backend().blockchain()
		.equals_to(net.peer(1).client.as_in_memory_backend().blockchain()));
}

#[test]
fn sync_no_common_longer_chain_fails() {
	let _ = ::env_logger::try_init();
	let mut net = TestNet::new(3);
	net.peer(0).push_blocks(20, true);
	net.peer(1).push_blocks(20, false);
	net.sync();
	assert!(!net.peer(0).client.as_in_memory_backend().blockchain()
		.canon_equals_to(net.peer(1).client.as_in_memory_backend().blockchain()));
}

#[test]
fn sync_justifications() {
	let _ = ::env_logger::try_init();
	let mut net = JustificationTestNet::new(3);
	net.peer(0).push_blocks(20, false);
	net.sync();

	// there's currently no justification for block #10
	assert_eq!(net.peer(0).client().justification(&BlockId::Number(10)).unwrap(), None);
	assert_eq!(net.peer(1).client().justification(&BlockId::Number(10)).unwrap(), None);

	// we finalize block #10, #15 and #20 for peer 0 with a justification
	net.peer(0).client().finalize_block(BlockId::Number(10), Some(Vec::new()), true).unwrap();
	net.peer(0).client().finalize_block(BlockId::Number(15), Some(Vec::new()), true).unwrap();
	net.peer(0).client().finalize_block(BlockId::Number(20), Some(Vec::new()), true).unwrap();

	let h1 = net.peer(1).client().header(&BlockId::Number(10)).unwrap().unwrap();
	let h2 = net.peer(1).client().header(&BlockId::Number(15)).unwrap().unwrap();
	let h3 = net.peer(1).client().header(&BlockId::Number(20)).unwrap().unwrap();

	// peer 1 should get the justifications from the network
	net.peer(1).request_justification(&h1.hash().into(), 10);
	net.peer(1).request_justification(&h2.hash().into(), 15);
	net.peer(1).request_justification(&h3.hash().into(), 20);

	net.sync();

	for height in (10..21).step_by(5) {
		assert_eq!(net.peer(0).client().justification(&BlockId::Number(height)).unwrap(), Some(Vec::new()));
		assert_eq!(net.peer(1).client().justification(&BlockId::Number(height)).unwrap(), Some(Vec::new()));
	}
}

#[test]
fn sync_justifications_across_forks() {
	let _ = ::env_logger::try_init();
	let mut net = JustificationTestNet::new(3);
	// we push 5 blocks
	net.peer(0).push_blocks(5, false);
	// and then two forks 5 and 6 blocks long
	let f1_best = net.peer(0).push_blocks_at(BlockId::Number(5), 5, false);
	let f2_best = net.peer(0).push_blocks_at(BlockId::Number(5), 6, false);

	// peer 1 will only see the longer fork. but we'll request justifications
	// for both and finalize the small fork instead.
	net.sync();

	net.peer(0).client().finalize_block(BlockId::Hash(f1_best), Some(Vec::new()), true).unwrap();

	net.peer(1).request_justification(&f1_best, 10);
	net.peer(1).request_justification(&f2_best, 11);

	net.sync();

	assert_eq!(net.peer(0).client().justification(&BlockId::Number(10)).unwrap(), Some(Vec::new()));
	assert_eq!(net.peer(1).client().justification(&BlockId::Number(10)).unwrap(), Some(Vec::new()));
}

#[test]
fn sync_after_fork_works() {
	let _ = ::env_logger::try_init();
	let mut net = TestNet::new(3);
	net.sync_step();
	net.peer(0).push_blocks(30, false);
	net.peer(1).push_blocks(30, false);
	net.peer(2).push_blocks(30, false);

	net.peer(0).push_blocks(10, true);
	net.peer(1).push_blocks(20, false);
	net.peer(2).push_blocks(20, false);

	net.peer(1).push_blocks(10, true);
	net.peer(2).push_blocks(1, false);

	// peer 1 has the best chain
	let peer1_chain = net.peer(1).client.as_in_memory_backend().blockchain().clone();
	net.sync();
	assert!(net.peer(0).client.as_in_memory_backend().blockchain().canon_equals_to(&peer1_chain));
	assert!(net.peer(1).client.as_in_memory_backend().blockchain().canon_equals_to(&peer1_chain));
	assert!(net.peer(2).client.as_in_memory_backend().blockchain().canon_equals_to(&peer1_chain));
}

#[test]
fn syncs_all_forks() {
	let _ = ::env_logger::try_init();
	let mut net = TestNet::new(4);
	net.sync_step();
	net.peer(0).push_blocks(2, false);
	net.peer(1).push_blocks(2, false);

	net.peer(0).push_blocks(2, true);
	net.peer(1).push_blocks(4, false);

	net.sync();
	// Check that all peers have all of the blocks.
	assert_eq!(9, net.peer(0).client.as_in_memory_backend().blockchain().blocks_count());
	assert_eq!(9, net.peer(1).client.as_in_memory_backend().blockchain().blocks_count());
}

#[test]
fn own_blocks_are_announced() {
	let _ = ::env_logger::try_init();
	let mut net = TestNet::new(3);
	net.sync(); // connect'em
	net.peer(0).generate_blocks(1, BlockOrigin::Own, |builder| builder.bake().unwrap());

	let header = net.peer(0).client().header(&BlockId::Number(1)).unwrap().unwrap();
	net.peer(0).on_block_imported(header.hash(), &header);
	net.sync();

	assert_eq!(net.peer(0).client.as_in_memory_backend().blockchain().info().best_number, 1);
	assert_eq!(net.peer(1).client.as_in_memory_backend().blockchain().info().best_number, 1);
	let peer0_chain = net.peer(0).client.as_in_memory_backend().blockchain().clone();
	assert!(net.peer(1).client.as_in_memory_backend().blockchain().canon_equals_to(&peer0_chain));
	assert!(net.peer(2).client.as_in_memory_backend().blockchain().canon_equals_to(&peer0_chain));
}

#[test]
fn blocks_are_not_announced_by_light_nodes() {
	let _ = ::env_logger::try_init();
	let mut net = TestNet::new(0);

	// full peer0 is connected to light peer
	// light peer1 is connected to full peer2
	let mut light_config = ProtocolConfig::default();
	light_config.roles = Roles::LIGHT;
	net.add_full_peer(&ProtocolConfig::default());
	net.add_full_peer(&light_config);
	net.add_full_peer(&ProtocolConfig::default());

	net.peer(0).push_blocks(1, false);
	net.peer(0).start();
	net.peer(1).start();
	net.peer(2).start();
	net.peer(0).on_connect(net.peer(1));
	net.peer(1).on_connect(net.peer(2));

	// Only sync between 0 -> 1, and 1 -> 2
	let mut disconnected = HashSet::new();
	disconnected.insert(0);
	disconnected.insert(2);
	net.sync_with(true, Some(disconnected));

	// peer 0 has the best chain
	// peer 1 has the best chain
	// peer 2 has genesis-chain only
	assert_eq!(net.peer(0).client.info().chain.best_number, 1);
	assert_eq!(net.peer(1).client.info().chain.best_number, 1);
	assert_eq!(net.peer(2).client.info().chain.best_number, 0);
}

#[test]
fn can_sync_small_non_best_forks() {
	let _ = ::env_logger::try_init();
	let mut net = TestNet::new(2);
	net.sync_step();
	net.peer(0).push_blocks(30, false);
	net.peer(1).push_blocks(30, false);

	// small fork + reorg on peer 1.
	net.peer(0).push_blocks_at(BlockId::Number(30), 2, true);
	let small_hash = net.peer(0).client().info().chain.best_hash;
	net.peer(0).push_blocks_at(BlockId::Number(30), 10, false);
	assert_eq!(net.peer(0).client().info().chain.best_number, 40);

	// peer 1 only ever had the long fork.
	net.peer(1).push_blocks(10, false);
	assert_eq!(net.peer(1).client().info().chain.best_number, 40);

	assert!(net.peer(0).client().header(&BlockId::Hash(small_hash)).unwrap().is_some());
	assert!(net.peer(1).client().header(&BlockId::Hash(small_hash)).unwrap().is_none());

	net.sync();

	// synchronization: 0 synced to longer chain and 1 didn't sync to small chain.

	assert_eq!(net.peer(0).client().info().chain.best_number, 40);

	assert!(net.peer(0).client().header(&BlockId::Hash(small_hash)).unwrap().is_some());
	assert!(!net.peer(1).client().header(&BlockId::Hash(small_hash)).unwrap().is_some());

	net.peer(0).announce_block(small_hash);
	net.sync();

	// after announcing, peer 1 downloads the block.

	assert!(net.peer(0).client().header(&BlockId::Hash(small_hash)).unwrap().is_some());
	assert!(net.peer(1).client().header(&BlockId::Hash(small_hash)).unwrap().is_some());
}

#[test]
fn can_not_sync_from_light_peer() {
	let _ = ::env_logger::try_init();

	// given the network with 1 full nodes (#0) and 1 light node (#1)
	let mut net = TestNet::new(1);
	net.add_light_peer(&Default::default());

	// generate some blocks on #0
	net.peer(0).push_blocks(1, false);

	// and let the light client sync from this node
	// (mind the #1 is disconnected && not syncing)
	net.sync();

	// ensure #0 && #1 have the same best block
	let full0_info = net.peer(0).client.info().chain;
	let light_info = net.peer(1).client.info().chain;
	assert_eq!(full0_info.best_number, 1);
	assert_eq!(light_info.best_number, 1);
	assert_eq!(light_info.best_hash, full0_info.best_hash);

	// add new full client (#2) && sync without #0
	net.add_full_peer(&Default::default());
	net.peer(1).on_connect(net.peer(2));
	net.peer(2).on_connect(net.peer(1));
	net.peer(1).announce_block(light_info.best_hash);
	net.sync_with(true, Some(vec![0].into_iter().collect()));

	// ensure that the #2 has failed to sync block #1
	assert_eq!(net.peer(2).client.info().chain.best_number, 0);
	// and that the #1 is still connected to #2
	// (because #2 has not tried to fetch block data from the #1 light node)
	assert_eq!(net.peer(1).num_peers(), 2);

	// and now try to fetch block data from light peer #1
	// (this should result in disconnect)
	net.peer(1).receive_message(
		&net.peer(2).peer_id,
		message::generic::Message::BlockRequest(message::generic::BlockRequest {
			id: 0,
			fields: message::BlockAttributes::HEADER,
			from: message::FromBlock::Hash(light_info.best_hash),
			to: None,
			direction: message::Direction::Ascending,
			max: Some(1),
		}),
	);
	net.sync();
	// check that light #1 has disconnected from #2
	assert_eq!(net.peer(1).num_peers(), 1);
}

#[test]
fn light_peer_imports_header_from_announce() {
	let _ = ::env_logger::try_init();

	fn import_with_announce(net: &mut TestNet, hash: H256) {
		let header = net.peer(0).client().header(&BlockId::Hash(hash)).unwrap().unwrap();
		net.peer(1).receive_message(
			&net.peer(0).peer_id,
			message::generic::Message::BlockAnnounce(message::generic::BlockAnnounce {
				header,
			}),
		);

		net.peer(1).import_queue_sync();
		assert!(net.peer(1).client().header(&BlockId::Hash(hash)).unwrap().is_some());
	}

	// given the network with 1 full nodes (#0) and 1 light node (#1)
	let mut net = TestNet::new(1);
	net.add_light_peer(&Default::default());

	// let them connect to each other
	net.sync();

	// check that NEW block is imported from announce message
	let new_hash = net.peer(0).push_blocks(1, false);
	import_with_announce(&mut net, new_hash);

	// check that KNOWN STALE block is imported from announce message
	let known_stale_hash = net.peer(0).push_blocks_at(BlockId::Number(0), 1, true);
	import_with_announce(&mut net, known_stale_hash);
}
