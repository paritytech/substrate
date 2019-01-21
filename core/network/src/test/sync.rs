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

use client::backend::Backend;
use client::blockchain::HeaderBackend as BlockchainHeaderBackend;
use config::Roles;
use consensus::BlockOrigin;
use sync::SyncState;
use super::*;

#[test]
fn sync_from_two_peers_works() {
	::env_logger::init().ok();
	let mut net = TestNet::new(3);
	net.peer(1).push_blocks(100, false);
	net.peer(2).push_blocks(100, false);
	net.sync();
	assert!(net.peer(0).client.backend().blockchain().equals_to(net.peer(1).client.backend().blockchain()));
	let status = net.peer(0).sync.status();
	assert_eq!(status.sync.state, SyncState::Idle);
}

#[test]
fn sync_from_two_peers_with_ancestry_search_works() {
	::env_logger::init().ok();
	let mut net = TestNet::new(3);
	net.peer(0).push_blocks(10, true);
	net.peer(1).push_blocks(100, false);
	net.peer(2).push_blocks(100, false);
	net.restart_peer(0);
	net.sync();
	assert!(net.peer(0).client.backend().blockchain().canon_equals_to(net.peer(1).client.backend().blockchain()));
}

#[test]
fn sync_long_chain_works() {
	let mut net = TestNet::new(2);
	net.peer(1).push_blocks(500, false);
	net.sync_steps(3);
	assert_eq!(net.peer(0).sync.status().sync.state, SyncState::Downloading);
	net.sync();
	assert!(net.peer(0).client.backend().blockchain().equals_to(net.peer(1).client.backend().blockchain()));
}

#[test]
fn sync_no_common_longer_chain_fails() {
	::env_logger::init().ok();
	let mut net = TestNet::new(3);
	net.peer(0).push_blocks(20, true);
	net.peer(1).push_blocks(20, false);
	net.sync();
	assert!(!net.peer(0).client.backend().blockchain().canon_equals_to(net.peer(1).client.backend().blockchain()));
}

#[test]
fn sync_justifications() {
	::env_logger::init().ok();
	let mut net = TestNet::new(3);
	net.peer(0).push_blocks(20, false);
	net.sync();

	// there's currently no justification for block #10
	assert_eq!(net.peer(0).client().justification(&BlockId::Number(10)).unwrap(), None);
	// we finalize block #10 for peer 0 with a justification
	net.peer(0).client().finalize_block(BlockId::Number(10), Some(Vec::new()), true).unwrap();

	let header = net.peer(1).client().header(&BlockId::Number(10)).unwrap().unwrap();
	net.peer(1).request_justification(&header.hash().into(), 10);

	net.sync();

	assert_eq!(net.peer(0).client().justification(&BlockId::Number(10)).unwrap(), Some(Vec::new()));
	assert_eq!(net.peer(1).client().justification(&BlockId::Number(10)).unwrap(), Some(Vec::new()));
}

#[test]
fn sync_after_fork_works() {
	::env_logger::init().ok();
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
	let peer1_chain = net.peer(1).client.backend().blockchain().clone();
	net.sync();
	assert!(net.peer(0).client.backend().blockchain().canon_equals_to(&peer1_chain));
	assert!(net.peer(1).client.backend().blockchain().canon_equals_to(&peer1_chain));
	assert!(net.peer(2).client.backend().blockchain().canon_equals_to(&peer1_chain));
}

#[test]
fn own_blocks_are_announced() {
	::env_logger::init().ok();
	let mut net = TestNet::new(3);
	net.sync(); // connect'em
	net.peer(0).generate_blocks(1, BlockOrigin::Own, |builder| builder.bake().unwrap());

	let header = net.peer(0).client().header(&BlockId::Number(1)).unwrap().unwrap();
	net.peer(0).with_io(|io| net.peer(0).sync.on_block_imported(io, header.hash(), &header));
	net.sync();
	assert_eq!(net.peer(0).client.backend().blockchain().info().unwrap().best_number, 1);
	assert_eq!(net.peer(1).client.backend().blockchain().info().unwrap().best_number, 1);
	let peer0_chain = net.peer(0).client.backend().blockchain().clone();
	assert!(net.peer(1).client.backend().blockchain().canon_equals_to(&peer0_chain));
	assert!(net.peer(2).client.backend().blockchain().canon_equals_to(&peer0_chain));
}

#[test]
fn blocks_are_not_announced_by_light_nodes() {
	::env_logger::init().ok();
	let mut net = TestNet::new(0);

	// full peer0 is connected to light peer
	// light peer1 is connected to full peer2
	let mut light_config = ProtocolConfig::default();
	light_config.roles = Roles::LIGHT;
	net.add_peer(&ProtocolConfig::default());
	net.add_peer(&light_config);
	net.add_peer(&ProtocolConfig::default());

	net.peer(0).push_blocks(1, false);
	net.peer(0).start();
	net.peer(1).start();
	net.peer(2).start();
	net.peer(0).on_connect(1);
	net.peer(1).on_connect(2);

	// generate block at peer0 && run sync
	while !net.done() {
		net.sync_step();
	}

	// peer 0 has the best chain
	// peer 1 has the best chain
	// peer 2 has genesis-chain only
	assert_eq!(net.peer(0).client.backend().blockchain().info().unwrap().best_number, 1);
	assert_eq!(net.peer(1).client.backend().blockchain().info().unwrap().best_number, 1);
	assert_eq!(net.peer(2).client.backend().blockchain().info().unwrap().best_number, 0);
}
