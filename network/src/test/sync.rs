// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

use client::backend::Backend;
use sync::SyncState;
use super::*;

#[test]
fn sync_from_two_peers_works() {
	::env_logger::init().ok();
	let mut net = TestNet::new(3);
	net.peer(1).chain.backend().push_blocks(100);
	net.peer(2).chain.backend().push_blocks(100);
	net.sync();
	assert!(net.peer(0).chain.backend().blockchain().equals_to(net.peer(1).chain.backend().blockchain()));
	let status = net.peer(0).sync.status();
	assert_eq!(status.sync.state, SyncState::Idle);
}

#[test]
fn sync_from_two_peers_with_ancestry_search_works() {
	::env_logger::init().ok();
	let mut net = TestNet::new(3);
	net.peer(0).chain.backend().generate_blocks(10, |header| header.state_root = 42.into());
	net.peer(1).chain.backend().push_blocks(100);
	net.peer(2).chain.backend().push_blocks(100);
	net.restart_peer(0);
	net.sync();
	assert!(net.peer(0).chain.backend().blockchain().canon_equals_to(net.peer(1).chain.backend().blockchain()));
}

#[test]
fn sync_long_chain_works() {
	let mut net = TestNet::new(2);
	net.peer(1).chain.backend().push_blocks(5000);
	net.sync_steps(3);
	assert_eq!(net.peer(0).sync.status().sync.state, SyncState::Downloading);
	net.sync();
	assert!(net.peer(0).chain.backend().blockchain().equals_to(net.peer(1).chain.backend().blockchain()));
}

#[test]
fn sync_no_common_longer_chain_fails() {
	::env_logger::init().ok();
	let mut net = TestNet::new(3);
	net.peer(0).chain.backend().generate_blocks(200, |header| header.state_root = 42.into());
	net.peer(1).chain.backend().push_blocks(200);
	net.sync();
	assert!(!net.peer(0).chain.backend().blockchain().canon_equals_to(net.peer(1).chain.backend().blockchain()));
}

#[test]
fn sync_after_fork_works() {
	::env_logger::init().ok();
	let mut net = TestNet::new(3);
	net.peer(0).chain.backend().push_blocks(30);
	net.peer(1).chain.backend().push_blocks(30);
	net.peer(2).chain.backend().push_blocks(30);

	net.peer(0).chain.backend().generate_blocks(10, |header| header.state_root = 42.into()); // fork
	net.peer(1).chain.backend().push_blocks(20);
	net.peer(2).chain.backend().push_blocks(20);

	net.peer(1).chain.backend().generate_blocks(10, |header| header.state_root = 42.into()); // second fork between 1 and 2
	net.peer(2).chain.backend().push_blocks(1);

	// peer 1 has the best chain
	let peer1_chain = net.peer(1).chain.backend().blockchain().clone();
	net.sync();
	assert!(net.peer(0).chain.backend().blockchain().canon_equals_to(&peer1_chain));
	assert!(net.peer(1).chain.backend().blockchain().canon_equals_to(&peer1_chain));
	assert!(net.peer(2).chain.backend().blockchain().canon_equals_to(&peer1_chain));
}

