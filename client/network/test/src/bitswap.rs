// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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

use futures::executor::block_on;
use super::*;
use std::ops::Range;

fn generate_block_and_cid(string: &str) -> (&[u8], cid::Cid) {
	let block = string.as_bytes();
	let hash = multihash::Code::Sha2_256.digest(block);
	let cid = cid::Cid::new_v1(cid::Codec::Raw, hash);
	(block, cid)
}

fn wait_until_x_peers_want_cid(net: &mut TestNet, x: usize, peers: Range<usize>, cid: &cid::Cid) {
	block_on(futures::future::poll_fn::<(), _>(|cx| {
		net.poll(cx);
		for peer in peers.clone() {
			if net.peer(peer).network.bitswap_num_peers_want(cid) != x {
				return Poll::Pending
			}
		}
		Poll::Ready(())
	}));
}

#[test]
fn test_bitswap_peers_connect() {
	let _ = ::env_logger::try_init();
	let mut net = TestNet::new(3);
	
	net.block_until_connected();

	for peer in 0 .. 3 {
		assert_eq!(net.peer(peer).network.bitswap_num_peers(), 2);
	}
}

#[test]
fn test_bitswap_peers_sending_and_cancelling_wants_works() {
	let _ = ::env_logger::try_init();
	let mut net = TestNet::new(3);

	let (_, cid) = generate_block_and_cid("test_bitswap_peers_sending_and_cancelling_wants_works");
	
	net.peer(0).network_service().bitswap_want_block(cid.clone(), 0);

	let peer_0 = net.peer(0).id();

	block_on(futures::future::poll_fn::<(), _>(|cx| {
		net.poll(cx);
		for peer in 1..3 {
			if !net.peer(peer).network.bitswap_peer_wants_cid(&peer_0, &cid) {
				return Poll::Pending
			}
		}
		Poll::Ready(())
	}));

	net.peer(0).network.service().bitswap_cancel_block(cid.clone());

	wait_until_x_peers_want_cid(&mut net, 0, 0..3, &cid);
}

#[test]
fn test_bitswap_sending_blocks_works() {
	let _ = ::env_logger::try_init();
	let mut net = TestNet::new(3);

	let (block, cid) = generate_block_and_cid("test_bitswap_sending_blocks_works");
	
	net.peer(0).network.service().bitswap_want_block(cid.clone(), 0);

	wait_until_x_peers_want_cid(&mut net, 1, 1..3, &cid);

	net.peer(2).network.service()
		.bitswap_send_block_all(cid.clone(), block.to_vec().into_boxed_slice());

	wait_until_x_peers_want_cid(&mut net, 0, 0..3, &cid);

	assert_eq!(
		net.peer(0).client.bitswap_storage().unwrap().get(&cid).ok(),
		Some(block.to_vec())
	);

	assert_eq!(
		net.peer(1).client.bitswap_storage().unwrap().get(&cid).ok(),
		None
	);

	assert_eq!(
		net.peer(2).client.bitswap_storage().unwrap().get(&cid).ok(),
		None
	);
}

#[test]
fn test_bitswap_sending_blocks_from_store_works() {
	let _ = ::env_logger::try_init();
	let mut net = TestNet::new(3);

	let (block, cid) = generate_block_and_cid("test_bitswap_sending_blocks_from_store_works");
	
	net.peer(2).client.bitswap_storage().unwrap().insert(&cid, block.into()).unwrap();

	net.block_until_connected();

	net.peer(0).network.service().bitswap_want_block(cid.clone(), 0);

	wait_until_x_peers_want_cid(&mut net, 1, 1..3, &cid);

	wait_until_x_peers_want_cid(&mut net, 0, 0..3, &cid);

	assert_eq!(
		net.peer(0).client.bitswap_storage().unwrap().get(&cid).ok(),
		Some(block.to_vec())
	);

	assert_eq!(
		net.peer(1).client.bitswap_storage().unwrap().get(&cid).ok(),
		None
	);

	assert_eq!(
		net.peer(2).client.bitswap_storage().unwrap().get(&cid).ok(),
		Some(block.to_vec())
	);
}
