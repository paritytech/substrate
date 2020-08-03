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
use sp_core::offchain::OffchainStorage;

#[test]
fn test_bitswap_peers_connect() {
	let _ = ::env_logger::try_init();
	let mut net = TestNet::new(3);
	
	net.block_until_connected();

	for peer in 0 .. 3 {
		assert_eq!(net.peer(peer).network.bitswap_api().num_peers(), 2);
	}
}

#[test]
fn test_bitswap_peers_sending_and_cancelling_wants_works() {
	let _ = ::env_logger::try_init();
	let mut net = TestNet::new(3);

	let cid: cid::Cid = "bafkreiaapsxdkhlebw676iqic2r7fmq3gngqqcvfwh7aisvnxl7zrt24em".parse().unwrap();
	
	net.peer(0).network.bitswap_api().want_block(cid.clone(), 0);

	let peer_0 = net.peer(0).id();

	block_on(futures::future::poll_fn::<(), _>(|cx| {
		net.poll(cx);
		for peer in 1..3 {
			if !net.peer(peer).network.bitswap_api().peer_wants_cid(&peer_0, &cid) {
				return Poll::Pending
			}
		}
		Poll::Ready(())
	}));

	net.peer(0).network.bitswap_api().cancel_block(&cid);

	wait_until_x_peers_want_cid(&mut net, 0, 0..3, &cid);
}

fn wait_until_x_peers_want_cid(net: &mut TestNet, x: usize, peers: std::ops::Range<usize>, cid: &cid::Cid) {
	block_on(futures::future::poll_fn::<(), _>(|cx| {
		net.poll(cx);
		for peer in peers.clone() {
			if net.peer(peer).network.bitswap_api().num_peers_want(cid) != x {
				return Poll::Pending
			}
		}
		Poll::Ready(())
	}));
}

#[test]
fn test_bitswap_sending_blocks_works() {
	let _ = ::env_logger::try_init();
	let mut net = TestNet::new(3);

	let block = "abcdefghi".as_bytes();
	
	let hash = multihash::Code::Sha2_256.digest(block);
	let cid = cid::Cid::new_v1(cid::Codec::Raw, hash);

	net.peer(0).network.bitswap_api().want_block(cid.clone(), 0);

	wait_until_x_peers_want_cid(&mut net, 1, 1..3, &cid);

	net.peer(2).network.bitswap_api().send_block_all(&cid, block);

	wait_until_x_peers_want_cid(&mut net, 0, 0..3, &cid);

	assert_eq!(
		net.peer(0).client.offchain_storage().unwrap().get(b"bitswap", &cid.to_bytes()),
		Some(block.to_vec())
	);

	assert_eq!(
		net.peer(1).client.offchain_storage().unwrap().get(b"bitswap", &cid.to_bytes()),
		None
	);

	assert_eq!(
		net.peer(2).client.offchain_storage().unwrap().get(b"bitswap", &cid.to_bytes()),
		None
	);
}

#[test]
fn test_bitswap_sending_blocks_from_store_works() {
	let _ = ::env_logger::try_init();
	let mut net = TestNet::new(3);

	let block = "abcdefghi".as_bytes();
	
	let hash = multihash::Code::Sha2_256.digest(block);
	let cid = cid::Cid::new_v1(cid::Codec::Raw, hash);

	net.peer(2).client.offchain_storage().unwrap().set(b"bitswap", &cid.to_bytes(), block);

	net.block_until_connected();

	net.peer(0).network.bitswap_api().want_block(cid.clone(), 0);

	wait_until_x_peers_want_cid(&mut net, 1, 1..3, &cid);

	wait_until_x_peers_want_cid(&mut net, 0, 0..3, &cid);

	assert_eq!(
		net.peer(0).client.offchain_storage().unwrap().get(b"bitswap", &cid.to_bytes()),
		Some(block.to_vec())
	);

	assert_eq!(
		net.peer(1).client.offchain_storage().unwrap().get(b"bitswap", &cid.to_bytes()),
		None
	);

	assert_eq!(
		net.peer(2).client.offchain_storage().unwrap().get(b"bitswap", &cid.to_bytes()),
		Some(block.to_vec())
	);
}
