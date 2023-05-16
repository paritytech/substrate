// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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
use futures::Future;
use sp_consensus::{block_validation::Validation, BlockOrigin};
use sp_runtime::Justifications;
use substrate_test_runtime::Header;

async fn test_ancestor_search_when_common_is(n: usize) {
	sp_tracing::try_init_simple();
	let mut net = TestNet::new(3);

	net.peer(0).push_blocks(n, false);
	net.peer(1).push_blocks(n, false);
	net.peer(2).push_blocks(n, false);

	net.peer(0).push_blocks(10, true);
	net.peer(1).push_blocks(100, false);
	net.peer(2).push_blocks(100, false);

	net.run_until_sync().await;
	let peer1 = &net.peers()[1];
	assert!(net.peers()[0].blockchain_canon_equals(peer1));
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn sync_peers_works() {
	sp_tracing::try_init_simple();
	let mut net = TestNet::new(3);

	futures::future::poll_fn::<(), _>(|cx| {
		net.poll(cx);
		for peer in 0..3 {
			if net.peer(peer).num_peers() != 2 {
				return Poll::Pending
			}
		}
		Poll::Ready(())
	})
	.await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn sync_cycle_from_offline_to_syncing_to_offline() {
	sp_tracing::try_init_simple();
	let mut net = TestNet::new(3);
	for peer in 0..3 {
		// Offline, and not major syncing.
		assert!(net.peer(peer).is_offline());
		assert!(!net.peer(peer).is_major_syncing());
	}

	// Generate blocks.
	net.peer(2).push_blocks(100, false);

	// Block until all nodes are online and nodes 0 and 1 and major syncing.
	futures::future::poll_fn::<(), _>(|cx| {
		net.poll(cx);
		for peer in 0..3 {
			// Online
			if net.peer(peer).is_offline() {
				return Poll::Pending
			}
			if peer < 2 {
				// Major syncing.
				if net.peer(peer).blocks_count() < 100 && !net.peer(peer).is_major_syncing() {
					return Poll::Pending
				}
			}
		}
		Poll::Ready(())
	})
	.await;

	// Block until all nodes are done syncing.
	futures::future::poll_fn::<(), _>(|cx| {
		net.poll(cx);
		for peer in 0..3 {
			if net.peer(peer).is_major_syncing() {
				return Poll::Pending
			}
		}
		Poll::Ready(())
	})
	.await;

	// Now drop nodes 1 and 2, and check that node 0 is offline.
	net.peers.remove(2);
	net.peers.remove(1);
	futures::future::poll_fn::<(), _>(|cx| {
		net.poll(cx);
		if !net.peer(0).is_offline() {
			Poll::Pending
		} else {
			Poll::Ready(())
		}
	})
	.await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn syncing_node_not_major_syncing_when_disconnected() {
	sp_tracing::try_init_simple();
	let mut net = TestNet::new(3);

	// Generate blocks.
	net.peer(2).push_blocks(100, false);

	// Check that we're not major syncing when disconnected.
	assert!(!net.peer(1).is_major_syncing());

	// Check that we switch to major syncing.
	futures::future::poll_fn::<(), _>(|cx| {
		net.poll(cx);
		if !net.peer(1).is_major_syncing() {
			Poll::Pending
		} else {
			Poll::Ready(())
		}
	})
	.await;

	// Destroy two nodes, and check that we switch to non-major syncing.
	net.peers.remove(2);
	net.peers.remove(0);
	futures::future::poll_fn::<(), _>(|cx| {
		net.poll(cx);
		if net.peer(0).is_major_syncing() {
			Poll::Pending
		} else {
			Poll::Ready(())
		}
	})
	.await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn sync_from_two_peers_works() {
	sp_tracing::try_init_simple();
	let mut net = TestNet::new(3);
	net.peer(1).push_blocks(100, false);
	net.peer(2).push_blocks(100, false);
	net.run_until_sync().await;
	let peer1 = &net.peers()[1];
	assert!(net.peers()[0].blockchain_canon_equals(peer1));
	assert!(!net.peer(0).is_major_syncing());
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn sync_from_two_peers_with_ancestry_search_works() {
	sp_tracing::try_init_simple();
	let mut net = TestNet::new(3);
	net.peer(0).push_blocks(10, true);
	net.peer(1).push_blocks(100, false);
	net.peer(2).push_blocks(100, false);
	net.run_until_sync().await;
	let peer1 = &net.peers()[1];
	assert!(net.peers()[0].blockchain_canon_equals(peer1));
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn ancestry_search_works_when_backoff_is_one() {
	sp_tracing::try_init_simple();
	let mut net = TestNet::new(3);

	net.peer(0).push_blocks(1, false);
	net.peer(1).push_blocks(2, false);
	net.peer(2).push_blocks(2, false);

	net.run_until_sync().await;
	let peer1 = &net.peers()[1];
	assert!(net.peers()[0].blockchain_canon_equals(peer1));
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn ancestry_search_works_when_ancestor_is_genesis() {
	sp_tracing::try_init_simple();
	let mut net = TestNet::new(3);

	net.peer(0).push_blocks(13, true);
	net.peer(1).push_blocks(100, false);
	net.peer(2).push_blocks(100, false);

	net.run_until_sync().await;
	let peer1 = &net.peers()[1];
	assert!(net.peers()[0].blockchain_canon_equals(peer1));
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn ancestry_search_works_when_common_is_one() {
	test_ancestor_search_when_common_is(1).await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn ancestry_search_works_when_common_is_two() {
	test_ancestor_search_when_common_is(2).await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn ancestry_search_works_when_common_is_hundred() {
	test_ancestor_search_when_common_is(100).await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn sync_long_chain_works() {
	sp_tracing::try_init_simple();
	let mut net = TestNet::new(2);
	net.peer(1).push_blocks(500, false);
	net.run_until_sync().await;
	let peer1 = &net.peers()[1];
	assert!(net.peers()[0].blockchain_canon_equals(peer1));
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn sync_no_common_longer_chain_fails() {
	sp_tracing::try_init_simple();
	let mut net = TestNet::new(3);
	net.peer(0).push_blocks(20, true);
	net.peer(1).push_blocks(20, false);
	futures::future::poll_fn::<(), _>(|cx| {
		net.poll(cx);
		if net.peer(0).is_major_syncing() {
			Poll::Pending
		} else {
			Poll::Ready(())
		}
	})
	.await;
	let peer1 = &net.peers()[1];
	assert!(!net.peers()[0].blockchain_canon_equals(peer1));
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn sync_justifications() {
	sp_tracing::try_init_simple();
	let mut net = JustificationTestNet::new(3);
	let hashes = net.peer(0).push_blocks(20, false);
	net.run_until_sync().await;

	let hashof10 = hashes[9];
	let hashof15 = hashes[14];
	let hashof20 = hashes[19];

	// there's currently no justification for block #10
	assert_eq!(net.peer(0).client().justifications(hashof10).unwrap(), None);
	assert_eq!(net.peer(1).client().justifications(hashof10).unwrap(), None);

	// we finalize block #10, #15 and #20 for peer 0 with a justification
	let just = (*b"FRNK", Vec::new());
	net.peer(0).client().finalize_block(hashof10, Some(just.clone()), true).unwrap();
	net.peer(0).client().finalize_block(hashof15, Some(just.clone()), true).unwrap();
	net.peer(0).client().finalize_block(hashof20, Some(just.clone()), true).unwrap();

	let hashof10 = net.peer(1).client().as_client().hash(10).unwrap().unwrap();
	let hashof15 = net.peer(1).client().as_client().hash(15).unwrap().unwrap();
	let hashof20 = net.peer(1).client().as_client().hash(20).unwrap().unwrap();

	// peer 1 should get the justifications from the network
	net.peer(1).request_justification(&hashof10, 10);
	net.peer(1).request_justification(&hashof15, 15);
	net.peer(1).request_justification(&hashof20, 20);

	futures::future::poll_fn::<(), _>(|cx| {
		net.poll(cx);

		for height in (10..21).step_by(5) {
			if net.peer(0).client().justifications(hashes[height - 1]).unwrap() !=
				Some(Justifications::from((*b"FRNK", Vec::new())))
			{
				return Poll::Pending
			}
			if net.peer(1).client().justifications(hashes[height - 1]).unwrap() !=
				Some(Justifications::from((*b"FRNK", Vec::new())))
			{
				return Poll::Pending
			}
		}

		Poll::Ready(())
	})
	.await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn sync_justifications_across_forks() {
	sp_tracing::try_init_simple();
	let mut net = JustificationTestNet::new(3);
	// we push 5 blocks
	net.peer(0).push_blocks(5, false);
	// and then two forks 5 and 6 blocks long
	let f1_best = net.peer(0).push_blocks_at(BlockId::Number(5), 5, false).pop().unwrap();
	let f2_best = net.peer(0).push_blocks_at(BlockId::Number(5), 6, false).pop().unwrap();

	// peer 1 will only see the longer fork. but we'll request justifications
	// for both and finalize the small fork instead.
	net.run_until_sync().await;

	let just = (*b"FRNK", Vec::new());
	net.peer(0).client().finalize_block(f1_best, Some(just), true).unwrap();

	net.peer(1).request_justification(&f1_best, 10);
	net.peer(1).request_justification(&f2_best, 11);

	futures::future::poll_fn::<(), _>(|cx| {
		net.poll(cx);

		if net.peer(0).client().justifications(f1_best).unwrap() ==
			Some(Justifications::from((*b"FRNK", Vec::new()))) &&
			net.peer(1).client().justifications(f1_best).unwrap() ==
				Some(Justifications::from((*b"FRNK", Vec::new())))
		{
			Poll::Ready(())
		} else {
			Poll::Pending
		}
	})
	.await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn sync_after_fork_works() {
	sp_tracing::try_init_simple();
	let mut net = TestNet::new(3);
	net.peer(0).push_blocks(30, false);
	net.peer(1).push_blocks(30, false);
	net.peer(2).push_blocks(30, false);

	net.peer(0).push_blocks(10, true);
	net.peer(1).push_blocks(20, false);
	net.peer(2).push_blocks(20, false);

	net.peer(1).push_blocks(10, true);
	net.peer(2).push_blocks(1, false);

	// peer 1 has the best chain
	net.run_until_sync().await;
	let peer1 = &net.peers()[1];
	assert!(net.peers()[0].blockchain_canon_equals(peer1));
	(net.peers()[1].blockchain_canon_equals(peer1));
	(net.peers()[2].blockchain_canon_equals(peer1));
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn syncs_all_forks() {
	sp_tracing::try_init_simple();
	let mut net = TestNet::new(4);
	net.peer(0).push_blocks(2, false);
	net.peer(1).push_blocks(2, false);

	let b1 = net.peer(0).push_blocks(2, true).pop().unwrap();
	let b2 = net.peer(1).push_blocks(4, false).pop().unwrap();

	net.run_until_sync().await;
	// Check that all peers have all of the branches.
	assert!(net.peer(0).has_block(b1));
	assert!(net.peer(0).has_block(b2));
	assert!(net.peer(1).has_block(b1));
	assert!(net.peer(1).has_block(b2));
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn own_blocks_are_announced() {
	sp_tracing::try_init_simple();
	let mut net = TestNet::new(3);
	net.run_until_sync().await; // connect'em
	net.peer(0)
		.generate_blocks(1, BlockOrigin::Own, |builder| builder.build().unwrap().block);

	net.run_until_sync().await;

	assert_eq!(net.peer(0).client.info().best_number, 1);
	assert_eq!(net.peer(1).client.info().best_number, 1);
	let peer0 = &net.peers()[0];
	assert!(net.peers()[1].blockchain_canon_equals(peer0));
	(net.peers()[2].blockchain_canon_equals(peer0));
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn can_sync_small_non_best_forks() {
	sp_tracing::try_init_simple();
	let mut net = TestNet::new(2);
	net.peer(0).push_blocks(30, false);
	net.peer(1).push_blocks(30, false);

	// small fork + reorg on peer 1.
	net.peer(0).push_blocks_at(BlockId::Number(30), 2, true);
	let small_hash = net.peer(0).client().info().best_hash;
	net.peer(0).push_blocks_at(BlockId::Number(30), 10, false);
	assert_eq!(net.peer(0).client().info().best_number, 40);

	// peer 1 only ever had the long fork.
	net.peer(1).push_blocks(10, false);
	assert_eq!(net.peer(1).client().info().best_number, 40);

	assert!(net.peer(0).client().header(small_hash).unwrap().is_some());
	assert!(net.peer(1).client().header(small_hash).unwrap().is_none());

	// poll until the two nodes connect, otherwise announcing the block will not work
	futures::future::poll_fn::<(), _>(|cx| {
		net.poll(cx);
		if net.peer(0).num_peers() == 0 || net.peer(1).num_peers() == 0 {
			Poll::Pending
		} else {
			Poll::Ready(())
		}
	})
	.await;

	// synchronization: 0 synced to longer chain and 1 didn't sync to small chain.

	assert_eq!(net.peer(0).client().info().best_number, 40);

	assert!(net.peer(0).client().header(small_hash).unwrap().is_some());
	assert!(!net.peer(1).client().header(small_hash).unwrap().is_some());

	net.peer(0).announce_block(small_hash, None);

	// after announcing, peer 1 downloads the block.

	futures::future::poll_fn::<(), _>(|cx| {
		net.poll(cx);

		assert!(net.peer(0).client().header(small_hash).unwrap().is_some());
		if net.peer(1).client().header(small_hash).unwrap().is_none() {
			return Poll::Pending
		}
		Poll::Ready(())
	})
	.await;
	net.run_until_sync().await;

	let another_fork = net.peer(0).push_blocks_at(BlockId::Number(35), 2, true).pop().unwrap();
	net.peer(0).announce_block(another_fork, None);
	futures::future::poll_fn::<(), _>(|cx| {
		net.poll(cx);
		if net.peer(1).client().header(another_fork).unwrap().is_none() {
			return Poll::Pending
		}
		Poll::Ready(())
	})
	.await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn can_sync_forks_ahead_of_the_best_chain() {
	sp_tracing::try_init_simple();
	let mut net = TestNet::new(2);
	net.peer(0).push_blocks(1, false);
	net.peer(1).push_blocks(1, false);

	net.run_until_connected().await;
	// Peer 0 is on 2-block fork which is announced with is_best=false
	let fork_hash = net
		.peer(0)
		.generate_blocks_with_fork_choice(
			2,
			BlockOrigin::Own,
			|builder| builder.build().unwrap().block,
			ForkChoiceStrategy::Custom(false),
		)
		.pop()
		.unwrap();
	// Peer 1 is on 1-block fork
	net.peer(1).push_blocks(1, false);
	assert!(net.peer(0).client().header(fork_hash).unwrap().is_some());
	assert_eq!(net.peer(0).client().info().best_number, 1);
	assert_eq!(net.peer(1).client().info().best_number, 2);

	// after announcing, peer 1 downloads the block.
	futures::future::poll_fn::<(), _>(|cx| {
		net.poll(cx);

		if net.peer(1).client().header(fork_hash).unwrap().is_none() {
			return Poll::Pending
		}
		Poll::Ready(())
	})
	.await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn can_sync_explicit_forks() {
	sp_tracing::try_init_simple();
	let mut net = TestNet::new(2);
	net.peer(0).push_blocks(30, false);
	net.peer(1).push_blocks(30, false);

	// small fork + reorg on peer 1.
	net.peer(0).push_blocks_at(BlockId::Number(30), 2, true);
	let small_hash = net.peer(0).client().info().best_hash;
	let small_number = net.peer(0).client().info().best_number;
	net.peer(0).push_blocks_at(BlockId::Number(30), 10, false);
	assert_eq!(net.peer(0).client().info().best_number, 40);

	// peer 1 only ever had the long fork.
	net.peer(1).push_blocks(10, false);
	assert_eq!(net.peer(1).client().info().best_number, 40);

	assert!(net.peer(0).client().header(small_hash).unwrap().is_some());
	assert!(net.peer(1).client().header(small_hash).unwrap().is_none());

	// poll until the two nodes connect, otherwise announcing the block will not work
	futures::future::poll_fn::<(), _>(|cx| {
		net.poll(cx);
		if net.peer(0).num_peers() == 0 || net.peer(1).num_peers() == 0 {
			Poll::Pending
		} else {
			Poll::Ready(())
		}
	})
	.await;

	// synchronization: 0 synced to longer chain and 1 didn't sync to small chain.

	assert_eq!(net.peer(0).client().info().best_number, 40);

	assert!(net.peer(0).client().header(small_hash).unwrap().is_some());
	assert!(!net.peer(1).client().header(small_hash).unwrap().is_some());

	// request explicit sync
	let first_peer_id = net.peer(0).id();
	net.peer(1).set_sync_fork_request(vec![first_peer_id], small_hash, small_number);

	// peer 1 downloads the block.
	futures::future::poll_fn::<(), _>(|cx| {
		net.poll(cx);

		assert!(net.peer(0).client().header(small_hash).unwrap().is_some());
		if net.peer(1).client().header(small_hash).unwrap().is_none() {
			return Poll::Pending
		}
		Poll::Ready(())
	})
	.await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn syncs_header_only_forks() {
	sp_tracing::try_init_simple();
	let mut net = TestNet::new(0);
	net.add_full_peer_with_config(Default::default());
	net.add_full_peer_with_config(FullPeerConfig { blocks_pruning: Some(3), ..Default::default() });
	net.peer(0).push_blocks(2, false);
	net.peer(1).push_blocks(2, false);

	net.peer(0).push_blocks(2, true);
	let small_hash = net.peer(0).client().info().best_hash;
	net.peer(1).push_blocks(4, false);

	// Peer 1 will sync the small fork even though common block state is missing
	while !net.peer(1).has_block(small_hash) {
		net.run_until_idle().await;
	}

	net.run_until_sync().await;
	assert_eq!(net.peer(0).client().info().best_hash, net.peer(1).client().info().best_hash);
	assert_ne!(small_hash, net.peer(0).client().info().best_hash);
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn does_not_sync_announced_old_best_block() {
	sp_tracing::try_init_simple();
	let mut net = TestNet::new(3);

	let old_hash = net.peer(0).push_blocks(1, false).pop().unwrap();
	let old_hash_with_parent = net.peer(0).push_blocks(1, false).pop().unwrap();
	net.peer(0).push_blocks(18, true);
	net.peer(1).push_blocks(20, true);

	net.peer(0).announce_block(old_hash, None);
	futures::future::poll_fn::<(), _>(|cx| {
		// poll once to import announcement
		net.poll(cx);
		Poll::Ready(())
	})
	.await;
	assert!(!net.peer(1).is_major_syncing());

	net.peer(0).announce_block(old_hash_with_parent, None);
	futures::future::poll_fn::<(), _>(|cx| {
		// poll once to import announcement
		net.poll(cx);
		Poll::Ready(())
	})
	.await;
	assert!(!net.peer(1).is_major_syncing());
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn full_sync_requires_block_body() {
	// Check that we don't sync headers-only in full mode.
	sp_tracing::try_init_simple();
	let mut net = TestNet::new(2);

	net.peer(0).push_headers(1);
	// Wait for nodes to connect
	futures::future::poll_fn::<(), _>(|cx| {
		net.poll(cx);
		if net.peer(0).num_peers() == 0 || net.peer(1).num_peers() == 0 {
			Poll::Pending
		} else {
			Poll::Ready(())
		}
	})
	.await;
	net.run_until_idle().await;
	assert_eq!(net.peer(1).client.info().best_number, 0);
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn imports_stale_once() {
	sp_tracing::try_init_simple();

	async fn import_with_announce(net: &mut TestNet, hash: H256) {
		// Announce twice
		net.peer(0).announce_block(hash, None);
		net.peer(0).announce_block(hash, None);

		futures::future::poll_fn::<(), _>(|cx| {
			net.poll(cx);
			if net.peer(1).client().header(hash).unwrap().is_some() {
				Poll::Ready(())
			} else {
				Poll::Pending
			}
		})
		.await;
	}

	// given the network with 2 full nodes
	let mut net = TestNet::new(2);

	// let them connect to each other
	net.run_until_sync().await;

	// check that NEW block is imported from announce message
	let new_hash = net.peer(0).push_blocks(1, false).pop().unwrap();
	import_with_announce(&mut net, new_hash).await;
	assert_eq!(net.peer(1).num_downloaded_blocks().await, 1);

	// check that KNOWN STALE block is imported from announce message
	let known_stale_hash = net.peer(0).push_blocks_at(BlockId::Number(0), 1, true).pop().unwrap();
	import_with_announce(&mut net, known_stale_hash).await;
	assert_eq!(net.peer(1).num_downloaded_blocks().await, 2);
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn can_sync_to_peers_with_wrong_common_block() {
	sp_tracing::try_init_simple();
	let mut net = TestNet::new(2);

	net.peer(0).push_blocks(2, true);
	net.peer(1).push_blocks(2, true);
	let fork_hash = net.peer(0).push_blocks_at(BlockId::Number(0), 2, false).pop().unwrap();
	net.peer(1).push_blocks_at(BlockId::Number(0), 2, false);
	// wait for connection
	net.run_until_connected().await;

	// both peers re-org to the same fork without notifying each other
	let just = Some((*b"FRNK", Vec::new()));
	net.peer(0).client().finalize_block(fork_hash, just.clone(), true).unwrap();
	net.peer(1).client().finalize_block(fork_hash, just, true).unwrap();
	let final_hash = net.peer(0).push_blocks(1, false).pop().unwrap();

	net.run_until_sync().await;

	assert!(net.peer(1).has_block(final_hash));
}

/// Returns `is_new_best = true` for each validated announcement.
struct NewBestBlockAnnounceValidator;

impl BlockAnnounceValidator<Block> for NewBestBlockAnnounceValidator {
	fn validate(
		&mut self,
		_: &Header,
		_: &[u8],
	) -> Pin<Box<dyn Future<Output = Result<Validation, Box<dyn std::error::Error + Send>>> + Send>>
	{
		async { Ok(Validation::Success { is_new_best: true }) }.boxed()
	}
}

/// Returns `Validation::Failure` for specified block number
struct FailingBlockAnnounceValidator(u64);

impl BlockAnnounceValidator<Block> for FailingBlockAnnounceValidator {
	fn validate(
		&mut self,
		header: &Header,
		_: &[u8],
	) -> Pin<Box<dyn Future<Output = Result<Validation, Box<dyn std::error::Error + Send>>> + Send>>
	{
		let number = *header.number();
		let target_number = self.0;
		async move {
			Ok(if number == target_number {
				Validation::Failure { disconnect: false }
			} else {
				Validation::Success { is_new_best: true }
			})
		}
		.boxed()
	}
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn sync_blocks_when_block_announce_validator_says_it_is_new_best() {
	sp_tracing::try_init_simple();
	let mut net = TestNet::new(0);
	net.add_full_peer_with_config(Default::default());
	net.add_full_peer_with_config(Default::default());
	net.add_full_peer_with_config(FullPeerConfig {
		block_announce_validator: Some(Box::new(NewBestBlockAnnounceValidator)),
		..Default::default()
	});

	net.run_until_connected().await;

	// Add blocks but don't set them as best
	let block_hash = net
		.peer(0)
		.generate_blocks_with_fork_choice(
			1,
			BlockOrigin::Own,
			|builder| builder.build().unwrap().block,
			ForkChoiceStrategy::Custom(false),
		)
		.pop()
		.unwrap();

	while !net.peer(2).has_block(block_hash) {
		net.run_until_idle().await;
	}
}

/// Waits for some time until the validation is successfull.
struct DeferredBlockAnnounceValidator;

impl BlockAnnounceValidator<Block> for DeferredBlockAnnounceValidator {
	fn validate(
		&mut self,
		_: &Header,
		_: &[u8],
	) -> Pin<Box<dyn Future<Output = Result<Validation, Box<dyn std::error::Error + Send>>> + Send>>
	{
		async {
			futures_timer::Delay::new(std::time::Duration::from_millis(500)).await;
			Ok(Validation::Success { is_new_best: false })
		}
		.boxed()
	}
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn wait_until_deferred_block_announce_validation_is_ready() {
	sp_tracing::try_init_simple();
	let mut net = TestNet::new(0);
	net.add_full_peer_with_config(Default::default());
	net.add_full_peer_with_config(FullPeerConfig {
		block_announce_validator: Some(Box::new(NewBestBlockAnnounceValidator)),
		..Default::default()
	});

	net.run_until_connected().await;

	// Add blocks but don't set them as best
	let block_hash = net
		.peer(0)
		.generate_blocks_with_fork_choice(
			1,
			BlockOrigin::Own,
			|builder| builder.build().unwrap().block,
			ForkChoiceStrategy::Custom(false),
		)
		.pop()
		.unwrap();

	while !net.peer(1).has_block(block_hash) {
		net.run_until_idle().await;
	}
}

/// When we don't inform the sync protocol about the best block, a node will not sync from us as the
/// handshake is not does not contain our best block.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn sync_to_tip_requires_that_sync_protocol_is_informed_about_best_block() {
	sp_tracing::try_init_simple();
	let mut net = TestNet::new(1);

	// Produce some blocks
	let block_hash = net
		.peer(0)
		.push_blocks_at_without_informing_sync(BlockId::Number(0), 3, true, true)
		.pop()
		.unwrap();

	// Add a node and wait until they are connected
	net.add_full_peer_with_config(Default::default());
	net.run_until_connected().await;
	net.run_until_idle().await;

	// The peer should not have synced the block.
	assert!(!net.peer(1).has_block(block_hash));

	// Make sync protocol aware of the best block
	net.peer(0).sync_service().new_best_block_imported(block_hash, 3);
	net.run_until_idle().await;

	// Connect another node that should now sync to the tip
	net.add_full_peer_with_config(FullPeerConfig {
		connect_to_peers: Some(vec![0]),
		..Default::default()
	});

	futures::future::poll_fn::<(), _>(|cx| {
		net.poll(cx);
		if net.peer(2).has_block(block_hash) {
			Poll::Ready(())
		} else {
			Poll::Pending
		}
	})
	.await;

	// However peer 1 should still not have the block.
	assert!(!net.peer(1).has_block(block_hash));
}

/// Ensures that if we as a syncing node sync to the tip while we are connected to another peer
/// that is currently also doing a major sync.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn sync_to_tip_when_we_sync_together_with_multiple_peers() {
	sp_tracing::try_init_simple();

	let mut net = TestNet::new(3);

	let block_hash = net
		.peer(0)
		.push_blocks_at_without_informing_sync(BlockId::Number(0), 10_000, false, false)
		.pop()
		.unwrap();

	net.peer(1)
		.push_blocks_at_without_informing_sync(BlockId::Number(0), 5_000, false, false);

	net.run_until_connected().await;
	net.run_until_idle().await;

	assert!(!net.peer(2).has_block(block_hash));

	net.peer(0).sync_service().new_best_block_imported(block_hash, 10_000);
	net.peer(0).sync_service().announce_block(block_hash, None);

	while !net.peer(2).has_block(block_hash) && !net.peer(1).has_block(block_hash) {
		net.run_until_idle().await;
	}
}

/// Ensures that when we receive a block announcement with some data attached, that we propagate
/// this data when reannouncing the block.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn block_announce_data_is_propagated() {
	struct TestBlockAnnounceValidator;

	impl BlockAnnounceValidator<Block> for TestBlockAnnounceValidator {
		fn validate(
			&mut self,
			_: &Header,
			data: &[u8],
		) -> Pin<
			Box<dyn Future<Output = Result<Validation, Box<dyn std::error::Error + Send>>> + Send>,
		> {
			let correct = data.get(0) == Some(&137);
			async move {
				if correct {
					Ok(Validation::Success { is_new_best: true })
				} else {
					Ok(Validation::Failure { disconnect: false })
				}
			}
			.boxed()
		}
	}

	sp_tracing::try_init_simple();
	let mut net = TestNet::new(1);

	net.add_full_peer_with_config(FullPeerConfig {
		block_announce_validator: Some(Box::new(TestBlockAnnounceValidator)),
		..Default::default()
	});

	net.add_full_peer_with_config(FullPeerConfig {
		block_announce_validator: Some(Box::new(TestBlockAnnounceValidator)),
		connect_to_peers: Some(vec![1]),
		..Default::default()
	});

	// Wait until peer 1 is connected to both nodes.
	futures::future::poll_fn::<(), _>(|cx| {
		net.poll(cx);
		if net.peer(1).num_peers() == 2 &&
			net.peer(0).num_peers() == 1 &&
			net.peer(2).num_peers() == 1
		{
			Poll::Ready(())
		} else {
			Poll::Pending
		}
	})
	.await;

	let block_hash = net
		.peer(0)
		.push_blocks_at_without_announcing(BlockId::Number(0), 1, true)
		.pop()
		.unwrap();
	net.peer(0).announce_block(block_hash, Some(vec![137]));

	while !net.peer(1).has_block(block_hash) || !net.peer(2).has_block(block_hash) {
		net.run_until_idle().await;
	}
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn continue_to_sync_after_some_block_announcement_verifications_failed() {
	struct TestBlockAnnounceValidator;

	impl BlockAnnounceValidator<Block> for TestBlockAnnounceValidator {
		fn validate(
			&mut self,
			header: &Header,
			_: &[u8],
		) -> Pin<
			Box<dyn Future<Output = Result<Validation, Box<dyn std::error::Error + Send>>> + Send>,
		> {
			let number = *header.number();
			async move {
				if number < 100 {
					Err(Box::<dyn std::error::Error + Send + Sync>::from(String::from("error"))
						as Box<_>)
				} else {
					Ok(Validation::Success { is_new_best: false })
				}
			}
			.boxed()
		}
	}

	sp_tracing::try_init_simple();
	let mut net = TestNet::new(1);

	net.add_full_peer_with_config(FullPeerConfig {
		block_announce_validator: Some(Box::new(TestBlockAnnounceValidator)),
		..Default::default()
	});

	net.run_until_connected().await;
	net.run_until_idle().await;

	let block_hash = net.peer(0).push_blocks(500, true).pop().unwrap();

	net.run_until_sync().await;
	assert!(net.peer(1).has_block(block_hash));
}

/// When being spammed by the same request of a peer, we ban this peer. However, we should only ban
/// this peer if the request was successful. In the case of a justification request for example,
/// we ask our peers multiple times until we got the requested justification. This test ensures that
/// asking for the same justification multiple times doesn't ban a peer.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn multiple_requests_are_accepted_as_long_as_they_are_not_fulfilled() {
	sp_tracing::try_init_simple();
	let mut net = JustificationTestNet::new(2);
	let hashes = net.peer(0).push_blocks(10, false);
	net.run_until_sync().await;

	// there's currently no justification for block #10
	let hashof10 = hashes[9];
	assert_eq!(net.peer(0).client().justifications(hashof10).unwrap(), None);
	assert_eq!(net.peer(1).client().justifications(hashof10).unwrap(), None);

	// Let's assume block 10 was finalized, but we still need the justification from the network.
	net.peer(1).request_justification(&hashof10, 10);

	// Let's build some more blocks and wait always for the network to have synced them
	for _ in 0..5 {
		// We need to sleep 10 seconds as this is the time we wait between sending a new
		// justification request.
		tokio::time::sleep(tokio::time::Duration::from_secs(10)).await;
		net.peer(0).push_blocks(1, false);
		net.run_until_sync().await;
		assert_eq!(1, net.peer(0).num_peers());
	}

	let hashof10 = hashes[9];
	// Finalize the 10th block and make the justification available.
	net.peer(0)
		.client()
		.finalize_block(hashof10, Some((*b"FRNK", Vec::new())), true)
		.unwrap();

	futures::future::poll_fn::<(), _>(|cx| {
		net.poll(cx);

		if net.peer(1).client().justifications(hashof10).unwrap() !=
			Some(Justifications::from((*b"FRNK", Vec::new())))
		{
			return Poll::Pending
		}

		Poll::Ready(())
	})
	.await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn syncs_all_forks_from_single_peer() {
	sp_tracing::try_init_simple();
	let mut net = TestNet::new(2);
	net.peer(0).push_blocks(10, false);
	net.peer(1).push_blocks(10, false);

	// poll until the two nodes connect, otherwise announcing the block will not work
	net.run_until_connected().await;

	// Peer 0 produces new blocks and announces.
	let branch1 = net.peer(0).push_blocks_at(BlockId::Number(10), 2, true).pop().unwrap();

	// Wait till peer 1 starts downloading
	loop {
		futures::future::poll_fn::<(), _>(|cx| {
			net.poll(cx);
			Poll::Ready(())
		})
		.await;

		if net.peer(1).sync_service().best_seen_block().await.unwrap() == Some(12) {
			break
		}
	}

	// Peer 0 produces and announces another fork
	let branch2 = net.peer(0).push_blocks_at(BlockId::Number(10), 2, false).pop().unwrap();

	net.run_until_sync().await;

	// Peer 1 should have both branches,
	assert!(net.peer(1).client().header(branch1).unwrap().is_some());
	assert!(net.peer(1).client().header(branch2).unwrap().is_some());
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn syncs_after_missing_announcement() {
	sp_tracing::try_init_simple();
	let mut net = TestNet::new(0);
	net.add_full_peer_with_config(Default::default());
	// Set peer 1 to ignore announcement
	net.add_full_peer_with_config(FullPeerConfig {
		block_announce_validator: Some(Box::new(FailingBlockAnnounceValidator(11))),
		..Default::default()
	});
	net.peer(0).push_blocks(10, false);
	net.peer(1).push_blocks(10, false);

	net.run_until_connected().await;

	// Peer 0 produces a new block and announces. Peer 1 ignores announcement.
	net.peer(0).push_blocks_at(BlockId::Number(10), 1, false);
	// Peer 0 produces another block and announces.
	let final_block = net.peer(0).push_blocks_at(BlockId::Number(11), 1, false).pop().unwrap();
	net.peer(1).push_blocks_at(BlockId::Number(10), 1, true);
	net.run_until_sync().await;
	assert!(net.peer(1).client().header(final_block).unwrap().is_some());
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn syncs_state() {
	sp_tracing::try_init_simple();
	for skip_proofs in &[false, true] {
		let mut net = TestNet::new(0);
		let mut genesis_storage: sp_core::storage::Storage = Default::default();
		genesis_storage.top.insert(b"additional_key".to_vec(), vec![1]);
		let mut child_data: std::collections::BTreeMap<Vec<u8>, Vec<u8>> = Default::default();
		for i in 0u8..16 {
			child_data.insert(vec![i; 5], vec![i; 33]);
		}
		let child1 = sp_core::storage::StorageChild {
			data: child_data.clone(),
			child_info: sp_core::storage::ChildInfo::new_default(b"child1"),
		};
		let child3 = sp_core::storage::StorageChild {
			data: child_data.clone(),
			child_info: sp_core::storage::ChildInfo::new_default(b"child3"),
		};
		for i in 22u8..33 {
			child_data.insert(vec![i; 5], vec![i; 33]);
		}
		let child2 = sp_core::storage::StorageChild {
			data: child_data.clone(),
			child_info: sp_core::storage::ChildInfo::new_default(b"child2"),
		};
		genesis_storage
			.children_default
			.insert(child1.child_info.storage_key().to_vec(), child1);
		genesis_storage
			.children_default
			.insert(child2.child_info.storage_key().to_vec(), child2);
		genesis_storage
			.children_default
			.insert(child3.child_info.storage_key().to_vec(), child3);
		let mut config_one = FullPeerConfig::default();
		config_one.extra_storage = Some(genesis_storage.clone());
		net.add_full_peer_with_config(config_one);
		let mut config_two = FullPeerConfig::default();
		config_two.extra_storage = Some(genesis_storage);
		config_two.sync_mode =
			SyncMode::Fast { skip_proofs: *skip_proofs, storage_chain_mode: false };
		net.add_full_peer_with_config(config_two);
		let hashes = net.peer(0).push_blocks(64, false);
		// Wait for peer 1 to sync header chain.
		net.run_until_sync().await;
		assert!(!net.peer(1).client().has_state_at(&BlockId::Number(64)));

		let just = (*b"FRNK", Vec::new());
		let hashof60 = hashes[59];
		net.peer(1).client().finalize_block(hashof60, Some(just), true).unwrap();
		// Wait for state sync.
		futures::future::poll_fn::<(), _>(|cx| {
			net.poll(cx);
			if net.peer(1).client.info().finalized_state.is_some() {
				Poll::Ready(())
			} else {
				Poll::Pending
			}
		})
		.await;
		assert!(!net.peer(1).client().has_state_at(&BlockId::Number(64)));
		// Wait for the rest of the states to be imported.
		futures::future::poll_fn::<(), _>(|cx| {
			net.poll(cx);
			if net.peer(1).client().has_state_at(&BlockId::Number(64)) {
				Poll::Ready(())
			} else {
				Poll::Pending
			}
		})
		.await;
	}
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn syncs_indexed_blocks() {
	use sp_runtime::traits::Hash;
	sp_tracing::try_init_simple();
	let mut net = TestNet::new(0);
	let mut n: u64 = 0;
	net.add_full_peer_with_config(FullPeerConfig { storage_chain: true, ..Default::default() });
	net.add_full_peer_with_config(FullPeerConfig {
		storage_chain: true,
		sync_mode: SyncMode::Fast { skip_proofs: false, storage_chain_mode: true },
		..Default::default()
	});
	net.peer(0).generate_blocks_at(
		BlockId::number(0),
		64,
		BlockOrigin::Own,
		|mut builder| {
			let ex = ExtrinsicBuilder::new_indexed_call(n.to_le_bytes().to_vec()).nonce(n).build();
			n += 1;
			builder.push(ex).unwrap();
			builder.build().unwrap().block
		},
		false,
		true,
		true,
		ForkChoiceStrategy::LongestChain,
	);
	let indexed_key = sp_runtime::traits::BlakeTwo256::hash(&42u64.to_le_bytes());
	assert!(net
		.peer(0)
		.client()
		.as_client()
		.indexed_transaction(indexed_key)
		.unwrap()
		.is_some());
	assert!(net
		.peer(1)
		.client()
		.as_client()
		.indexed_transaction(indexed_key)
		.unwrap()
		.is_none());

	net.run_until_sync().await;
	assert!(net
		.peer(1)
		.client()
		.as_client()
		.indexed_transaction(indexed_key)
		.unwrap()
		.is_some());
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn warp_sync() {
	sp_tracing::try_init_simple();
	let mut net = TestNet::new(0);
	// Create 3 synced peers and 1 peer trying to warp sync.
	net.add_full_peer_with_config(Default::default());
	net.add_full_peer_with_config(Default::default());
	net.add_full_peer_with_config(Default::default());
	net.add_full_peer_with_config(FullPeerConfig {
		sync_mode: SyncMode::Warp,
		..Default::default()
	});
	let gap_end = net.peer(0).push_blocks(63, false).pop().unwrap();
	let target = net.peer(0).push_blocks(1, false).pop().unwrap();
	net.peer(1).push_blocks(64, false);
	net.peer(2).push_blocks(64, false);
	// Wait for peer 1 to sync state.
	net.run_until_sync().await;
	assert!(!net.peer(3).client().has_state_at(&BlockId::Number(1)));
	assert!(net.peer(3).client().has_state_at(&BlockId::Number(64)));

	// Wait for peer 1 download block history
	futures::future::poll_fn::<(), _>(|cx| {
		net.poll(cx);
		if net.peer(3).has_body(gap_end) && net.peer(3).has_body(target) {
			Poll::Ready(())
		} else {
			Poll::Pending
		}
	})
	.await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn warp_sync_to_target_block() {
	sp_tracing::try_init_simple();
	let mut net = TestNet::new(0);
	// Create 3 synced peers and 1 peer trying to warp sync.
	net.add_full_peer_with_config(Default::default());
	net.add_full_peer_with_config(Default::default());
	net.add_full_peer_with_config(Default::default());

	let blocks = net.peer(0).push_blocks(64, false);
	let target = blocks[63];
	net.peer(1).push_blocks(64, false);
	net.peer(2).push_blocks(64, false);

	let target_block = net.peer(0).client.header(target).unwrap().unwrap();

	net.add_full_peer_with_config(FullPeerConfig {
		sync_mode: SyncMode::Warp,
		target_block: Some(target_block),
		..Default::default()
	});

	net.run_until_sync().await;
	assert!(net.peer(3).client().has_state_at(&BlockId::Number(64)));

	// Wait for peer 1 download block history
	futures::future::poll_fn::<(), _>(|cx| {
		net.poll(cx);
		let peer = net.peer(3);
		if blocks.iter().all(|b| peer.has_body(*b)) {
			Poll::Ready(())
		} else {
			Poll::Pending
		}
	})
	.await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn syncs_huge_blocks() {
	use sp_core::storage::well_known_keys::HEAP_PAGES;
	use sp_runtime::codec::Encode;
	use substrate_test_runtime_client::BlockBuilderExt;

	sp_tracing::try_init_simple();
	let mut net = TestNet::new(2);

	// Increase heap space for bigger blocks.
	net.peer(0).generate_blocks(1, BlockOrigin::Own, |mut builder| {
		builder.push_storage_change(HEAP_PAGES.to_vec(), Some(256u64.encode())).unwrap();
		builder.build().unwrap().block
	});

	let mut nonce = 0;
	net.peer(0).generate_blocks(32, BlockOrigin::Own, |mut builder| {
		// Add 32 extrinsics 32k each = 1MiB total
		for _ in 0..32u64 {
			let ex = ExtrinsicBuilder::new_include_data(vec![42u8; 32 * 1024]).nonce(nonce).build();
			builder.push(ex).unwrap();
			nonce += 1;
		}
		builder.build().unwrap().block
	});

	net.run_until_sync().await;
	assert_eq!(net.peer(0).client.info().best_number, 33);
	assert_eq!(net.peer(1).client.info().best_number, 33);
}
