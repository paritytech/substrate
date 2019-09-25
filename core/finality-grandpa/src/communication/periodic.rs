// Copyright 2019 Parity Technologies (UK) Ltd.
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

//! Periodic rebroadcast of neighbor packets.

use std::collections::VecDeque;
use std::time::{Instant, Duration};

use codec::Encode;
use futures::prelude::*;
use futures::sync::mpsc;
use log::{debug, warn};
use tokio_timer::Delay;

use network::PeerId;
use sr_primitives::traits::{NumberFor, Block as BlockT};
use super::{gossip::{NeighborPacket, GossipMessage}, Network};

// how often to rebroadcast, if no other
const REBROADCAST_AFTER: Duration = Duration::from_secs(2 * 60);

/// The number of block hashes that we have previously voted on that we should
/// keep around for announcement. The current value should be enough for 3
/// rounds assuming we have prevoted and precommited on different blocks.
const LATEST_VOTED_BLOCKS_TO_ANNOUNCE: usize = 6;

fn rebroadcast_instant() -> Instant {
	Instant::now() + REBROADCAST_AFTER
}

/// A sender used to send neighbor packets to a background job.
#[derive(Clone)]
pub(super) struct NeighborPacketSender<B: BlockT>(
	mpsc::UnboundedSender<(Vec<PeerId>, NeighborPacket<NumberFor<B>>)>
);

impl<B: BlockT> NeighborPacketSender<B> {
	/// Send a neighbor packet for the background worker to gossip to peers.
	pub fn send(
		&self,
		who: Vec<network::PeerId>,
		neighbor_packet: NeighborPacket<NumberFor<B>>,
	) {
		if let Err(err) = self.0.unbounded_send((who, neighbor_packet)) {
			debug!(target: "afg", "Failed to send neighbor packet: {:?}", err);
		}
	}
}

/// Does the work of sending neighbor packets, asynchronously.
///
/// It may rebroadcast the last neighbor packet periodically when no
/// progress is made.
pub(super) fn neighbor_packet_worker<B, N>(net: N) -> (
	impl Future<Item = (), Error = ()> + Send + 'static,
	NeighborPacketSender<B>,
) where
	B: BlockT,
	N: Network<B>,
{
	let mut last = None;
	let (tx, mut rx) = mpsc::unbounded::<(Vec<PeerId>, NeighborPacket<NumberFor<B>>)>();
	let mut delay = Delay::new(rebroadcast_instant());

	let work = futures::future::poll_fn(move || {
		loop {
			match rx.poll().expect("unbounded receivers do not error; qed") {
				Async::Ready(None) => return Ok(Async::Ready(())),
				Async::Ready(Some((to, packet))) => {
					// send to peers.
					net.send_message(to.clone(), GossipMessage::<B>::from(packet.clone()).encode());

					// rebroadcasting network.
					delay.reset(rebroadcast_instant());
					last = Some((to, packet));
				}
				Async::NotReady => break,
			}
		}

		// has to be done in a loop because it needs to be polled after
		// re-scheduling.
		loop {
			match delay.poll() {
				Err(e) => {
					warn!(target: "afg", "Could not rebroadcast neighbor packets: {:?}", e);
					delay.reset(rebroadcast_instant());
				}
				Ok(Async::Ready(())) => {
					delay.reset(rebroadcast_instant());

					if let Some((ref to, ref packet)) = last {
						// send to peers.
						net.send_message(to.clone(), GossipMessage::<B>::from(packet.clone()).encode());
					}
				}
				Ok(Async::NotReady) => return Ok(Async::NotReady),
			}
		}
	});

	(work, NeighborPacketSender(tx))
}

/// A background worker for performing block announcements.
struct BlockAnnouncer<B: BlockT, N> {
	net: N,
	block_rx: mpsc::UnboundedReceiver<(B::Hash, Vec<u8>)>,
	latest_voted_blocks: VecDeque<B::Hash>,
	reannounce_after: Duration,
	delay: Delay,
}

/// A background worker for announcing block hashes to peers. The worker keeps
/// track of `LATEST_VOTED_BLOCKS_TO_ANNOUNCE` and periodically announces these
/// blocks to all peers if no new blocks to announce are noted (i.e. presumably
/// GRANDPA progress is stalled).
pub(super) fn block_announce_worker<B: BlockT, N: Network<B>>(net: N) -> (
	impl Future<Item = (), Error = ()>,
	BlockAnnounceSender<B>,
) {
	block_announce_worker_aux(net, REBROADCAST_AFTER)
}

#[cfg(test)]
pub(super) fn block_announce_worker_with_delay<B: BlockT, N: Network<B>>(
	net: N,
	reannounce_after: Duration,
) -> (
	impl Future<Item = (), Error = ()>,
	BlockAnnounceSender<B>,
) {
	block_announce_worker_aux(net, reannounce_after)
}

fn block_announce_worker_aux<B: BlockT, N: Network<B>>(
	net: N,
	reannounce_after: Duration,
) -> (
	impl Future<Item = (), Error = ()>,
	BlockAnnounceSender<B>,
) {
	let latest_voted_blocks = VecDeque::with_capacity(LATEST_VOTED_BLOCKS_TO_ANNOUNCE);

	let (block_tx, block_rx) = mpsc::unbounded();

	let announcer = BlockAnnouncer {
		net,
		block_rx,
		latest_voted_blocks,
		reannounce_after,
		delay: Delay::new(Instant::now() + reannounce_after),
	};

	(announcer, BlockAnnounceSender(block_tx))
}


impl<B: BlockT, N> BlockAnnouncer<B, N> {
	fn note_block(&mut self, block: B::Hash) -> bool {
		if !self.latest_voted_blocks.contains(&block) {
			if self.latest_voted_blocks.len() >= LATEST_VOTED_BLOCKS_TO_ANNOUNCE {
				self.latest_voted_blocks.pop_front();
			}

			self.latest_voted_blocks.push_back(block);

			true
		} else {
			false
		}
	}

	fn reset_delay(&mut self) {
		self.delay.reset(Instant::now() + self.reannounce_after);
	}
}

impl<B: BlockT, N: Network<B>> Future for BlockAnnouncer<B, N> {
	type Item = ();
	type Error = ();

	fn poll(&mut self) -> Poll<Self::Item, Self::Error> {
		// note any new blocks to announce and announce them
		loop {
			match self.block_rx.poll().expect("unbounded receivers do not error; qed") {
				Async::Ready(None) => return Ok(Async::Ready(())),
				Async::Ready(Some(block)) => {
					if self.note_block(block.0) {
						self.net.announce(block.0, block.1);
						self.reset_delay();
					}
				},
				Async::NotReady => break,
			}
		}

		// check the reannouncement delay timer, has to be done in a loop
		// because it needs to be polled after re-scheduling.
		loop {
			match self.delay.poll() {
				Err(e) => {
					warn!(target: "afg", "Error in periodic block announcer timer: {:?}", e);
					self.reset_delay();
				},
				// after the delay fires announce all blocks that we have
				// stored. note that this only happens if we don't receive any
				// new blocks above for the duration of `reannounce_after`.
				Ok(Async::Ready(())) => {
					self.reset_delay();

					debug!(
						target: "afg",
						"Re-announcing latest voted blocks due to lack of progress: {:?}",
						self.latest_voted_blocks,
					);

					for block in self.latest_voted_blocks.iter() {
						self.net.announce(*block, Vec::new());
					}
				},
				Ok(Async::NotReady) => return Ok(Async::NotReady),
			}
		}
	}
}

/// A sender used to send block hashes to announce to a background job.
#[derive(Clone)]
pub(super) struct BlockAnnounceSender<B: BlockT>(mpsc::UnboundedSender<(B::Hash, Vec<u8>)>);

impl<B: BlockT> BlockAnnounceSender<B> {
	/// Send a block hash for the background worker to announce.
	pub fn send(&self, block: B::Hash, associated_data: Vec<u8>) {
		if let Err(err) = self.0.unbounded_send((block, associated_data)) {
			debug!(target: "afg", "Failed to send block to background announcer: {:?}", err);
		}
	}
}
