// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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

use std::time::{Instant, Duration};
use std::pin::Pin;
use std::task::Poll;

use parity_scale_codec::Encode;
use futures::prelude::*;
use futures::channel::mpsc;
use futures_timer::Delay;
use log::debug;

use sc_network::PeerId;
use sc_network_gossip::GossipEngine;
use sp_runtime::traits::{NumberFor, Block as BlockT};
use super::gossip::{NeighborPacket, GossipMessage};

// how often to rebroadcast, if no other
const REBROADCAST_AFTER: Duration = Duration::from_secs(2 * 60);

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
		who: Vec<sc_network::PeerId>,
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
pub(super) fn neighbor_packet_worker<B>(net: GossipEngine<B>) -> (
	impl Future<Output = ()> + Unpin + Send + 'static,
	NeighborPacketSender<B>,
) where
	B: BlockT,
{
	let mut last = None;
	let (tx, mut rx) = mpsc::unbounded::<(Vec<PeerId>, NeighborPacket<NumberFor<B>>)>();
	let mut delay = Delay::new(REBROADCAST_AFTER);

	let work = futures::future::poll_fn(move |cx| {
		loop {
			match Pin::new(&mut rx).poll_next(cx) {
				Poll::Ready(None) => return Poll::Ready(()),
				Poll::Ready(Some((to, packet))) => {
					// send to peers.
					net.send_message(to.clone(), GossipMessage::<B>::from(packet.clone()).encode());

					// rebroadcasting network.
					delay.reset(rebroadcast_instant());
					last = Some((to, packet));
				}
				Poll::Pending => break,
			}
		}

		// has to be done in a loop because it needs to be polled after
		// re-scheduling.
		loop {
			match Pin::new(&mut delay).poll(cx) {
				Poll::Ready(()) => {
					delay.reset(rebroadcast_instant());

					if let Some((ref to, ref packet)) = last {
						// send to peers.
						net.send_message(to.clone(), GossipMessage::<B>::from(packet.clone()).encode());
					}
				}
				Poll::Pending => return Poll::Pending,
			}
		}
	});

	(work, NeighborPacketSender(tx))
}
