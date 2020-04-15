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

use futures_timer::Delay;
use futures::{future::{FutureExt as _}, prelude::*, ready, stream::Stream};
use log::debug;
use std::{pin::Pin, task::{Context, Poll}, time::Duration};
use sp_utils::mpsc::{tracing_unbounded, TracingUnboundedReceiver, TracingUnboundedSender};

use sc_network::PeerId;
use sp_runtime::traits::{NumberFor, Block as BlockT};
use super::gossip::{NeighborPacket, GossipMessage};

// How often to rebroadcast, in cases where no new packets are created.
const REBROADCAST_AFTER: Duration = Duration::from_secs(2 * 60);

/// A sender used to send neighbor packets to a background job.
#[derive(Clone)]
pub(super) struct NeighborPacketSender<B: BlockT>(
	TracingUnboundedSender<(Vec<PeerId>, NeighborPacket<NumberFor<B>>)>
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

/// NeighborPacketWorker is listening on a channel for new neighbor packets being produced by
/// components within `finality-grandpa` and forwards those packets to the underlying
/// `NetworkEngine` through the `NetworkBridge` that it is being polled by (see `Stream`
/// implementation). Periodically it sends out the last packet in cases where no new ones arrive.
pub(super) struct NeighborPacketWorker<B: BlockT> {
	last: Option<(Vec<PeerId>, NeighborPacket<NumberFor<B>>)>,
	delay: Delay,
	rx: TracingUnboundedReceiver<(Vec<PeerId>, NeighborPacket<NumberFor<B>>)>,
}

impl<B: BlockT> Unpin for NeighborPacketWorker<B> {}

impl<B: BlockT> NeighborPacketWorker<B> {
	pub(super) fn new() -> (Self, NeighborPacketSender<B>){
		let (tx, rx) = tracing_unbounded::<(Vec<PeerId>, NeighborPacket<NumberFor<B>>)>
			("mpsc_grandpa_neighbor_packet_worker");
		let delay = Delay::new(REBROADCAST_AFTER);

		(NeighborPacketWorker {
			last: None,
			delay,
			rx,
		}, NeighborPacketSender(tx))
	}
}

impl <B: BlockT> Stream for NeighborPacketWorker<B> {
	type Item = (Vec<PeerId>, GossipMessage<B>);

	fn poll_next(mut self: Pin<&mut Self>, cx: &mut Context) -> Poll<Option<Self::Item>>
	{
		let this = &mut *self;
		match this.rx.poll_next_unpin(cx) {
			Poll::Ready(None) => return Poll::Ready(None),
			Poll::Ready(Some((to, packet))) => {
				this.delay.reset(REBROADCAST_AFTER);
				this.last = Some((to.clone(), packet.clone()));

				return Poll::Ready(Some((to, GossipMessage::<B>::from(packet.clone()))));
			}
			// Don't return yet, maybe the timer fired.
			Poll::Pending => {},
		};

		ready!(this.delay.poll_unpin(cx));

		// Getting this far here implies that the timer fired.

		this.delay.reset(REBROADCAST_AFTER);

		// Make sure the underlying task is scheduled for wake-up.
		//
		// Note: In case poll_unpin is called after the resetted delay fires again, this
		// will drop one tick. Deemed as very unlikely and also not critical.
		while let Poll::Ready(()) = this.delay.poll_unpin(cx) {};

		if let Some((ref to, ref packet)) = this.last {
			return Poll::Ready(Some((to.clone(), GossipMessage::<B>::from(packet.clone()))));
		}

		return Poll::Pending;
	}
}
