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

use futures::prelude::*;
use libp2p::Multiaddr;
use libp2p::core::{ConnectedPoint, PeerId};
use libp2p::swarm::{IntoProtocolsHandler, ProtocolsHandler};
use libp2p::swarm::{NetworkBehaviour, NetworkBehaviourAction, PollParameters};
use std::task::{Context, Poll};

/// Implementation of `NetworkBehaviour` that wraps events.
pub struct WrappedBehaviour<T> {
	inner: T,
}

impl<T> WrappedBehaviour<T> {
	pub fn new(inner: T) -> Self {
		WrappedBehaviour {
			inner,
		}
	}
}

/// Wrapped event.
pub struct WrappedEvent<T>(pub T);

impl<T> NetworkBehaviour for WrappedBehaviour<T>
where T: NetworkBehaviour {
	type ProtocolsHandler = T::ProtocolsHandler;
	type OutEvent = WrappedEvent<T::OutEvent>;

	fn new_handler(&mut self) -> Self::ProtocolsHandler {
		self.inner.new_handler()
	}

	fn addresses_of_peer(&mut self, peer_id: &PeerId) -> Vec<Multiaddr> {
		self.inner.addresses_of_peer(peer_id)
	}

	fn inject_connected(&mut self, peer_id: PeerId, endpoint: ConnectedPoint) {
		self.inner.inject_connected(peer_id, endpoint)
	}

	fn inject_disconnected(&mut self, peer_id: &PeerId, endpoint: ConnectedPoint) {
		self.inner.inject_disconnected(peer_id, endpoint)
	}

	fn inject_node_event(
		&mut self,
		peer_id: PeerId,
		event: <<Self::ProtocolsHandler as IntoProtocolsHandler>::Handler as ProtocolsHandler>::OutEvent
	) {
		self.inner.inject_node_event(peer_id, event)
	}

	fn inject_replaced(&mut self, peer_id: PeerId, closed_endpoint: ConnectedPoint, new_endpoint: ConnectedPoint) {
		self.inner.inject_replaced(peer_id, closed_endpoint, new_endpoint)
	}

	fn inject_addr_reach_failure(&mut self, peer_id: Option<&PeerId>, addr: &Multiaddr, error: &dyn std::error::Error) {
		self.inner.inject_addr_reach_failure(peer_id, addr, error)
	}

	fn inject_dial_failure(&mut self, peer_id: &PeerId) {
		self.inner.inject_dial_failure(peer_id)
	}

	fn inject_new_listen_addr(&mut self, addr: &Multiaddr) {
		self.inner.inject_new_listen_addr(addr)
	}

	fn inject_expired_listen_addr(&mut self, addr: &Multiaddr) {
		self.inner.inject_expired_listen_addr(addr)
	}

	fn inject_new_external_addr(&mut self, addr: &Multiaddr) {
		self.inner.inject_new_external_addr(addr)
	}

	fn poll(
		&mut self,
		cx: &mut Context,
		params: &mut impl PollParameters
	) -> Poll<
		NetworkBehaviourAction<
			<<Self::ProtocolsHandler as IntoProtocolsHandler>::Handler as ProtocolsHandler>::InEvent,
			Self::OutEvent
		>
	> {
		match self.inner.poll(cx, params) {
			Poll::Pending => Poll::Pending,
			Poll::Ready(NetworkBehaviourAction::GenerateEvent(ev)) =>
				Poll::Ready(NetworkBehaviourAction::GenerateEvent(WrappedEvent(ev))),
			Poll::Ready(NetworkBehaviourAction::DialAddress { address }) =>
				Poll::Ready(NetworkBehaviourAction::DialAddress { address }),
			Poll::Ready(NetworkBehaviourAction::DialPeer { peer_id }) =>
				Poll::Ready(NetworkBehaviourAction::DialPeer { peer_id }),
			Poll::Ready(NetworkBehaviourAction::SendEvent { peer_id, event }) =>
				Poll::Ready(NetworkBehaviourAction::SendEvent { peer_id, event }),
			Poll::Ready(NetworkBehaviourAction::ReportObservedAddr { address }) =>
				Poll::Ready(NetworkBehaviourAction::ReportObservedAddr { address }),
		}
	}
}
