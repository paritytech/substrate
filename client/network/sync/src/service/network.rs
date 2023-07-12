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

use futures::{channel::oneshot, StreamExt};
use libp2p::PeerId;

use sc_network::{
	request_responses::{IfDisconnected, RequestFailure},
	types::ProtocolName,
	NetworkNotification, NetworkPeers, NetworkRequest, ReputationChange,
};
use sc_utils::mpsc::{tracing_unbounded, TracingUnboundedReceiver, TracingUnboundedSender};

use std::sync::Arc;

/// Network-related services required by `sc-network-sync`
pub trait Network: NetworkPeers + NetworkRequest + NetworkNotification {}

impl<T> Network for T where T: NetworkPeers + NetworkRequest + NetworkNotification {}

/// Network service provider for `ChainSync`
///
/// It runs as an asynchronous task and listens to commands coming from `ChainSync` and
/// calls the `NetworkService` on its behalf.
pub struct NetworkServiceProvider {
	rx: TracingUnboundedReceiver<ToServiceCommand>,
}

/// Commands that `ChainSync` wishes to send to `NetworkService`
pub enum ToServiceCommand {
	/// Call `NetworkPeers::disconnect_peer()`
	DisconnectPeer(PeerId, ProtocolName),

	/// Call `NetworkPeers::report_peer()`
	ReportPeer(PeerId, ReputationChange),

	/// Call `NetworkRequest::start_request()`
	StartRequest(
		PeerId,
		ProtocolName,
		Vec<u8>,
		oneshot::Sender<Result<Vec<u8>, RequestFailure>>,
		IfDisconnected,
	),

	/// Call `NetworkNotification::write_notification()`
	WriteNotification(PeerId, ProtocolName, Vec<u8>),

	/// Call `NetworkNotification::set_notification_handshake()`
	SetNotificationHandshake(ProtocolName, Vec<u8>),
}

/// Handle that is (temporarily) passed to `ChainSync` so it can
/// communicate with `NetworkService` through `SyncingEngine`
#[derive(Clone)]
pub struct NetworkServiceHandle {
	tx: TracingUnboundedSender<ToServiceCommand>,
}

impl NetworkServiceHandle {
	/// Create new service handle
	pub fn new(tx: TracingUnboundedSender<ToServiceCommand>) -> NetworkServiceHandle {
		Self { tx }
	}

	/// Report peer
	pub fn report_peer(&self, who: PeerId, cost_benefit: ReputationChange) {
		let _ = self.tx.unbounded_send(ToServiceCommand::ReportPeer(who, cost_benefit));
	}

	/// Disconnect peer
	pub fn disconnect_peer(&self, who: PeerId, protocol: ProtocolName) {
		let _ = self.tx.unbounded_send(ToServiceCommand::DisconnectPeer(who, protocol));
	}

	/// Send request to peer
	pub fn start_request(
		&self,
		who: PeerId,
		protocol: ProtocolName,
		request: Vec<u8>,
		tx: oneshot::Sender<Result<Vec<u8>, RequestFailure>>,
		connect: IfDisconnected,
	) {
		let _ = self
			.tx
			.unbounded_send(ToServiceCommand::StartRequest(who, protocol, request, tx, connect));
	}

	/// Send notification to peer
	pub fn write_notification(&self, who: PeerId, protocol: ProtocolName, message: Vec<u8>) {
		let _ = self
			.tx
			.unbounded_send(ToServiceCommand::WriteNotification(who, protocol, message));
	}

	/// Set handshake for the notification protocol.
	pub fn set_notification_handshake(&self, protocol: ProtocolName, handshake: Vec<u8>) {
		let _ = self
			.tx
			.unbounded_send(ToServiceCommand::SetNotificationHandshake(protocol, handshake));
	}
}

impl NetworkServiceProvider {
	/// Create new `NetworkServiceProvider`
	pub fn new() -> (Self, NetworkServiceHandle) {
		let (tx, rx) = tracing_unbounded("mpsc_network_service_provider", 100_000);

		(Self { rx }, NetworkServiceHandle::new(tx))
	}

	/// Run the `NetworkServiceProvider`
	pub async fn run(mut self, service: Arc<dyn Network + Send + Sync>) {
		while let Some(inner) = self.rx.next().await {
			match inner {
				ToServiceCommand::DisconnectPeer(peer, protocol_name) =>
					service.disconnect_peer(peer, protocol_name),
				ToServiceCommand::ReportPeer(peer, reputation_change) =>
					service.report_peer(peer, reputation_change),
				ToServiceCommand::StartRequest(peer, protocol, request, tx, connect) =>
					service.start_request(peer, protocol, request, tx, connect),
				ToServiceCommand::WriteNotification(peer, protocol, message) =>
					service.write_notification(peer, protocol, message),
				ToServiceCommand::SetNotificationHandshake(protocol, handshake) =>
					service.set_notification_handshake(protocol, handshake),
			}
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::service::mock::MockNetwork;

	// typical pattern in `Protocol` code where peer is disconnected
	// and then reported
	#[tokio::test]
	async fn disconnect_and_report_peer() {
		let (provider, handle) = NetworkServiceProvider::new();

		let peer = PeerId::random();
		let proto = ProtocolName::from("test-protocol");
		let proto_clone = proto.clone();
		let change = sc_network::ReputationChange::new_fatal("test-change");

		let mut mock_network = MockNetwork::new();
		mock_network
			.expect_disconnect_peer()
			.withf(move |in_peer, in_proto| &peer == in_peer && &proto == in_proto)
			.once()
			.returning(|_, _| ());
		mock_network
			.expect_report_peer()
			.withf(move |in_peer, in_change| &peer == in_peer && &change == in_change)
			.once()
			.returning(|_, _| ());

		tokio::spawn(async move {
			provider.run(Arc::new(mock_network)).await;
		});

		handle.disconnect_peer(peer, proto_clone);
		handle.report_peer(peer, change);
	}
}
