// Copyright 2017 Parity Technologies (UK) Ltd.
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

use network_libp2p::{NetworkContext, Severity, NodeIndex, SessionInfo};

/// IO interface for the syncing handler.
/// Provides peer connection management and an interface to the blockchain client.
pub trait SyncIo {
	/// Report a peer for misbehaviour.
	fn report_peer(&mut self, who: NodeIndex, reason: Severity);
	/// Send a packet to a peer.
	fn send(&mut self, who: NodeIndex, data: Vec<u8>);
	/// Returns peer identifier string
	fn peer_info(&self, who: NodeIndex) -> String {
		who.to_string()
	}
	/// Returns information on p2p session
	fn peer_session_info(&self, who: NodeIndex) -> Option<SessionInfo>;
	/// Check if the session is expired
	fn is_expired(&self) -> bool;
}

/// Wraps `NetworkContext` and the blockchain client
pub struct NetSyncIo<'s> {
	network: &'s NetworkContext,
}

impl<'s> NetSyncIo<'s> {
	/// Creates a new instance from the `NetworkContext` and the blockchain client reference.
	pub fn new(network: &'s NetworkContext) -> NetSyncIo<'s> {
		NetSyncIo {
			network: network,
		}
	}
}

impl<'s> SyncIo for NetSyncIo<'s> {
	fn report_peer(&mut self, who: NodeIndex, reason: Severity) {
		self.network.report_peer(who, reason);
	}

	fn send(&mut self, who: NodeIndex, data: Vec<u8>) {
		self.network.send(who, 0, data)
	}

	fn peer_session_info(&self, who: NodeIndex) -> Option<SessionInfo> {
		self.network.session_info(who)
	}

	fn is_expired(&self) -> bool {
		self.network.is_expired()
	}

	fn peer_info(&self, who: NodeIndex) -> String {
		self.network.peer_client_version(who)
	}
}


