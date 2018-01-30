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
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.?

use network::{NetworkContext, PeerId, Error as NetworkError, SessionInfo};

/// IO interface for the syncing handler.
/// Provides peer connection management and an interface to the blockchain client.
pub trait SyncIo {
	/// Disable a peer
	fn disable_peer(&mut self, peer_id: PeerId);
	/// Disconnect peer
	fn disconnect_peer(&mut self, peer_id: PeerId);
	/// Send a packet to a peer.
	fn send(&mut self, peer_id: PeerId, data: Vec<u8>) -> Result<(), NetworkError>;
	/// Returns peer identifier string
	fn peer_info(&self, peer_id: PeerId) -> String {
		peer_id.to_string()
	}
	/// Returns information on p2p session
	fn peer_session_info(&self, peer_id: PeerId) -> Option<SessionInfo>;
	/// Check if the session is expired
	fn is_expired(&self) -> bool;
}

/// Wraps `NetworkContext` and the blockchain client
pub struct NetSyncIo<'s, 'h> where 'h: 's {
	network: &'s NetworkContext<'h>,
}

impl<'s, 'h> NetSyncIo<'s, 'h> {
	/// Creates a new instance from the `NetworkContext` and the blockchain client reference.
	pub fn new(network: &'s NetworkContext<'h>) -> NetSyncIo<'s, 'h> {
		NetSyncIo {
			network: network,
		}
	}
}

impl<'s, 'h> SyncIo for NetSyncIo<'s, 'h> {
	fn disable_peer(&mut self, peer_id: PeerId) {
		self.network.disable_peer(peer_id);
	}

	fn disconnect_peer(&mut self, peer_id: PeerId) {
		self.network.disconnect_peer(peer_id);
	}

	fn send(&mut self, peer_id: PeerId, data: Vec<u8>) -> Result<(), NetworkError>{
		self.network.send(peer_id, 0, data)
	}

	fn peer_session_info(&self, peer_id: PeerId) -> Option<SessionInfo> {
		self.network.session_info(peer_id)
	}

	fn is_expired(&self) -> bool {
		self.network.is_expired()
	}

	fn peer_info(&self, peer_id: PeerId) -> String {
		self.network.peer_client_version(peer_id)
	}
}


