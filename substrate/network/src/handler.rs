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

use std::collections::BTreeMap;
use core_io::{TimerToken};
use network::{PeerId, ProtocolId, NetworkProtocolHandler, NetworkContext, HostInfo};
use primitives::block::{HeaderHash, Header, ExtrinsicHash};
use io::{SyncIo, NetSyncIo};
use full::protocol::Protocol as FullProtocol;
use light::protocol::Protocol as LightProtocol;
use {ProtocolStatus, SyncStatus, SyncState, TransactionStats,
	ProtocolPeerInfo};

/// Polkadot devp2p full protocol id
pub const DOT_PROTOCOL_ID: ProtocolId = *b"dot";
/// Polkadot devp2p light protocol id
pub const LIGHT_DOT_PROTOCOL_ID: ProtocolId = *b"ldt";

/// Protocol handler aapter.
pub enum ProtocolHandler {
	/// Full protocol handler.
	Full(FullProtocol),
	/// Light protocol handler.
	Light(LightProtocol),
}

/// Protocol trait.
pub trait Protocol: Send + Sync {
	/// When peer is connected.
	fn on_peer_connected(&self, io: &mut SyncIo, peer_id: PeerId);

	/// When peer is disconnected.
	fn on_peer_disconnected(&self, io: &mut SyncIo, peer: PeerId);

	/// When new packet from peer is received.
	fn handle_packet(&self, io: &mut SyncIo, peer_id: PeerId, data: &[u8]);

	/// Perform time based maintenance.
	fn tick(&self, io: &mut SyncIo);
}

impl ProtocolHandler {
	/// As protocol reference.
	pub fn as_protocol(&self) -> &Protocol {
		match *self {
			ProtocolHandler::Full(ref protocol) => protocol,
			ProtocolHandler::Light(ref protocol) => protocol,
		}
	}

	/// Get protocol ID.
	pub fn protocol_id(&self) -> ProtocolId {
		match *self {
			ProtocolHandler::Full(_) => DOT_PROTOCOL_ID,
			ProtocolHandler::Light(_) => LIGHT_DOT_PROTOCOL_ID,
		}
	}

	/// Get full protocol handler.
	pub fn full(&self) -> Option<&FullProtocol> {
		match *self {
			ProtocolHandler::Full(ref protocol) => Some(protocol),
			ProtocolHandler::Light(_) => None,
		}
	}

	/// Abort protocol.
	pub fn abort(&self) {
		match *self {
			ProtocolHandler::Full(ref protocol) => protocol.abort(),
			ProtocolHandler::Light(_) => (),
		}
	}

	/// When block is imported by client.
	pub fn on_block_imported(&self, io: &mut SyncIo, hash: HeaderHash, header: &Header) {
		match *self {
			ProtocolHandler::Full(ref protocol) => protocol.on_block_imported(io, hash, header),
			ProtocolHandler::Light(_) => (),
		}
	}

	/// When new transactions are imported by client.
	pub fn on_new_transactions(&self, io: &mut SyncIo, transactions: &[(ExtrinsicHash, Vec<u8>)]) {
		match *self {
			ProtocolHandler::Full(ref protocol) => protocol.propagate_transactions(io, transactions),
			ProtocolHandler::Light(_) => (),
		}
	}

	/// Get sync status
	pub fn status(&self) -> ProtocolStatus {
		match *self {
			ProtocolHandler::Full(ref protocol) => protocol.status(),
			ProtocolHandler::Light(_) => ProtocolStatus {
				sync: SyncStatus {
					state: SyncState::Idle,
					best_seen_block: None,
				},
				num_peers: 0,
				num_active_peers: 0,
			},
		}
	}

	/// Get protocol peer info
	pub fn protocol_peer_info(&self, peer: PeerId) -> Option<ProtocolPeerInfo> {
		match *self {
			ProtocolHandler::Full(ref protocol) => protocol.peer_info(peer),
			ProtocolHandler::Light(_) => None,
		}
	}

	/// Get transactions statis
	pub fn transactions_stats(&self) -> BTreeMap<ExtrinsicHash, TransactionStats> {
		match *self {
			ProtocolHandler::Full(ref protocol) => protocol.transactions_stats(),
			ProtocolHandler::Light(_) => BTreeMap::new(),
		}
	}
}

impl NetworkProtocolHandler for ProtocolHandler {
	fn initialize(&self, io: &NetworkContext, _host_info: &HostInfo) {
		io.register_timer(0, 1000).expect("Error registering sync timer");
	}

	fn read(&self, io: &NetworkContext, peer: &PeerId, _packet_id: u8, data: &[u8]) {
		self.as_protocol().handle_packet(&mut NetSyncIo::new(io), *peer, data);
	}

	fn connected(&self, io: &NetworkContext, peer: &PeerId) {
		self.as_protocol().on_peer_connected(&mut NetSyncIo::new(io), *peer);
	}

	fn disconnected(&self, io: &NetworkContext, peer: &PeerId) {
		self.as_protocol().on_peer_disconnected(&mut NetSyncIo::new(io), *peer);
	}

	fn timeout(&self, io: &NetworkContext, _timer: TimerToken) {
		self.as_protocol().tick(&mut NetSyncIo::new(io));
	}
}

