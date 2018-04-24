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

use std::sync::Arc;
use std::collections::BTreeMap;
use network::{PeerId, ProtocolId};
use network_devp2p::NetworkService;
use primitives::block::{HeaderHash, Header, ExtrinsicHash};
use io::SyncIo;
use full::handler::ProtocolHandler as FullProtocolHandler;
use {ProtocolStatus, SyncStatus, SyncState, TransactionStats,
	ProtocolPeerInfo};

/// Polkadot devp2p full protocol id
pub const DOT_PROTOCOL_ID: ProtocolId = *b"dot";
/// Polkadot devp2p light protocol id
pub const LIGHT_DOT_PROTOCOL_ID: ProtocolId = *b"ldt";

/// Protocol handler aapter.
pub enum ProtocolHandler {
	/// Full protocol handler.
	Full(Arc<FullProtocolHandler>),
	/// Light protocol handler.
	Light(()),
}

impl ProtocolHandler {
	/// Get protocol ID.
	pub fn protocol_id(&self) -> ProtocolId {
		match *self {
			ProtocolHandler::Full(_) => DOT_PROTOCOL_ID,
			ProtocolHandler::Light(_) => LIGHT_DOT_PROTOCOL_ID,
		}
	}

	/// Get full protocol handler.
	pub fn full(&self) -> Option<&Arc<FullProtocolHandler>> {
		match *self {
			ProtocolHandler::Full(ref handler) => Some(handler),
			ProtocolHandler::Light(_) => None,
		}
	}

	/// Register protocol.
	pub fn register(&self, network: &NetworkService) {
		match *self {
			ProtocolHandler::Full(ref handler) => network
				.register_protocol(handler.clone(), DOT_PROTOCOL_ID, 1, &[0u8])
				.unwrap_or_else(|e| warn!("Error registering polkadot protocol: {:?}", e)),
			ProtocolHandler::Light(_) => (),
		}
	}

	/// Abort protocol.
	pub fn abort(&self) {
		match *self {
			ProtocolHandler::Full(ref handler) => handler.protocol.abort(),
			ProtocolHandler::Light(_) => (),
		}
	}

	/// When block is imported by client.
	pub fn on_block_imported(&self, io: &mut SyncIo, hash: HeaderHash, header: &Header) {
		match *self {
			ProtocolHandler::Full(ref handler) => handler.protocol.on_block_imported(io, hash, header),
			ProtocolHandler::Light(_) => (),
		}
	}

	/// When new transactions are imported by client.
	pub fn on_new_transactions(&self, io: &mut SyncIo, transactions: &[(ExtrinsicHash, Vec<u8>)]) {
		match *self {
			ProtocolHandler::Full(ref handler) => handler.protocol.propagate_transactions(io, transactions),
			ProtocolHandler::Light(_) => (),
		}
	}

	/// Get sync status
	pub fn status(&self) -> ProtocolStatus {
		match *self {
			ProtocolHandler::Full(ref handler) => handler.protocol.status(),
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
			ProtocolHandler::Full(ref handler) => handler.protocol.peer_info(peer),
			ProtocolHandler::Light(_) => None,
		}
	}

	/// Get transactions statis
	pub fn transactions_stats(&self) -> BTreeMap<ExtrinsicHash, TransactionStats> {
		match *self {
			ProtocolHandler::Full(ref handler) => handler.protocol.transactions_stats(),
			ProtocolHandler::Light(_) => BTreeMap::new(),
		}
	}
}
