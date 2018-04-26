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

use io::SyncIo;
use network::PeerId;
use handler::Protocol as ProtocolApi;

/// Light protocol implementation.
pub struct Protocol;

impl ProtocolApi for Protocol {
	fn handle_packet(&self, _io: &mut SyncIo, _peer_id: PeerId, _data: &[u8]) {
	}

	fn on_peer_connected(&self, _io: &mut SyncIo, _peer_id: PeerId) {
	}

	fn on_peer_disconnected(&self, _io: &mut SyncIo, _peer: PeerId) {
	}

	fn tick(&self, _io: &mut SyncIo) {
	}
}
