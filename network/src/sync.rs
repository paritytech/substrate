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
use protocol::Protocol;
use network::PeerId;

/// Relay chain sync strategy.
pub struct ChainSync;

/// Syncing status and statistics
#[derive(Clone, Copy)]
pub struct Status;

impl ChainSync {
	pub fn new() -> ChainSync {
		ChainSync
	}

	/// Returns sync status
	pub fn status(&self) -> Status {
		Status
	}

	pub fn new_peer(&mut self, _io: &mut SyncIo, _protocol: &Protocol, _peer: PeerId,) {
	}

	pub fn peer_disconnected(&mut self, _io: &mut SyncIo, _protocol: &Protocol, _peer: PeerId,) {
	}

	pub fn start(&mut self, _protocol: &Protocol) {
	}

	pub fn abort(&mut self) {
	}
}




