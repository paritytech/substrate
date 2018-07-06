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

//! Specializations of the substrate network protocol to allow more complex forms of communication.

use ::PeerId;
use runtime_primitives::traits::Block as BlockT;
use protocol::Context;

/// A specialization of the substrate network protocol. Handles events and sends messages.
pub trait Specialization<B: BlockT>: Send + Sync + 'static {
	/// Get the current specialization-status.
	fn status(&self) -> Vec<u8>;

	/// Called on start-up.
	fn on_start(&mut self) { }

	/// Called when a peer successfully handshakes.
	fn on_connect(&mut self, ctx: &mut Context<B>, peer_id: PeerId, status: ::message::Status<B>);

	/// Called when a peer is disconnected. If the peer ID is unknown, it should be ignored.
	fn on_disconnect(&mut self, ctx: &mut Context<B>, peer_id: PeerId);

	/// Called when a network-specific message arrives.
	fn on_message(&mut self, ctx: &mut Context<B>, peer_id: PeerId, message: ::message::Message<B>);

	/// Called on abort.
	fn on_abort(&mut self) { }

	/// Called periodically to maintain peers and handle timeouts.
	fn maintain_peers(&mut self, _ctx: &mut Context<B>) { }
}
