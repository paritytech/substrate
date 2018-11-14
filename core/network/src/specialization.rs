// Copyright 2017-2018 Parity Technologies (UK) Ltd.
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

use ::NodeIndex;
use runtime_primitives::traits::Block as BlockT;
use protocol::Context;

/// A specialization of the substrate network protocol. Handles events and sends messages.
pub trait NetworkSpecialization<B: BlockT>: Send + Sync + 'static {
	/// Get the current specialization-status.
	fn status(&self) -> Vec<u8>;

	/// Called when a peer successfully handshakes.
	fn on_connect(&mut self, ctx: &mut Context<B>, who: NodeIndex, status: ::message::Status<B>);

	/// Called when a peer is disconnected. If the peer ID is unknown, it should be ignored.
	fn on_disconnect(&mut self, ctx: &mut Context<B>, who: NodeIndex);

	/// Called when a network-specific message arrives.
	fn on_message(&mut self, ctx: &mut Context<B>, who: NodeIndex, message: &mut Option<::message::Message<B>>);

	/// Called on abort.
	fn on_abort(&mut self) { }

	/// Called periodically to maintain peers and handle timeouts.
	fn maintain_peers(&mut self, _ctx: &mut Context<B>) { }

	/// Called when a block is _imported_ at the head of the chain (not during major sync).
	/// Not guaranteed to be called for every block, but will be most of the after major sync.
	fn on_block_imported(&mut self, _ctx: &mut Context<B>, _hash: B::Hash, _header: &B::Header) { }
}
