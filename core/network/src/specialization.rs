// Copyright 2017-2019 Parity Technologies (UK) Ltd
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Specializations of the substrate network protocol to allow more complex forms of communication.

use crate::PeerId;
use runtime_primitives::traits::Block as BlockT;
use crate::protocol::Context;

/// A specialization of the substrate network protocol. Handles events and sends messages.
pub trait NetworkSpecialization<B: BlockT>: Send + Sync + 'static {
	/// Get the current specialization-status.
	fn status(&self) -> Vec<u8>;

	/// Called when a peer successfully handshakes.
	fn on_connect(&mut self, ctx: &mut Context<B>, who: PeerId, status: crate::message::Status<B>);

	/// Called when a peer is disconnected. If the peer ID is unknown, it should be ignored.
	fn on_disconnect(&mut self, ctx: &mut Context<B>, who: PeerId);

	/// Called when a network-specific message arrives.
	fn on_message(&mut self, ctx: &mut Context<B>, who: PeerId, message: &mut Option<crate::message::Message<B>>);

	/// Called on abort.
	fn on_abort(&mut self) { }

	/// Called periodically to maintain peers and handle timeouts.
	fn maintain_peers(&mut self, _ctx: &mut Context<B>) { }

	/// Called when a block is _imported_ at the head of the chain (not during major sync).
	/// Not guaranteed to be called for every block, but will be most of the after major sync.
	fn on_block_imported(&mut self, _ctx: &mut Context<B>, _hash: B::Hash, _header: &B::Header) { }
}
