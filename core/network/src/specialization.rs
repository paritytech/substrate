// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

use crate::PeerId;
use runtime_primitives::traits::Block as BlockT;
use crate::protocol::Context;

/// A specialization of the substrate network protocol. Handles events and sends messages.
pub trait NetworkSpecialization<B: BlockT>: Send + Sync + 'static {
	/// Get the current specialization-status.
	fn status(&self) -> Vec<u8>;

	/// Called when a peer successfully handshakes.
	fn on_connect(&mut self, ctx: &mut dyn Context<B>, who: PeerId, status: crate::message::Status<B>);

	/// Called when a peer is disconnected. If the peer ID is unknown, it should be ignored.
	fn on_disconnect(&mut self, ctx: &mut dyn Context<B>, who: PeerId);

	/// Called when a network-specific message arrives.
	fn on_message(
		&mut self,
		ctx: &mut dyn Context<B>,
		who: PeerId,
		message: &mut Option<crate::message::Message<B>>
	);

	/// Called on abort.
	#[deprecated(note = "This method is never called; aborting corresponds to dropping the object")]
	fn on_abort(&mut self) { }

	/// Called periodically to maintain peers and handle timeouts.
	fn maintain_peers(&mut self, _ctx: &mut dyn Context<B>) { }

	/// Called when a block is _imported_ at the head of the chain (not during major sync).
	/// Not guaranteed to be called for every block, but will be most of the after major sync.
	fn on_block_imported(&mut self, _ctx: &mut dyn Context<B>, _hash: B::Hash, _header: &B::Header) { }
}

/// Construct a simple protocol that is composed of several sub protocols.
/// Each "sub protocol" needs to implement `Specialization` and needs to provide a `new()` function.
/// For more fine grained implementations, this macro is not usable.
///
/// # Example
///
/// ```nocompile
/// construct_simple_protocol! {
///     pub struct MyProtocol where Block = MyBlock {
///         consensus_gossip: ConsensusGossip<MyBlock>,
///         other_protocol: MyCoolStuff,
///     }
/// }
/// ```
///
/// You can also provide an optional parameter after `where Block = MyBlock`, so it looks like
/// `where Block = MyBlock, Status = consensus_gossip`. This will instruct the implementation to
/// use the `status()` function from the `ConsensusGossip` protocol. By default, `status()` returns
/// an empty vector.
#[macro_export]
macro_rules! construct_simple_protocol {
	(
		$( #[ $attr:meta ] )*
		pub struct $protocol:ident where
			Block = $block:ident
			$( , Status = $status_protocol_name:ident )*
		{
			$( $sub_protocol_name:ident : $sub_protocol:ident $( <$protocol_block:ty> )*, )*
		}
	) => {
		$( #[$attr] )*
		pub struct $protocol {
			$( $sub_protocol_name: $sub_protocol $( <$protocol_block> )*, )*
		}

		impl $protocol {
			/// Instantiate a node protocol handler.
			pub fn new() -> Self {
				Self {
					$( $sub_protocol_name: $sub_protocol::new(), )*
				}
			}
		}

		impl $crate::specialization::NetworkSpecialization<$block> for $protocol {
			fn status(&self) -> Vec<u8> {
				$(
					let status = self.$status_protocol_name.status();

					if !status.is_empty() {
						return status;
					}
				)*

				Vec::new()
			}

			fn on_connect(
				&mut self,
				_ctx: &mut $crate::Context<$block>,
				_who: $crate::PeerId,
				_status: $crate::StatusMessage<$block>
			) {
				$( self.$sub_protocol_name.on_connect(_ctx, _who, _status); )*
			}

			fn on_disconnect(&mut self, _ctx: &mut $crate::Context<$block>, _who: $crate::PeerId) {
				$( self.$sub_protocol_name.on_disconnect(_ctx, _who); )*
			}

			fn on_message(
				&mut self,
				_ctx: &mut $crate::Context<$block>,
				_who: $crate::PeerId,
				_message: &mut Option<$crate::message::Message<$block>>
			) {
				$( self.$sub_protocol_name.on_message(_ctx, _who, _message); )*
			}

			fn on_abort(&mut self) {
				$( self.$sub_protocol_name.on_abort(); )*
			}

			fn maintain_peers(&mut self, _ctx: &mut $crate::Context<$block>) {
				$( self.$sub_protocol_name.maintain_peers(_ctx); )*
			}

			fn on_block_imported(
				&mut self,
				_ctx: &mut $crate::Context<$block>,
				_hash: <$block as $crate::BlockT>::Hash,
				_header: &<$block as $crate::BlockT>::Header
			) {
				$( self.$sub_protocol_name.on_block_imported(_ctx, _hash, _header); )*
			}
		}
	}
}
