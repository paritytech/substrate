// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! Polite gossiping.
//!
//! This crate provides gossiping capabilities on top of a network.
//!
//! Gossip messages are separated by two categories: "topics" and consensus engine ID.
//! The consensus engine ID is sent over the wire with the message, while the topic is not,
//! with the expectation that the topic can be derived implicitly from the content of the
//! message, assuming it is valid.
//!
//! Topics are a single 32-byte tag associated with a message, used to group those messages
//! in an opaque way. Consensus code can invoke `broadcast_topic` to attempt to send all messages
//! under a single topic to all peers who don't have them yet, and `send_topic` to
//! send all messages under a single topic to a specific peer.
//!
//! # Usage
//!
//! - Implement the `Network` trait, representing the low-level networking primitives. It is
//!   already implemented on `sc_network::NetworkService`.
//! - Implement the `Validator` trait. See the section below.
//! - Decide on a protocol name. Each gossiping protocol should have a different one.
//! - Build a `GossipEngine` using these three elements.
//! - Use the methods of the `GossipEngine` in order to send out messages and receive incoming
//!   messages.
//!
//! The `GossipEngine` will automatically use `Network::add_set_reserved` and
//! `Network::remove_set_reserved` to maintain a set of peers equal to the set of peers the
//! node is syncing from. See the documentation of `sc-network` for more explanations about the
//! concepts of peer sets.
//!
//! # What is a validator?
//!
//! The primary role of a `Validator` is to process incoming messages from peers, and decide
//! whether to discard them or process them. It also decides whether to re-broadcast the message.
//!
//! The secondary role of the `Validator` is to check if a message is allowed to be sent to a given
//! peer. All messages, before being sent, will be checked against this filter.
//! This enables the validator to use information it's aware of about connected peers to decide
//! whether to send messages to them at any given moment in time - In particular, to wait until
//! peers can accept and process the message before sending it.
//!
//! Lastly, the fact that gossip validators can decide not to rebroadcast messages
//! opens the door for neighbor status packets to be baked into the gossip protocol.
//! These status packets will typically contain light pieces of information
//! used to inform peers of a current view of protocol state.

pub use self::{
	bridge::GossipEngine,
	state_machine::TopicNotification,
	validator::{DiscardAll, MessageIntent, ValidationResult, Validator, ValidatorContext},
};

use futures::prelude::*;
use sc_network::{multiaddr, Event, ExHashT, NetworkService, PeerId, ReputationChange};
use sp_runtime::traits::Block as BlockT;
use std::{borrow::Cow, iter, pin::Pin, sync::Arc};

mod bridge;
mod state_machine;
mod validator;

/// Abstraction over a network.
pub trait Network<B: BlockT> {
	/// Returns a stream of events representing what happens on the network.
	fn event_stream(&self) -> Pin<Box<dyn Stream<Item = Event> + Send>>;

	/// Adjust the reputation of a node.
	fn report_peer(&self, peer_id: PeerId, reputation: ReputationChange);

	/// Adds the peer to the set of peers to be connected to with this protocol.
	fn add_set_reserved(&self, who: PeerId, protocol: Cow<'static, str>);

	/// Removes the peer from the set of peers to be connected to with this protocol.
	fn remove_set_reserved(&self, who: PeerId, protocol: Cow<'static, str>);

	/// Force-disconnect a peer.
	fn disconnect_peer(&self, who: PeerId, protocol: Cow<'static, str>);

	/// Send a notification to a peer.
	fn write_notification(&self, who: PeerId, protocol: Cow<'static, str>, message: Vec<u8>);

	/// Notify everyone we're connected to that we have the given block.
	///
	/// Note: this method isn't strictly related to gossiping and should eventually be moved
	/// somewhere else.
	fn announce(&self, block: B::Hash, associated_data: Option<Vec<u8>>);
}

impl<B: BlockT, H: ExHashT> Network<B> for Arc<NetworkService<B, H>> {
	fn event_stream(&self) -> Pin<Box<dyn Stream<Item = Event> + Send>> {
		Box::pin(NetworkService::event_stream(self, "network-gossip"))
	}

	fn report_peer(&self, peer_id: PeerId, reputation: ReputationChange) {
		NetworkService::report_peer(self, peer_id, reputation);
	}

	fn add_set_reserved(&self, who: PeerId, protocol: Cow<'static, str>) {
		let addr =
			iter::once(multiaddr::Protocol::P2p(who.into())).collect::<multiaddr::Multiaddr>();
		let result =
			NetworkService::add_peers_to_reserved_set(self, protocol, iter::once(addr).collect());
		if let Err(err) = result {
			log::error!(target: "gossip", "add_set_reserved failed: {}", err);
		}
	}

	fn remove_set_reserved(&self, who: PeerId, protocol: Cow<'static, str>) {
		let addr =
			iter::once(multiaddr::Protocol::P2p(who.into())).collect::<multiaddr::Multiaddr>();
		let result = NetworkService::remove_peers_from_reserved_set(
			self,
			protocol,
			iter::once(addr).collect(),
		);
		if let Err(err) = result {
			log::error!(target: "gossip", "remove_set_reserved failed: {}", err);
		}
	}

	fn disconnect_peer(&self, who: PeerId, protocol: Cow<'static, str>) {
		NetworkService::disconnect_peer(self, who, protocol)
	}

	fn write_notification(&self, who: PeerId, protocol: Cow<'static, str>, message: Vec<u8>) {
		NetworkService::write_notification(self, who, protocol, message)
	}

	fn announce(&self, block: B::Hash, associated_data: Option<Vec<u8>>) {
		NetworkService::announce_block(self, block, associated_data)
	}
}
