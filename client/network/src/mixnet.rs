// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

//! Mixnet substrate topology.
//!
//! This topology is a simple star limited to authorities.

use futures::Stream;
use log::error;
use mixnet::{MixPeerId, MixPublicKey, Topology};
use sp_runtime::traits::Block as BlockT;
use std::{collections::BTreeMap, pin::Pin};
pub use sp_finality_grandpa::{AuthorityList, SetId};

type EventsStream = Pin<Box<dyn Stream<Item = Command> + Send>>;

/// Command for the mixnet behaviour.
#[derive(Clone, Debug)]
pub enum Command {
	/// Finalized block.
	BlockFinalized,
	/// New authority set on block finalized.
	NewAuthoritySet(AuthorityList),
}

// TODO could be a ratio with the number of hop
// require.
const LOW_MIXNET_THRESHOLD: usize = 5;

/// Substrate specific params for mixnet.
#[derive(Clone, Debug)]
pub struct MixnetParams {
	/// Protocol to listen for authority node connection.
	/// TODO remove: no need for it
	pub authority_protocol: &'static str,
}

/// Topology for mixnet.
/// This restrict the nodes for routing to authorities.
///
/// Other nodes can join the swarm but will not participate
/// in the mixnet.
///
/// When sending a message, the message can only reach nodes
/// that are part of the topology.
///
/// TODO allow validator/authorith to gossip/commit to a different
/// node.
/// TODO node with only mix component (proxying transaction and query).
pub struct AuthorityStar {
	authorities: BTreeMap<MixPeerId, MixPeerInfo>,
	// protocol to listen to for notification to identify authorities connection.
	authority_protocol: &'static str,
	// Is this node part of the topology and routing message.
	routing: bool,
}

/// Information related to a peer in the mixnet topology.
pub struct MixPeerInfo {
	id: MixPeerId,
	public_key: MixPublicKey,
}

impl AuthorityStar {
	/// Instantiate a new topology.
	pub fn new(authority_protocol: &'static str, routing: bool) -> Self {
		AuthorityStar {
			authorities: BTreeMap::new(), // TODO should we insert our node?
			authority_protocol,
			routing,
		}
	}

	/*
	/// Build the command stream for this topology.
	pub fn command_stream(event_streams: &mut out_events::OutChannels) -> EventsStream {
		let (tx, rx) = out_events::channel("mixnet-handler", Some(event_filter));
		event_streams.push(tx);
		Box::pin(rx)
	}
	*/
}

impl Topology for AuthorityStar {
	fn random_recipient(&self) -> Option<MixPeerId> {
		use rand::RngCore;
		if self.authorities.len() < LOW_MIXNET_THRESHOLD || self.authorities.len() == 0 {
			return None
		}
		// Warning this assume that PeerId is a random value.
		// This is currently the case (sha256 of encoded ed25519 key).
		let mut ix = [0u8; 32];
		rand::thread_rng().fill_bytes(&mut ix[..]); // TODO can less than 32 bytes.
		let ix = match MixPeerId::from_bytes(&ix[..]) {
			Ok(ix) => ix,
			Err(err) => {
				error!(target: "mixnet", "Invalid key for mixnet random selection {:?}", err);
				return None
			},
		};
		if let Some(key) = self.authorities.range(ix..).next() {
			Some(key.1.id.clone())
		} else {
			self.authorities.range(..ix).rev().next().map(|key| key.1.id.clone())
		}
	}

	/// For a given peer return a list of peers it is supposed to be connected to.
	/// Return `None` if peer is unknown to the topology.
	/// TODO when `None` allow sending even if not part of topology but in the mixnet:
	/// external hop for latest (see gen_path function). Then last hop will expose
	/// a new connection, so it need to be an additional hop (if possible).
	fn neighbors(&self, id: &MixPeerId) -> Option<Vec<(MixPeerId, MixPublicKey)>> {
		// TODO check maintaining neighbor table
		None
	}

	fn routing(&self) -> bool {
		self.routing
	}
}
/*
fn event_filter(event: &Event) -> bool {
	match event {
		Event::NotificationStreamOpened { .. } | Event::NotificationStreamClosed { .. } => true,
		_ => false,
	}
}*/
