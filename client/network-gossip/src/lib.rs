// Copyright 2019 Parity Technologies (UK) Ltd.
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

pub use self::bridge::GossipEngine;
// TODO: remove
pub use self::state_machine::*;

use network::{specialization::NetworkSpecialization, Event, ExHashT, NetworkService, PeerId};
use network::message::generic::ConsensusMessage;
use sr_primitives::{traits::Block as BlockT, ConsensusEngineId};
use std::{borrow::Cow, sync::Arc};

mod bridge;
mod state_machine;

/// Abstraction over a network.
pub trait Network {
	/// Returns a stream of events representing what happens on the network.
	fn events_stream(&self) -> Box<dyn futures01::Stream<Item = Event, Error = ()> + Send>;

	/// Adjust the reputation of a node.
	fn report_peer(&self, peer_id: PeerId, reputation: i32);

	/// Force-disconnect a peer.
	fn disconnect_peer(&mut self, who: PeerId);

	/// Send a notification to a peer.
	fn write_notif(&self, who: PeerId, proto_name: Cow<'static, [u8]>, engine_id: ConsensusEngineId, message: Vec<u8>);

	/// Registers a notifications protocol.
	///
	/// See the documentation of [`NetworkService:register_notif_protocol`] for more information.
	fn register_notif_protocol(
		&self,
		proto_name: impl Into<Cow<'static, [u8]>>,
		engine_id: ConsensusEngineId,
		handshake: impl Into<Vec<u8>>
	);
}

impl<B: BlockT, S: NetworkSpecialization<B>, H: ExHashT> Network for Arc<NetworkService<B, S, H>> {
	fn events_stream(&self) -> Box<dyn futures01::Stream<Item = Event, Error = ()> + Send> {
		Box::new(NetworkService::events_stream(self))
	}

	fn report_peer(&self, peer_id: PeerId, reputation: i32) {
		NetworkService::report_peer(self, peer_id, reputation);
	}

	fn disconnect_peer(&mut self, who: PeerId) {
		unimplemented!()		// TODO:
	}

	fn write_notif(&self, who: PeerId, proto_name: Cow<'static, [u8]>, engine_id: ConsensusEngineId, message: Vec<u8>) {
		let message = ConsensusMessage {
			engine_id,
			data: message,
		};

		NetworkService::write_notif(self, who, proto_name, message)
	}

	fn register_notif_protocol(
		&self,
		proto_name: impl Into<Cow<'static, [u8]>>,
		engine_id: ConsensusEngineId,
		handshake: impl Into<Vec<u8>>
	) {
		NetworkService::register_notif_protocol(self, proto_name, engine_id, handshake)
	}
}
