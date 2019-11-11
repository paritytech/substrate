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

//! Substrate system API.

#[cfg(test)]
mod tests;

use futures::{channel::{mpsc, oneshot}, compat::Compat};
use api::Receiver;
use sr_primitives::traits::{self, Header as HeaderT};
use self::error::Result;

pub use api::system::*;
pub use self::helpers::{Properties, SystemInfo, Health, PeerInfo, NodeRole};
pub use self::gen_client::Client as SystemClient;

/// System API implementation
pub struct System<B: traits::Block> {
	info: SystemInfo,
	send_back: mpsc::UnboundedSender<Request<B>>,
}

/// Request to be processed.
pub enum Request<B: traits::Block> {
	/// Must return the health of the network.
	Health(oneshot::Sender<Health>),
	/// Must return information about the peers we are connected to.
	Peers(oneshot::Sender<Vec<PeerInfo<B::Hash, <B::Header as HeaderT>::Number>>>),
	/// Must return the state of the network.
	NetworkState(oneshot::Sender<rpc::Value>),
	/// Must return the node role.
	NodeRoles(oneshot::Sender<Vec<NodeRole>>)
}

impl<B: traits::Block> System<B> {
	/// Creates new `System`.
	///
	/// The `send_back` will be used to transmit some of the requests. The user is responsible for
	/// reading from that channel and answering the requests.
	pub fn new(
		info: SystemInfo,
		send_back: mpsc::UnboundedSender<Request<B>>
	) -> Self {
		System {
			info,
			send_back,
		}
	}
}

impl<B: traits::Block> SystemApi<B::Hash, <B::Header as HeaderT>::Number> for System<B> {
	fn system_name(&self) -> Result<String> {
		Ok(self.info.impl_name.clone())
	}

	fn system_version(&self) -> Result<String> {
		Ok(self.info.impl_version.clone())
	}

	fn system_chain(&self) -> Result<String> {
		Ok(self.info.chain_name.clone())
	}

	fn system_properties(&self) -> Result<Properties> {
		Ok(self.info.properties.clone())
	}

	fn system_health(&self) -> Receiver<Health> {
		let (tx, rx) = oneshot::channel();
		let _ = self.send_back.unbounded_send(Request::Health(tx));
		Receiver(Compat::new(rx))
	}

	fn system_peers(&self) -> Receiver<Vec<PeerInfo<B::Hash, <B::Header as HeaderT>::Number>>> {
		let (tx, rx) = oneshot::channel();
		let _ = self.send_back.unbounded_send(Request::Peers(tx));
		Receiver(Compat::new(rx))
	}

	fn system_network_state(&self) -> Receiver<rpc::Value> {
		let (tx, rx) = oneshot::channel();
		let _ = self.send_back.unbounded_send(Request::NetworkState(tx));
		Receiver(Compat::new(rx))
	}

	fn system_node_roles(&self) -> Receiver<Vec<NodeRole>> {
		let (tx, rx) = oneshot::channel();
		let _ = self.send_back.unbounded_send(Request::NodeRoles(tx));
		Receiver(Compat::new(rx))
	}
}
