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

pub mod error;
pub mod helpers;

#[cfg(test)]
mod tests;

use crate::helpers::Receiver;
use futures::sync::{mpsc, oneshot};
use jsonrpc_derive::rpc;
use network;
use runtime_primitives::traits::{self, Header as HeaderT};

use self::error::Result;
pub use self::helpers::{Properties, SystemInfo, Health, PeerInfo};

pub use self::gen_client::Client as SystemClient;

/// Substrate system RPC API
#[rpc]
pub trait SystemApi<Hash, Number> {
	/// Get the node's implementation name. Plain old string.
	#[rpc(name = "system_name")]
	fn system_name(&self) -> Result<String>;

	/// Get the node implementation's version. Should be a semver string.
	#[rpc(name = "system_version")]
	fn system_version(&self) -> Result<String>;

	/// Get the chain's type. Given as a string identifier.
	#[rpc(name = "system_chain")]
	fn system_chain(&self) -> Result<String>;

	/// Get a custom set of properties as a JSON object, defined in the chain spec.
	#[rpc(name = "system_properties")]
	fn system_properties(&self) -> Result<Properties>;

	/// Return health status of the node.
	///
	/// Node is considered healthy if it is:
	/// - connected to some peers (unless running in dev mode)
	/// - not performing a major sync
	#[rpc(name = "system_health", returns = "Health")]
	fn system_health(&self) -> Receiver<Health>;

	/// Returns currently connected peers
	#[rpc(name = "system_peers", returns = "Vec<PeerInfo<Hash, Number>>")]
	fn system_peers(&self) -> Receiver<Vec<PeerInfo<Hash, Number>>>;

	/// Returns current state of the network.
	///
	/// **Warning**: This API is not stable.
	// TODO: make this stable and move structs https://github.com/paritytech/substrate/issues/1890
	#[rpc(name = "system_networkState", returns = "network::NetworkState")]
	fn system_network_state(&self) -> Receiver<network::NetworkState>;
}

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
	NetworkState(oneshot::Sender<network::NetworkState>),
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
		Receiver(rx)
	}

	fn system_peers(&self) -> Receiver<Vec<PeerInfo<B::Hash, <B::Header as HeaderT>::Number>>> {
		let (tx, rx) = oneshot::channel();
		let _ = self.send_back.unbounded_send(Request::Peers(tx));
		Receiver(rx)
	}

	fn system_network_state(&self) -> Receiver<network::NetworkState> {
		let (tx, rx) = oneshot::channel();
		let _ = self.send_back.unbounded_send(Request::NetworkState(tx));
		Receiver(rx)
	}
}
