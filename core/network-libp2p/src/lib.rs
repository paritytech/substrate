// Copyright 2018 Parity Technologies (UK) Ltd.
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

//! Networking layer of Substrate.

mod behaviour;
mod custom_proto;
mod error;
mod secret;
mod service_task;
mod traits;
mod transport;

pub use crate::custom_proto::{CustomMessage, RegisteredProtocol};
pub use crate::error::{Error, ErrorKind, DisconnectReason};
pub use crate::secret::obtain_private_key;
pub use crate::service_task::{start_service, Service, ServiceEvent};
pub use crate::traits::{NetworkConfiguration, NodeIndex, NodeId, NonReservedPeerMode};
pub use crate::traits::{ProtocolId, Secret, Severity};
pub use libp2p::{Multiaddr, multiaddr::{Protocol}, multiaddr, PeerId, core::PublicKey};

/// Check if node url is valid
pub fn validate_node_url(url: &str) -> Result<(), Error> {
	match url.parse::<Multiaddr>() {
		Ok(_) => Ok(()),
		Err(_) => Err(ErrorKind::InvalidNodeId.into()),
	}
}

/// Parses a string address and returns the component, if valid.
pub fn parse_str_addr(addr_str: &str) -> Result<(PeerId, Multiaddr), Error> {
	let mut addr: Multiaddr = addr_str.parse().map_err(|_| ErrorKind::AddressParse)?;
	let who = match addr.pop() {
		Some(Protocol::P2p(key)) =>
			PeerId::from_multihash(key).map_err(|_| ErrorKind::AddressParse)?,
		_ => return Err(ErrorKind::AddressParse.into()),
	};
	Ok((who, addr))
}
