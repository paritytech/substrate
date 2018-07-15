// Copyright 2018 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.?

#![type_length_limit = "268435456"]

extern crate parking_lot;
extern crate fnv;
extern crate futures;
extern crate tokio_core;
extern crate tokio_io;
extern crate tokio_timer;
extern crate ethkey;
extern crate ethcore_network as network;
extern crate libp2p;
extern crate rand;
extern crate bytes;
extern crate varint;

#[macro_use]
extern crate log;

mod custom_proto;
mod network_state;
mod service;
mod timeouts;
mod transport;

pub use service::NetworkService;

/// Check if node url is valid
pub fn validate_node_url(url: &str) -> Result<(), network::Error> {
	match url.parse::<libp2p::multiaddr::Multiaddr>() {
		Ok(_) => Ok(()),
		Err(_) => Err(network::ErrorKind::InvalidNodeId.into()),
	}
}
