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
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.?

#![recursion_limit="128"]
#![type_length_limit = "268435456"]

extern crate parking_lot;
extern crate fnv;
extern crate futures;
extern crate tokio;
extern crate tokio_io;
extern crate tokio_timer;
extern crate ethkey;
extern crate libc;
extern crate libp2p;
extern crate rand;
extern crate bytes;
extern crate varint;

extern crate ethcore_io as io;
extern crate ethereum_types;
extern crate ipnetwork;

#[macro_use]
extern crate error_chain;
#[macro_use]
extern crate log;
#[cfg(test)] #[macro_use]
extern crate assert_matches;

pub use connection_filter::{ConnectionFilter, ConnectionDirection};
pub use io::TimerToken;
pub use error::{Error, ErrorKind, DisconnectReason};
pub use traits::*;

mod connection_filter;
mod custom_proto;
mod error;
mod network_state;
mod service;
mod timeouts;
mod traits;
mod transport;

pub use service::NetworkService;

/// Check if node url is valid
pub fn validate_node_url(url: &str) -> Result<(), Error> {
	match url.parse::<libp2p::multiaddr::Multiaddr>() {
		Ok(_) => Ok(()),
		Err(_) => Err(ErrorKind::InvalidNodeId.into()),
	}
}
