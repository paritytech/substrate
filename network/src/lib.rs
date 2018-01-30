// Copyright 2017 Parity Technologies (UK) Ltd.
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

#![warn(missing_docs)]

//! Implements polkadot protocol version as specified here:
//! https://github.com/paritytech/polkadot/wiki/Network-protocol

extern crate ethcore_network as network;
extern crate ethcore_io as core_io;
extern crate env_logger;
extern crate rand;
extern crate semver;
extern crate parking_lot;
extern crate smallvec;
extern crate ipnetwork;
extern crate polkadot_primitives as primitives;
extern crate polkadot_client as client;
extern crate polkadot_state_machine as state_machine;
extern crate polkadot_serializer as ser;
extern crate serde;
extern crate serde_json;
#[macro_use] extern crate serde_derive;
#[macro_use] extern crate log;
#[macro_use] extern crate bitflags;
#[macro_use] extern crate error_chain;

mod service;
mod sync;
mod protocol;
mod io;
mod message;
mod error;
mod config;
mod chain;
mod blocks;

#[cfg(test)]
mod test;

pub use service::Service;
pub use protocol::{ProtocolStatus};
pub use network::{NonReservedPeerMode, ConnectionFilter, ConnectionDirection, NetworkConfiguration};

// TODO: move it elsewhere
fn header_hash(header: &primitives::block::Header) -> primitives::block::HeaderHash {
	primitives::hash(&ser::to_vec(header))
}

