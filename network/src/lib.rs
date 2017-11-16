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

extern crate ethcore_network as network;
extern crate ethcore_io as core_io;
extern crate env_logger;
extern crate rand;
extern crate semver;
extern crate parking_lot;
extern crate smallvec;
extern crate ipnetwork;
extern crate polkadot_primitives as primitives;
extern crate serde;
extern crate serde_json;
#[macro_use] extern crate serde_derive;
#[macro_use] extern crate log;
#[macro_use] extern crate bitflags;
#[macro_use] extern crate error_chain;

pub mod service;
mod sync;
mod protocol;
mod io;
mod message;
mod error;
mod config;

#[cfg(test)]
mod tests;

pub use service::Service;
pub use protocol::{ProtocolStatus};
pub use network::{NonReservedPeerMode, ConnectionFilter, ConnectionDirection, NetworkConfiguration};
