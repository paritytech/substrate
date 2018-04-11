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

extern crate ethcore_network_devp2p as network_devp2p;
extern crate ethcore_network as network;
extern crate ethcore_io as core_io;
extern crate rand;
extern crate parking_lot;
extern crate substrate_primitives as primitives;
extern crate substrate_state_machine as state_machine;
extern crate substrate_serializer as ser;
extern crate substrate_client as client;
extern crate substrate_runtime_support as runtime_support;
extern crate substrate_bft;
extern crate serde;
extern crate serde_json;
extern crate futures;
extern crate ed25519;
#[macro_use] extern crate serde_derive;
#[macro_use] extern crate log;
#[macro_use] extern crate bitflags;
#[macro_use] extern crate error_chain;

#[cfg(test)] extern crate env_logger;
#[cfg(test)] extern crate substrate_test_runtime as test_runtime;
#[cfg(test)] extern crate substrate_keyring as keyring;
#[cfg(test)] #[macro_use] extern crate substrate_executor as executor;
#[cfg(test)] extern crate substrate_codec as codec;
#[cfg(test)] extern crate substrate_bft as bft;

mod service;
mod sync;
mod protocol;
mod io;
mod message;
mod config;
mod chain;
mod blocks;
mod consensus;
pub mod error;

#[cfg(test)] mod test;

pub use service::{Service, FetchFuture, StatementStream, ConsensusService, BftMessageStream,
	TransactionPool, Params, ManageNetwork, SyncProvider};
pub use protocol::{ProtocolStatus};
pub use sync::{Status as SyncStatus, SyncState};
pub use network::{NonReservedPeerMode, NetworkConfiguration};
pub use network_devp2p::{ConnectionFilter, ConnectionDirection};
pub use message::{Statement, BftMessage, LocalizedBftMessage, ConsensusVote, SignedConsensusVote, SignedConsensusMessage, SignedConsensusProposal};
pub use error::Error;
pub use config::{Role, ProtocolConfig};

// TODO: move it elsewhere
fn header_hash(header: &primitives::Header) -> primitives::block::HeaderHash {
	use runtime_support::Hashable;
	header.blake2_256().into()
}
