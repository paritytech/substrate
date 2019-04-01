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

#![warn(unused_extern_crates)]
#![warn(missing_docs)]

//! Substrate-specific P2P networking: synchronizing blocks, propagating BFT messages.
//! Allows attachment of an optional subprotocol for chain-specific requests.

mod service;
mod sync;
#[macro_use]
mod protocol;
mod blocks;
mod chain;
pub mod config;
pub mod consensus_gossip;
pub mod error;
pub mod message;
mod on_demand;
pub mod specialization;
mod util;

#[cfg(any(test, feature = "test-helpers"))]
pub mod test;

pub use chain::Client as ClientHandle;
pub use error::Error;
pub use message::{generic as generic_message, RequestId, Status as StatusMessage};
pub use network_libp2p::{
    build_multiaddr, identity, multiaddr, Ed25519Secret, Multiaddr, NetworkState,
    NetworkStateNotConnectedPeer, NetworkStatePeer, NetworkStatePeerEndpoint, NodeKeyConfig,
    PeerId, ProtocolId, PublicKey, Secp256k1Secret, Secret, Severity,
};
pub use on_demand::{OnDemand, OnDemandService, RemoteResponse};
pub use protocol::{Context, PeerInfo, ProtocolStatus};
#[doc(hidden)]
pub use runtime_primitives::traits::Block as BlockT;
pub use service::{
    ExHashT, FetchFuture, ManageNetwork, NetworkMsg, Service, SyncProvider, TransactionPool,
};
pub use sync::{Status as SyncStatus, SyncState};
