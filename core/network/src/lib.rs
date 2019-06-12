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
//!
//! **Important**: This crate is unstable and the API and usage may change.
//!

mod service;
#[macro_use]
mod protocol;
mod chain;
mod on_demand_layer;
pub mod config;
pub mod error;

#[cfg(any(test, feature = "test-helpers"))]
pub mod test;

pub use chain::{Client as ClientHandle, FinalityProofProvider};
pub use service::{
	NetworkService, NetworkWorker, FetchFuture, TransactionPool, ManageNetwork,
	NetworkMsg, SyncProvider, ExHashT, ReportHandle,
};
pub use protocol::{ProtocolStatus, PeerInfo, Context, consensus_gossip, message, specialization};
pub use protocol::sync::{Status as SyncStatus, SyncState};
pub use network_libp2p::{
	identity, multiaddr,
	ProtocolId, Multiaddr,
	NetworkState, NetworkStatePeer, NetworkStateNotConnectedPeer, NetworkStatePeerEndpoint,
	NodeKeyConfig, Secret, Secp256k1Secret, Ed25519Secret,
	build_multiaddr, PeerId, PublicKey
};
pub use message::{generic as generic_message, RequestId, Status as StatusMessage};
pub use error::Error;
pub use protocol::on_demand::AlwaysBadChecker;
pub use on_demand_layer::{OnDemand, RemoteResponse};
#[doc(hidden)]
pub use runtime_primitives::traits::Block as BlockT;
