// Copyright 2017-2019 Parity Technologies (UK) Ltd
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
#![warn(unused_extern_crates)]
#![warn(missing_docs)]

//! Substrate-specific P2P networking: synchronizing blocks, propagating BFT messages.
//! Allows attachment of an optional subprotocol for chain-specific requests.
//! 
//! **Important**: This crate is unstable and the API and usage may change.
//!

mod service;
mod sync;
#[macro_use]
mod protocol;
mod chain;
mod blocks;
mod on_demand;
mod util;
pub mod config;
pub mod consensus_gossip;
pub mod error;
pub mod message;
pub mod specialization;

#[cfg(any(test, feature = "test-helpers"))]
pub mod test;

pub use chain::Client as ClientHandle;
pub use service::{Service, FetchFuture, TransactionPool, ManageNetwork, NetworkMsg, SyncProvider, ExHashT};
pub use protocol::{ProtocolStatus, PeerInfo, Context};
pub use sync::{Status as SyncStatus, SyncState};
pub use network_libp2p::{
	identity, multiaddr,
	ProtocolId, Severity, Multiaddr,
	NetworkState, NetworkStatePeer, NetworkStateNotConnectedPeer, NetworkStatePeerEndpoint,
	NodeKeyConfig, Secret, Secp256k1Secret, Ed25519Secret,
	build_multiaddr, PeerId, PublicKey
};
pub use message::{generic as generic_message, RequestId, Status as StatusMessage};
pub use error::Error;
pub use on_demand::{OnDemand, OnDemandService, RemoteResponse};
#[doc(hidden)]
pub use runtime_primitives::traits::Block as BlockT;
