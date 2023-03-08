// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! Configuration of the networking layer.
//!
//! The [`Params`] struct is the struct that must be passed in order to initialize the networking.
//! See the documentation of [`Params`].

pub use sc_network_common::{
	config::{NetworkConfiguration, ProtocolId},
	protocol::role::Role,
	request_responses::{
		IncomingRequest, OutgoingResponse, ProtocolConfig as RequestResponseConfig,
	},
	sync::warp::WarpSyncProvider,
	ExHashT,
};

pub use libp2p::{build_multiaddr, core::PublicKey, identity};

use prometheus_endpoint::Registry;
use sc_network_common::config::NonDefaultSetConfig;
use std::{future::Future, pin::Pin, sync::Arc};

/// Network initialization parameters.
pub struct Params<Client> {
	/// Assigned role for our node (full, light, ...).
	pub role: Role,

	/// How to spawn background tasks.
	pub executor: Box<dyn Fn(Pin<Box<dyn Future<Output = ()> + Send>>) + Send>,

	/// Network layer configuration.
	pub network_config: NetworkConfiguration,

	/// Client that contains the blockchain.
	pub chain: Arc<Client>,

	/// Legacy name of the protocol to use on the wire. Should be different for each chain.
	pub protocol_id: ProtocolId,

	/// Fork ID to distinguish protocols of different hard forks. Part of the standard protocol
	/// name on the wire.
	pub fork_id: Option<String>,

	/// Registry for recording prometheus metrics to.
	pub metrics_registry: Option<Registry>,

	/// Block announce protocol configuration
	pub block_announce_config: NonDefaultSetConfig,

	/// Request response protocol configurations
	pub request_response_protocol_configs: Vec<RequestResponseConfig>,
}
