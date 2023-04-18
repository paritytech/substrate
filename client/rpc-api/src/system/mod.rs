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

//! Substrate system API.

pub mod error;
pub mod helpers;

use jsonrpsee::{core::JsonValue, proc_macros::rpc};

pub use self::helpers::{Health, NodeRole, PeerInfo, SyncState, SystemInfo};
pub use error::Error;

/// Substrate system RPC API
#[rpc(client, server)]
pub trait SystemApi<Hash, Number> {
	/// Get the node's implementation name. Plain old string.
	#[method(name = "system_name")]
	fn system_name(&self) -> Result<String, Error>;

	/// Get the node implementation's version. Should be a semver string.
	#[method(name = "system_version")]
	fn system_version(&self) -> Result<String, Error>;

	/// Get the chain's name. Given as a string identifier.
	#[method(name = "system_chain")]
	fn system_chain(&self) -> Result<String, Error>;

	/// Get the chain's type.
	#[method(name = "system_chainType")]
	fn system_type(&self) -> Result<sc_chain_spec::ChainType, Error>;

	/// Get a custom set of properties as a JSON object, defined in the chain spec.
	#[method(name = "system_properties")]
	fn system_properties(&self) -> Result<sc_chain_spec::Properties, Error>;

	/// Return health status of the node.
	///
	/// Node is considered healthy if it is:
	/// - connected to some peers (unless running in dev mode)
	/// - not performing a major sync
	#[method(name = "system_health")]
	async fn system_health(&self) -> Result<Health, Error>;

	/// Returns the base58-encoded PeerId of the node.
	#[method(name = "system_localPeerId")]
	async fn system_local_peer_id(&self) -> Result<String, Error>;

	/// Returns the multi-addresses that the local node is listening on
	///
	/// The addresses include a trailing `/p2p/` with the local PeerId, and are thus suitable to
	/// be passed to `addReservedPeer` or as a bootnode address for example.
	#[method(name = "system_localListenAddresses")]
	async fn system_local_listen_addresses(&self) -> Result<Vec<String>, Error>;

	/// Returns currently connected peers
	#[method(name = "system_peers")]
	async fn system_peers(&self) -> Result<Vec<PeerInfo<Hash, Number>>, Error>;

	/// Returns current state of the network.
	///
	/// **Warning**: This API is not stable. Please do not programmatically interpret its output,
	/// as its format might change at any time.
	// TODO: the future of this call is uncertain: https://github.com/paritytech/substrate/issues/1890
	// https://github.com/paritytech/substrate/issues/5541
	#[method(name = "system_unstable_networkState")]
	async fn system_network_state(&self) -> Result<JsonValue, Error>;

	/// Adds a reserved peer. Returns the empty string or an error. The string
	/// parameter should encode a `p2p` multiaddr.
	///
	/// `/ip4/198.51.100.19/tcp/30333/p2p/QmSk5HQbn6LhUwDiNMseVUjuRYhEtYj4aUZ6WfWoGURpdV`
	/// is an example of a valid, passing multiaddr with PeerId attached.
	#[method(name = "system_addReservedPeer")]
	async fn system_add_reserved_peer(&self, peer: String) -> Result<(), Error>;

	/// Remove a reserved peer. Returns the empty string or an error. The string
	/// should encode only the PeerId e.g. `QmSk5HQbn6LhUwDiNMseVUjuRYhEtYj4aUZ6WfWoGURpdV`.
	#[method(name = "system_removeReservedPeer")]
	async fn system_remove_reserved_peer(&self, peer_id: String) -> Result<(), Error>;

	/// Returns the list of reserved peers
	#[method(name = "system_reservedPeers")]
	async fn system_reserved_peers(&self) -> Result<Vec<String>, Error>;

	/// Returns the roles the node is running as.
	#[method(name = "system_nodeRoles")]
	async fn system_node_roles(&self) -> Result<Vec<NodeRole>, Error>;

	/// Returns the state of the syncing of the node: starting block, current best block, highest
	/// known block.
	#[method(name = "system_syncState")]
	async fn system_sync_state(&self) -> Result<SyncState<Number>, Error>;

	/// Adds the supplied directives to the current log filter
	///
	/// The syntax is identical to the CLI `<target>=<level>`:
	///
	/// `sync=debug,state=trace`
	#[method(name = "system_addLogFilter")]
	fn system_add_log_filter(&self, directives: String) -> Result<(), Error>;

	/// Resets the log filter to Substrate defaults
	#[method(name = "system_resetLogFilter")]
	fn system_reset_log_filter(&self) -> Result<(), Error>;
}
