// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
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

use crate::helpers::Receiver;
use jsonrpc_derive::rpc;
use futures::{future::BoxFuture, compat::Compat};

use self::error::Result as SystemResult;

pub use self::helpers::{SystemInfo, Health, PeerInfo, NodeRole, SyncState};
pub use self::gen_client::Client as SystemClient;

/// Substrate system RPC API
#[rpc]
pub trait SystemApi<Hash, Number> {
	/// Get the node's implementation name. Plain old string.
	#[rpc(name = "system_name")]
	fn system_name(&self) -> SystemResult<String>;

	/// Get the node implementation's version. Should be a semver string.
	#[rpc(name = "system_version")]
	fn system_version(&self) -> SystemResult<String>;

	/// Get the chain's name. Given as a string identifier.
	#[rpc(name = "system_chain")]
	fn system_chain(&self) -> SystemResult<String>;

	/// Get the chain's type.
	#[rpc(name = "system_chainType")]
	fn system_type(&self) -> SystemResult<sc_chain_spec::ChainType>;

	/// Get a custom set of properties as a JSON object, defined in the chain spec.
	#[rpc(name = "system_properties")]
	fn system_properties(&self) -> SystemResult<sc_chain_spec::Properties>;

	/// Return health status of the node.
	///
	/// Node is considered healthy if it is:
	/// - connected to some peers (unless running in dev mode)
	/// - not performing a major sync
	#[rpc(name = "system_health", returns = "Health")]
	fn system_health(&self) -> Receiver<Health>;

	/// Returns the base58-encoded PeerId of the node.
	#[rpc(name = "system_localPeerId", returns = "String")]
	fn system_local_peer_id(&self) -> Receiver<String>;

	/// Returns the multiaddresses that the local node is listening on
	///
	/// The addresses include a trailing `/p2p/` with the local PeerId, and are thus suitable to
	/// be passed to `system_addReservedPeer` or as a bootnode address for example.
	#[rpc(name = "system_localListenAddresses", returns = "Vec<String>")]
	fn system_local_listen_addresses(&self) -> Receiver<Vec<String>>;

	/// Returns currently connected peers
	#[rpc(name = "system_peers", returns = "Vec<PeerInfo<Hash, Number>>")]
	fn system_peers(&self)
		-> Compat<BoxFuture<'static, jsonrpc_core::Result<Vec<PeerInfo<Hash, Number>>>>>;

	/// Returns current state of the network.
	///
	/// **Warning**: This API is not stable. Please do not programmatically interpret its output,
	/// as its format might change at any time.
	// TODO: the future of this call is uncertain: https://github.com/paritytech/substrate/issues/1890
	// https://github.com/paritytech/substrate/issues/5541
	#[rpc(name = "system_unstable_networkState", returns = "jsonrpc_core::Value")]
	fn system_network_state(&self)
		-> Compat<BoxFuture<'static, jsonrpc_core::Result<jsonrpc_core::Value>>>;

	/// Adds a reserved peer. Returns the empty string or an error. The string
	/// parameter should encode a `p2p` multiaddr.
	///
	/// `/ip4/198.51.100.19/tcp/30333/p2p/QmSk5HQbn6LhUwDiNMseVUjuRYhEtYj4aUZ6WfWoGURpdV`
	/// is an example of a valid, passing multiaddr with PeerId attached.
	#[rpc(name = "system_addReservedPeer", returns = "()")]
	fn system_add_reserved_peer(&self, peer: String)
		-> Compat<BoxFuture<'static, Result<(), jsonrpc_core::Error>>>;

	/// Remove a reserved peer. Returns the empty string or an error. The string
	/// should encode only the PeerId e.g. `QmSk5HQbn6LhUwDiNMseVUjuRYhEtYj4aUZ6WfWoGURpdV`.
	#[rpc(name = "system_removeReservedPeer", returns = "()")]
	fn system_remove_reserved_peer(&self, peer_id: String)
		-> Compat<BoxFuture<'static, Result<(), jsonrpc_core::Error>>>;

	/// Returns the list of reserved peers
	#[rpc(name = "system_reservedPeers", returns = "Vec<String>")]
	fn system_reserved_peers(&self) -> Receiver<Vec<String>>;

	/// Returns the roles the node is running as.
	#[rpc(name = "system_nodeRoles", returns = "Vec<NodeRole>")]
	fn system_node_roles(&self) -> Receiver<Vec<NodeRole>>;

	/// Returns the state of the syncing of the node: starting block, current best block, highest
	/// known block.
	#[rpc(name = "system_syncState", returns = "SyncState<Number>")]
	fn system_sync_state(&self) -> Receiver<SyncState<Number>>;

	/// Adds the supplied directives to the current log filter
	///
	/// The syntax is identical to the CLI `<target>=<level>`:
	///
	/// `sync=debug,state=trace`
	#[rpc(name = "system_addLogFilter", returns = "()")]
	fn system_add_log_filter(&self, directives: String)
		-> Result<(), jsonrpc_core::Error>;

	/// Resets the log filter to Substrate defaults
	#[rpc(name = "system_resetLogFilter", returns = "()")]
	fn system_reset_log_filter(&self)
		-> Result<(), jsonrpc_core::Error>;
}
