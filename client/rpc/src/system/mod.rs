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

#[cfg(test)]
mod tests;

use futures::channel::oneshot;
use jsonrpsee::{
	core::{async_trait, error::Error as JsonRpseeError, JsonValue, RpcResult},
	types::error::{CallError, ErrorCode, ErrorObject},
};
use sc_rpc_api::DenyUnsafe;
use sc_tracing::logging;
use sc_utils::mpsc::TracingUnboundedSender;
use sp_runtime::traits::{self, Header as HeaderT};

use self::error::Result;

pub use self::helpers::{Health, NodeRole, PeerInfo, SyncState, SystemInfo};
pub use sc_rpc_api::system::*;

/// System API implementation
pub struct System<B: traits::Block> {
	info: SystemInfo,
	send_back: TracingUnboundedSender<Request<B>>,
	deny_unsafe: DenyUnsafe,
}

/// Request to be processed.
pub enum Request<B: traits::Block> {
	/// Must return the health of the network.
	Health(oneshot::Sender<Health>),
	/// Must return the base58-encoded local `PeerId`.
	LocalPeerId(oneshot::Sender<String>),
	/// Must return the string representation of the addresses we listen on, including the
	/// trailing `/p2p/`.
	LocalListenAddresses(oneshot::Sender<Vec<String>>),
	/// Must return information about the peers we are connected to.
	Peers(oneshot::Sender<Vec<PeerInfo<B::Hash, <B::Header as HeaderT>::Number>>>),
	/// Must return the state of the network.
	NetworkState(oneshot::Sender<serde_json::Value>),
	/// Must return any potential parse error.
	NetworkAddReservedPeer(String, oneshot::Sender<Result<()>>),
	/// Must return any potential parse error.
	NetworkRemoveReservedPeer(String, oneshot::Sender<Result<()>>),
	/// Must return the list of reserved peers
	NetworkReservedPeers(oneshot::Sender<Vec<String>>),
	/// Must return the node role.
	NodeRoles(oneshot::Sender<Vec<NodeRole>>),
	/// Must return the state of the node syncing.
	SyncState(oneshot::Sender<SyncState<<B::Header as HeaderT>::Number>>),
}

impl<B: traits::Block> System<B> {
	/// Creates new `System`.
	///
	/// The `send_back` will be used to transmit some of the requests. The user is responsible for
	/// reading from that channel and answering the requests.
	pub fn new(
		info: SystemInfo,
		send_back: TracingUnboundedSender<Request<B>>,
		deny_unsafe: DenyUnsafe,
	) -> Self {
		System { info, send_back, deny_unsafe }
	}
}

#[async_trait]
impl<B: traits::Block> SystemApiServer<B::Hash, <B::Header as HeaderT>::Number> for System<B> {
	fn system_name(&self) -> RpcResult<String> {
		Ok(self.info.impl_name.clone())
	}

	fn system_version(&self) -> RpcResult<String> {
		Ok(self.info.impl_version.clone())
	}

	fn system_chain(&self) -> RpcResult<String> {
		Ok(self.info.chain_name.clone())
	}

	fn system_type(&self) -> RpcResult<sc_chain_spec::ChainType> {
		Ok(self.info.chain_type.clone())
	}

	fn system_properties(&self) -> RpcResult<sc_chain_spec::Properties> {
		Ok(self.info.properties.clone())
	}

	async fn system_health(&self) -> RpcResult<Health> {
		let (tx, rx) = oneshot::channel();
		let _ = self.send_back.unbounded_send(Request::Health(tx));
		rx.await.map_err(|e| JsonRpseeError::to_call_error(e))
	}

	async fn system_local_peer_id(&self) -> RpcResult<String> {
		let (tx, rx) = oneshot::channel();
		let _ = self.send_back.unbounded_send(Request::LocalPeerId(tx));
		rx.await.map_err(|e| JsonRpseeError::to_call_error(e))
	}

	async fn system_local_listen_addresses(&self) -> RpcResult<Vec<String>> {
		let (tx, rx) = oneshot::channel();
		let _ = self.send_back.unbounded_send(Request::LocalListenAddresses(tx));
		rx.await.map_err(|e| JsonRpseeError::to_call_error(e))
	}

	async fn system_peers(
		&self,
	) -> RpcResult<Vec<PeerInfo<B::Hash, <B::Header as HeaderT>::Number>>> {
		self.deny_unsafe.check_if_safe()?;
		let (tx, rx) = oneshot::channel();
		let _ = self.send_back.unbounded_send(Request::Peers(tx));
		rx.await.map_err(|e| JsonRpseeError::to_call_error(e))
	}

	async fn system_network_state(&self) -> RpcResult<JsonValue> {
		self.deny_unsafe.check_if_safe()?;
		let (tx, rx) = oneshot::channel();
		let _ = self.send_back.unbounded_send(Request::NetworkState(tx));
		rx.await.map_err(|e| JsonRpseeError::to_call_error(e))
	}

	async fn system_add_reserved_peer(&self, peer: String) -> RpcResult<()> {
		self.deny_unsafe.check_if_safe()?;
		let (tx, rx) = oneshot::channel();
		let _ = self.send_back.unbounded_send(Request::NetworkAddReservedPeer(peer, tx));
		match rx.await {
			Ok(Ok(())) => Ok(()),
			Ok(Err(e)) => Err(JsonRpseeError::from(e)),
			Err(e) => Err(JsonRpseeError::to_call_error(e)),
		}
	}

	async fn system_remove_reserved_peer(&self, peer: String) -> RpcResult<()> {
		self.deny_unsafe.check_if_safe()?;
		let (tx, rx) = oneshot::channel();
		let _ = self.send_back.unbounded_send(Request::NetworkRemoveReservedPeer(peer, tx));
		match rx.await {
			Ok(Ok(())) => Ok(()),
			Ok(Err(e)) => Err(JsonRpseeError::from(e)),
			Err(e) => Err(JsonRpseeError::to_call_error(e)),
		}
	}

	async fn system_reserved_peers(&self) -> RpcResult<Vec<String>> {
		let (tx, rx) = oneshot::channel();
		let _ = self.send_back.unbounded_send(Request::NetworkReservedPeers(tx));
		rx.await.map_err(|e| JsonRpseeError::to_call_error(e))
	}

	async fn system_node_roles(&self) -> RpcResult<Vec<NodeRole>> {
		let (tx, rx) = oneshot::channel();
		let _ = self.send_back.unbounded_send(Request::NodeRoles(tx));
		rx.await.map_err(|e| JsonRpseeError::to_call_error(e))
	}

	async fn system_sync_state(&self) -> RpcResult<SyncState<<B::Header as HeaderT>::Number>> {
		let (tx, rx) = oneshot::channel();
		let _ = self.send_back.unbounded_send(Request::SyncState(tx));
		rx.await.map_err(|e| JsonRpseeError::to_call_error(e))
	}

	fn system_add_log_filter(&self, directives: String) -> RpcResult<()> {
		self.deny_unsafe.check_if_safe()?;

		logging::add_directives(&directives);
		logging::reload_filter().map_err(|e| {
			JsonRpseeError::Call(CallError::Custom(ErrorObject::owned(
				ErrorCode::InternalError.code(),
				e,
				None::<()>,
			)))
		})
	}

	fn system_reset_log_filter(&self) -> RpcResult<()> {
		self.deny_unsafe.check_if_safe()?;
		logging::reset_log_filter().map_err(|e| {
			JsonRpseeError::Call(CallError::Custom(ErrorObject::owned(
				ErrorCode::InternalError.code(),
				e,
				None::<()>,
			)))
		})
	}
}
