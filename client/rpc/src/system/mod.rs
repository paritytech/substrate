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

#[cfg(test)]
mod tests;

use futures::{FutureExt, channel::oneshot};
use sc_rpc_api::DenyUnsafe;
use sc_tracing::logging;
use sp_utils::mpsc::TracingUnboundedSender;
use sp_runtime::traits::{self, Header as HeaderT};
use jsonrpsee_ws_server::RpcModule;
use jsonrpsee_types::error::{Error as JsonRpseeError, CallError as JsonRpseeCallError};

use self::error::Result;

pub use sc_rpc_api::system::*;
pub use self::helpers::{SystemInfo, Health, PeerInfo, NodeRole, SyncState};
pub use self::gen_client::Client as SystemClient;

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
	NetworkState(oneshot::Sender<rpc::Value>),
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
		System {
			info,
			send_back,
			deny_unsafe,
		}
	}

	/// Convert to a RPC Module.
	pub fn into_rpc_module(self) -> std::result::Result<RpcModule<Self>, JsonRpseeError> {
		let mut rpc_module = RpcModule::new(self);

		rpc_module.register_method("system_name", |_, system| {
			Ok(system.info.impl_name.clone())
		})?;

		rpc_module.register_method("system_version", |_, system| {
			Ok(system.info.impl_version.clone())
		})?;

		rpc_module.register_method("system_chain", |_, system| {
			Ok(system.info.chain_name.clone())
		})?;

		rpc_module.register_method("system_type", |_, system| {
			Ok(system.info.chain_type.clone())
		})?;

		rpc_module.register_method("system_properties", |_, system| {
			Ok(system.info.chain_type.clone())
		})?;

		rpc_module.register_async_method("system_health", |_, system| {
			async move {
				let (tx, rx) = oneshot::channel();
				let _ = system.send_back.unbounded_send(Request::Health(tx));
				rx.await.map_err(oneshot_canceled_err)
			}.boxed()
		})?;

		rpc_module.register_async_method("system_local_peer_id", |_, system| {
			async move {
				let (tx, rx) = oneshot::channel();
				let _ = system.send_back.unbounded_send(Request::LocalPeerId(tx));
				rx.await.map_err(oneshot_canceled_err)
			}.boxed()
		})?;

		rpc_module.register_async_method("system_local_listen_addresses", |_, system| {
			async move {
				let (tx, rx) = oneshot::channel();
				let _ = system.send_back.unbounded_send(Request::LocalListenAddresses(tx));
				rx.await.map_err(oneshot_canceled_err)
			}.boxed()
		})?;

		rpc_module.register_async_method("system_peers", |_, system| {
			async move {
				system.deny_unsafe.check_if_safe()?;
				let (tx, rx) = oneshot::channel();
				let _ = system.send_back.unbounded_send(Request::Peers(tx));
				rx.await.map_err(oneshot_canceled_err)
			}.boxed()
		})?;

		rpc_module.register_async_method("system_network_state", |_, system| {
			async move {
				system.deny_unsafe.check_if_safe()?;
				let (tx, rx) = oneshot::channel();
				let _ = system.send_back.unbounded_send(Request::NetworkState(tx));
				rx.await.map_err(oneshot_canceled_err)
			}.boxed()
		})?;

		rpc_module.register_async_method("system_add_reserved_peer", |param, system| {
			let peer = match param.one() {
				Ok(peer) => peer,
				Err(e) => return Box::pin(futures::future::err(e)),
			};
			async move {
				system.deny_unsafe.check_if_safe()?;
				let (tx, rx) = oneshot::channel();
				let _ = system.send_back.unbounded_send(Request::NetworkAddReservedPeer(peer, tx));
				rx.await.map_err(oneshot_canceled_err)
			}.boxed()
		})?;

		rpc_module.register_async_method("system_reserved_peers", |_, system| {
			async move {
				system.deny_unsafe.check_if_safe()?;
				let (tx, rx) = oneshot::channel();
				let _ = system.send_back.unbounded_send(Request::NetworkReservedPeers(tx));
				rx.await.map_err(oneshot_canceled_err)
			}.boxed()
		})?;

		rpc_module.register_async_method("system_node_roles", |_, system| {
			async move {
				system.deny_unsafe.check_if_safe()?;
				let (tx, rx) = oneshot::channel();
				let _ = system.send_back.unbounded_send(Request::NodeRoles(tx));
				rx.await.map_err(oneshot_canceled_err)
			}.boxed()
		})?;

		rpc_module.register_async_method("system_sync_state", |_, system| {
			async move {
				system.deny_unsafe.check_if_safe()?;
				let (tx, rx) = oneshot::channel();
				let _ = system.send_back.unbounded_send(Request::SyncState(tx));
				rx.await.map_err(oneshot_canceled_err)
			}.boxed()
		})?;

		rpc_module.register_method("system_add_log_filter", |param, system| {
			system.deny_unsafe.check_if_safe()?;

			let directives = param.one().map_err(|_| JsonRpseeCallError::InvalidParams)?;
			logging::add_directives(directives);
			logging::reload_filter().map_err(|e| JsonRpseeCallError::Failed(anyhow::anyhow!("{:?}", e).into()))
		})?;

		rpc_module.register_method("system_reset_log_filter", |_, system| {
			system.deny_unsafe.check_if_safe()?;
			logging::reset_log_filter().map_err(|e| JsonRpseeCallError::Failed(anyhow::anyhow!("{:?}", e).into()))
		})?;

		Ok(rpc_module)
	}
}


fn oneshot_canceled_err(canc: oneshot::Canceled) -> JsonRpseeCallError {
	JsonRpseeCallError::Failed(Box::new(canc))
}
