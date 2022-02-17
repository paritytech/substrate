// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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

use self::error::Result;
use futures::{channel::oneshot, FutureExt};
use sc_rpc_api::{DenyUnsafe, Receiver};
use sc_tracing::logging;
use sc_utils::mpsc::TracingUnboundedSender;
use sp_runtime::traits::{self, Header as HeaderT};

pub use self::{
	gen_client::Client as SystemClient,
	helpers::{Health, NodeRole, PeerInfo, SyncState, SystemInfo},
};
pub use sc_rpc_api::system::*;

#[cfg(test)]
mod tests;

/// Early exit for RPCs that require `--rpc-methods=Unsafe` to be enabled
macro_rules! bail_if_unsafe {
	($value: expr) => {
		if let Err(err) = $value.check_if_safe() {
			return async move { Err(err.into()) }.boxed()
		}
	};
}

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
		System { info, send_back, deny_unsafe }
	}
}

impl<B: traits::Block> SystemApi<B::Hash, <B::Header as HeaderT>::Number> for System<B> {
	fn system_name(&self) -> Result<String> {
		Ok(self.info.impl_name.clone())
	}

	fn system_version(&self) -> Result<String> {
		Ok(self.info.impl_version.clone())
	}

	fn system_chain(&self) -> Result<String> {
		Ok(self.info.chain_name.clone())
	}

	fn system_type(&self) -> Result<sc_chain_spec::ChainType> {
		Ok(self.info.chain_type.clone())
	}

	fn system_properties(&self) -> Result<sc_chain_spec::Properties> {
		Ok(self.info.properties.clone())
	}

	fn system_health(&self) -> Receiver<Health> {
		let (tx, rx) = oneshot::channel();
		let _ = self.send_back.unbounded_send(Request::Health(tx));
		Receiver(rx)
	}

	fn system_local_peer_id(&self) -> Receiver<String> {
		let (tx, rx) = oneshot::channel();
		let _ = self.send_back.unbounded_send(Request::LocalPeerId(tx));
		Receiver(rx)
	}

	fn system_local_listen_addresses(&self) -> Receiver<Vec<String>> {
		let (tx, rx) = oneshot::channel();
		let _ = self.send_back.unbounded_send(Request::LocalListenAddresses(tx));
		Receiver(rx)
	}

	fn system_peers(
		&self,
	) -> rpc::BoxFuture<rpc::Result<Vec<PeerInfo<B::Hash, <B::Header as HeaderT>::Number>>>> {
		bail_if_unsafe!(self.deny_unsafe);

		let (tx, rx) = oneshot::channel();
		let _ = self.send_back.unbounded_send(Request::Peers(tx));

		async move { rx.await.map_err(|_| rpc::Error::internal_error()) }.boxed()
	}

	fn system_network_state(&self) -> rpc::BoxFuture<rpc::Result<rpc::Value>> {
		bail_if_unsafe!(self.deny_unsafe);

		let (tx, rx) = oneshot::channel();
		let _ = self.send_back.unbounded_send(Request::NetworkState(tx));

		async move { rx.await.map_err(|_| rpc::Error::internal_error()) }.boxed()
	}

	fn system_add_reserved_peer(&self, peer: String) -> rpc::BoxFuture<rpc::Result<()>> {
		bail_if_unsafe!(self.deny_unsafe);

		let (tx, rx) = oneshot::channel();
		let _ = self.send_back.unbounded_send(Request::NetworkAddReservedPeer(peer, tx));
		async move {
			match rx.await {
				Ok(Ok(())) => Ok(()),
				Ok(Err(e)) => Err(rpc::Error::from(e)),
				Err(_) => Err(rpc::Error::internal_error()),
			}
		}
		.boxed()
	}

	fn system_remove_reserved_peer(&self, peer: String) -> rpc::BoxFuture<rpc::Result<()>> {
		bail_if_unsafe!(self.deny_unsafe);

		let (tx, rx) = oneshot::channel();
		let _ = self.send_back.unbounded_send(Request::NetworkRemoveReservedPeer(peer, tx));
		async move {
			match rx.await {
				Ok(Ok(())) => Ok(()),
				Ok(Err(e)) => Err(rpc::Error::from(e)),
				Err(_) => Err(rpc::Error::internal_error()),
			}
		}
		.boxed()
	}

	fn system_reserved_peers(&self) -> Receiver<Vec<String>> {
		let (tx, rx) = oneshot::channel();
		let _ = self.send_back.unbounded_send(Request::NetworkReservedPeers(tx));
		Receiver(rx)
	}

	fn system_node_roles(&self) -> Receiver<Vec<NodeRole>> {
		let (tx, rx) = oneshot::channel();
		let _ = self.send_back.unbounded_send(Request::NodeRoles(tx));
		Receiver(rx)
	}

	fn system_sync_state(&self) -> Receiver<SyncState<<B::Header as HeaderT>::Number>> {
		let (tx, rx) = oneshot::channel();
		let _ = self.send_back.unbounded_send(Request::SyncState(tx));
		Receiver(rx)
	}

	fn system_add_log_filter(&self, directives: String) -> rpc::Result<()> {
		self.deny_unsafe.check_if_safe()?;
		logging::add_directives(&directives);
		logging::reload_filter().map_err(|_e| rpc::Error::internal_error())
	}

	fn system_reset_log_filter(&self) -> rpc::Result<()> {
		self.deny_unsafe.check_if_safe()?;
		logging::reset_log_filter().map_err(|_e| rpc::Error::internal_error())
	}
}
