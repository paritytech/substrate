// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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

#![warn(missing_docs)]
#![recursion_limit = "1024"]
//! Substrate authority discovery.
//!
//! This crate enables Substrate authorities to discover and directly connect to
//! other authorities. It is split into two components the [`Worker`] and the
//! [`Service`].
//!
//! See [`Worker`] and [`Service`] for more documentation.

pub use crate::{service::Service, worker::{NetworkProvider, Worker, Role}};

use std::sync::Arc;

use futures::channel::{mpsc, oneshot};
use futures::Stream;

use sc_client_api::blockchain::HeaderBackend;
use sc_network::{DhtEvent, Multiaddr, PeerId};
use sp_authority_discovery::{AuthorityDiscoveryApi, AuthorityId};
use sp_runtime::traits::Block as BlockT;
use sp_api::ProvideRuntimeApi;

mod error;
mod service;
#[cfg(test)]
mod tests;
mod worker;

/// Create a new authority discovery [`Worker`] and [`Service`].
///
/// See the struct documentation of each for more details.
pub fn new_worker_and_service<Client, Network, Block, DhtEventStream>(
	client: Arc<Client>,
	network: Arc<Network>,
	dht_event_rx: DhtEventStream,
	role: Role,
	prometheus_registry: Option<prometheus_endpoint::Registry>,
) -> (Worker<Client, Network, Block, DhtEventStream>, Service)
where
	Block: BlockT + Unpin + 'static,
	Network: NetworkProvider,
	Client: ProvideRuntimeApi<Block> + Send + Sync + 'static + HeaderBackend<Block>,
	<Client as ProvideRuntimeApi<Block>>::Api: AuthorityDiscoveryApi<Block, Error = sp_blockchain::Error>,
	DhtEventStream: Stream<Item = DhtEvent> + Unpin,
{
	let (to_worker, from_service) = mpsc::channel(0);

	let worker = Worker::new(
		from_service, client, network, dht_event_rx, role, prometheus_registry,
	);
	let service = Service::new(to_worker);

	(worker, service)
}

/// Message send from the [`Service`] to the [`Worker`].
pub(crate) enum ServicetoWorkerMsg {
	/// See [`Service::get_addresses_by_authority_id`].
	GetAddressesByAuthorityId(AuthorityId, oneshot::Sender<Option<Vec<Multiaddr>>>),
	/// See [`Service::get_authority_id_by_peer_id`].
	GetAuthorityIdByPeerId(PeerId, oneshot::Sender<Option<AuthorityId>>)
}
