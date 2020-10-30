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

use std::{sync::Arc, time::Duration};

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

/// Configuration of [`Worker`].
pub struct WorkerConfig {
	/// The interval in which the node will publish its own address on the DHT.
	///
	/// By default this is set to 12 hours.
	pub publish_interval: Duration,
	/// The interval in which the node will query the DHT for new entries.
	///
	/// By default this is set to 10 minutes.
	pub query_interval: Duration,
	/// The time the node will wait before triggering the first DHT query or publish.
	///
	/// By default this is set to 30 seconds.
	///
	/// This default is based on the rough boostrap time required by libp2p Kademlia.
	pub query_start_delay: Duration,
	/// The interval in which the worker will instruct the peerset to connect to a random subset
	/// of discovered validators.
	///
	/// By default this is set to 10 minutes.
	pub priority_group_set_interval: Duration,
	/// The time the worker will wait after each query interval tick to pass a subset of
	/// the cached authority addresses down to the peerset.
	///
	/// Be aware that the actual delay will be computed by [`Self::query_start_delay`] +
	/// [`Self::priority_group_set_start_delay`]
	///
	/// By default this is set to 5 minutes.
	pub priority_group_set_offset: Duration,
}

impl Default for WorkerConfig {
	fn default() -> Self {
		Self {
			publish_interval: Duration::from_secs(12 * 60 * 60),
			query_interval: Duration::from_secs(10 * 60),
			query_start_delay: Duration::from_secs(30),
			priority_group_set_interval: Duration::from_secs(10 * 60),
			priority_group_set_offset: Duration::from_secs(5 * 60),
		}
	}
}

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
	new_worker_and_service_with_config(
		Default::default(),
		client,
		network,
		dht_event_rx,
		role,
		prometheus_registry,
	)
}

/// Same as [`new_worker_and_service`] but with support for providing the `config`.
///
/// When in doubt use [`new_worker_and_service`] as it will use the default configuration.
pub fn new_worker_and_service_with_config<Client, Network, Block, DhtEventStream>(
	config: WorkerConfig,
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
		from_service,
		client,
		network,
		dht_event_rx,
		role,
		prometheus_registry,
		config,
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
