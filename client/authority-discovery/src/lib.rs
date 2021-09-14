// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

#![warn(missing_docs)]
#![recursion_limit = "1024"]
//! Substrate authority discovery.
//!
//! This crate enables Substrate authorities to discover and directly connect to
//! other authorities. It is split into two components the [`Worker`] and the
//! [`Service`].
//!
//! See [`Worker`] and [`Service`] for more documentation.

pub use crate::{
	service::Service,
	worker::{NetworkProvider, Role, Worker},
};

use std::{sync::Arc, time::Duration};

use futures::{
	channel::{mpsc, oneshot},
	Stream,
};

use sc_client_api::blockchain::HeaderBackend;
use sc_network::{DhtEvent, Multiaddr, PeerId};
use sp_api::ProvideRuntimeApi;
use sp_authority_discovery::{AuthorityDiscoveryApi, AuthorityId};
use sp_runtime::traits::Block as BlockT;

mod error;
mod interval;
mod service;
mod worker;

#[cfg(test)]
mod tests;

/// Configuration of [`Worker`].
pub struct WorkerConfig {
	/// The maximum interval in which the node will publish its own address on the DHT.
	///
	/// By default this is set to 1 hour.
	pub max_publish_interval: Duration,
	/// Interval at which the keystore is queried. If the keys have changed, unconditionally
	/// re-publish its addresses on the DHT.
	///
	/// By default this is set to 1 minute.
	pub keystore_refresh_interval: Duration,
	/// The maximum interval in which the node will query the DHT for new entries.
	///
	/// By default this is set to 10 minutes.
	pub max_query_interval: Duration,

	/// If `false`, the node won't publish on the DHT multiaddresses that contain non-global
	/// IP addresses (such as 10.0.0.1).
	///
	/// Recommended: `false` for live chains, and `true` for local chains or for testing.
	///
	/// Defaults to `true` to avoid the surprise factor.
	pub publish_non_global_ips: bool,
}

impl Default for WorkerConfig {
	fn default() -> Self {
		Self {
			// Kademlia's default time-to-live for Dht records is 36h, republishing records every
			// 24h through libp2p-kad. Given that a node could restart at any point in time, one can
			// not depend on the republishing process, thus publishing own external addresses should
			// happen on an interval < 36h.
			max_publish_interval: Duration::from_secs(1 * 60 * 60),
			keystore_refresh_interval: Duration::from_secs(60),
			// External addresses of remote authorities can change at any given point in time. The
			// interval on which to trigger new queries for the current and next authorities is a
			// trade off between efficiency and performance.
			//
			// Querying 700 [`AuthorityId`]s takes ~8m on the Kusama DHT (16th Nov 2020) when
			// comparing `authority_discovery_authority_addresses_requested_total` and
			// `authority_discovery_dht_event_received`.
			max_query_interval: Duration::from_secs(10 * 60),
			publish_non_global_ips: true,
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
	<Client as ProvideRuntimeApi<Block>>::Api: AuthorityDiscoveryApi<Block>,
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
	<Client as ProvideRuntimeApi<Block>>::Api: AuthorityDiscoveryApi<Block>,
	DhtEventStream: Stream<Item = DhtEvent> + Unpin,
{
	let (to_worker, from_service) = mpsc::channel(0);

	let worker =
		Worker::new(from_service, client, network, dht_event_rx, role, prometheus_registry, config);
	let service = Service::new(to_worker);

	(worker, service)
}

/// Message send from the [`Service`] to the [`Worker`].
pub(crate) enum ServicetoWorkerMsg {
	/// See [`Service::get_addresses_by_authority_id`].
	GetAddressesByAuthorityId(AuthorityId, oneshot::Sender<Option<Vec<Multiaddr>>>),
	/// See [`Service::get_authority_id_by_peer_id`].
	GetAuthorityIdByPeerId(PeerId, oneshot::Sender<Option<AuthorityId>>),
}
