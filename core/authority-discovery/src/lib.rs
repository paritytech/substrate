// Copyright 2019 Parity Technologies (UK) Ltd.
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

//! Substrate authority discovery.
//!
//! This crate enables Substrate authorities to directly connect to other
//! authorities. [`AuthorityDiscovery`] implements the Future trait. By polling
//! a [`AuthorityDiscovery`] an authority:
//!
//!
//! 1. **Makes itself discoverable**
//!
//!    1. Retrieves its external addresses.
//!
//!    2. Adds its network peer id to the addresses.
//!
//!    3. Signs the above.
//!
//!    4. Puts the signature and the addresses on the libp2p Kademlia DHT.
//!
//!
//! 2. **Discovers other authorities**
//!
//!    1. Retrieves the current set of authorities..
//!
//!    2. Starts DHT queries for the ids of the authorities.
//!
//!    3. Validates the signatures of the retrieved key value pairs.
//!
//!    4. Adds the retrieved external addresses as priority nodes to the
//!    peerset.

use authority_discovery_primitives::AuthorityDiscoveryApi;
use client::blockchain::HeaderBackend;
use error::{Error, Result};
use futures::{prelude::*, sync::mpsc::Receiver};
use log::{debug, error, log_enabled, warn};
use network::specialization::NetworkSpecialization;
use network::{DhtEvent, ExHashT, NetworkStateInfo};
use prost::Message;
use sr_primitives::generic::BlockId;
use sr_primitives::traits::{Block, ProvideRuntimeApi};
use std::collections::{HashMap, HashSet};
use std::iter::FromIterator;
use std::marker::PhantomData;
use std::sync::Arc;
use std::time::Duration;

mod error;
/// Dht payload schemas generated from Protobuf definitions via Prost crate in build.rs.
mod schema {
	include!(concat!(env!("OUT_DIR"), "/authority_discovery.rs"));
}

/// A AuthorityDiscovery makes a given authority discoverable as well as
/// discovers other authoritys.
pub struct AuthorityDiscovery<AuthorityId, Client, B, S, H>
where
	B: Block + 'static,
	S: NetworkSpecialization<B>,
	H: ExHashT,
	AuthorityId: std::string::ToString
		+ codec::Codec
		+ std::convert::AsRef<[u8]>
		+ std::clone::Clone
		+ std::fmt::Debug
		+ std::hash::Hash
		+ std::cmp::Eq,
	Client: ProvideRuntimeApi + Send + Sync + 'static + HeaderBackend<B>,
	<Client as ProvideRuntimeApi>::Api: AuthorityDiscoveryApi<B, AuthorityId>,
{
	client: Arc<Client>,

	network: Arc<network::NetworkService<B, S, H>>,
	/// Channel we receive Dht events on.
	dht_event_rx: Receiver<DhtEvent>,

	/// Interval to be proactive on, e.g. publishing own addresses or starting
	/// to query for addresses.
	interval: tokio_timer::Interval,

	/// The network peerset interface for priority groups lets us only set an
	/// entire group, but we retrieve the addresses of other authorities one by
	/// one from the network. To use the peerset interface we need to cache the
	/// addresses and always overwrite the entire peerset priority group. To
	/// ensure this map doesn't grow indefinitely
	/// `purge_old_authorities_from_cache` function is called each time we add a
	/// new entry.
	address_cache: HashMap<AuthorityId, Vec<libp2p::Multiaddr>>,

	phantom_authority_id: PhantomData<AuthorityId>,
}

impl<AuthorityId, Client, B, S, H> AuthorityDiscovery<AuthorityId, Client, B, S, H>
where
	B: Block + 'static,
	S: NetworkSpecialization<B>,
	H: ExHashT,
	AuthorityId: std::string::ToString
		+ codec::Codec
		+ std::convert::AsRef<[u8]>
		+ std::clone::Clone
		+ std::fmt::Debug
		+ std::hash::Hash
		+ std::cmp::Eq,
	Client: ProvideRuntimeApi + Send + Sync + 'static + HeaderBackend<B>,
	<Client as ProvideRuntimeApi>::Api: AuthorityDiscoveryApi<B, AuthorityId>,
{
	/// Return a new authority discovery.
	pub fn new(
		client: Arc<Client>,
		network: Arc<network::NetworkService<B, S, H>>,
		dht_event_rx: futures::sync::mpsc::Receiver<DhtEvent>,
	) -> AuthorityDiscovery<AuthorityId, Client, B, S, H> {
		// TODO: 5 seconds is probably a bit spammy, figure out what Kademlias
		// time to live for dht entries is and adjust accordingly.
		let interval = tokio_timer::Interval::new_interval(Duration::from_secs(5));
		let address_cache = HashMap::new();

		AuthorityDiscovery {
			client,
			network,
			dht_event_rx,
			interval,
			address_cache,
			phantom_authority_id: PhantomData,
		}
	}
}

impl<AuthorityId, Client, B, S, H> futures::Future
	for AuthorityDiscovery<AuthorityId, Client, B, S, H>
where
	B: Block + 'static,
	S: NetworkSpecialization<B>,
	H: ExHashT,
	AuthorityId: std::string::ToString
		+ codec::Codec
		+ std::convert::AsRef<[u8]>
		+ std::clone::Clone
		+ std::fmt::Debug
		+ std::hash::Hash
		+ std::cmp::Eq,
	Client: ProvideRuntimeApi + Send + Sync + 'static + HeaderBackend<B>,
	<Client as ProvideRuntimeApi>::Api: AuthorityDiscoveryApi<B, AuthorityId>,
{
	type Item = ();
	type Error = ();

	fn poll(&mut self) -> futures::Poll<Self::Item, Self::Error> {
		// Make sure to always return NotReady as this is a long running task
		// with the same lifetime of the node itself.
		Ok(futures::Async::NotReady)
	}
}
