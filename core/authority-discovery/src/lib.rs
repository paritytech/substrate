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

	fn publish_own_ext_addresses(&mut self) -> Result<()> {
		let id = BlockId::hash(self.client.info().best_hash);

		let authority_id = self
			.client
			.runtime_api()
			.authority_id(&id)
			.map_err(Error::CallingRuntime)?
			.ok_or(Error::RetrievingAuthorityId)?;

		let addresses = self
			.network
			.external_addresses()
			.into_iter()
			.map(|mut a| {
				a.push(libp2p::core::multiaddr::Protocol::P2p(
					self.network.peer_id().into(),
				));
				a
			})
			.map(|a| a.to_string())
			.collect();

		let mut serialized_addresses = vec![];
		{
			let mut a = schema::AuthorityAddresses::default();
			a.addresses = addresses;
			a.encode(&mut serialized_addresses)
				.map_err(Error::Encoding)?;
		};

		let sig = self
			.client
			.runtime_api()
			.sign(&id, serialized_addresses.clone(), authority_id.clone())
			.map_err(Error::CallingRuntime)?
			.ok_or(Error::SigningDhtPayload)?;

		let mut signed_addresses = vec![];
		{
			let mut a = schema::SignedAuthorityAddresses::default();
			a.addresses = serialized_addresses;
			a.signature = sig;
			a.encode(&mut signed_addresses).map_err(Error::Encoding)?;
		};

		self.network
			.put_value(hash_authority_id(authority_id.as_ref())?, signed_addresses);

		Ok(())
	}

	fn request_addresses_of_others(&mut self) -> Result<()> {
		let id = BlockId::hash(self.client.info().best_hash);

		let authorities = self
			.client
			.runtime_api()
			.authorities(&id)
			.map_err(Error::CallingRuntime)?;

		for authority_id in authorities.iter() {
			self.network
				.get_value(&hash_authority_id(authority_id.as_ref())?);
		}

		Ok(())
	}

	fn handle_dht_events(&mut self) -> Result<()> {
		while let Ok(Async::Ready(Some(event))) = self.dht_event_rx.poll() {
			match event {
				DhtEvent::ValueFound(v) => {
					if log_enabled!(log::Level::Debug) {
						let hashes = v.iter().map(|(hash, _value)| hash.clone());
						debug!(target: "sub-authority-discovery", "Value for hash '{:?}' found on Dht.", hashes);
					}

					self.handle_dht_value_found_event(v)?;
				}
				DhtEvent::ValueNotFound(hash) => {
					warn!(target: "sub-authority-discovery", "Value for hash '{:?}' not found on Dht.", hash)
				}
				DhtEvent::ValuePut(hash) => {
					debug!(target: "sub-authority-discovery", "Successfully put hash '{:?}' on Dht.", hash)
				}
				DhtEvent::ValuePutFailed(hash) => {
					warn!(target: "sub-authority-discovery", "Failed to put hash '{:?}' on Dht.", hash)
				}
			}
		}

		Ok(())
	}

	fn handle_dht_value_found_event(
		&mut self,
		values: Vec<(libp2p::kad::record::Key, Vec<u8>)>,
	) -> Result<()> {
		println!("==== dht found handling, cache: {:?}", self.address_cache);
		let id = BlockId::hash(self.client.info().best_hash);

		// From the Dht we only get the hashed authority id. In order to retrieve the actual authority id and to ensure
		// it is actually an authority, we match the hash against the hash of the authority id of all other authorities.
		let authorities = self.client.runtime_api().authorities(&id)?;
		self.purge_old_authorities_from_cache(&authorities);

		let authorities = authorities
			.into_iter()
			.map(|a| hash_authority_id(a.as_ref()).map(|h| (h, a)))
			.collect::<Result<HashMap<_, _>>>()?;

		for (key, value) in values.iter() {
			// Check if the event origins from an authority in the current
			// authority set.
			let authority_pub_key: &AuthorityId = authorities
				.get(key)
				.ok_or(Error::MatchingHashedAuthorityIdWithAuthorityId)?;

			let signed_addresses =
				schema::SignedAuthorityAddresses::decode(value).map_err(Error::Decoding)?;

			let is_verified = self
				.client
				.runtime_api()
				.verify(
					&id,
					signed_addresses.addresses.clone(),
					signed_addresses.signature.clone(),
					authority_pub_key.clone(),
				)
				.map_err(Error::CallingRuntime)?;

			if !is_verified {
				return Err(Error::VerifyingDhtPayload);
			}

			let addresses: Vec<libp2p::Multiaddr> =
				schema::AuthorityAddresses::decode(signed_addresses.addresses)
					.map(|a| a.addresses)
					.map_err(Error::Decoding)?
					.into_iter()
					.map(|a| a.parse())
					.collect::<std::result::Result<_, _>>()
					.map_err(Error::ParsingMultiaddress)?;

			self.address_cache
				.insert(authority_pub_key.clone(), addresses);
		}

		// Let's update the peerset priority group with the all the addresses we
		// have in our cache.

		let addresses = HashSet::from_iter(
			self.address_cache
				.iter()
				.map(|(_peer_id, addresses)| addresses.clone())
				.flatten(),
		);

		self.network
			.set_priority_group("authorities".to_string(), addresses)
			.map_err(Error::SettingPeersetPriorityGroup)?;

		Ok(())
	}

	fn purge_old_authorities_from_cache(&mut self, authorities: &Vec<AuthorityId>) {
		self.address_cache
			.retain(|peer_id, _addresses| authorities.contains(peer_id))
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
		let mut inner = || -> Result<()> {
			// Process incoming events before triggering new ones.
			self.handle_dht_events()?;

			if let Ok(Async::Ready(_)) = self.interval.poll() {
				// Make sure to call interval.poll until it returns Async::NotReady once. Otherwise, in case one of the
				// function calls within this block do a `return`, we don't call `interval.poll` again and thereby the
				// underlying Tokio task is never registered with Tokios Reactor to be woken up on the next interval
				// tick.
				while let Ok(Async::Ready(_)) = self.interval.poll() {}

				self.publish_own_ext_addresses()?;
				self.request_addresses_of_others()?;
			}

			Ok(())
		};

		match inner() {
			Ok(()) => {}
			Err(e) => error!(target: "sub-authority-discovery", "Poll failure: {:?}", e),
		};

		// Make sure to always return NotReady as this is a long running task
		// with the same lifetime of the node itself.
		Ok(futures::Async::NotReady)
	}
}

fn hash_authority_id(id: &[u8]) -> Result<(libp2p::kad::record::Key)> {
	libp2p::multihash::encode(libp2p::multihash::Hash::SHA2256, id)
		.map(|k| libp2p::kad::record::Key::new(&k))
		.map_err(Error::HashingAuthorityId)
}
