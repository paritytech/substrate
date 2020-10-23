// Copyright 2020 Parity Technologies (UK) Ltd.
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

use crate::{error::{Error, Result}, ServicetoWorkerMsg};

use std::collections::{HashMap, HashSet};
use std::convert::TryInto;
use std::marker::PhantomData;
use std::sync::Arc;
use std::time::{Duration, Instant};

use futures::channel::mpsc;
use futures::{FutureExt, Stream, StreamExt, stream::Fuse};
use futures_timer::Delay;

use addr_cache::AddrCache;
use async_trait::async_trait;
use codec::Decode;
use either::Either;
use libp2p::{core::multiaddr, multihash::Multihash};
use log::{debug, error, log_enabled};
use prometheus_endpoint::{Counter, CounterVec, Gauge, Opts, U64, register};
use prost::Message;
use rand::{seq::SliceRandom, thread_rng};
use sc_client_api::blockchain::HeaderBackend;
use sc_network::{
	config::MultiaddrWithPeerId,
	DhtEvent,
	ExHashT,
	Multiaddr,
	NetworkStateInfo,
	PeerId,
};
use sp_authority_discovery::{AuthorityDiscoveryApi, AuthorityId, AuthoritySignature, AuthorityPair};
use sp_core::crypto::{key_types, Pair};
use sp_keystore::CryptoStore;
use sp_runtime::{traits::Block as BlockT, generic::BlockId};
use sp_api::ProvideRuntimeApi;

mod addr_cache;
/// Dht payload schemas generated from Protobuf definitions via Prost crate in build.rs.
mod schema { include!(concat!(env!("OUT_DIR"), "/authority_discovery.rs")); }
#[cfg(test)]
pub mod tests;

type Interval = Box<dyn Stream<Item = ()> + Unpin + Send + Sync>;

const LOG_TARGET: &'static str = "sub-authority-discovery";

/// Upper bound estimation on how long one should wait before accessing the Kademlia DHT.
const LIBP2P_KADEMLIA_BOOTSTRAP_TIME: Duration = Duration::from_secs(30);

/// Name of the Substrate peerset priority group for authorities discovered through the authority
/// discovery module.
const AUTHORITIES_PRIORITY_GROUP_NAME: &'static str = "authorities";

/// Maximum number of addresses cached per authority. Additional addresses are discarded.
const MAX_ADDRESSES_PER_AUTHORITY: usize = 10;

/// Maximum number of in-flight DHT lookups at any given point in time.
const MAX_IN_FLIGHT_LOOKUPS: usize = 8;

/// Role an authority discovery module can run as.
pub enum Role {
	/// Actual authority as well as a reference to its key store.
	Authority(Arc<dyn CryptoStore>),
	/// Sentry node that guards an authority.
	///
	/// No reference to its key store needed, as sentry nodes don't have an identity to sign
	/// addresses with in the first place.
	Sentry,
}

/// A [`Worker`] makes a given authority discoverable and discovers other
/// authorities.
///
/// The [`Worker`] implements the Future trait. By
/// polling [`Worker`] an authority:
///
/// 1. **Makes itself discoverable**
///
///    1. Retrieves its external addresses (including peer id) or the ones of
///    its sentry nodes.
///
///    2. Signs the above.
///
///    3. Puts the signature and the addresses on the libp2p Kademlia DHT.
///
///
/// 2. **Discovers other authorities**
///
///    1. Retrieves the current and next set of authorities.
///
///    2. Starts DHT queries for the ids of the authorities.
///
///    3. Validates the signatures of the retrieved key value pairs.
///
///    4. Adds the retrieved external addresses as priority nodes to the
///    peerset.
///
/// When run as a sentry node, the [`Worker`] does not publish
/// any addresses to the DHT but still discovers validators and sentry nodes of
/// validators, i.e. only step 2 (Discovers other authorities) is executed.
pub struct Worker<Client, Network, Block, DhtEventStream>
where
	Block: BlockT + 'static,
	Network: NetworkProvider,
	Client: ProvideRuntimeApi<Block> + Send + Sync + 'static + HeaderBackend<Block>,
	<Client as ProvideRuntimeApi<Block>>::Api: AuthorityDiscoveryApi<Block>,
{
	/// Channel receiver for messages send by an [`Service`].
	from_service: Fuse<mpsc::Receiver<ServicetoWorkerMsg>>,

	client: Arc<Client>,

	network: Arc<Network>,
	/// List of sentry node public addresses.
	//
	// There are 3 states:
	//   - None: No addresses were specified.
	//   - Some(vec![]): Addresses were specified, but none could be parsed as proper
	//     Multiaddresses.
	//   - Some(vec![a, b, c, ...]): Valid addresses were specified.
	sentry_nodes: Option<Vec<Multiaddr>>,
	/// Channel we receive Dht events on.
	dht_event_rx: DhtEventStream,

	/// Interval to be proactive, publishing own addresses.
	publish_interval: Interval,
	/// Interval at which to request addresses of authorities, refilling the pending lookups queue.
	query_interval: Interval,
	/// Interval on which to set the peerset priority group to a new random
	/// set of addresses.
	priority_group_set_interval: Interval,

	/// Queue of throttled lookups pending to be passed to the network.
	pending_lookups: Vec<AuthorityId>,
	/// Set of in-flight lookups.
	in_flight_lookups: HashMap<libp2p::kad::record::Key, AuthorityId>,

	addr_cache: addr_cache::AddrCache,

	metrics: Option<Metrics>,

	role: Role,

	phantom: PhantomData<Block>,
}

impl<Client, Network, Block, DhtEventStream> Worker<Client, Network, Block, DhtEventStream>
where
	Block: BlockT + Unpin + 'static,
	Network: NetworkProvider,
	Client: ProvideRuntimeApi<Block> + Send + Sync + 'static + HeaderBackend<Block>,
	<Client as ProvideRuntimeApi<Block>>::Api:
		AuthorityDiscoveryApi<Block, Error = sp_blockchain::Error>,
	DhtEventStream: Stream<Item = DhtEvent> + Unpin,
{
	/// Return a new [`Worker`].
	///
	/// Note: When specifying `sentry_nodes` this module will not advertise the public addresses of
	/// the node itself but only the public addresses of its sentry nodes.
	pub(crate) fn new(
		from_service: mpsc::Receiver<ServicetoWorkerMsg>,
		client: Arc<Client>,
		network: Arc<Network>,
		sentry_nodes: Vec<MultiaddrWithPeerId>,
		dht_event_rx: DhtEventStream,
		role: Role,
		prometheus_registry: Option<prometheus_endpoint::Registry>,
	) -> Self {
		// Kademlia's default time-to-live for Dht records is 36h, republishing records every 24h.
		// Given that a node could restart at any point in time, one can not depend on the
		// republishing process, thus publishing own external addresses should happen on an interval
		// < 36h.
		let publish_interval = interval_at(
			Instant::now() + LIBP2P_KADEMLIA_BOOTSTRAP_TIME,
			Duration::from_secs(12 * 60 * 60),
		);

		// External addresses of remote authorities can change at any given point in time. The
		// interval on which to trigger new queries for the current authorities is a trade off
		// between efficiency and performance.
		let query_interval_start = Instant::now() + LIBP2P_KADEMLIA_BOOTSTRAP_TIME;
		let query_interval_duration = Duration::from_secs(10 * 60);
		let query_interval = interval_at(query_interval_start, query_interval_duration);

		// Querying 500 [`AuthorityId`]s takes ~1m on the Kusama DHT (10th of August 2020) when
		// comparing `authority_discovery_authority_addresses_requested_total` and
		// `authority_discovery_dht_event_received`. With that in mind set the peerset priority
		// group on the same interval as the [`query_interval`] above, just delayed by 5 minutes.
		let priority_group_set_interval = interval_at(
			query_interval_start + Duration::from_secs(5 * 60),
			query_interval_duration,
		);

		let sentry_nodes = if !sentry_nodes.is_empty() {
			Some(sentry_nodes.into_iter().map(|ma| ma.concat()).collect::<Vec<_>>())
		} else {
			None
		};

		let addr_cache = AddrCache::new();

		let metrics = match prometheus_registry {
			Some(registry) => {
				match Metrics::register(&registry) {
					Ok(metrics) => Some(metrics),
					Err(e) => {
						error!(target: LOG_TARGET, "Failed to register metrics: {:?}", e);
						None
					},
				}
			},
			None => None,
		};

		Worker {
			from_service: from_service.fuse(),
			client,
			network,
			sentry_nodes,
			dht_event_rx,
			publish_interval,
			query_interval,
			priority_group_set_interval,
			pending_lookups: Vec::new(),
			in_flight_lookups: HashMap::new(),
			addr_cache,
			role,
			metrics,
			phantom: PhantomData,
		}
	}

	/// Start the worker
	pub async fn run(mut self) {
		loop {
			self.start_new_lookups();

			futures::select! {
				// Process incoming events.
				event = self.dht_event_rx.next().fuse() => {
					if let Some(event) = event {
						self.handle_dht_event(event).await;
					} else {
						// This point is reached if the network has shut down, at which point there is not
						// much else to do than to shut down the authority discovery as well.
						return;
					}
				},
				// Handle messages from [`Service`]. Ignore if sender side is closed.
				msg = self.from_service.select_next_some() => {
					self.process_message_from_service(msg);
				},
				// Set peerset priority group to a new random set of addresses.
				_ = self.priority_group_set_interval.next().fuse() => {
					if let Err(e) = self.set_priority_group().await {
						error!(
							target: LOG_TARGET,
							"Failed to set priority group: {:?}", e,
						);
					}
				},
				// Publish own addresses.
				_ = self.publish_interval.next().fuse() => {
					if let Err(e) = self.publish_ext_addresses().await {
						error!(
							target: LOG_TARGET,
							"Failed to publish external addresses: {:?}", e,
						);
					}
				},
				// Request addresses of authorities.
				_ = self.query_interval.next().fuse() => {
					if let Err(e) = self.refill_pending_lookups_queue().await {
						error!(
							target: LOG_TARGET,
							"Failed to request addresses of authorities: {:?}", e,
						);
					}
				},
			}
		}
	}

	fn process_message_from_service(&self, msg: ServicetoWorkerMsg) {
		match msg {
			ServicetoWorkerMsg::GetAddressesByAuthorityId(authority, sender) => {
				let _ = sender.send(
					self.addr_cache.get_addresses_by_authority_id(&authority).map(Clone::clone),
				);
			}
			ServicetoWorkerMsg::GetAuthorityIdByPeerId(peer_id, sender) => {
				let _ = sender.send(
					self.addr_cache.get_authority_id_by_peer_id(&peer_id).map(Clone::clone),
				);
			}
		}
	}

	fn addresses_to_publish(&self) -> impl ExactSizeIterator<Item = Multiaddr> {
		match &self.sentry_nodes {
			Some(addrs) => Either::Left(addrs.clone().into_iter()),
			None => {
				let peer_id: Multihash = self.network.local_peer_id().into();
				Either::Right(
					self.network.external_addresses()
						.into_iter()
						.map(move |a| {
							if a.iter().any(|p| matches!(p, multiaddr::Protocol::P2p(_))) {
								a
							} else {
								a.with(multiaddr::Protocol::P2p(peer_id.clone()))
							}
						}),
				)
			}
		}
	}

	/// Publish either our own or if specified the public addresses of our sentry nodes.
	async fn publish_ext_addresses(&mut self) -> Result<()> {
		let key_store = match &self.role {
			Role::Authority(key_store) => key_store,
			// Only authority nodes can put addresses (their own or the ones of their sentry nodes)
			// on the Dht. Sentry nodes don't have a known identity to authenticate such addresses,
			// thus `publish_ext_addresses` becomes a no-op.
			Role::Sentry => return Ok(()),
		};

		let addresses = self.addresses_to_publish();

		if let Some(metrics) = &self.metrics {
			metrics.publish.inc();
			metrics.amount_addresses_last_published.set(
				addresses.len().try_into().unwrap_or(std::u64::MAX),
			);
		}

		let mut serialized_addresses = vec![];
		schema::AuthorityAddresses { addresses: addresses.map(|a| a.to_vec()).collect() }
			.encode(&mut serialized_addresses)
			.map_err(Error::EncodingProto)?;

		let keys = Worker::<Client, Network, Block, DhtEventStream>::get_own_public_keys_within_authority_set(
			key_store.clone(),
			self.client.as_ref(),
		).await?.into_iter().map(Into::into).collect::<Vec<_>>();

		let signatures = key_store.sign_with_all(
			key_types::AUTHORITY_DISCOVERY,
			keys.clone(),
			serialized_addresses.as_slice(),
		).await.map_err(|_| Error::Signing)?;

		for (sign_result, key) in signatures.into_iter().zip(keys) {
			let mut signed_addresses = vec![];

			// sign_with_all returns Result<Signature, Error> signature
			// is generated for a public key that is supported.
			// Verify that all signatures exist for all provided keys.
			let signature = sign_result.map_err(|_| Error::MissingSignature(key.clone()))?;
			schema::SignedAuthorityAddresses {
				addresses: serialized_addresses.clone(),
				signature,
			}
			.encode(&mut signed_addresses)
				.map_err(Error::EncodingProto)?;

			self.network.put_value(
				hash_authority_id(key.1.as_ref()),
				signed_addresses,
			);
		}

		Ok(())
	}

	async fn refill_pending_lookups_queue(&mut self) -> Result<()> {
		let id = BlockId::hash(self.client.info().best_hash);

		let local_keys = match &self.role {
			Role::Authority(key_store) => {
				key_store.sr25519_public_keys(
					key_types::AUTHORITY_DISCOVERY
				).await.into_iter().collect::<HashSet<_>>()
			},
			Role::Sentry => HashSet::new(),
		};

		let mut authorities = self
			.client
			.runtime_api()
			.authorities(&id)
			.map_err(Error::CallingRuntime)?
			.into_iter()
			.filter(|id| !local_keys.contains(id.as_ref()))
			.collect();

		self.addr_cache.retain_ids(&authorities);

		authorities.shuffle(&mut thread_rng());
		self.pending_lookups = authorities;
		// Ignore all still in-flight lookups. Those that are still in-flight are likely stalled as
		// query interval ticks are far enough apart for all lookups to succeed.
		self.in_flight_lookups.clear();

		if let Some(metrics) = &self.metrics {
			metrics.requests_pending.set(
				self.pending_lookups.len().try_into().unwrap_or(std::u64::MAX),
			);
		}

		Ok(())
	}

	fn start_new_lookups(&mut self) {
		while self.in_flight_lookups.len() < MAX_IN_FLIGHT_LOOKUPS {
			let authority_id = match self.pending_lookups.pop() {
				Some(authority) => authority,
				None => return,
			};
			let hash = hash_authority_id(authority_id.as_ref());
			self.network
				.get_value(&hash);
			self.in_flight_lookups.insert(hash, authority_id);

			if let Some(metrics) = &self.metrics {
				metrics.requests.inc();
				metrics.requests_pending.set(
					self.pending_lookups.len().try_into().unwrap_or(std::u64::MAX),
				);
			}
		}
	}

	/// Handle incoming Dht events.
	async fn handle_dht_event(&mut self, event: DhtEvent) {
		match event {
			DhtEvent::ValueFound(v) => {
				if let Some(metrics) = &self.metrics {
					metrics.dht_event_received.with_label_values(&["value_found"]).inc();
				}

				if log_enabled!(log::Level::Debug) {
					let hashes = v.iter().map(|(hash, _value)| hash.clone());
					debug!(
						target: LOG_TARGET,
						"Value for hash '{:?}' found on Dht.", hashes,
					);
				}

				if let Err(e) = self.handle_dht_value_found_event(v) {
					if let Some(metrics) = &self.metrics {
						metrics.handle_value_found_event_failure.inc();
					}

					debug!(
						target: LOG_TARGET,
						"Failed to handle Dht value found event: {:?}", e,
					);
				}
			}
			DhtEvent::ValueNotFound(hash) => {
				if let Some(metrics) = &self.metrics {
					metrics.dht_event_received.with_label_values(&["value_not_found"]).inc();
				}

				if self.in_flight_lookups.remove(&hash).is_some() {
					debug!(
						target: LOG_TARGET,
						"Value for hash '{:?}' not found on Dht.", hash
					)
				} else {
					debug!(
						target: LOG_TARGET,
						"Received 'ValueNotFound' for unexpected hash '{:?}'.", hash
					)
				}
			},
			DhtEvent::ValuePut(hash) => {
				if let Some(metrics) = &self.metrics {
					metrics.dht_event_received.with_label_values(&["value_put"]).inc();
				}

				debug!(
					target: LOG_TARGET,
					"Successfully put hash '{:?}' on Dht.", hash,
				)
			},
			DhtEvent::ValuePutFailed(hash) => {
				if let Some(metrics) = &self.metrics {
					metrics.dht_event_received.with_label_values(&["value_put_failed"]).inc();
				}

				debug!(
					target: LOG_TARGET,
					"Failed to put hash '{:?}' on Dht.", hash
				)
			}
		}
	}

	fn handle_dht_value_found_event(
		&mut self,
		values: Vec<(libp2p::kad::record::Key, Vec<u8>)>,
	) -> Result<()> {
		// Ensure `values` is not empty and all its keys equal.
		let remote_key = values.iter().fold(Ok(None), |acc, (key, _)| {
			match acc {
				Ok(None) => Ok(Some(key.clone())),
				Ok(Some(ref prev_key)) if prev_key != key => Err(
					Error::ReceivingDhtValueFoundEventWithDifferentKeys
				),
				x @ Ok(_) => x,
				Err(e) => Err(e),
			}
		})?.ok_or(Error::ReceivingDhtValueFoundEventWithNoRecords)?;

		let authority_id: AuthorityId = self.in_flight_lookups
			.remove(&remote_key)
			.ok_or(Error::ReceivingUnexpectedRecord)?;

		let local_peer_id = self.network.local_peer_id();

		let remote_addresses: Vec<Multiaddr> = values.into_iter()
			.map(|(_k, v)| {
				let schema::SignedAuthorityAddresses { signature, addresses } =
					schema::SignedAuthorityAddresses::decode(v.as_slice())
					.map_err(Error::DecodingProto)?;

				let signature = AuthoritySignature::decode(&mut &signature[..])
					.map_err(Error::EncodingDecodingScale)?;

				if !AuthorityPair::verify(&signature, &addresses, &authority_id) {
					return Err(Error::VerifyingDhtPayload);
				}

				let addresses = schema::AuthorityAddresses::decode(addresses.as_slice())
					.map(|a| a.addresses)
					.map_err(Error::DecodingProto)?
					.into_iter()
					.map(|a| a.try_into())
					.collect::<std::result::Result<_, _>>()
					.map_err(Error::ParsingMultiaddress)?;

				Ok(addresses)
			})
			.collect::<Result<Vec<Vec<Multiaddr>>>>()?
			.into_iter()
			.flatten()
			// Ignore [`Multiaddr`]s without [`PeerId`] and own addresses.
			.filter(|addr| addr.iter().any(|protocol| {
				// Parse to PeerId first as Multihashes of old and new PeerId
				// representation don't equal.
				//
				// See https://github.com/libp2p/rust-libp2p/issues/555 for
				// details.
				if let multiaddr::Protocol::P2p(hash) = protocol {
					let peer_id = match PeerId::from_multihash(hash) {
						Ok(peer_id) => peer_id,
						Err(_) => return false, // Discard address.
					};

					// Discard if equal to local peer id, keep if it differs.
					return !(peer_id == local_peer_id);
				}

				false // `protocol` is not a [`Protocol::P2p`], let's keep looking.
			}))
			.take(MAX_ADDRESSES_PER_AUTHORITY)
			.collect();

		if !remote_addresses.is_empty() {
			self.addr_cache.insert(authority_id, remote_addresses);
			if let Some(metrics) = &self.metrics {
				metrics.known_authorities_count.set(
					self.addr_cache.num_ids().try_into().unwrap_or(std::u64::MAX)
				);
			}
		}
		Ok(())
	}

	/// Retrieve our public keys within the current and next authority set.
	//
	// A node might have multiple authority discovery keys within its keystore, e.g. an old one and
	// one for the upcoming session. In addition it could be participating in the current and (/ or)
	// next authority set with two keys. The function does not return all of the local authority
	// discovery public keys, but only the ones intersecting with the current or next authority set.
	async fn get_own_public_keys_within_authority_set(
		key_store: Arc<dyn CryptoStore>,
		client: &Client,
	) -> Result<HashSet<AuthorityId>> {
		let local_pub_keys = key_store
			.sr25519_public_keys(key_types::AUTHORITY_DISCOVERY)
			.await
			.into_iter()
			.collect::<HashSet<_>>();

		let id = BlockId::hash(client.info().best_hash);
		let authorities = client.runtime_api()
			.authorities(&id)
			.map_err(Error::CallingRuntime)?
			.into_iter()
			.map(std::convert::Into::into)
			.collect::<HashSet<_>>();

		let intersection = local_pub_keys.intersection(&authorities)
			.cloned()
			.map(std::convert::Into::into)
			.collect();

		Ok(intersection)
	}

	/// Set the peer set 'authority' priority group to a new random set of
	/// [`Multiaddr`]s.
	async fn set_priority_group(&self) -> Result<()> {
		let addresses = self.addr_cache.get_random_subset();

		if addresses.is_empty() {
			debug!(
				target: LOG_TARGET,
				"Got no addresses in cache for peerset priority group.",
			);
			return Ok(());
		}

		if let Some(metrics) = &self.metrics {
			metrics.priority_group_size.set(addresses.len().try_into().unwrap_or(std::u64::MAX));
		}

		debug!(
			target: LOG_TARGET,
			"Applying priority group {:?} to peerset.", addresses,
		);

		self.network
			.set_priority_group(
				AUTHORITIES_PRIORITY_GROUP_NAME.to_string(),
				addresses.into_iter().collect(),
			).await
			.map_err(Error::SettingPeersetPriorityGroup)?;

		Ok(())
	}
}

/// NetworkProvider provides [`Worker`] with all necessary hooks into the
/// underlying Substrate networking. Using this trait abstraction instead of [`NetworkService`]
/// directly is necessary to unit test [`Worker`].
#[async_trait]
pub trait NetworkProvider: NetworkStateInfo {
	/// Modify a peerset priority group.
	async fn set_priority_group(
		&self,
		group_id: String,
		peers: HashSet<libp2p::Multiaddr>,
	) -> std::result::Result<(), String>;

	/// Start putting a value in the Dht.
	fn put_value(&self, key: libp2p::kad::record::Key, value: Vec<u8>);

	/// Start getting a value from the Dht.
	fn get_value(&self, key: &libp2p::kad::record::Key);
}

#[async_trait::async_trait]
impl<B, H> NetworkProvider for sc_network::NetworkService<B, H>
where
	B: BlockT + 'static,
	H: ExHashT,
{
	async fn set_priority_group(
		&self,
		group_id: String,
		peers: HashSet<libp2p::Multiaddr>,
	) -> std::result::Result<(), String> {
		self.set_priority_group(group_id, peers).await
	}
	fn put_value(&self, key: libp2p::kad::record::Key, value: Vec<u8>) {
		self.put_value(key, value)
	}
	fn get_value(&self, key: &libp2p::kad::record::Key) {
		self.get_value(key)
	}
}

fn hash_authority_id(id: &[u8]) -> libp2p::kad::record::Key {
	libp2p::kad::record::Key::new(&libp2p::multihash::Sha2_256::digest(id))
}

fn interval_at(start: Instant, duration: Duration) -> Interval {
	let stream = futures::stream::unfold(start, move |next| {
		let time_until_next =  next.saturating_duration_since(Instant::now());

		Delay::new(time_until_next).map(move |_| Some(((), next + duration)))
	});

	Box::new(stream)
}

/// Prometheus metrics for a [`Worker`].
#[derive(Clone)]
pub(crate) struct Metrics {
	publish: Counter<U64>,
	amount_addresses_last_published: Gauge<U64>,
	requests: Counter<U64>,
	requests_pending: Gauge<U64>,
	dht_event_received: CounterVec<U64>,
	handle_value_found_event_failure: Counter<U64>,
	known_authorities_count: Gauge<U64>,
	priority_group_size: Gauge<U64>,
}

impl Metrics {
	pub(crate) fn register(registry: &prometheus_endpoint::Registry) -> Result<Self> {
		Ok(Self {
			publish: register(
				Counter::new(
					"authority_discovery_times_published_total",
					"Number of times authority discovery has published external addresses."
				)?,
				registry,
			)?,
			amount_addresses_last_published: register(
				Gauge::new(
					"authority_discovery_amount_external_addresses_last_published",
					"Number of external addresses published when authority discovery last \
					 published addresses."
				)?,
				registry,
			)?,
			requests: register(
				Counter::new(
					"authority_discovery_authority_addresses_requested_total",
					"Number of times authority discovery has requested external addresses of a \
					 single authority."
				)?,
				registry,
			)?,
			requests_pending: register(
				Gauge::new(
					"authority_discovery_authority_address_requests_pending",
					"Number of pending authority address requests."
				)?,
				registry,
			)?,
			dht_event_received: register(
				CounterVec::new(
					Opts::new(
						"authority_discovery_dht_event_received",
						"Number of dht events received by authority discovery."
					),
					&["name"],
				)?,
				registry,
			)?,
			handle_value_found_event_failure: register(
				Counter::new(
					"authority_discovery_handle_value_found_event_failure",
					"Number of times handling a dht value found event failed."
				)?,
				registry,
			)?,
			known_authorities_count: register(
				Gauge::new(
					"authority_discovery_known_authorities_count",
					"Number of authorities known by authority discovery."
				)?,
				registry,
			)?,
			priority_group_size: register(
				Gauge::new(
					"authority_discovery_priority_group_size",
					"Number of addresses passed to the peer set as a priority group."
				)?,
				registry,
			)?,
		})
	}
}

// Helper functions for unit testing.
#[cfg(test)]
impl<Block, Client, Network, DhtEventStream> Worker<Client, Network, Block, DhtEventStream>
where
	Block: BlockT + 'static,
	Network: NetworkProvider,
	Client: ProvideRuntimeApi<Block> + Send + Sync + 'static + HeaderBackend<Block>,
	<Client as ProvideRuntimeApi<Block>>::Api: AuthorityDiscoveryApi<Block>,
{
	pub(crate) fn inject_addresses(&mut self, authority: AuthorityId, addresses: Vec<Multiaddr>) {
		self.addr_cache.insert(authority, addresses);
	}
}
