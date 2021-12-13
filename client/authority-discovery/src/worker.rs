// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
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

use crate::{
	error::{Error, Result},
	interval::ExpIncInterval,
	ServicetoWorkerMsg, WorkerConfig,
};

use std::{
	collections::{HashMap, HashSet},
	convert::TryInto,
	marker::PhantomData,
	sync::Arc,
	time::Duration,
};

use futures::{channel::mpsc, future, stream::Fuse, FutureExt, Stream, StreamExt};

use addr_cache::AddrCache;
use async_trait::async_trait;
use codec::Decode;
use ip_network::IpNetwork;
use libp2p::{
	core::multiaddr,
	multihash::{Hasher, Multihash},
};
use log::{debug, error, log_enabled};
use prometheus_endpoint::{register, Counter, CounterVec, Gauge, Opts, U64};
use prost::Message;
use rand::{seq::SliceRandom, thread_rng};
use sc_client_api::blockchain::HeaderBackend;
use sc_network::{DhtEvent, ExHashT, Multiaddr, NetworkStateInfo, PeerId};
use sp_api::ProvideRuntimeApi;
use sp_authority_discovery::{
	AuthorityDiscoveryApi, AuthorityId, AuthorityPair, AuthoritySignature,
};
use sp_core::crypto::{key_types, CryptoTypePublicPair, Pair};
use sp_keystore::CryptoStore;
use sp_runtime::{generic::BlockId, traits::Block as BlockT};

mod addr_cache;
/// Dht payload schemas generated from Protobuf definitions via Prost crate in build.rs.
mod schema {
	#[cfg(test)]
	mod tests;

	include!(concat!(env!("OUT_DIR"), "/authority_discovery_v2.rs"));
}
#[cfg(test)]
pub mod tests;

const LOG_TARGET: &'static str = "sub-authority-discovery";

/// Maximum number of addresses cached per authority. Additional addresses are discarded.
const MAX_ADDRESSES_PER_AUTHORITY: usize = 10;

/// Maximum number of in-flight DHT lookups at any given point in time.
const MAX_IN_FLIGHT_LOOKUPS: usize = 8;

/// Role an authority discovery [`Worker`] can run as.
pub enum Role {
	/// Publish own addresses and discover addresses of others.
	PublishAndDiscover(Arc<dyn CryptoStore>),
	/// Discover addresses of others.
	Discover,
}

/// An authority discovery [`Worker`] can publish the local node's addresses as well as discover
/// those of other nodes via a Kademlia DHT.
///
/// When constructed with [`Role::PublishAndDiscover`] a [`Worker`] will
///
///    1. Retrieve its external addresses (including peer id).
///
///    2. Get the list of keys owned by the local node participating in the current authority set.
///
///    3. Sign the addresses with the keys.
///
///    4. Put addresses and signature as a record with the authority id as a key on a Kademlia DHT.
///
/// When constructed with either [`Role::PublishAndDiscover`] or [`Role::Discover`] a [`Worker`]
/// will
///
///    1. Retrieve the current and next set of authorities.
///
///    2. Start DHT queries for the ids of the authorities.
///
///    3. Validate the signatures of the retrieved key value pairs.
///
///    4. Add the retrieved external addresses as priority nodes to the
///    network peerset.
///
///    5. Allow querying of the collected addresses via the [`crate::Service`].
pub struct Worker<Client, Network, Block, DhtEventStream> {
	/// Channel receiver for messages send by a [`crate::Service`].
	from_service: Fuse<mpsc::Receiver<ServicetoWorkerMsg>>,

	client: Arc<Client>,

	network: Arc<Network>,

	/// Channel we receive Dht events on.
	dht_event_rx: DhtEventStream,

	/// Interval to be proactive, publishing own addresses.
	publish_interval: ExpIncInterval,
	/// Pro-actively publish our own addresses at this interval, if the keys in the keystore
	/// have changed.
	publish_if_changed_interval: ExpIncInterval,
	/// List of keys onto which addresses have been published at the latest publication.
	/// Used to check whether they have changed.
	latest_published_keys: HashSet<CryptoTypePublicPair>,
	/// Same value as in the configuration.
	publish_non_global_ips: bool,
	/// Same value as in the configuration.
	strict_record_validation: bool,

	/// Interval at which to request addresses of authorities, refilling the pending lookups queue.
	query_interval: ExpIncInterval,

	/// Queue of throttled lookups pending to be passed to the network.
	pending_lookups: Vec<AuthorityId>,
	/// Set of in-flight lookups.
	in_flight_lookups: HashMap<sc_network::KademliaKey, AuthorityId>,

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
	<Client as ProvideRuntimeApi<Block>>::Api: AuthorityDiscoveryApi<Block>,
	DhtEventStream: Stream<Item = DhtEvent> + Unpin,
{
	/// Construct a [`Worker`].
	pub(crate) fn new(
		from_service: mpsc::Receiver<ServicetoWorkerMsg>,
		client: Arc<Client>,
		network: Arc<Network>,
		dht_event_rx: DhtEventStream,
		role: Role,
		prometheus_registry: Option<prometheus_endpoint::Registry>,
		config: WorkerConfig,
	) -> Self {
		// When a node starts up publishing and querying might fail due to various reasons, for
		// example due to being not yet fully bootstrapped on the DHT. Thus one should retry rather
		// sooner than later. On the other hand, a long running node is likely well connected and
		// thus timely retries are not needed. For this reasoning use an exponentially increasing
		// interval for `publish_interval`, `query_interval` and `priority_group_set_interval`
		// instead of a constant interval.
		let publish_interval =
			ExpIncInterval::new(Duration::from_secs(2), config.max_publish_interval);
		let query_interval = ExpIncInterval::new(Duration::from_secs(2), config.max_query_interval);

		// An `ExpIncInterval` is overkill here because the interval is constant, but consistency
		// is more simple.
		let publish_if_changed_interval =
			ExpIncInterval::new(config.keystore_refresh_interval, config.keystore_refresh_interval);

		let addr_cache = AddrCache::new();

		let metrics = match prometheus_registry {
			Some(registry) => match Metrics::register(&registry) {
				Ok(metrics) => Some(metrics),
				Err(e) => {
					error!(target: LOG_TARGET, "Failed to register metrics: {:?}", e);
					None
				},
			},
			None => None,
		};

		Worker {
			from_service: from_service.fuse(),
			client,
			network,
			dht_event_rx,
			publish_interval,
			publish_if_changed_interval,
			latest_published_keys: HashSet::new(),
			publish_non_global_ips: config.publish_non_global_ips,
			strict_record_validation: config.strict_record_validation,
			query_interval,
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
				// Publish own addresses.
				only_if_changed = future::select(
					self.publish_interval.next().map(|_| false),
					self.publish_if_changed_interval.next().map(|_| true)
				).map(|e| e.factor_first().0).fuse() => {
					if let Err(e) = self.publish_ext_addresses(only_if_changed).await {
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
			},
			ServicetoWorkerMsg::GetAuthorityIdsByPeerId(peer_id, sender) => {
				let _ = sender
					.send(self.addr_cache.get_authority_ids_by_peer_id(&peer_id).map(Clone::clone));
			},
		}
	}

	fn addresses_to_publish(&self) -> impl Iterator<Item = Multiaddr> {
		let peer_id: Multihash = self.network.local_peer_id().into();
		let publish_non_global_ips = self.publish_non_global_ips;
		self.network
			.external_addresses()
			.into_iter()
			.filter(move |a| {
				if publish_non_global_ips {
					return true
				}

				a.iter().all(|p| match p {
					// The `ip_network` library is used because its `is_global()` method is stable,
					// while `is_global()` in the standard library currently isn't.
					multiaddr::Protocol::Ip4(ip) if !IpNetwork::from(ip).is_global() => false,
					multiaddr::Protocol::Ip6(ip) if !IpNetwork::from(ip).is_global() => false,
					_ => true,
				})
			})
			.map(move |a| {
				if a.iter().any(|p| matches!(p, multiaddr::Protocol::P2p(_))) {
					a
				} else {
					a.with(multiaddr::Protocol::P2p(peer_id))
				}
			})
	}

	/// Publish own public addresses.
	///
	/// If `only_if_changed` is true, the function has no effect if the list of keys to publish
	/// is equal to `self.latest_published_keys`.
	async fn publish_ext_addresses(&mut self, only_if_changed: bool) -> Result<()> {
		let key_store = match &self.role {
			Role::PublishAndDiscover(key_store) => key_store,
			Role::Discover => return Ok(()),
		};

		let keys = Worker::<Client, Network, Block, DhtEventStream>::get_own_public_keys_within_authority_set(
			key_store.clone(),
			self.client.as_ref(),
		).await?.into_iter().map(Into::into).collect::<HashSet<_>>();

		if only_if_changed && keys == self.latest_published_keys {
			return Ok(())
		}

		let addresses = serialize_addresses(self.addresses_to_publish());

		if let Some(metrics) = &self.metrics {
			metrics.publish.inc();
			metrics
				.amount_addresses_last_published
				.set(addresses.len().try_into().unwrap_or(std::u64::MAX));
		}

		let serialized_record = serialize_authority_record(addresses)?;
		let peer_signature = sign_record_with_peer_id(&serialized_record, self.network.as_ref())?;

		let keys_vec = keys.iter().cloned().collect::<Vec<_>>();

		let kv_pairs = sign_record_with_authority_ids(
			serialized_record,
			Some(peer_signature),
			key_store.as_ref(),
			keys_vec,
		)
		.await?;

		for (key, value) in kv_pairs.into_iter() {
			self.network.put_value(key, value);
		}

		self.latest_published_keys = keys;

		Ok(())
	}

	async fn refill_pending_lookups_queue(&mut self) -> Result<()> {
		let id = BlockId::hash(self.client.info().best_hash);

		let local_keys = match &self.role {
			Role::PublishAndDiscover(key_store) => key_store
				.sr25519_public_keys(key_types::AUTHORITY_DISCOVERY)
				.await
				.into_iter()
				.collect::<HashSet<_>>(),
			Role::Discover => HashSet::new(),
		};

		let mut authorities = self
			.client
			.runtime_api()
			.authorities(&id)
			.map_err(|e| Error::CallingRuntime(e.into()))?
			.into_iter()
			.filter(|id| !local_keys.contains(id.as_ref()))
			.collect::<Vec<_>>();

		self.addr_cache.retain_ids(&authorities);

		authorities.shuffle(&mut thread_rng());
		self.pending_lookups = authorities;
		// Ignore all still in-flight lookups. Those that are still in-flight are likely stalled as
		// query interval ticks are far enough apart for all lookups to succeed.
		self.in_flight_lookups.clear();

		if let Some(metrics) = &self.metrics {
			metrics
				.requests_pending
				.set(self.pending_lookups.len().try_into().unwrap_or(std::u64::MAX));
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
			self.network.get_value(&hash);
			self.in_flight_lookups.insert(hash, authority_id);

			if let Some(metrics) = &self.metrics {
				metrics.requests.inc();
				metrics
					.requests_pending
					.set(self.pending_lookups.len().try_into().unwrap_or(std::u64::MAX));
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
					let hashes: Vec<_> = v.iter().map(|(hash, _value)| hash.clone()).collect();
					debug!(target: LOG_TARGET, "Value for hash '{:?}' found on Dht.", hashes);
				}

				if let Err(e) = self.handle_dht_value_found_event(v) {
					if let Some(metrics) = &self.metrics {
						metrics.handle_value_found_event_failure.inc();
					}

					debug!(target: LOG_TARGET, "Failed to handle Dht value found event: {:?}", e);
				}
			},
			DhtEvent::ValueNotFound(hash) => {
				if let Some(metrics) = &self.metrics {
					metrics.dht_event_received.with_label_values(&["value_not_found"]).inc();
				}

				if self.in_flight_lookups.remove(&hash).is_some() {
					debug!(target: LOG_TARGET, "Value for hash '{:?}' not found on Dht.", hash)
				} else {
					debug!(
						target: LOG_TARGET,
						"Received 'ValueNotFound' for unexpected hash '{:?}'.", hash
					)
				}
			},
			DhtEvent::ValuePut(hash) => {
				// Fast forward the exponentially increasing interval to the configured maximum. In
				// case this was the first successful address publishing there is no need for a
				// timely retry.
				self.publish_interval.set_to_max();

				if let Some(metrics) = &self.metrics {
					metrics.dht_event_received.with_label_values(&["value_put"]).inc();
				}

				debug!(target: LOG_TARGET, "Successfully put hash '{:?}' on Dht.", hash)
			},
			DhtEvent::ValuePutFailed(hash) => {
				if let Some(metrics) = &self.metrics {
					metrics.dht_event_received.with_label_values(&["value_put_failed"]).inc();
				}

				debug!(target: LOG_TARGET, "Failed to put hash '{:?}' on Dht.", hash)
			},
		}
	}

	fn handle_dht_value_found_event(
		&mut self,
		values: Vec<(sc_network::KademliaKey, Vec<u8>)>,
	) -> Result<()> {
		// Ensure `values` is not empty and all its keys equal.
		let remote_key = single(values.iter().map(|(key, _)| key.clone()))
			.map_err(|_| Error::ReceivingDhtValueFoundEventWithDifferentKeys)?
			.ok_or(Error::ReceivingDhtValueFoundEventWithNoRecords)?;

		let authority_id: AuthorityId = self
			.in_flight_lookups
			.remove(&remote_key)
			.ok_or(Error::ReceivingUnexpectedRecord)?;

		let local_peer_id = self.network.local_peer_id();

		let remote_addresses: Vec<Multiaddr> = values
			.into_iter()
			.map(|(_k, v)| {
				let schema::SignedAuthorityRecord { record, auth_signature, peer_signature } =
					schema::SignedAuthorityRecord::decode(v.as_slice())
						.map_err(Error::DecodingProto)?;

				let auth_signature = AuthoritySignature::decode(&mut &auth_signature[..])
					.map_err(Error::EncodingDecodingScale)?;

				if !AuthorityPair::verify(&auth_signature, &record, &authority_id) {
					return Err(Error::VerifyingDhtPayload)
				}

				let addresses: Vec<Multiaddr> = schema::AuthorityRecord::decode(record.as_slice())
					.map(|a| a.addresses)
					.map_err(Error::DecodingProto)?
					.into_iter()
					.map(|a| a.try_into())
					.collect::<std::result::Result<_, _>>()
					.map_err(Error::ParsingMultiaddress)?;

				let get_peer_id = |a: &Multiaddr| match a.iter().last() {
					Some(multiaddr::Protocol::P2p(key)) => PeerId::from_multihash(key).ok(),
					_ => None,
				};

				// Ignore [`Multiaddr`]s without [`PeerId`] or with own addresses.
				let addresses: Vec<Multiaddr> = addresses
					.into_iter()
					.filter(|a| get_peer_id(&a).filter(|p| *p != local_peer_id).is_some())
					.collect();

				let remote_peer_id = single(addresses.iter().map(get_peer_id))
					.map_err(|_| Error::ReceivingDhtValueFoundEventWithDifferentPeerIds)? // different peer_id in records
					.flatten()
					.ok_or(Error::ReceivingDhtValueFoundEventWithNoPeerIds)?; // no records with peer_id in them

				// At this point we know all the valid multiaddresses from the record, know that
				// each of them belong to the same PeerId, we just need to check if the record is
				// properly signed by the owner of the PeerId

				if let Some(peer_signature) = peer_signature {
					let public_key =
						sc_network::PublicKey::from_protobuf_encoding(&peer_signature.public_key)
							.map_err(|e| Error::ParsingLibp2pIdentity(e))?;
					let signature =
						sc_network::Signature { public_key, bytes: peer_signature.signature };

					if !signature.verify(record, &remote_peer_id) {
						return Err(Error::VerifyingDhtPayload)
					}
				} else if self.strict_record_validation {
					return Err(Error::MissingPeerIdSignature)
				} else {
					debug!(
						target: LOG_TARGET,
						"Received unsigned authority discovery record from {}", authority_id
					);
				}
				Ok(addresses)
			})
			.collect::<Result<Vec<Vec<Multiaddr>>>>()?
			.into_iter()
			.flatten()
			.take(MAX_ADDRESSES_PER_AUTHORITY)
			.collect();

		if !remote_addresses.is_empty() {
			self.addr_cache.insert(authority_id, remote_addresses);
			if let Some(metrics) = &self.metrics {
				metrics
					.known_authorities_count
					.set(self.addr_cache.num_authority_ids().try_into().unwrap_or(std::u64::MAX));
			}
		}
		Ok(())
	}

	/// Retrieve our public keys within the current and next authority set.
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
		let authorities = client
			.runtime_api()
			.authorities(&id)
			.map_err(|e| Error::CallingRuntime(e.into()))?
			.into_iter()
			.map(std::convert::Into::into)
			.collect::<HashSet<_>>();

		let intersection = local_pub_keys
			.intersection(&authorities)
			.cloned()
			.map(std::convert::Into::into)
			.collect();

		Ok(intersection)
	}
}

pub trait NetworkSigner {
	/// Sign a message in the name of `self.local_peer_id()`
	fn sign_with_local_identity(
		&self,
		msg: impl AsRef<[u8]>,
	) -> std::result::Result<sc_network::Signature, sc_network::SigningError>;
}

/// NetworkProvider provides [`Worker`] with all necessary hooks into the
/// underlying Substrate networking. Using this trait abstraction instead of
/// [`sc_network::NetworkService`] directly is necessary to unit test [`Worker`].
#[async_trait]
pub trait NetworkProvider: NetworkStateInfo + NetworkSigner {
	/// Start putting a value in the Dht.
	fn put_value(&self, key: sc_network::KademliaKey, value: Vec<u8>);

	/// Start getting a value from the Dht.
	fn get_value(&self, key: &sc_network::KademliaKey);
}

impl<B, H> NetworkSigner for sc_network::NetworkService<B, H>
where
	B: BlockT + 'static,
	H: ExHashT,
{
	fn sign_with_local_identity(
		&self,
		msg: impl AsRef<[u8]>,
	) -> std::result::Result<sc_network::Signature, sc_network::SigningError> {
		self.sign_with_local_identity(msg)
	}
}

#[async_trait::async_trait]
impl<B, H> NetworkProvider for sc_network::NetworkService<B, H>
where
	B: BlockT + 'static,
	H: ExHashT,
{
	fn put_value(&self, key: sc_network::KademliaKey, value: Vec<u8>) {
		self.put_value(key, value)
	}
	fn get_value(&self, key: &sc_network::KademliaKey) {
		self.get_value(key)
	}
}

fn hash_authority_id(id: &[u8]) -> sc_network::KademliaKey {
	sc_network::KademliaKey::new(&libp2p::multihash::Sha2_256::digest(id))
}

// Makes sure all values are the same and returns it
//
// Returns Err(_) if not all values are equal. Returns Ok(None) if there are
// no values.
fn single<T>(values: impl IntoIterator<Item = T>) -> std::result::Result<Option<T>, ()>
where
	T: PartialEq<T>,
{
	values.into_iter().try_fold(None, |acc, item| match acc {
		None => Ok(Some(item)),
		Some(ref prev) if *prev != item => Err(()),
		Some(x) => Ok(Some(x)),
	})
}

fn serialize_addresses(addresses: impl Iterator<Item = Multiaddr>) -> Vec<Vec<u8>> {
	addresses.map(|a| a.to_vec()).collect()
}

fn serialize_authority_record(addresses: Vec<Vec<u8>>) -> Result<Vec<u8>> {
	let mut serialized_record = vec![];
	schema::AuthorityRecord { addresses }
		.encode(&mut serialized_record)
		.map_err(Error::EncodingProto)?;
	Ok(serialized_record)
}

fn sign_record_with_peer_id(
	serialized_record: &[u8],
	network: &impl NetworkSigner,
) -> Result<schema::PeerSignature> {
	let signature = network
		.sign_with_local_identity(serialized_record)
		.map_err(|_| Error::Signing)?;
	let public_key = signature.public_key.to_protobuf_encoding();
	let signature = signature.bytes;
	Ok(schema::PeerSignature { signature, public_key })
}

async fn sign_record_with_authority_ids(
	serialized_record: Vec<u8>,
	peer_signature: Option<schema::PeerSignature>,
	key_store: &dyn CryptoStore,
	keys: Vec<CryptoTypePublicPair>,
) -> Result<Vec<(sc_network::KademliaKey, Vec<u8>)>> {
	let signatures = key_store
		.sign_with_all(key_types::AUTHORITY_DISCOVERY, keys.clone(), &serialized_record)
		.await
		.map_err(|_| Error::Signing)?;

	let mut result = vec![];
	for (sign_result, key) in signatures.into_iter().zip(keys.iter()) {
		let mut signed_record = vec![];

		// Verify that all signatures exist for all provided keys.
		let auth_signature =
			sign_result.ok().flatten().ok_or_else(|| Error::MissingSignature(key.clone()))?;
		schema::SignedAuthorityRecord {
			record: serialized_record.clone(),
			auth_signature,
			peer_signature: peer_signature.clone(),
		}
		.encode(&mut signed_record)
		.map_err(Error::EncodingProto)?;

		result.push((hash_authority_id(key.1.as_ref()), signed_record));
	}

	Ok(result)
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
}

impl Metrics {
	pub(crate) fn register(registry: &prometheus_endpoint::Registry) -> Result<Self> {
		Ok(Self {
			publish: register(
				Counter::new(
					"substrate_authority_discovery_times_published_total",
					"Number of times authority discovery has published external addresses.",
				)?,
				registry,
			)?,
			amount_addresses_last_published: register(
				Gauge::new(
					"substrate_authority_discovery_amount_external_addresses_last_published",
					"Number of external addresses published when authority discovery last \
					 published addresses.",
				)?,
				registry,
			)?,
			requests: register(
				Counter::new(
					"substrate_authority_discovery_authority_addresses_requested_total",
					"Number of times authority discovery has requested external addresses of a \
					 single authority.",
				)?,
				registry,
			)?,
			requests_pending: register(
				Gauge::new(
					"substrate_authority_discovery_authority_address_requests_pending",
					"Number of pending authority address requests.",
				)?,
				registry,
			)?,
			dht_event_received: register(
				CounterVec::new(
					Opts::new(
						"substrate_authority_discovery_dht_event_received",
						"Number of dht events received by authority discovery.",
					),
					&["name"],
				)?,
				registry,
			)?,
			handle_value_found_event_failure: register(
				Counter::new(
					"substrate_authority_discovery_handle_value_found_event_failure",
					"Number of times handling a dht value found event failed.",
				)?,
				registry,
			)?,
			known_authorities_count: register(
				Gauge::new(
					"substrate_authority_discovery_known_authorities_count",
					"Number of authorities known by authority discovery.",
				)?,
				registry,
			)?,
		})
	}
}

// Helper functions for unit testing.
#[cfg(test)]
impl<Block, Client, Network, DhtEventStream> Worker<Client, Network, Block, DhtEventStream> {
	pub(crate) fn inject_addresses(&mut self, authority: AuthorityId, addresses: Vec<Multiaddr>) {
		self.addr_cache.insert(authority, addresses);
	}
}
