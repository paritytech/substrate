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

//! Discovery mechanisms of Substrate.
//!
//! The `DiscoveryBehaviour` struct implements the `NetworkBehaviour` trait of libp2p and is
//! responsible for discovering other nodes that are part of the network.
//!
//! Substrate uses the following mechanisms in order to discover nodes that are part of the network:
//!
//! - Bootstrap nodes. These are hard-coded node identities and addresses passed in the constructor
//! of the `DiscoveryBehaviour`. You can also call `add_known_address` later to add an entry.
//!
//! - mDNS. Discovers nodes on the local network by broadcasting UDP packets.
//!
//! - Kademlia random walk. Once connected, we perform random Kademlia `FIND_NODE` requests on the
//! configured Kademlia DHTs in order for nodes to propagate to us their view of the network. This
//! is performed automatically by the `DiscoveryBehaviour`.
//!
//! Additionally, the `DiscoveryBehaviour` is also capable of storing and loading value in the
//! configured DHTs.
//!
//! ## Usage
//!
//! The `DiscoveryBehaviour` generates events of type `DiscoveryOut`, most notably
//! `DiscoveryOut::Discovered` that is generated whenever we discover a node.
//! Only the identity of the node is returned. The node's addresses are stored within the
//! `DiscoveryBehaviour` and can be queried through the `NetworkBehaviour` trait.
//!
//! **Important**: In order for the discovery mechanism to work properly, there needs to be an
//! active mechanism that asks nodes for the addresses they are listening on. Whenever we learn
//! of a node's address, you must call `add_self_reported_address`.

use crate::{config::ProtocolId, utils::LruHashSet};

use array_bytes::bytes2hex;
use futures::prelude::*;
use futures_timer::Delay;
use ip_network::IpNetwork;
use libp2p::{
	core::{Endpoint, Multiaddr},
	kad::{
		handler::KademliaHandler,
		record::store::{MemoryStore, RecordStore},
		GetClosestPeersError, GetRecordOk, Kademlia, KademliaBucketInserts, KademliaConfig,
		KademliaEvent, QueryId, QueryResult, Quorum, Record, RecordKey,
	},
	mdns::{self, tokio::Behaviour as TokioMdns},
	multiaddr::Protocol,
	swarm::{
		behaviour::{
			toggle::{Toggle, ToggleConnectionHandler},
			DialFailure, FromSwarm, NewExternalAddr,
		},
		ConnectionDenied, ConnectionId, DialError, NetworkBehaviour, PollParameters, THandler,
		THandlerInEvent, THandlerOutEvent, ToSwarm,
	},
	PeerId,
};
use log::{debug, info, trace, warn};
use sp_core::hexdisplay::HexDisplay;
use std::{
	cmp,
	collections::{hash_map::Entry, HashMap, HashSet, VecDeque},
	num::NonZeroUsize,
	task::{Context, Poll},
	time::Duration,
};

/// Maximum number of known external addresses that we will cache.
/// This only affects whether we will log whenever we (re-)discover
/// a given address.
const MAX_KNOWN_EXTERNAL_ADDRESSES: usize = 32;

/// Default value for Kademlia replication factor which  determines to how many closest peers a
/// record is replicated to.
pub const DEFAULT_KADEMLIA_REPLICATION_FACTOR: usize = 20;

/// `DiscoveryBehaviour` configuration.
///
/// Note: In order to discover nodes or load and store values via Kademlia one has to add
///       Kademlia protocol via [`DiscoveryConfig::with_kademlia`].
pub struct DiscoveryConfig {
	local_peer_id: PeerId,
	permanent_addresses: Vec<(PeerId, Multiaddr)>,
	dht_random_walk: bool,
	allow_private_ip: bool,
	allow_non_globals_in_dht: bool,
	discovery_only_if_under_num: u64,
	enable_mdns: bool,
	kademlia_disjoint_query_paths: bool,
	kademlia_protocols: Vec<Vec<u8>>,
	kademlia_replication_factor: NonZeroUsize,
}

impl DiscoveryConfig {
	/// Create a default configuration with the given public key.
	pub fn new(local_peer_id: PeerId) -> Self {
		Self {
			local_peer_id,
			permanent_addresses: Vec::new(),
			dht_random_walk: true,
			allow_private_ip: true,
			allow_non_globals_in_dht: false,
			discovery_only_if_under_num: std::u64::MAX,
			enable_mdns: false,
			kademlia_disjoint_query_paths: false,
			kademlia_protocols: Vec::new(),
			kademlia_replication_factor: NonZeroUsize::new(DEFAULT_KADEMLIA_REPLICATION_FACTOR)
				.expect("value is a constant; constant is non-zero; qed."),
		}
	}

	/// Set the number of active connections at which we pause discovery.
	pub fn discovery_limit(&mut self, limit: u64) -> &mut Self {
		self.discovery_only_if_under_num = limit;
		self
	}

	/// Set custom nodes which never expire, e.g. bootstrap or reserved nodes.
	pub fn with_permanent_addresses<I>(&mut self, permanent_addresses: I) -> &mut Self
	where
		I: IntoIterator<Item = (PeerId, Multiaddr)>,
	{
		self.permanent_addresses.extend(permanent_addresses);
		self
	}

	/// Whether the discovery behaviour should periodically perform a random
	/// walk on the DHT to discover peers.
	pub fn with_dht_random_walk(&mut self, value: bool) -> &mut Self {
		self.dht_random_walk = value;
		self
	}

	/// Should private IPv4/IPv6 addresses be reported?
	pub fn allow_private_ip(&mut self, value: bool) -> &mut Self {
		self.allow_private_ip = value;
		self
	}

	/// Should non-global addresses be inserted to the DHT?
	pub fn allow_non_globals_in_dht(&mut self, value: bool) -> &mut Self {
		self.allow_non_globals_in_dht = value;
		self
	}

	/// Should MDNS discovery be supported?
	pub fn with_mdns(&mut self, value: bool) -> &mut Self {
		self.enable_mdns = value;
		self
	}

	/// Add discovery via Kademlia for the given protocol.
	///
	/// Currently accepts `protocol_id`. This should be removed once all the nodes
	/// are upgraded to genesis hash- and fork ID-based Kademlia protocol name.
	pub fn with_kademlia<Hash: AsRef<[u8]>>(
		&mut self,
		genesis_hash: Hash,
		fork_id: Option<&str>,
		protocol_id: &ProtocolId,
	) -> &mut Self {
		self.kademlia_protocols = Vec::new();
		self.kademlia_protocols.push(kademlia_protocol_name(genesis_hash, fork_id));
		self.kademlia_protocols.push(legacy_kademlia_protocol_name(protocol_id));
		self
	}

	/// Require iterative Kademlia DHT queries to use disjoint paths for increased resiliency in the
	/// presence of potentially adversarial nodes.
	pub fn use_kademlia_disjoint_query_paths(&mut self, value: bool) -> &mut Self {
		self.kademlia_disjoint_query_paths = value;
		self
	}

	/// Sets Kademlia replication factor.
	pub fn with_kademlia_replication_factor(&mut self, value: NonZeroUsize) -> &mut Self {
		self.kademlia_replication_factor = value;
		self
	}

	/// Create a `DiscoveryBehaviour` from this config.
	pub fn finish(self) -> DiscoveryBehaviour {
		let Self {
			local_peer_id,
			permanent_addresses,
			dht_random_walk,
			allow_private_ip,
			allow_non_globals_in_dht,
			discovery_only_if_under_num,
			enable_mdns,
			kademlia_disjoint_query_paths,
			kademlia_protocols,
			kademlia_replication_factor,
		} = self;

		let kademlia = if !kademlia_protocols.is_empty() {
			let mut config = KademliaConfig::default();

			config.set_replication_factor(kademlia_replication_factor);
			config.set_protocol_names(kademlia_protocols.into_iter().map(Into::into).collect());
			// By default Kademlia attempts to insert all peers into its routing table once a
			// dialing attempt succeeds. In order to control which peer is added, disable the
			// auto-insertion and instead add peers manually.
			config.set_kbucket_inserts(KademliaBucketInserts::Manual);
			config.disjoint_query_paths(kademlia_disjoint_query_paths);

			let store = MemoryStore::new(local_peer_id);
			let mut kad = Kademlia::with_config(local_peer_id, store, config);

			for (peer_id, addr) in &permanent_addresses {
				kad.add_address(peer_id, addr.clone());
			}

			Some(kad)
		} else {
			None
		};

		DiscoveryBehaviour {
			permanent_addresses,
			ephemeral_addresses: HashMap::new(),
			kademlia: Toggle::from(kademlia),
			next_kad_random_query: if dht_random_walk {
				Some(Delay::new(Duration::new(0, 0)))
			} else {
				None
			},
			duration_to_next_kad: Duration::from_secs(1),
			pending_events: VecDeque::new(),
			local_peer_id,
			num_connections: 0,
			allow_private_ip,
			discovery_only_if_under_num,
			mdns: if enable_mdns {
				match TokioMdns::new(mdns::Config::default(), local_peer_id) {
					Ok(mdns) => Some(mdns),
					Err(err) => {
						warn!(target: "sub-libp2p", "Failed to initialize mDNS: {:?}", err);
						None
					},
				}
			} else {
				None
			},
			allow_non_globals_in_dht,
			known_external_addresses: LruHashSet::new(
				NonZeroUsize::new(MAX_KNOWN_EXTERNAL_ADDRESSES)
					.expect("value is a constant; constant is non-zero; qed."),
			),
			records_to_publish: Default::default(),
		}
	}
}

/// Implementation of `NetworkBehaviour` that discovers the nodes on the network.
pub struct DiscoveryBehaviour {
	/// User-defined list of nodes and their addresses. Typically includes bootstrap nodes and
	/// reserved nodes.
	permanent_addresses: Vec<(PeerId, Multiaddr)>,
	/// Same as `permanent_addresses`, except that addresses that fail to reach a peer are
	/// removed.
	ephemeral_addresses: HashMap<PeerId, Vec<Multiaddr>>,
	/// Kademlia requests and answers. Even though it's wrapped in `Toggle`, currently
	/// it's always enabled in `NetworkWorker::new()`.
	kademlia: Toggle<Kademlia<MemoryStore>>,
	/// Discovers nodes on the local network.
	mdns: Option<TokioMdns>,
	/// Stream that fires when we need to perform the next random Kademlia query. `None` if
	/// random walking is disabled.
	next_kad_random_query: Option<Delay>,
	/// After `next_kad_random_query` triggers, the next one triggers after this duration.
	duration_to_next_kad: Duration,
	/// Events to return in priority when polled.
	pending_events: VecDeque<DiscoveryOut>,
	/// Identity of our local node.
	local_peer_id: PeerId,
	/// Number of nodes we're currently connected to.
	num_connections: u64,
	/// If false, `addresses_of_peer` won't return any private IPv4/IPv6 address, except for the
	/// ones stored in `permanent_addresses` or `ephemeral_addresses`.
	allow_private_ip: bool,
	/// Number of active connections over which we interrupt the discovery process.
	discovery_only_if_under_num: u64,
	/// Should non-global addresses be added to the DHT?
	allow_non_globals_in_dht: bool,
	/// A cache of discovered external addresses. Only used for logging purposes.
	known_external_addresses: LruHashSet<Multiaddr>,
	/// Records to publish per QueryId.
	///
	/// After finishing a Kademlia query, libp2p will return us a list of the closest peers that
	/// did not return the record(in `FinishedWithNoAdditionalRecord`). We will then put the record
	/// to these peers.
	records_to_publish: HashMap<QueryId, Record>,
}

impl DiscoveryBehaviour {
	/// Returns the list of nodes that we know exist in the network.
	pub fn known_peers(&mut self) -> HashSet<PeerId> {
		let mut peers = HashSet::new();
		if let Some(k) = self.kademlia.as_mut() {
			for b in k.kbuckets() {
				for e in b.iter() {
					if !peers.contains(e.node.key.preimage()) {
						peers.insert(*e.node.key.preimage());
					}
				}
			}
		}
		peers
	}

	/// Adds a hard-coded address for the given peer, that never expires.
	///
	/// This adds an entry to the parameter that was passed to `new`.
	///
	/// If we didn't know this address before, also generates a `Discovered` event.
	pub fn add_known_address(&mut self, peer_id: PeerId, addr: Multiaddr) {
		let addrs_list = self.ephemeral_addresses.entry(peer_id).or_default();
		if addrs_list.contains(&addr) {
			return
		}

		if let Some(k) = self.kademlia.as_mut() {
			k.add_address(&peer_id, addr.clone());
		}

		self.pending_events.push_back(DiscoveryOut::Discovered(peer_id));
		addrs_list.push(addr);
	}

	/// Add a self-reported address of a remote peer to the k-buckets of the DHT
	/// if it has compatible `supported_protocols`.
	///
	/// **Note**: It is important that you call this method. The discovery mechanism will not
	/// automatically add connecting peers to the Kademlia k-buckets.
	pub fn add_self_reported_address(
		&mut self,
		peer_id: &PeerId,
		supported_protocols: &[impl AsRef<[u8]>],
		addr: Multiaddr,
	) {
		if let Some(kademlia) = self.kademlia.as_mut() {
			if !self.allow_non_globals_in_dht && !Self::can_add_to_dht(&addr) {
				trace!(
					target: "sub-libp2p",
					"Ignoring self-reported non-global address {} from {}.", addr, peer_id
				);
				return
			}

			if let Some(matching_protocol) = supported_protocols
				.iter()
				.find(|p| kademlia.protocol_names().iter().any(|k| k.as_ref() == p.as_ref()))
			{
				trace!(
					target: "sub-libp2p",
					"Adding self-reported address {} from {} to Kademlia DHT {}.",
					addr, peer_id, String::from_utf8_lossy(matching_protocol.as_ref()),
				);
				kademlia.add_address(peer_id, addr.clone());
			} else {
				trace!(
					target: "sub-libp2p",
					"Ignoring self-reported address {} from {} as remote node is not part of the \
					 Kademlia DHT supported by the local node.", addr, peer_id,
				);
			}
		}
	}

	/// Start fetching a record from the DHT.
	///
	/// A corresponding `ValueFound` or `ValueNotFound` event will later be generated.
	pub fn get_value(&mut self, key: RecordKey) {
		if let Some(k) = self.kademlia.as_mut() {
			k.get_record(key.clone());
		}
	}

	/// Start putting a record into the DHT. Other nodes can later fetch that value with
	/// `get_value`.
	///
	/// A corresponding `ValuePut` or `ValuePutFailed` event will later be generated.
	pub fn put_value(&mut self, key: RecordKey, value: Vec<u8>) {
		if let Some(k) = self.kademlia.as_mut() {
			if let Err(e) = k.put_record(Record::new(key.clone(), value.clone()), Quorum::All) {
				warn!(target: "sub-libp2p", "Libp2p => Failed to put record: {:?}", e);
				self.pending_events
					.push_back(DiscoveryOut::ValuePutFailed(key.clone(), Duration::from_secs(0)));
			}
		}
	}

	/// Returns the number of nodes in each Kademlia kbucket for each Kademlia instance.
	///
	/// Identifies Kademlia instances by their [`ProtocolId`] and kbuckets by the base 2 logarithm
	/// of their lower bound.
	pub fn num_entries_per_kbucket(&mut self) -> Option<Vec<(u32, usize)>> {
		self.kademlia.as_mut().map(|kad| {
			kad.kbuckets()
				.map(|bucket| (bucket.range().0.ilog2().unwrap_or(0), bucket.iter().count()))
				.collect()
		})
	}

	/// Returns the number of records in the Kademlia record stores.
	pub fn num_kademlia_records(&mut self) -> Option<usize> {
		// Note that this code is ok only because we use a `MemoryStore`.
		self.kademlia.as_mut().map(|kad| kad.store_mut().records().count())
	}

	/// Returns the total size in bytes of all the records in the Kademlia record stores.
	pub fn kademlia_records_total_size(&mut self) -> Option<usize> {
		// Note that this code is ok only because we use a `MemoryStore`. If the records were
		// for example stored on disk, this would load every single one of them every single time.
		self.kademlia
			.as_mut()
			.map(|kad| kad.store_mut().records().fold(0, |tot, rec| tot + rec.value.len()))
	}

	/// Can the given `Multiaddr` be put into the DHT?
	///
	/// This test is successful only for global IP addresses and DNS names.
	// NB: Currently all DNS names are allowed and no check for TLD suffixes is done
	// because the set of valid domains is highly dynamic and would require frequent
	// updates, for example by utilising publicsuffix.org or IANA.
	pub fn can_add_to_dht(addr: &Multiaddr) -> bool {
		let ip = match addr.iter().next() {
			Some(Protocol::Ip4(ip)) => IpNetwork::from(ip),
			Some(Protocol::Ip6(ip)) => IpNetwork::from(ip),
			Some(Protocol::Dns(_)) | Some(Protocol::Dns4(_)) | Some(Protocol::Dns6(_)) =>
				return true,
			_ => return false,
		};
		ip.is_global()
	}
}

/// Event generated by the `DiscoveryBehaviour`.
#[derive(Debug)]
pub enum DiscoveryOut {
	/// A connection to a peer has been established but the peer has not been
	/// added to the routing table because [`KademliaBucketInserts::Manual`] is
	/// configured. If the peer is to be included in the routing table, it must
	/// be explicitly added via
	/// [`DiscoveryBehaviour::add_self_reported_address`].
	Discovered(PeerId),

	/// A peer connected to this node for whom no listen address is known.
	///
	/// In order for the peer to be added to the Kademlia routing table, a known
	/// listen address must be added via
	/// [`DiscoveryBehaviour::add_self_reported_address`], e.g. obtained through
	/// the `identify` protocol.
	UnroutablePeer(PeerId),

	/// The DHT yielded results for the record request.
	///
	/// Returning the result grouped in (key, value) pairs as well as the request duration.
	ValueFound(Vec<(RecordKey, Vec<u8>)>, Duration),

	/// The record requested was not found in the DHT.
	///
	/// Returning the corresponding key as well as the request duration.
	ValueNotFound(RecordKey, Duration),

	/// The record with a given key was successfully inserted into the DHT.
	///
	/// Returning the corresponding key as well as the request duration.
	ValuePut(RecordKey, Duration),

	/// Inserting a value into the DHT failed.
	///
	/// Returning the corresponding key as well as the request duration.
	ValuePutFailed(RecordKey, Duration),

	/// Started a random Kademlia query.
	///
	/// Only happens if [`DiscoveryConfig::with_dht_random_walk`] has been configured to `true`.
	RandomKademliaStarted,
}

impl NetworkBehaviour for DiscoveryBehaviour {
	type ConnectionHandler = ToggleConnectionHandler<KademliaHandler<QueryId>>;
	type OutEvent = DiscoveryOut;

	fn handle_established_inbound_connection(
		&mut self,
		connection_id: ConnectionId,
		peer: PeerId,
		local_addr: &Multiaddr,
		remote_addr: &Multiaddr,
	) -> Result<THandler<Self>, ConnectionDenied> {
		self.kademlia.handle_established_inbound_connection(
			connection_id,
			peer,
			local_addr,
			remote_addr,
		)
	}

	fn handle_established_outbound_connection(
		&mut self,
		connection_id: ConnectionId,
		peer: PeerId,
		addr: &Multiaddr,
		role_override: Endpoint,
	) -> Result<THandler<Self>, ConnectionDenied> {
		self.kademlia.handle_established_outbound_connection(
			connection_id,
			peer,
			addr,
			role_override,
		)
	}

	fn handle_pending_inbound_connection(
		&mut self,
		connection_id: ConnectionId,
		local_addr: &Multiaddr,
		remote_addr: &Multiaddr,
	) -> Result<(), ConnectionDenied> {
		self.kademlia
			.handle_pending_inbound_connection(connection_id, local_addr, remote_addr)
	}

	fn handle_pending_outbound_connection(
		&mut self,
		connection_id: ConnectionId,
		maybe_peer: Option<PeerId>,
		addresses: &[Multiaddr],
		effective_role: Endpoint,
	) -> Result<Vec<Multiaddr>, ConnectionDenied> {
		let Some(peer_id) = maybe_peer else { return Ok(Vec::new()); };

		let mut list = self
			.permanent_addresses
			.iter()
			.filter_map(|(p, a)| (*p == peer_id).then_some(a.clone()))
			.collect::<Vec<_>>();

		if let Some(ephemeral_addresses) = self.ephemeral_addresses.get(&peer_id) {
			list.extend(ephemeral_addresses.clone());
		}

		{
			let mut list_to_filter = self.kademlia.handle_pending_outbound_connection(
				connection_id,
				maybe_peer,
				addresses,
				effective_role,
			)?;

			if let Some(ref mut mdns) = self.mdns {
				list_to_filter.extend(mdns.handle_pending_outbound_connection(
					connection_id,
					maybe_peer,
					addresses,
					effective_role,
				)?);
			}

			if !self.allow_private_ip {
				list_to_filter.retain(|addr| match addr.iter().next() {
					Some(Protocol::Ip4(addr)) if !IpNetwork::from(addr).is_global() => false,
					Some(Protocol::Ip6(addr)) if !IpNetwork::from(addr).is_global() => false,
					_ => true,
				});
			}

			list.extend(list_to_filter);
		}

		trace!(target: "sub-libp2p", "Addresses of {:?}: {:?}", peer_id, list);

		Ok(list)
	}

	fn on_swarm_event(&mut self, event: FromSwarm<Self::ConnectionHandler>) {
		match event {
			FromSwarm::ConnectionEstablished(e) => {
				self.num_connections += 1;
				self.kademlia.on_swarm_event(FromSwarm::ConnectionEstablished(e));
			},
			FromSwarm::ConnectionClosed(e) => {
				self.num_connections -= 1;
				self.kademlia.on_swarm_event(FromSwarm::ConnectionClosed(e));
			},
			FromSwarm::DialFailure(e @ DialFailure { peer_id, error, .. }) => {
				if let Some(peer_id) = peer_id {
					if let DialError::Transport(errors) = error {
						if let Entry::Occupied(mut entry) = self.ephemeral_addresses.entry(peer_id)
						{
							for (addr, _error) in errors {
								entry.get_mut().retain(|a| a != addr);
							}
							if entry.get().is_empty() {
								entry.remove();
							}
						}
					}
				}

				self.kademlia.on_swarm_event(FromSwarm::DialFailure(e));
			},
			FromSwarm::ListenerClosed(e) => {
				self.kademlia.on_swarm_event(FromSwarm::ListenerClosed(e));
			},
			FromSwarm::ListenFailure(e) => {
				self.kademlia.on_swarm_event(FromSwarm::ListenFailure(e));
			},
			FromSwarm::ListenerError(e) => {
				self.kademlia.on_swarm_event(FromSwarm::ListenerError(e));
			},
			FromSwarm::ExpiredExternalAddr(e) => {
				// We intentionally don't remove the element from `known_external_addresses` in
				// order to not print the log line again.

				self.kademlia.on_swarm_event(FromSwarm::ExpiredExternalAddr(e));
			},
			FromSwarm::NewListener(e) => {
				self.kademlia.on_swarm_event(FromSwarm::NewListener(e));
			},
			FromSwarm::ExpiredListenAddr(e) => {
				self.kademlia.on_swarm_event(FromSwarm::ExpiredListenAddr(e));
			},
			FromSwarm::NewExternalAddr(e @ NewExternalAddr { addr }) => {
				let new_addr = addr.clone().with(Protocol::P2p(self.local_peer_id.into()));

				if Self::can_add_to_dht(addr) {
					// NOTE: we might re-discover the same address multiple times
					// in which case we just want to refrain from logging.
					if self.known_external_addresses.insert(new_addr.clone()) {
						info!(
						  target: "sub-libp2p",
						  "🔍 Discovered new external address for our node: {}",
						  new_addr,
						);
					}
				}

				self.kademlia.on_swarm_event(FromSwarm::NewExternalAddr(e));
			},
			FromSwarm::AddressChange(e) => {
				self.kademlia.on_swarm_event(FromSwarm::AddressChange(e));
			},
			FromSwarm::NewListenAddr(e) => {
				self.kademlia.on_swarm_event(FromSwarm::NewListenAddr(e));

				if let Some(ref mut mdns) = self.mdns {
					mdns.on_swarm_event(FromSwarm::NewListenAddr(e));
				}
			},
		}
	}

	fn on_connection_handler_event(
		&mut self,
		peer_id: PeerId,
		connection_id: ConnectionId,
		event: THandlerOutEvent<Self>,
	) {
		self.kademlia.on_connection_handler_event(peer_id, connection_id, event);
	}

	fn poll(
		&mut self,
		cx: &mut Context,
		params: &mut impl PollParameters,
	) -> Poll<ToSwarm<Self::OutEvent, THandlerInEvent<Self>>> {
		// Immediately process the content of `discovered`.
		if let Some(ev) = self.pending_events.pop_front() {
			return Poll::Ready(ToSwarm::GenerateEvent(ev))
		}

		// Poll the stream that fires when we need to start a random Kademlia query.
		if let Some(kademlia) = self.kademlia.as_mut() {
			if let Some(next_kad_random_query) = self.next_kad_random_query.as_mut() {
				while next_kad_random_query.poll_unpin(cx).is_ready() {
					let actually_started =
						if self.num_connections < self.discovery_only_if_under_num {
							let random_peer_id = PeerId::random();
							debug!(
								target: "sub-libp2p",
								"Libp2p <= Starting random Kademlia request for {:?}",
								random_peer_id,
							);
							kademlia.get_closest_peers(random_peer_id);
							true
						} else {
							debug!(
								target: "sub-libp2p",
								"Kademlia paused due to high number of connections ({})",
								self.num_connections
							);
							false
						};

					// Schedule the next random query with exponentially increasing delay,
					// capped at 60 seconds.
					*next_kad_random_query = Delay::new(self.duration_to_next_kad);
					self.duration_to_next_kad =
						cmp::min(self.duration_to_next_kad * 2, Duration::from_secs(60));

					if actually_started {
						let ev = DiscoveryOut::RandomKademliaStarted;
						return Poll::Ready(ToSwarm::GenerateEvent(ev))
					}
				}
			}
		}

		while let Poll::Ready(ev) = self.kademlia.poll(cx, params) {
			match ev {
				ToSwarm::GenerateEvent(ev) => match ev {
					KademliaEvent::RoutingUpdated { peer, .. } => {
						let ev = DiscoveryOut::Discovered(peer);
						return Poll::Ready(ToSwarm::GenerateEvent(ev))
					},
					KademliaEvent::UnroutablePeer { peer, .. } => {
						let ev = DiscoveryOut::UnroutablePeer(peer);
						return Poll::Ready(ToSwarm::GenerateEvent(ev))
					},
					KademliaEvent::RoutablePeer { peer, .. } => {
						let ev = DiscoveryOut::Discovered(peer);
						return Poll::Ready(ToSwarm::GenerateEvent(ev))
					},
					KademliaEvent::PendingRoutablePeer { .. } |
					KademliaEvent::InboundRequest { .. } => {
						// We are not interested in this event at the moment.
					},
					KademliaEvent::OutboundQueryProgressed {
						result: QueryResult::GetClosestPeers(res),
						..
					} => match res {
						Err(GetClosestPeersError::Timeout { key, peers }) => {
							debug!(
								target: "sub-libp2p",
								"Libp2p => Query for {:?} timed out with {} results",
								HexDisplay::from(&key), peers.len(),
							);
						},
						Ok(ok) => {
							trace!(
								target: "sub-libp2p",
								"Libp2p => Query for {:?} yielded {:?} results",
								HexDisplay::from(&ok.key), ok.peers.len(),
							);
							if ok.peers.is_empty() && self.num_connections != 0 {
								debug!(
									target: "sub-libp2p",
									"Libp2p => Random Kademlia query has yielded empty results",
								);
							}
						},
					},
					KademliaEvent::OutboundQueryProgressed {
						result: QueryResult::GetRecord(res),
						stats,
						id,
						..
					} => {
						let ev = match res {
							Ok(GetRecordOk::FoundRecord(r)) => {
								debug!(
									target: "sub-libp2p",
									"Libp2p => Found record ({:?}) with value: {:?}",
									r.record.key,
									r.record.value,
								);

								// Let's directly finish the query, as we are only interested in a
								// quorum of 1.
								if let Some(kad) = self.kademlia.as_mut() {
									if let Some(mut query) = kad.query_mut(&id) {
										query.finish();
									}
								}

								// Will be removed below when we receive
								// `FinishedWithNoAdditionalRecord`.
								self.records_to_publish.insert(id, r.record.clone());

								DiscoveryOut::ValueFound(
									vec![(r.record.key, r.record.value)],
									stats.duration().unwrap_or_default(),
								)
							},
							Ok(GetRecordOk::FinishedWithNoAdditionalRecord {
								cache_candidates,
							}) => {
								// We always need to remove the record to not leak any data!
								if let Some(record) = self.records_to_publish.remove(&id) {
									if cache_candidates.is_empty() {
										continue
									}

									// Put the record to the `cache_candidates` that are nearest to
									// the record key from our point of view of the network.
									if let Some(kad) = self.kademlia.as_mut() {
										kad.put_record_to(
											record,
											cache_candidates.into_iter().map(|v| v.1),
											Quorum::One,
										);
									}
								}

								continue
							},
							Err(e @ libp2p::kad::GetRecordError::NotFound { .. }) => {
								trace!(
									target: "sub-libp2p",
									"Libp2p => Failed to get record: {:?}",
									e,
								);
								DiscoveryOut::ValueNotFound(
									e.into_key(),
									stats.duration().unwrap_or_default(),
								)
							},
							Err(e) => {
								debug!(
									target: "sub-libp2p",
									"Libp2p => Failed to get record: {:?}",
									e,
								);
								DiscoveryOut::ValueNotFound(
									e.into_key(),
									stats.duration().unwrap_or_default(),
								)
							},
						};
						return Poll::Ready(ToSwarm::GenerateEvent(ev))
					},
					KademliaEvent::OutboundQueryProgressed {
						result: QueryResult::PutRecord(res),
						stats,
						..
					} => {
						let ev = match res {
							Ok(ok) =>
								DiscoveryOut::ValuePut(ok.key, stats.duration().unwrap_or_default()),
							Err(e) => {
								debug!(
									target: "sub-libp2p",
									"Libp2p => Failed to put record: {:?}",
									e,
								);
								DiscoveryOut::ValuePutFailed(
									e.into_key(),
									stats.duration().unwrap_or_default(),
								)
							},
						};
						return Poll::Ready(ToSwarm::GenerateEvent(ev))
					},
					KademliaEvent::OutboundQueryProgressed {
						result: QueryResult::RepublishRecord(res),
						..
					} => match res {
						Ok(ok) => debug!(
							target: "sub-libp2p",
							"Libp2p => Record republished: {:?}",
							ok.key,
						),
						Err(e) => debug!(
							target: "sub-libp2p",
							"Libp2p => Republishing of record {:?} failed with: {:?}",
							e.key(), e,
						),
					},
					// We never start any other type of query.
					KademliaEvent::OutboundQueryProgressed { result: e, .. } => {
						warn!(target: "sub-libp2p", "Libp2p => Unhandled Kademlia event: {:?}", e)
					},
				},
				ToSwarm::Dial { opts } => return Poll::Ready(ToSwarm::Dial { opts }),
				ToSwarm::NotifyHandler { peer_id, handler, event } =>
					return Poll::Ready(ToSwarm::NotifyHandler { peer_id, handler, event }),
				ToSwarm::ReportObservedAddr { address, score } =>
					return Poll::Ready(ToSwarm::ReportObservedAddr { address, score }),
				ToSwarm::CloseConnection { peer_id, connection } =>
					return Poll::Ready(ToSwarm::CloseConnection { peer_id, connection }),
			}
		}

		// Poll mDNS.
		if let Some(ref mut mdns) = self.mdns {
			while let Poll::Ready(ev) = mdns.poll(cx, params) {
				match ev {
					ToSwarm::GenerateEvent(event) => match event {
						mdns::Event::Discovered(list) => {
							if self.num_connections >= self.discovery_only_if_under_num {
								continue
							}

							self.pending_events
								.extend(list.map(|(peer_id, _)| DiscoveryOut::Discovered(peer_id)));
							if let Some(ev) = self.pending_events.pop_front() {
								return Poll::Ready(ToSwarm::GenerateEvent(ev))
							}
						},
						mdns::Event::Expired(_) => {},
					},
					ToSwarm::Dial { .. } => {
						unreachable!("mDNS never dials!");
					},
					ToSwarm::NotifyHandler { event, .. } => match event {}, /* `event` is an */
					// enum with no
					// variant
					ToSwarm::ReportObservedAddr { address, score } =>
						return Poll::Ready(ToSwarm::ReportObservedAddr { address, score }),
					ToSwarm::CloseConnection { peer_id, connection } =>
						return Poll::Ready(ToSwarm::CloseConnection { peer_id, connection }),
				}
			}
		}

		Poll::Pending
	}
}

/// Legacy (fallback) Kademlia protocol name based on `protocol_id`.
fn legacy_kademlia_protocol_name(id: &ProtocolId) -> Vec<u8> {
	let mut v = vec![b'/'];
	v.extend_from_slice(id.as_ref().as_bytes());
	v.extend_from_slice(b"/kad");
	v
}

/// Kademlia protocol name based on `genesis_hash` and `fork_id`.
fn kademlia_protocol_name<Hash: AsRef<[u8]>>(genesis_hash: Hash, fork_id: Option<&str>) -> Vec<u8> {
	let genesis_hash_hex = bytes2hex("", genesis_hash.as_ref());
	if let Some(fork_id) = fork_id {
		format!("/{}/{}/kad", genesis_hash_hex, fork_id).as_bytes().into()
	} else {
		format!("/{}/kad", genesis_hash_hex).as_bytes().into()
	}
}

#[cfg(test)]
mod tests {
	use super::{
		kademlia_protocol_name, legacy_kademlia_protocol_name, DiscoveryConfig, DiscoveryOut,
	};
	use crate::config::ProtocolId;
	use futures::prelude::*;
	use libp2p::{
		core::{
			transport::{MemoryTransport, Transport},
			upgrade,
		},
		identity::Keypair,
		noise,
		swarm::{Executor, Swarm, SwarmBuilder, SwarmEvent},
		yamux, Multiaddr,
	};
	use sp_core::hash::H256;
	use std::{collections::HashSet, pin::Pin, task::Poll};

	struct TokioExecutor(tokio::runtime::Runtime);
	impl Executor for TokioExecutor {
		fn exec(&self, f: Pin<Box<dyn Future<Output = ()> + Send>>) {
			let _ = self.0.spawn(f);
		}
	}

	#[test]
	fn discovery_working() {
		let mut first_swarm_peer_id_and_addr = None;

		let genesis_hash = H256::from_low_u64_be(1);
		let fork_id = Some("test-fork-id");
		let protocol_id = ProtocolId::from("dot");

		// Build swarms whose behaviour is `DiscoveryBehaviour`, each aware of
		// the first swarm via `with_permanent_addresses`.
		let mut swarms = (0..25)
			.map(|i| {
				let keypair = Keypair::generate_ed25519();

				let transport = MemoryTransport::new()
					.upgrade(upgrade::Version::V1)
					.authenticate(noise::Config::new(&keypair).unwrap())
					.multiplex(yamux::Config::default())
					.boxed();

				let behaviour = {
					let mut config = DiscoveryConfig::new(keypair.public().to_peer_id());
					config
						.with_permanent_addresses(first_swarm_peer_id_and_addr.clone())
						.allow_private_ip(true)
						.allow_non_globals_in_dht(true)
						.discovery_limit(50)
						.with_kademlia(genesis_hash, fork_id, &protocol_id);

					config.finish()
				};

				let runtime = tokio::runtime::Runtime::new().unwrap();
				let mut swarm = SwarmBuilder::with_executor(
					transport,
					behaviour,
					keypair.public().to_peer_id(),
					TokioExecutor(runtime),
				)
				.build();
				let listen_addr: Multiaddr =
					format!("/memory/{}", rand::random::<u64>()).parse().unwrap();

				if i == 0 {
					first_swarm_peer_id_and_addr =
						Some((keypair.public().to_peer_id(), listen_addr.clone()))
				}

				swarm.listen_on(listen_addr.clone()).unwrap();
				(swarm, listen_addr)
			})
			.collect::<Vec<_>>();

		// Build a `Vec<HashSet<PeerId>>` with the list of nodes remaining to be discovered.
		let mut to_discover = (0..swarms.len())
			.map(|n| {
				(0..swarms.len())
					// Skip the first swarm as all other swarms already know it.
					.skip(1)
					.filter(|p| *p != n)
					.map(|p| *Swarm::local_peer_id(&swarms[p].0))
					.collect::<HashSet<_>>()
			})
			.collect::<Vec<_>>();

		let fut = futures::future::poll_fn(move |cx| {
			'polling: loop {
				for swarm_n in 0..swarms.len() {
					match swarms[swarm_n].0.poll_next_unpin(cx) {
						Poll::Ready(Some(e)) => {
							match e {
								SwarmEvent::Behaviour(behavior) => {
									match behavior {
										DiscoveryOut::UnroutablePeer(other) |
										DiscoveryOut::Discovered(other) => {
											// Call `add_self_reported_address` to simulate identify
											// happening.
											let addr = swarms
												.iter()
												.find_map(|(s, a)| {
													if s.behaviour().local_peer_id == other {
														Some(a.clone())
													} else {
														None
													}
												})
												.unwrap();
											// Test both genesis hash-based and legacy
											// protocol names.
											let protocol_name = if swarm_n % 2 == 0 {
												kademlia_protocol_name(genesis_hash, fork_id)
											} else {
												legacy_kademlia_protocol_name(&protocol_id)
											};
											swarms[swarm_n]
												.0
												.behaviour_mut()
												.add_self_reported_address(
													&other,
													&[protocol_name],
													addr,
												);

											to_discover[swarm_n].remove(&other);
										},
										DiscoveryOut::RandomKademliaStarted => {},
										e => {
											panic!("Unexpected event: {:?}", e)
										},
									}
								},
								// ignore non Behaviour events
								_ => {},
							}
							continue 'polling
						},
						_ => {},
					}
				}
				break
			}

			if to_discover.iter().all(|l| l.is_empty()) {
				Poll::Ready(())
			} else {
				Poll::Pending
			}
		});

		futures::executor::block_on(fut);
	}

	#[test]
	fn discovery_ignores_peers_with_unknown_protocols() {
		let supported_genesis_hash = H256::from_low_u64_be(1);
		let unsupported_genesis_hash = H256::from_low_u64_be(2);
		let supported_protocol_id = ProtocolId::from("a");
		let unsupported_protocol_id = ProtocolId::from("b");

		let mut discovery = {
			let keypair = Keypair::generate_ed25519();
			let mut config = DiscoveryConfig::new(keypair.public().to_peer_id());
			config
				.allow_private_ip(true)
				.allow_non_globals_in_dht(true)
				.discovery_limit(50)
				.with_kademlia(supported_genesis_hash, None, &supported_protocol_id);
			config.finish()
		};

		let predictable_peer_id = |bytes: &[u8; 32]| {
			Keypair::ed25519_from_bytes(bytes.to_owned()).unwrap().public().to_peer_id()
		};

		let remote_peer_id = predictable_peer_id(b"00000000000000000000000000000001");
		let remote_addr: Multiaddr = "/memory/1".parse().unwrap();
		let another_peer_id = predictable_peer_id(b"00000000000000000000000000000002");
		let another_addr: Multiaddr = "/memory/2".parse().unwrap();

		// Try adding remote peers with unsupported protocols.
		discovery.add_self_reported_address(
			&remote_peer_id,
			&[kademlia_protocol_name(unsupported_genesis_hash, None)],
			remote_addr.clone(),
		);
		discovery.add_self_reported_address(
			&another_peer_id,
			&[legacy_kademlia_protocol_name(&unsupported_protocol_id)],
			another_addr.clone(),
		);

		{
			let kademlia = discovery.kademlia.as_mut().unwrap();
			assert!(
				kademlia
					.kbucket(remote_peer_id)
					.expect("Remote peer id not to be equal to local peer id.")
					.is_empty(),
				"Expect peer with unsupported protocol not to be added."
			);
			assert!(
				kademlia
					.kbucket(another_peer_id)
					.expect("Remote peer id not to be equal to local peer id.")
					.is_empty(),
				"Expect peer with unsupported protocol not to be added."
			);
		}

		// Add remote peers with supported protocols.
		discovery.add_self_reported_address(
			&remote_peer_id,
			&[kademlia_protocol_name(supported_genesis_hash, None)],
			remote_addr.clone(),
		);
		discovery.add_self_reported_address(
			&another_peer_id,
			&[legacy_kademlia_protocol_name(&supported_protocol_id)],
			another_addr.clone(),
		);

		{
			let kademlia = discovery.kademlia.as_mut().unwrap();
			assert_eq!(
				2,
				kademlia.kbuckets().fold(0, |acc, bucket| acc + bucket.num_entries()),
				"Expect peers with supported protocol to be added."
			);
		}
	}
}
