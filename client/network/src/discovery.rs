// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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

use array_bytes::bytes2hex;
use futures::prelude::*;
use futures_timer::Delay;
use ip_network::IpNetwork;
use libp2p::{
	core::{
		connection::ConnectionId, transport::ListenerId, ConnectedPoint, Multiaddr, PeerId,
		PublicKey,
	},
	kad::{
		handler::KademliaHandlerProto,
		record::{
			self,
			store::{MemoryStore, RecordStore},
		},
		GetClosestPeersError, Kademlia, KademliaBucketInserts, KademliaConfig, KademliaEvent,
		QueryId, QueryResult, Quorum, Record,
	},
	mdns::{MdnsConfig, MdnsEvent, TokioMdns},
	multiaddr::Protocol,
	swarm::{
		behaviour::toggle::{Toggle, ToggleIntoConnectionHandler},
		ConnectionHandler, DialError, IntoConnectionHandler, NetworkBehaviour,
		NetworkBehaviourAction, PollParameters,
	},
};
use log::{debug, info, trace, warn};
use sc_network_common::{config::ProtocolId, utils::LruHashSet};
use sp_core::hexdisplay::HexDisplay;
use std::{
	cmp,
	collections::{HashMap, HashSet, VecDeque},
	io,
	num::NonZeroUsize,
	task::{Context, Poll},
	time::Duration,
};

/// Maximum number of known external addresses that we will cache.
/// This only affects whether we will log whenever we (re-)discover
/// a given address.
const MAX_KNOWN_EXTERNAL_ADDRESSES: usize = 32;

/// `DiscoveryBehaviour` configuration.
///
/// Note: In order to discover nodes or load and store values via Kademlia one has to add
///       Kademlia protocol via [`DiscoveryConfig::with_kademlia`].
pub struct DiscoveryConfig {
	local_peer_id: PeerId,
	permanent_addresses: Vec<(PeerId, Multiaddr)>,
	dht_random_walk: bool,
	allow_private_ipv4: bool,
	allow_non_globals_in_dht: bool,
	discovery_only_if_under_num: u64,
	enable_mdns: bool,
	kademlia_disjoint_query_paths: bool,
	kademlia_protocols: Vec<Vec<u8>>,
}

impl DiscoveryConfig {
	/// Create a default configuration with the given public key.
	pub fn new(local_public_key: PublicKey) -> Self {
		Self {
			local_peer_id: local_public_key.to_peer_id(),
			permanent_addresses: Vec::new(),
			dht_random_walk: true,
			allow_private_ipv4: true,
			allow_non_globals_in_dht: false,
			discovery_only_if_under_num: std::u64::MAX,
			enable_mdns: false,
			kademlia_disjoint_query_paths: false,
			kademlia_protocols: Vec::new(),
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

	/// Should private IPv4 addresses be reported?
	pub fn allow_private_ipv4(&mut self, value: bool) -> &mut Self {
		self.allow_private_ipv4 = value;
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

	/// Create a `DiscoveryBehaviour` from this config.
	pub fn finish(self) -> DiscoveryBehaviour {
		let Self {
			local_peer_id,
			permanent_addresses,
			dht_random_walk,
			allow_private_ipv4,
			allow_non_globals_in_dht,
			discovery_only_if_under_num,
			enable_mdns,
			kademlia_disjoint_query_paths,
			kademlia_protocols,
		} = self;

		let kademlia = if !kademlia_protocols.is_empty() {
			let mut config = KademliaConfig::default();
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
			allow_private_ipv4,
			discovery_only_if_under_num,
			mdns: if enable_mdns {
				match TokioMdns::new(MdnsConfig::default()) {
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
	/// If false, `addresses_of_peer` won't return any private IPv4 address, except for the ones
	/// stored in `permanent_addresses` or `ephemeral_addresses`.
	allow_private_ipv4: bool,
	/// Number of active connections over which we interrupt the discovery process.
	discovery_only_if_under_num: u64,
	/// Should non-global addresses be added to the DHT?
	allow_non_globals_in_dht: bool,
	/// A cache of discovered external addresses. Only used for logging purposes.
	known_external_addresses: LruHashSet<Multiaddr>,
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
		if !addrs_list.iter().any(|a| *a == addr) {
			if let Some(k) = self.kademlia.as_mut() {
				k.add_address(&peer_id, addr.clone());
			}

			self.pending_events.push_back(DiscoveryOut::Discovered(peer_id));
			addrs_list.push(addr);
		}
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
	pub fn get_value(&mut self, key: record::Key) {
		if let Some(k) = self.kademlia.as_mut() {
			k.get_record(key.clone(), Quorum::One);
		}
	}

	/// Start putting a record into the DHT. Other nodes can later fetch that value with
	/// `get_value`.
	///
	/// A corresponding `ValuePut` or `ValuePutFailed` event will later be generated.
	pub fn put_value(&mut self, key: record::Key, value: Vec<u8>) {
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
	/// Returning the result grouped in (key, value) pairs as well as the request duration..
	ValueFound(Vec<(record::Key, Vec<u8>)>, Duration),

	/// The record requested was not found in the DHT.
	///
	/// Returning the corresponding key as well as the request duration.
	ValueNotFound(record::Key, Duration),

	/// The record with a given key was successfully inserted into the DHT.
	///
	/// Returning the corresponding key as well as the request duration.
	ValuePut(record::Key, Duration),

	/// Inserting a value into the DHT failed.
	///
	/// Returning the corresponding key as well as the request duration.
	ValuePutFailed(record::Key, Duration),

	/// Started a random Kademlia query.
	///
	/// Only happens if [`DiscoveryConfig::with_dht_random_walk`] has been configured to `true`.
	RandomKademliaStarted,
}

impl NetworkBehaviour for DiscoveryBehaviour {
	type ConnectionHandler = ToggleIntoConnectionHandler<KademliaHandlerProto<QueryId>>;
	type OutEvent = DiscoveryOut;

	fn new_handler(&mut self) -> Self::ConnectionHandler {
		self.kademlia.new_handler()
	}

	fn addresses_of_peer(&mut self, peer_id: &PeerId) -> Vec<Multiaddr> {
		let mut list = self
			.permanent_addresses
			.iter()
			.filter_map(|(p, a)| if p == peer_id { Some(a.clone()) } else { None })
			.collect::<Vec<_>>();

		if let Some(ephemeral_addresses) = self.ephemeral_addresses.get(peer_id) {
			list.extend(ephemeral_addresses.clone());
		}

		{
			let mut list_to_filter = self.kademlia.addresses_of_peer(peer_id);

			if let Some(ref mut mdns) = self.mdns {
				list_to_filter.extend(mdns.addresses_of_peer(peer_id));
			}

			if !self.allow_private_ipv4 {
				list_to_filter.retain(|addr| match addr.iter().next() {
					Some(Protocol::Ip4(addr)) if !IpNetwork::from(addr).is_global() => false,
					Some(Protocol::Ip6(addr)) if !IpNetwork::from(addr).is_global() => false,
					_ => true,
				});
			}

			list.extend(list_to_filter);
		}

		trace!(target: "sub-libp2p", "Addresses of {:?}: {:?}", peer_id, list);

		list
	}

	fn inject_address_change(
		&mut self,
		peer_id: &PeerId,
		connection_id: &ConnectionId,
		old: &ConnectedPoint,
		new: &ConnectedPoint,
	) {
		self.kademlia.inject_address_change(peer_id, connection_id, old, new)
	}

	fn inject_connection_established(
		&mut self,
		peer_id: &PeerId,
		conn: &ConnectionId,
		endpoint: &ConnectedPoint,
		failed_addresses: Option<&Vec<Multiaddr>>,
		other_established: usize,
	) {
		self.num_connections += 1;
		self.kademlia.inject_connection_established(
			peer_id,
			conn,
			endpoint,
			failed_addresses,
			other_established,
		)
	}

	fn inject_connection_closed(
		&mut self,
		peer_id: &PeerId,
		conn: &ConnectionId,
		endpoint: &ConnectedPoint,
		handler: <Self::ConnectionHandler as IntoConnectionHandler>::Handler,
		remaining_established: usize,
	) {
		self.num_connections -= 1;
		self.kademlia.inject_connection_closed(
			peer_id,
			conn,
			endpoint,
			handler,
			remaining_established,
		)
	}

	fn inject_dial_failure(
		&mut self,
		peer_id: Option<PeerId>,
		handler: Self::ConnectionHandler,
		error: &DialError,
	) {
		if let Some(peer_id) = peer_id {
			if let DialError::Transport(errors) = error {
				if let Some(list) = self.ephemeral_addresses.get_mut(&peer_id) {
					for (addr, _error) in errors {
						list.retain(|a| a != addr);
					}
				}
			}
		}

		self.kademlia.inject_dial_failure(peer_id, handler, error)
	}

	fn inject_event(
		&mut self,
		peer_id: PeerId,
		connection: ConnectionId,
		event: <<Self::ConnectionHandler as IntoConnectionHandler>::Handler as ConnectionHandler>::OutEvent,
	) {
		self.kademlia.inject_event(peer_id, connection, event)
	}

	fn inject_new_external_addr(&mut self, addr: &Multiaddr) {
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

		self.kademlia.inject_new_external_addr(addr)
	}

	fn inject_expired_external_addr(&mut self, addr: &Multiaddr) {
		// We intentionally don't remove the element from `known_external_addresses` in order
		// to not print the log line again.

		self.kademlia.inject_expired_external_addr(addr)
	}

	fn inject_expired_listen_addr(&mut self, id: ListenerId, addr: &Multiaddr) {
		self.kademlia.inject_expired_listen_addr(id, addr)
	}

	fn inject_new_listener(&mut self, id: ListenerId) {
		self.kademlia.inject_new_listener(id)
	}

	fn inject_new_listen_addr(&mut self, id: ListenerId, addr: &Multiaddr) {
		self.kademlia.inject_new_listen_addr(id, addr)
	}

	fn inject_listen_failure(&mut self, _: &Multiaddr, _: &Multiaddr, _: Self::ConnectionHandler) {
		// NetworkBehaviour::inject_listen_failure on Kademlia<MemoryStore> does nothing.
	}

	fn inject_listener_error(&mut self, id: ListenerId, err: &(dyn std::error::Error + 'static)) {
		self.kademlia.inject_listener_error(id, err)
	}

	fn inject_listener_closed(&mut self, id: ListenerId, reason: Result<(), &io::Error>) {
		self.kademlia.inject_listener_closed(id, reason)
	}

	fn poll(
		&mut self,
		cx: &mut Context,
		params: &mut impl PollParameters,
	) -> Poll<NetworkBehaviourAction<Self::OutEvent, Self::ConnectionHandler>> {
		// Immediately process the content of `discovered`.
		if let Some(ev) = self.pending_events.pop_front() {
			return Poll::Ready(NetworkBehaviourAction::GenerateEvent(ev))
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
						return Poll::Ready(NetworkBehaviourAction::GenerateEvent(ev))
					}
				}
			}
		}

		while let Poll::Ready(ev) = self.kademlia.poll(cx, params) {
			match ev {
				NetworkBehaviourAction::GenerateEvent(ev) => match ev {
					KademliaEvent::RoutingUpdated { peer, .. } => {
						let ev = DiscoveryOut::Discovered(peer);
						return Poll::Ready(NetworkBehaviourAction::GenerateEvent(ev))
					},
					KademliaEvent::UnroutablePeer { peer, .. } => {
						let ev = DiscoveryOut::UnroutablePeer(peer);
						return Poll::Ready(NetworkBehaviourAction::GenerateEvent(ev))
					},
					KademliaEvent::RoutablePeer { peer, .. } => {
						let ev = DiscoveryOut::Discovered(peer);
						return Poll::Ready(NetworkBehaviourAction::GenerateEvent(ev))
					},
					KademliaEvent::PendingRoutablePeer { .. } |
					KademliaEvent::InboundRequest { .. } => {
						// We are not interested in this event at the moment.
					},
					KademliaEvent::OutboundQueryCompleted {
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
					KademliaEvent::OutboundQueryCompleted {
						result: QueryResult::GetRecord(res),
						stats,
						..
					} => {
						let ev = match res {
							Ok(ok) => {
								let results = ok
									.records
									.into_iter()
									.map(|r| (r.record.key, r.record.value))
									.collect();

								DiscoveryOut::ValueFound(
									results,
									stats.duration().unwrap_or_default(),
								)
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
						return Poll::Ready(NetworkBehaviourAction::GenerateEvent(ev))
					},
					KademliaEvent::OutboundQueryCompleted {
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
						return Poll::Ready(NetworkBehaviourAction::GenerateEvent(ev))
					},
					KademliaEvent::OutboundQueryCompleted {
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
					KademliaEvent::OutboundQueryCompleted { result: e, .. } => {
						warn!(target: "sub-libp2p", "Libp2p => Unhandled Kademlia event: {:?}", e)
					},
				},
				NetworkBehaviourAction::Dial { opts, handler } =>
					return Poll::Ready(NetworkBehaviourAction::Dial { opts, handler }),
				NetworkBehaviourAction::NotifyHandler { peer_id, handler, event } =>
					return Poll::Ready(NetworkBehaviourAction::NotifyHandler {
						peer_id,
						handler,
						event,
					}),
				NetworkBehaviourAction::ReportObservedAddr { address, score } =>
					return Poll::Ready(NetworkBehaviourAction::ReportObservedAddr {
						address,
						score,
					}),
				NetworkBehaviourAction::CloseConnection { peer_id, connection } =>
					return Poll::Ready(NetworkBehaviourAction::CloseConnection {
						peer_id,
						connection,
					}),
			}
		}

		// Poll mDNS.
		if let Some(ref mut mdns) = self.mdns {
			while let Poll::Ready(ev) = mdns.poll(cx, params) {
				match ev {
					NetworkBehaviourAction::GenerateEvent(event) => match event {
						MdnsEvent::Discovered(list) => {
							if self.num_connections >= self.discovery_only_if_under_num {
								continue
							}

							self.pending_events
								.extend(list.map(|(peer_id, _)| DiscoveryOut::Discovered(peer_id)));
							if let Some(ev) = self.pending_events.pop_front() {
								return Poll::Ready(NetworkBehaviourAction::GenerateEvent(ev))
							}
						},
						MdnsEvent::Expired(_) => {},
					},
					NetworkBehaviourAction::Dial { .. } => {
						unreachable!("mDNS never dials!");
					},
					NetworkBehaviourAction::NotifyHandler { event, .. } => match event {}, /* `event` is an enum with no variant */
					NetworkBehaviourAction::ReportObservedAddr { address, score } =>
						return Poll::Ready(NetworkBehaviourAction::ReportObservedAddr {
							address,
							score,
						}),
					NetworkBehaviourAction::CloseConnection { peer_id, connection } =>
						return Poll::Ready(NetworkBehaviourAction::CloseConnection {
							peer_id,
							connection,
						}),
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
	use futures::prelude::*;
	use libp2p::{
		core::{
			transport::{MemoryTransport, Transport},
			upgrade,
		},
		identity::{ed25519, Keypair},
		noise,
		swarm::{Swarm, SwarmEvent},
		yamux, Multiaddr,
	};
	use sc_network_common::config::ProtocolId;
	use sp_core::hash::H256;
	use std::{collections::HashSet, task::Poll};

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

				let noise_keys =
					noise::Keypair::<noise::X25519Spec>::new().into_authentic(&keypair).unwrap();

				let transport = MemoryTransport::new()
					.upgrade(upgrade::Version::V1)
					.authenticate(noise::NoiseConfig::xx(noise_keys).into_authenticated())
					.multiplex(yamux::YamuxConfig::default())
					.boxed();

				let behaviour = {
					let mut config = DiscoveryConfig::new(keypair.public());
					config
						.with_permanent_addresses(first_swarm_peer_id_and_addr.clone())
						.allow_private_ipv4(true)
						.allow_non_globals_in_dht(true)
						.discovery_limit(50)
						.with_kademlia(genesis_hash, fork_id, &protocol_id);

					config.finish()
				};

				let mut swarm = Swarm::new(transport, behaviour, keypair.public().to_peer_id());
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
			let mut config = DiscoveryConfig::new(keypair.public());
			config
				.allow_private_ipv4(true)
				.allow_non_globals_in_dht(true)
				.discovery_limit(50)
				.with_kademlia(supported_genesis_hash, None, &supported_protocol_id);
			config.finish()
		};

		let predictable_peer_id = |bytes: &[u8; 32]| {
			Keypair::Ed25519(ed25519::Keypair::from(
				ed25519::SecretKey::from_bytes(bytes.to_owned()).unwrap(),
			))
			.public()
			.to_peer_id()
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
