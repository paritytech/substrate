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

use crate::config::ProtocolId;
use crate::protocol::generic_proto::handler::{NotifsHandlerProto, NotifsHandlerOut, NotifsHandlerIn};
use crate::protocol::generic_proto::upgrade::RegisteredProtocol;

use bytes::BytesMut;
use fnv::FnvHashMap;
use futures::prelude::*;
use libp2p::core::{ConnectedPoint, Multiaddr, PeerId, connection::ConnectionId};
use libp2p::swarm::{
	DialPeerCondition,
	NetworkBehaviour,
	NetworkBehaviourAction,
	NotifyHandler,
	PollParameters
};
use log::{debug, error, trace, warn};
use prometheus_endpoint::HistogramVec;
use rand::distributions::{Distribution as _, Uniform};
use smallvec::SmallVec;
use std::task::{Context, Poll};
use std::{borrow::Cow, cmp, collections::hash_map::Entry};
use std::{error, mem, pin::Pin, str, time::Duration};
use wasm_timer::Instant;

/// Network behaviour that handles opening substreams for custom protocols with other peers.
///
/// ## Legacy vs new protocol
///
/// The `GenericProto` behaves as following:
///
/// - Whenever a connection is established, we open a single substream (called "legacy protocol" in
/// the source code) on that connection. This substream name depends on the `protocol_id` and
/// `versions` passed at initialization. If the remote refuses this substream, we close the
/// connection.
///
/// - For each registered protocol, we also open an additional substream for this protocol. If the
/// remote refuses this substream, then it's fine.
///
/// - Whenever we want to send a message, we can call either `send_packet` to force the legacy
/// substream, or `write_notification` to indicate a registered protocol. If the registered
/// protocol was refused or isn't supported by the remote, we always use the legacy instead.
///
/// ## How it works
///
/// The role of the `GenericProto` is to synchronize the following components:
///
/// - The libp2p swarm that opens new connections and reports disconnects.
/// - The connection handler (see `handler.rs`) that handles individual connections.
/// - The peerset manager (PSM) that requests links to peers to be established or broken.
/// - The external API, that requires knowledge of the links that have been established.
///
/// Each connection handler can be in four different states: Enabled+Open, Enabled+Closed,
/// Disabled+Open, or Disabled+Closed. The Enabled/Disabled component must be in sync with the
/// peerset manager. For example, if the peerset manager requires a disconnection, we disable the
/// connection handlers of that peer. The Open/Closed component must be in sync with the external
/// API.
///
/// However, a connection handler for a peer only exists if we are actually connected to that peer.
/// What this means is that there are six possible states for each peer: Disconnected, Dialing
/// (trying to connect), Enabled+Open, Enabled+Closed, Disabled+Open, Disabled+Closed.
/// Most notably, the Dialing state must correspond to a "link established" state in the peerset
/// manager. In other words, the peerset manager doesn't differentiate whether we are dialing a
/// peer or connected to it.
///
/// There may be multiple connections to a peer. However, the status of a peer on
/// the API of this behaviour and towards the peerset manager is aggregated in
/// the following way:
///
///   1. The enabled/disabled status is the same across all connections, as
///      decided by the peerset manager.
///   2. `send_packet` and `write_notification` always send all data over
///      the same connection to preserve the ordering provided by the transport,
///      as long as that connection is open. If it closes, a second open
///      connection may take over, if one exists, but that case should be no
///      different than a single connection failing and being re-established
///      in terms of potential reordering and dropped messages. Messages can
///      be received on any connection.
///   3. The behaviour reports `GenericProtoOut::CustomProtocolOpen` when the
///      first connection reports `NotifsHandlerOut::Open`.
///   4. The behaviour reports `GenericProtoOut::CustomProtocolClosed` when the
///      last connection reports `NotifsHandlerOut::Closed`.
///
/// In this way, the number of actual established connections to the peer is
/// an implementation detail of this behaviour. Note that, in practice and at
/// the time of this writing, there may be at most two connections to a peer
/// and only as a result of simultaneous dialing. However, the implementation
/// accommodates for any number of connections.
///
/// Additionally, there also exists a "banning" system. If we fail to dial a peer, we "ban" it for
/// a few seconds. If the PSM requests connecting to a peer that is currently "banned", the next
/// dialing attempt is delayed until after the ban expires. However, the PSM will still consider
/// the peer to be connected. This "ban" is thus not a ban in a strict sense: If a "banned" peer
/// tries to connect, the connection is accepted. A ban only delays dialing attempts.
///
pub struct GenericProto {
	/// Legacy protocol to open with peers. Never modified.
	legacy_protocol: RegisteredProtocol,

	/// Notification protocols. Entries are only ever added and not removed.
	/// Contains, for each protocol, the protocol name and the message to send as part of the
	/// initial handshake.
	notif_protocols: Vec<(Cow<'static, [u8]>, Vec<u8>)>,

	/// Receiver for instructions about who to connect to or disconnect from.
	peerset: sc_peerset::Peerset,

	/// List of peers in our state.
	peers: FnvHashMap<PeerId, PeerState>,

	/// List of incoming messages we have sent to the peer set manager and that are waiting for an
	/// answer.
	incoming: SmallVec<[IncomingPeer; 6]>,

	/// We generate indices to identify incoming connections. This is the next value for the index
	/// to use when a connection is incoming.
	next_incoming_index: sc_peerset::IncomingIndex,

	/// Events to produce from `poll()`.
	events: SmallVec<[NetworkBehaviourAction<NotifsHandlerIn, GenericProtoOut>; 4]>,

	/// If `Some`, report the message queue sizes on this `Histogram`.
	queue_size_report: Option<HistogramVec>,
}

/// State of a peer we're connected to.
#[derive(Debug)]
enum PeerState {
	/// State is poisoned. This is a temporary state for a peer and we should always switch back
	/// to it later. If it is found in the wild, that means there was either a panic or a bug in
	/// the state machine code.
	Poisoned,

	/// The peer misbehaved. If the PSM wants us to connect to this peer, we will add an artificial
	/// delay to the connection.
	Banned {
		/// Until when the peer is banned.
		until: Instant,
	},

	/// The peerset requested that we connect to this peer. We are currently not connected.
	PendingRequest {
		/// When to actually start dialing.
		timer: futures_timer::Delay,
		/// When the `timer` will trigger.
		timer_deadline: Instant,
	},

	/// The peerset requested that we connect to this peer. We are currently dialing this peer.
	Requested,

	/// We are connected to this peer but the peerset refused it.
	///
	/// We may still have ongoing traffic with that peer, but it should cease shortly.
	Disabled {
		/// The connections that are currently open for custom protocol traffic.
		open: SmallVec<[ConnectionId; crate::MAX_CONNECTIONS_PER_PEER]>,
		/// If `Some`, any dial attempts to this peer are delayed until the given `Instant`.
		banned_until: Option<Instant>,
	},

	/// We are connected to this peer but we are not opening any Substrate substream. The handler
	/// will be enabled when `timer` fires. This peer can still perform Kademlia queries and such,
	/// but should get disconnected in a few seconds.
	DisabledPendingEnable {
		/// The connections that are currently open for custom protocol traffic.
		open: SmallVec<[ConnectionId; crate::MAX_CONNECTIONS_PER_PEER]>,
		/// When to enable this remote.
		timer: futures_timer::Delay,
		/// When the `timer` will trigger.
		timer_deadline: Instant,
	},

	/// We are connected to this peer and the peerset has accepted it. The handler is in the
	/// enabled state.
	Enabled {
		/// The connections that are currently open for custom protocol traffic.
		open: SmallVec<[ConnectionId; crate::MAX_CONNECTIONS_PER_PEER]>,
	},

	/// We received an incoming connection from this peer and forwarded that
	/// connection request to the peerset. The connection handlers are waiting
	/// for initialisation, i.e. to be enabled or disabled based on whether
	/// the peerset accepts or rejects the peer.
	Incoming,
}

impl PeerState {
	/// True if there exists any established connection to the peer.
	fn is_connected(&self) -> bool {
		match self {
			PeerState::Disabled { .. } |
			PeerState::DisabledPendingEnable { .. } |
			PeerState::Enabled { .. } |
			PeerState::PendingRequest { .. } |
			PeerState::Requested |
			PeerState::Incoming { .. } => true,
			PeerState::Poisoned |
			PeerState::Banned { .. } => false,
		}
	}

	/// True if there exists an established connection to the peer
	/// that is open for custom protocol traffic.
	fn is_open(&self) -> bool {
		self.get_open().is_some()
	}

	/// Returns the connection ID of the first established connection
	/// that is open for custom protocol traffic.
	fn get_open(&self) -> Option<ConnectionId> {
		match self {
			PeerState::Disabled { open, .. } |
			PeerState::DisabledPendingEnable { open, .. } |
			PeerState::Enabled { open, .. } =>
				if !open.is_empty() {
					Some(open[0])
				} else {
					None
				}
			PeerState::Poisoned => None,
			PeerState::Banned { .. } => None,
			PeerState::PendingRequest { .. } => None,
			PeerState::Requested => None,
			PeerState::Incoming { .. } => None,
		}
	}

	/// True if that node has been requested by the PSM.
	fn is_requested(&self) -> bool {
		match self {
			PeerState::Poisoned => false,
			PeerState::Banned { .. } => false,
			PeerState::PendingRequest { .. } => true,
			PeerState::Requested => true,
			PeerState::Disabled { .. } => false,
			PeerState::DisabledPendingEnable { .. } => true,
			PeerState::Enabled { .. } => true,
			PeerState::Incoming { .. } => false,
		}
	}
}

/// State of an "incoming" message sent to the peer set manager.
#[derive(Debug)]
struct IncomingPeer {
	/// Id of the remote peer of the incoming connection.
	peer_id: PeerId,
	/// If true, this "incoming" still corresponds to an actual connection. If false, then the
	/// connection corresponding to it has been closed or replaced already.
	alive: bool,
	/// Id that the we sent to the peerset.
	incoming_id: sc_peerset::IncomingIndex,
}

/// Event that can be emitted by the `GenericProto`.
#[derive(Debug)]
pub enum GenericProtoOut {
	/// Opened a custom protocol with the remote.
	CustomProtocolOpen {
		/// Id of the peer we are connected to.
		peer_id: PeerId,
	},

	/// Closed a custom protocol with the remote.
	CustomProtocolClosed {
		/// Id of the peer we were connected to.
		peer_id: PeerId,
		/// Reason why the substream closed, for debugging purposes.
		reason: Cow<'static, str>,
	},

	/// Receives a message on the legacy substream.
	LegacyMessage {
		/// Id of the peer the message came from.
		peer_id: PeerId,
		/// Message that has been received.
		message: BytesMut,
	},

	/// Receives a message on a custom protocol substream.
	///
	/// Also concerns received notifications for the notifications API.
	Notification {
		/// Id of the peer the message came from.
		peer_id: PeerId,
		/// Engine corresponding to the message.
		protocol_name: Cow<'static, [u8]>,
		/// Message that has been received.
		message: BytesMut,
	},

	/// The substream used by the protocol is pretty large. We should print avoid sending more
	/// messages on it if possible.
	Clogged {
		/// Id of the peer which is clogged.
		peer_id: PeerId,
		/// Copy of the messages that are within the buffer, for further diagnostic.
		messages: Vec<Vec<u8>>,
	},
}

impl GenericProto {
	/// Creates a `CustomProtos`.
	///
	/// The `queue_size_report` is an optional Prometheus metric that can report the size of the
	/// messages queue. If passed, it must have one label for the protocol name.
	pub fn new(
		protocol: impl Into<ProtocolId>,
		versions: &[u8],
		peerset: sc_peerset::Peerset,
		queue_size_report: Option<HistogramVec>,
	) -> Self {
		let legacy_protocol = RegisteredProtocol::new(protocol, versions);

		GenericProto {
			legacy_protocol,
			notif_protocols: Vec::new(),
			peerset,
			peers: FnvHashMap::default(),
			incoming: SmallVec::new(),
			next_incoming_index: sc_peerset::IncomingIndex(0),
			events: SmallVec::new(),
			queue_size_report,
		}
	}

	/// Registers a new notifications protocol.
	///
	/// You are very strongly encouraged to call this method very early on. Any open connection
	/// will retain the protocols that were registered then, and not any new one.
	pub fn register_notif_protocol(
		&mut self,
		protocol_name: impl Into<Cow<'static, [u8]>>,
		handshake_msg: impl Into<Vec<u8>>
	) {
		self.notif_protocols.push((protocol_name.into(), handshake_msg.into()));
	}

	/// Modifies the handshake of the given notifications protocol.
	///
	/// Has no effect if the protocol is unknown.
	pub fn set_notif_protocol_handshake(
		&mut self,
		protocol_name: &[u8],
		handshake_message: impl Into<Vec<u8>>
	) {
		let handshake_message = handshake_message.into();
		if let Some(protocol) = self.notif_protocols.iter_mut().find(|(name, _)| name == &protocol_name) {
			protocol.1 = handshake_message.clone();
		} else {
			return;
		}

		// Send an event to all the peers we're connected to, updating the handshake message.
		for (peer_id, _) in self.peers.iter().filter(|(_, state)| state.is_connected()) {
			self.events.push(NetworkBehaviourAction::NotifyHandler {
				peer_id: peer_id.clone(),
				handler: NotifyHandler::All,
				event: NotifsHandlerIn::UpdateHandshake {
					protocol_name: Cow::Owned(protocol_name.to_owned()),
					handshake_message: handshake_message.clone(),
				},
			});
		}
	}

	/// Returns the number of discovered nodes that we keep in memory.
	pub fn num_discovered_peers(&self) -> usize {
		self.peerset.num_discovered_peers()
	}

	/// Returns the list of all the peers we have an open channel to.
	pub fn open_peers<'a>(&'a self) -> impl Iterator<Item = &'a PeerId> + 'a {
		self.peers.iter().filter(|(_, state)| state.is_open()).map(|(id, _)| id)
	}

	/// Returns true if we have an open connection to the given peer.
	pub fn is_open(&self, peer_id: &PeerId) -> bool {
		self.peers.get(peer_id).map(|p| p.is_open()).unwrap_or(false)
	}

	/// Disconnects the given peer if we are connected to it.
	pub fn disconnect_peer(&mut self, peer_id: &PeerId) {
		debug!(target: "sub-libp2p", "External API => Disconnect {:?}", peer_id);
		self.disconnect_peer_inner(peer_id, None);
	}

	/// Inner implementation of `disconnect_peer`. If `ban` is `Some`, we ban the peer
	/// for the specific duration.
	fn disconnect_peer_inner(&mut self, peer_id: &PeerId, ban: Option<Duration>) {
		let mut entry = if let Entry::Occupied(entry) = self.peers.entry(peer_id.clone()) {
			entry
		} else {
			return
		};

		match mem::replace(entry.get_mut(), PeerState::Poisoned) {
			// We're not connected anyway.
			st @ PeerState::Disabled { .. } => *entry.into_mut() = st,
			st @ PeerState::Requested => *entry.into_mut() = st,
			st @ PeerState::PendingRequest { .. } => *entry.into_mut() = st,
			st @ PeerState::Banned { .. } => *entry.into_mut() = st,

			// DisabledPendingEnable => Disabled.
			PeerState::DisabledPendingEnable {
				open,
				timer_deadline,
				timer: _
			} => {
				debug!(target: "sub-libp2p", "PSM <= Dropped({:?})", peer_id);
				self.peerset.dropped(peer_id.clone());
				let banned_until = Some(if let Some(ban) = ban {
					cmp::max(timer_deadline, Instant::now() + ban)
				} else {
					timer_deadline
				});
				*entry.into_mut() = PeerState::Disabled {
					open,
					banned_until
				}
			},

			// Enabled => Disabled.
			PeerState::Enabled { open } => {
				debug!(target: "sub-libp2p", "PSM <= Dropped({:?})", peer_id);
				self.peerset.dropped(peer_id.clone());
				debug!(target: "sub-libp2p", "Handler({:?}) <= Disable", peer_id);
				self.events.push(NetworkBehaviourAction::NotifyHandler {
					peer_id: peer_id.clone(),
					handler: NotifyHandler::All,
					event: NotifsHandlerIn::Disable,
				});
				let banned_until = ban.map(|dur| Instant::now() + dur);
				*entry.into_mut() = PeerState::Disabled {
					open,
					banned_until
				}
			},

			// Incoming => Disabled.
			PeerState::Incoming => {
				let inc = if let Some(inc) = self.incoming.iter_mut()
					.find(|i| i.peer_id == *entry.key() && i.alive) {
					inc
				} else {
					error!(target: "sub-libp2p", "State mismatch in libp2p: no entry in \
						incoming for incoming peer");
					return
				};

				inc.alive = false;
				debug!(target: "sub-libp2p", "Handler({:?}) <= Disable", peer_id);
				self.events.push(NetworkBehaviourAction::NotifyHandler {
					peer_id: peer_id.clone(),
					handler: NotifyHandler::All,
					event: NotifsHandlerIn::Disable,
				});
				let banned_until = ban.map(|dur| Instant::now() + dur);
				*entry.into_mut() = PeerState::Disabled {
					open: SmallVec::new(),
					banned_until
				}
			},

			PeerState::Poisoned =>
				error!(target: "sub-libp2p", "State of {:?} is poisoned", peer_id),
		}
	}

	/// Returns the list of all the peers that the peerset currently requests us to be connected to.
	pub fn requested_peers<'a>(&'a self) -> impl Iterator<Item = &'a PeerId> + 'a {
		self.peers.iter().filter(|(_, state)| state.is_requested()).map(|(id, _)| id)
	}

	/// Returns true if we try to open protocols with the given peer.
	pub fn is_enabled(&self, peer_id: &PeerId) -> bool {
		match self.peers.get(peer_id) {
			None => false,
			Some(PeerState::Disabled { .. }) => false,
			Some(PeerState::DisabledPendingEnable { .. }) => false,
			Some(PeerState::Enabled { .. }) => true,
			Some(PeerState::Incoming { .. }) => false,
			Some(PeerState::Requested) => false,
			Some(PeerState::PendingRequest { .. }) => false,
			Some(PeerState::Banned { .. }) => false,
			Some(PeerState::Poisoned) => false,
		}
	}

	/// Notify the behaviour that we have learned about the existence of nodes.
	///
	/// Can be called multiple times with the same `PeerId`s.
	pub fn add_discovered_nodes(&mut self, peer_ids: impl Iterator<Item = PeerId>) {
		self.peerset.discovered(peer_ids.into_iter().map(|peer_id| {
			debug!(target: "sub-libp2p", "PSM <= Discovered({:?})", peer_id);
			peer_id
		}));
	}

	/// Sends a notification to a peer.
	///
	/// Has no effect if the custom protocol is not open with the given peer.
	///
	/// Also note that even if we have a valid open substream, it may in fact be already closed
	/// without us knowing, in which case the packet will not be received.
	///
	/// The `fallback` parameter is used for backwards-compatibility reason if the remote doesn't
	/// support our protocol. One needs to pass the equivalent of what would have been passed
	/// with `send_packet`.
	pub fn write_notification(
		&mut self,
		target: &PeerId,
		protocol_name: Cow<'static, [u8]>,
		message: impl Into<Vec<u8>>,
		encoded_fallback_message: Vec<u8>,
	) {
		let conn = match self.peers.get(target).and_then(|p| p.get_open()) {
			None => {
				debug!(target: "sub-libp2p",
					"Tried to sent notification to {:?} without an open channel.",
					target);
				return
			},
			Some(conn) => conn
		};

		trace!(
			target: "sub-libp2p",
			"External API => Notification({:?}, {:?})",
			target,
			str::from_utf8(&protocol_name)
		);
		trace!(target: "sub-libp2p", "Handler({:?}) <= Packet", target);

		self.events.push(NetworkBehaviourAction::NotifyHandler {
			peer_id: target.clone(),
			handler: NotifyHandler::One(conn),
			event: NotifsHandlerIn::SendNotification {
				message: message.into(),
				encoded_fallback_message,
				protocol_name,
			},
		});
	}

	/// Sends a message to a peer.
	///
	/// Has no effect if the custom protocol is not open with the given peer.
	///
	/// Also note that even we have a valid open substream, it may in fact be already closed
	/// without us knowing, in which case the packet will not be received.
	pub fn send_packet(&mut self, target: &PeerId, message: Vec<u8>) {
		let conn = match self.peers.get(target).and_then(|p| p.get_open()) {
			None => {
				debug!(target: "sub-libp2p",
					"Tried to sent packet to {:?} without an open channel.",
					target);
				return
			}
			Some(conn) => conn
		};

		trace!(target: "sub-libp2p", "External API => Packet for {:?}", target);
		trace!(target: "sub-libp2p", "Handler({:?}) <= Packet", target);
		self.events.push(NetworkBehaviourAction::NotifyHandler {
			peer_id: target.clone(),
			handler: NotifyHandler::One(conn),
			event: NotifsHandlerIn::SendLegacy {
				message,
			}
		});
	}

	/// Returns the state of the peerset manager, for debugging purposes.
	pub fn peerset_debug_info(&mut self) -> serde_json::Value {
		self.peerset.debug_info()
	}

	/// Function that is called when the peerset wants us to connect to a peer.
	fn peerset_report_connect(&mut self, peer_id: PeerId) {
		let mut occ_entry = match self.peers.entry(peer_id) {
			Entry::Occupied(entry) => entry,
			Entry::Vacant(entry) => {
				// If there's no entry in `self.peers`, start dialing.
				debug!(target: "sub-libp2p", "PSM => Connect({:?}): Starting to connect", entry.key());
				debug!(target: "sub-libp2p", "Libp2p <= Dial {:?}", entry.key());
				self.events.push(NetworkBehaviourAction::DialPeer {
					peer_id: entry.key().clone(),
					condition: DialPeerCondition::Disconnected
				});
				entry.insert(PeerState::Requested);
				return;
			}
		};

		let now = Instant::now();

		match mem::replace(occ_entry.get_mut(), PeerState::Poisoned) {
			PeerState::Banned { ref until } if *until > now => {
				debug!(target: "sub-libp2p", "PSM => Connect({:?}): Will start to connect at \
					until {:?}", occ_entry.key(), until);
				*occ_entry.into_mut() = PeerState::PendingRequest {
					timer: futures_timer::Delay::new(until.clone() - now),
					timer_deadline: until.clone(),
				};
			},

			PeerState::Banned { .. } => {
				debug!(target: "sub-libp2p", "PSM => Connect({:?}): Starting to connect", occ_entry.key());
				debug!(target: "sub-libp2p", "Libp2p <= Dial {:?}", occ_entry.key());
				self.events.push(NetworkBehaviourAction::DialPeer {
					peer_id: occ_entry.key().clone(),
					condition: DialPeerCondition::Disconnected
				});
				*occ_entry.into_mut() = PeerState::Requested;
			},

			PeerState::Disabled {
				open,
				banned_until: Some(ref banned)
			} if *banned > now => {
				debug!(target: "sub-libp2p", "PSM => Connect({:?}): But peer is banned until {:?}",
					occ_entry.key(), banned);
				*occ_entry.into_mut() = PeerState::DisabledPendingEnable {
					open,
					timer: futures_timer::Delay::new(banned.clone() - now),
					timer_deadline: banned.clone(),
				};
			},

			PeerState::Disabled { open, banned_until: _ } => {
				debug!(target: "sub-libp2p", "PSM => Connect({:?}): Enabling connections.",
					occ_entry.key());
				debug!(target: "sub-libp2p", "Handler({:?}) <= Enable", occ_entry.key());
				self.events.push(NetworkBehaviourAction::NotifyHandler {
					peer_id: occ_entry.key().clone(),
					handler: NotifyHandler::All,
					event: NotifsHandlerIn::Enable,
				});
				*occ_entry.into_mut() = PeerState::Enabled { open };
			},

			PeerState::Incoming => {
				debug!(target: "sub-libp2p", "PSM => Connect({:?}): Enabling connections.",
					occ_entry.key());
				if let Some(inc) = self.incoming.iter_mut()
					.find(|i| i.peer_id == *occ_entry.key() && i.alive) {
					inc.alive = false;
				} else {
					error!(target: "sub-libp2p", "State mismatch in libp2p: no entry in \
						incoming for incoming peer")
				}
				debug!(target: "sub-libp2p", "Handler({:?}) <= Enable", occ_entry.key());
				self.events.push(NetworkBehaviourAction::NotifyHandler {
					peer_id: occ_entry.key().clone(),
					handler: NotifyHandler::All,
					event: NotifsHandlerIn::Enable,
				});
				*occ_entry.into_mut() = PeerState::Enabled { open: SmallVec::new() };
			},

			st @ PeerState::Enabled { .. } => {
				warn!(target: "sub-libp2p",
					"PSM => Connect({:?}): Already connected.",
					occ_entry.key());
				*occ_entry.into_mut() = st;
			},
			st @ PeerState::DisabledPendingEnable { .. } => {
				warn!(target: "sub-libp2p",
					"PSM => Connect({:?}): Already pending enabling.",
					occ_entry.key());
				*occ_entry.into_mut() = st;
			},
			st @ PeerState::Requested { .. } | st @ PeerState::PendingRequest { .. } => {
				warn!(target: "sub-libp2p",
					"PSM => Connect({:?}): Duplicate request.",
					occ_entry.key());
				*occ_entry.into_mut() = st;
			},

			PeerState::Poisoned =>
				error!(target: "sub-libp2p", "State of {:?} is poisoned", occ_entry.key()),
		}
	}

	/// Function that is called when the peerset wants us to disconnect from a peer.
	fn peerset_report_disconnect(&mut self, peer_id: PeerId) {
		let mut entry = match self.peers.entry(peer_id) {
			Entry::Occupied(entry) => entry,
			Entry::Vacant(entry) => {
				debug!(target: "sub-libp2p", "PSM => Drop({:?}): Already disabled.", entry.key());
				return
			}
		};

		match mem::replace(entry.get_mut(), PeerState::Poisoned) {
			st @ PeerState::Disabled { .. } | st @ PeerState::Banned { .. } => {
				debug!(target: "sub-libp2p", "PSM => Drop({:?}): Already disabled.", entry.key());
				*entry.into_mut() = st;
			},

			PeerState::DisabledPendingEnable {
				open,
				timer_deadline,
				timer: _
			} => {
				debug!(target: "sub-libp2p",
					"PSM => Drop({:?}): Interrupting pending enabling.",
					entry.key());
				*entry.into_mut() = PeerState::Disabled {
					open,
					banned_until: Some(timer_deadline),
				};
			},

			PeerState::Enabled { open } => {
				debug!(target: "sub-libp2p", "PSM => Drop({:?}): Disabling connections.", entry.key());
				debug!(target: "sub-libp2p", "Handler({:?}) <= Disable", entry.key());
				self.events.push(NetworkBehaviourAction::NotifyHandler {
					peer_id: entry.key().clone(),
					handler: NotifyHandler::All,
					event: NotifsHandlerIn::Disable,
				});
				*entry.into_mut() = PeerState::Disabled {
					open,
					banned_until: None
				}
			},
			st @ PeerState::Incoming => {
				error!(target: "sub-libp2p", "PSM => Drop({:?}): Not enabled (Incoming).",
					entry.key());
				*entry.into_mut() = st;
			},
			PeerState::Requested => {
				// We don't cancel dialing. Libp2p doesn't expose that on purpose, as other
				// sub-systems (such as the discovery mechanism) may require dialing this peer as
				// well at the same time.
				debug!(target: "sub-libp2p", "PSM => Drop({:?}): Not yet connected.", entry.key());
				entry.remove();
			},
			PeerState::PendingRequest { timer_deadline, .. } => {
				debug!(target: "sub-libp2p", "PSM => Drop({:?}): Not yet connected", entry.key());
				*entry.into_mut() = PeerState::Banned { until: timer_deadline }
			},

			PeerState::Poisoned =>
				error!(target: "sub-libp2p", "State of {:?} is poisoned", entry.key()),
		}
	}

	/// Function that is called when the peerset wants us to accept a connection
	/// request from a peer.
	fn peerset_report_accept(&mut self, index: sc_peerset::IncomingIndex) {
		let incoming = if let Some(pos) = self.incoming.iter().position(|i| i.incoming_id == index) {
			self.incoming.remove(pos)
		} else {
			error!(target: "sub-libp2p", "PSM => Accept({:?}): Invalid index", index);
			return
		};

		if !incoming.alive {
			debug!(target: "sub-libp2p", "PSM => Accept({:?}, {:?}): Obsolete incoming,
				sending back dropped", index, incoming.peer_id);
			debug!(target: "sub-libp2p", "PSM <= Dropped({:?})", incoming.peer_id);
			self.peerset.dropped(incoming.peer_id.clone());
			return
		}

		match self.peers.get_mut(&incoming.peer_id) {
			Some(state @ PeerState::Incoming) => {
				debug!(target: "sub-libp2p", "PSM => Accept({:?}, {:?}): Enabling connections.",
					index, incoming.peer_id);
				debug!(target: "sub-libp2p", "Handler({:?}) <= Enable", incoming.peer_id);
				self.events.push(NetworkBehaviourAction::NotifyHandler {
					peer_id: incoming.peer_id,
					handler: NotifyHandler::All,
					event: NotifsHandlerIn::Enable,
				});
				*state = PeerState::Enabled { open: SmallVec::new() };
			}
			peer => error!(target: "sub-libp2p",
				"State mismatch in libp2p: Expected alive incoming. Got {:?}.",
				peer)
		}
	}

	/// Function that is called when the peerset wants us to reject an incoming peer.
	fn peerset_report_reject(&mut self, index: sc_peerset::IncomingIndex) {
		let incoming = if let Some(pos) = self.incoming.iter().position(|i| i.incoming_id == index) {
			self.incoming.remove(pos)
		} else {
			error!(target: "sub-libp2p", "PSM => Reject({:?}): Invalid index", index);
			return
		};

		if !incoming.alive {
			debug!(target: "sub-libp2p", "PSM => Reject({:?}, {:?}): Obsolete incoming, \
				ignoring", index, incoming.peer_id);
			return
		}

		match self.peers.get_mut(&incoming.peer_id) {
			Some(state @ PeerState::Incoming) => {
				debug!(target: "sub-libp2p", "PSM => Reject({:?}, {:?}): Rejecting connections.",
					index, incoming.peer_id);
				debug!(target: "sub-libp2p", "Handler({:?}) <= Disable", incoming.peer_id);
				self.events.push(NetworkBehaviourAction::NotifyHandler {
					peer_id: incoming.peer_id,
					handler: NotifyHandler::All,
					event: NotifsHandlerIn::Disable,
				});
				*state = PeerState::Disabled {
					open: SmallVec::new(),
					banned_until: None
				};
			}
			peer => error!(target: "sub-libp2p",
				"State mismatch in libp2p: Expected alive incoming. Got {:?}.",
				peer)
		}
	}
}

impl NetworkBehaviour for GenericProto {
	type ProtocolsHandler = NotifsHandlerProto;
	type OutEvent = GenericProtoOut;

	fn new_handler(&mut self) -> Self::ProtocolsHandler {
		NotifsHandlerProto::new(
			self.legacy_protocol.clone(),
			self.notif_protocols.clone(),
			self.queue_size_report.clone()
		)
	}

	fn addresses_of_peer(&mut self, _: &PeerId) -> Vec<Multiaddr> {
		Vec::new()
	}

	fn inject_connected(&mut self, _: &PeerId) {
	}

	fn inject_connection_established(&mut self, peer_id: &PeerId, conn: &ConnectionId, endpoint: &ConnectedPoint) {
		debug!(target: "sub-libp2p", "Libp2p => Connection ({:?},{:?}) to {} established.",
			conn, endpoint, peer_id);
		match (self.peers.entry(peer_id.clone()).or_insert(PeerState::Poisoned), endpoint) {
			(st @ &mut PeerState::Requested, endpoint) |
			(st @ &mut PeerState::PendingRequest { .. }, endpoint) => {
				debug!(target: "sub-libp2p",
					"Libp2p => Connected({}, {:?}): Connection was requested by PSM.",
					peer_id, endpoint
				);
				*st = PeerState::Enabled { open: SmallVec::new() };
				self.events.push(NetworkBehaviourAction::NotifyHandler {
					peer_id: peer_id.clone(),
					handler: NotifyHandler::One(*conn),
					event: NotifsHandlerIn::Enable
				});
			}

			// Note: it may seem weird that "Banned" peers get treated as if they were absent.
			// This is because the word "Banned" means "temporarily prevent outgoing connections to
			// this peer", and not "banned" in the sense that we would refuse the peer altogether.
			(st @ &mut PeerState::Poisoned, endpoint @ ConnectedPoint::Listener { .. }) |
			(st @ &mut PeerState::Banned { .. }, endpoint @ ConnectedPoint::Listener { .. }) => {
				let incoming_id = self.next_incoming_index.clone();
				self.next_incoming_index.0 = match self.next_incoming_index.0.checked_add(1) {
					Some(v) => v,
					None => {
						error!(target: "sub-libp2p", "Overflow in next_incoming_index");
						return
					}
				};
				debug!(target: "sub-libp2p", "Libp2p => Connected({}, {:?}): Incoming connection",
					peer_id, endpoint);
				debug!(target: "sub-libp2p", "PSM <= Incoming({}, {:?}).",
					peer_id, incoming_id);
				self.peerset.incoming(peer_id.clone(), incoming_id);
				self.incoming.push(IncomingPeer {
					peer_id: peer_id.clone(),
					alive: true,
					incoming_id,
				});
				*st = PeerState::Incoming { };
			}

			(st @ &mut PeerState::Poisoned, endpoint) |
			(st @ &mut PeerState::Banned { .. }, endpoint) => {
				let banned_until = if let PeerState::Banned { until } = st {
					Some(*until)
				} else {
					None
				};
				debug!(target: "sub-libp2p",
					"Libp2p => Connected({},{:?}): Not requested by PSM, disabling.",
					peer_id, endpoint);
				*st = PeerState::Disabled { open: SmallVec::new(), banned_until };
				self.events.push(NetworkBehaviourAction::NotifyHandler {
					peer_id: peer_id.clone(),
					handler: NotifyHandler::One(*conn),
					event: NotifsHandlerIn::Disable
				});
			}

			(PeerState::Incoming { .. }, _) => {
				debug!(target: "sub-libp2p",
					"Secondary connection {:?} to {} waiting for PSM decision.",
					conn, peer_id);
			},

			(PeerState::Enabled { .. }, _) => {
				debug!(target: "sub-libp2p", "Handler({},{:?}) <= Enable secondary connection",
					peer_id, conn);
				self.events.push(NetworkBehaviourAction::NotifyHandler {
					peer_id: peer_id.clone(),
					handler: NotifyHandler::One(*conn),
					event: NotifsHandlerIn::Enable
				});
			}

			(PeerState::Disabled { .. }, _) | (PeerState::DisabledPendingEnable { .. }, _) => {
				debug!(target: "sub-libp2p", "Handler({},{:?}) <= Disable secondary connection",
					peer_id, conn);
				self.events.push(NetworkBehaviourAction::NotifyHandler {
					peer_id: peer_id.clone(),
					handler: NotifyHandler::One(*conn),
					event: NotifsHandlerIn::Disable
				});
			}
		}
	}

	fn inject_connection_closed(&mut self, peer_id: &PeerId, conn: &ConnectionId, endpoint: &ConnectedPoint) {
		debug!(target: "sub-libp2p", "Libp2p => Connection ({:?},{:?}) to {} closed.",
			conn, endpoint, peer_id);
		match self.peers.get_mut(peer_id) {
			Some(PeerState::Disabled { open, .. }) |
			Some(PeerState::DisabledPendingEnable { open, .. }) |
			Some(PeerState::Enabled { open, .. }) => {
				// Check if the "link" to the peer is already considered closed,
				// i.e. there is no connection that is open for custom protocols,
				// in which case `CustomProtocolClosed` was already emitted.
				let closed = open.is_empty();
				open.retain(|c| c != conn);
				if open.is_empty() && !closed {
					debug!(target: "sub-libp2p", "External API <= Closed({})", peer_id);
					let event = GenericProtoOut::CustomProtocolClosed {
						peer_id: peer_id.clone(),
						reason: "Disconnected by libp2p".into(),
					};

					self.events.push(NetworkBehaviourAction::GenerateEvent(event));
				}
			}
			_ => {}
		}
	}

	fn inject_disconnected(&mut self, peer_id: &PeerId) {
		match self.peers.remove(peer_id) {
			None | Some(PeerState::Requested) | Some(PeerState::PendingRequest { .. }) |
			Some(PeerState::Banned { .. }) =>
				// This is a serious bug either in this state machine or in libp2p.
				error!(target: "sub-libp2p",
					"`inject_disconnected` called for unknown peer {}",
					peer_id),

			Some(PeerState::Disabled { banned_until, .. }) => {
				debug!(target: "sub-libp2p", "Libp2p => Disconnected({}): Was disabled.", peer_id);
				if let Some(until) = banned_until {
					self.peers.insert(peer_id.clone(), PeerState::Banned { until });
				}
			}

			Some(PeerState::DisabledPendingEnable { timer_deadline, .. }) => {
				debug!(target: "sub-libp2p",
					"Libp2p => Disconnected({}): Was disabled but pending enable.",
					peer_id);
				debug!(target: "sub-libp2p", "PSM <= Dropped({})", peer_id);
				self.peerset.dropped(peer_id.clone());
				self.peers.insert(peer_id.clone(), PeerState::Banned { until: timer_deadline });
			}

			Some(PeerState::Enabled { .. }) => {
				debug!(target: "sub-libp2p", "Libp2p => Disconnected({}): Was enabled.", peer_id);
				debug!(target: "sub-libp2p", "PSM <= Dropped({})", peer_id);
				self.peerset.dropped(peer_id.clone());
				let ban_dur = Uniform::new(5, 10).sample(&mut rand::thread_rng());
				self.peers.insert(peer_id.clone(), PeerState::Banned {
					until: Instant::now() + Duration::from_secs(ban_dur)
				});
			}

			// In the incoming state, we don't report "Dropped". Instead we will just ignore the
			// corresponding Accept/Reject.
			Some(PeerState::Incoming { }) => {
				if let Some(state) = self.incoming.iter_mut().find(|i| i.peer_id == *peer_id) {
					debug!(target: "sub-libp2p",
						"Libp2p => Disconnected({}): Was in incoming mode with id {:?}.",
						peer_id, state.incoming_id);
					state.alive = false;
				} else {
					error!(target: "sub-libp2p", "State mismatch in libp2p: no entry in incoming \
						corresponding to an incoming state in peers")
				}
			}

			Some(PeerState::Poisoned) =>
				error!(target: "sub-libp2p", "State of peer {} is poisoned", peer_id),
		}
	}

	fn inject_addr_reach_failure(&mut self, peer_id: Option<&PeerId>, addr: &Multiaddr, error: &dyn error::Error) {
		trace!(target: "sub-libp2p", "Libp2p => Reach failure for {:?} through {:?}: {:?}", peer_id, addr, error);
	}

	fn inject_dial_failure(&mut self, peer_id: &PeerId) {
		if let Entry::Occupied(mut entry) = self.peers.entry(peer_id.clone()) {
			match mem::replace(entry.get_mut(), PeerState::Poisoned) {
				// The peer is not in our list.
				st @ PeerState::Banned { .. } => {
					trace!(target: "sub-libp2p", "Libp2p => Dial failure for {:?}", peer_id);
					*entry.into_mut() = st;
				},

				// "Basic" situation: we failed to reach a peer that the peerset requested.
				PeerState::Requested | PeerState::PendingRequest { .. } => {
					debug!(target: "sub-libp2p", "Libp2p => Dial failure for {:?}", peer_id);
					*entry.into_mut() = PeerState::Banned {
						until: Instant::now() + Duration::from_secs(5)
					};
					debug!(target: "sub-libp2p", "PSM <= Dropped({:?})", peer_id);
					self.peerset.dropped(peer_id.clone())
				},

				// We can still get dial failures even if we are already connected to the peer,
				// as an extra diagnostic for an earlier attempt.
				st @ PeerState::Disabled { .. } | st @ PeerState::Enabled { .. } |
					st @ PeerState::DisabledPendingEnable { .. } | st @ PeerState::Incoming { .. } => {
					debug!(target: "sub-libp2p", "Libp2p => Dial failure for {:?}", peer_id);
					*entry.into_mut() = st;
				},

				PeerState::Poisoned =>
					error!(target: "sub-libp2p", "State of {:?} is poisoned", peer_id),
			}

		} else {
			// The peer is not in our list.
			trace!(target: "sub-libp2p", "Libp2p => Dial failure for {:?}", peer_id);
		}
	}

	fn inject_event(
		&mut self,
		source: PeerId,
		connection: ConnectionId,
		event: NotifsHandlerOut,
	) {
		match event {
			NotifsHandlerOut::Closed { endpoint, reason } => {
				debug!(target: "sub-libp2p",
					"Handler({:?}) => Endpoint {:?} closed for custom protocols: {}",
					source, endpoint, reason);

				let mut entry = if let Entry::Occupied(entry) = self.peers.entry(source.clone()) {
					entry
				} else {
					error!(target: "sub-libp2p", "Closed: State mismatch in the custom protos handler");
					return
				};

				let last = match mem::replace(entry.get_mut(), PeerState::Poisoned) {
					PeerState::Enabled { mut open } => {
						debug_assert!(open.iter().any(|c| c == &connection));
						open.retain(|c| c != &connection);

						debug!(target: "sub-libp2p", "Handler({:?}) <= Disable", source);
						self.events.push(NetworkBehaviourAction::NotifyHandler {
							peer_id: source.clone(),
							handler: NotifyHandler::One(connection),
							event: NotifsHandlerIn::Disable,
						});

						let last = open.is_empty();

						if last {
							debug!(target: "sub-libp2p", "PSM <= Dropped({:?})", source);
							self.peerset.dropped(source.clone());
							*entry.into_mut() = PeerState::Disabled {
								open,
								banned_until: None
							};
						} else {
							*entry.into_mut() = PeerState::Enabled { open };
						}

						last
					},
					PeerState::Disabled { mut open, banned_until } => {
						debug_assert!(open.iter().any(|c| c == &connection));
						open.retain(|c| c != &connection);
						let last = open.is_empty();
						*entry.into_mut() = PeerState::Disabled {
							open,
							banned_until
						};
						last
					},
					PeerState::DisabledPendingEnable {
						mut open,
						timer,
						timer_deadline
					} => {
						debug_assert!(open.iter().any(|c| c == &connection));
						open.retain(|c| c != &connection);
						let last = open.is_empty();
						*entry.into_mut() = PeerState::DisabledPendingEnable {
							open,
							timer,
							timer_deadline
						};
						last
					},
					state => {
						error!(target: "sub-libp2p",
							"Unexpected state in the custom protos handler: {:?}",
							state);
						return
					}
				};

				if last {
					debug!(target: "sub-libp2p", "External API <= Closed({:?})", source);
					let event = GenericProtoOut::CustomProtocolClosed {
						reason,
						peer_id: source.clone(),
					};
					self.events.push(NetworkBehaviourAction::GenerateEvent(event));
				} else {
					debug!(target: "sub-libp2p", "Secondary connection closed custom protocol.");
				}
			}

			NotifsHandlerOut::Open { endpoint } => {
				debug!(target: "sub-libp2p",
					"Handler({:?}) => Endpoint {:?} open for custom protocols.",
					source, endpoint);

				let first = match self.peers.get_mut(&source) {
					Some(PeerState::Enabled { ref mut open, .. }) |
					Some(PeerState::DisabledPendingEnable { ref mut open, .. }) |
					Some(PeerState::Disabled { ref mut open, .. }) => {
						let first = open.is_empty();
						open.push(connection);
						first
					}
					state => {
						error!(target: "sub-libp2p",
							   "Open: Unexpected state in the custom protos handler: {:?}",
							   state);
						return
					}
				};

				if first {
					debug!(target: "sub-libp2p", "External API <= Open({:?})", source);
					let event = GenericProtoOut::CustomProtocolOpen { peer_id: source };
					self.events.push(NetworkBehaviourAction::GenerateEvent(event));
				} else {
					debug!(target: "sub-libp2p", "Secondary connection opened custom protocol.");
				}
			}

			NotifsHandlerOut::CustomMessage { message } => {
				debug_assert!(self.is_open(&source));
				trace!(target: "sub-libp2p", "Handler({:?}) => Message", source);
				trace!(target: "sub-libp2p", "External API <= Message({:?})", source);
				let event = GenericProtoOut::LegacyMessage {
					peer_id: source,
					message,
				};

				self.events.push(NetworkBehaviourAction::GenerateEvent(event));
			}

			NotifsHandlerOut::Notification { protocol_name, message } => {
				debug_assert!(self.is_open(&source));
				trace!(
					target: "sub-libp2p",
					"Handler({:?}) => Notification({:?})",
					source,
					str::from_utf8(&protocol_name)
				);
				trace!(target: "sub-libp2p", "External API <= Message({:?}, {:?})", protocol_name, source);
				let event = GenericProtoOut::Notification {
					peer_id: source,
					protocol_name,
					message,
				};

				self.events.push(NetworkBehaviourAction::GenerateEvent(event));
			}

			NotifsHandlerOut::Clogged { messages } => {
				debug_assert!(self.is_open(&source));
				trace!(target: "sub-libp2p", "Handler({:?}) => Clogged", source);
				trace!(target: "sub-libp2p", "External API <= Clogged({:?})", source);
				warn!(target: "sub-libp2p", "Queue of packets to send to {:?} is \
					pretty large", source);
				self.events.push(NetworkBehaviourAction::GenerateEvent(GenericProtoOut::Clogged {
					peer_id: source,
					messages,
				}));
			}

			// Don't do anything for non-severe errors except report them.
			NotifsHandlerOut::ProtocolError { is_severe, ref error } if !is_severe => {
				debug!(target: "sub-libp2p", "Handler({:?}) => Benign protocol error: {:?}",
					source, error)
			}

			NotifsHandlerOut::ProtocolError { error, .. } => {
				debug!(target: "sub-libp2p",
					"Handler({:?}) => Severe protocol error: {:?}",
					source, error);
				// A severe protocol error happens when we detect a "bad" peer, such as a peer on
				// a different chain, or a peer that doesn't speak the same protocol(s). We
				// decrease the peer's reputation, hence lowering the chances we try this peer
				// again in the short term.
				self.peerset.report_peer(
					source.clone(),
					sc_peerset::ReputationChange::new(i32::min_value(), "Protocol error")
				);
				self.disconnect_peer_inner(&source, Some(Duration::from_secs(5)));
			}
		}
	}

	fn poll(
		&mut self,
		cx: &mut Context,
		_params: &mut impl PollParameters,
	) -> Poll<
		NetworkBehaviourAction<
			NotifsHandlerIn,
			Self::OutEvent,
		>,
	> {
		// Poll for instructions from the peerset.
		// Note that the peerset is a *best effort* crate, and we have to use defensive programming.
		loop {
			match futures::Stream::poll_next(Pin::new(&mut self.peerset), cx) {
				Poll::Ready(Some(sc_peerset::Message::Accept(index))) => {
					self.peerset_report_accept(index);
				}
				Poll::Ready(Some(sc_peerset::Message::Reject(index))) => {
					self.peerset_report_reject(index);
				}
				Poll::Ready(Some(sc_peerset::Message::Connect(id))) => {
					self.peerset_report_connect(id);
				}
				Poll::Ready(Some(sc_peerset::Message::Drop(id))) => {
					self.peerset_report_disconnect(id);
				}
				Poll::Ready(None) => {
					error!(target: "sub-libp2p", "Peerset receiver stream has returned None");
					break;
				}
				Poll::Pending => break,
			}
		}

		for (peer_id, peer_state) in self.peers.iter_mut() {
			match mem::replace(peer_state, PeerState::Poisoned) {
				PeerState::PendingRequest { mut timer, timer_deadline } => {
					if let Poll::Pending = Pin::new(&mut timer).poll(cx) {
						*peer_state = PeerState::PendingRequest { timer, timer_deadline };
						continue;
					}

					debug!(target: "sub-libp2p", "Libp2p <= Dial {:?} now that ban has expired", peer_id);
					self.events.push(NetworkBehaviourAction::DialPeer {
						peer_id: peer_id.clone(),
						condition: DialPeerCondition::Disconnected
					});
					*peer_state = PeerState::Requested;
				}

				PeerState::DisabledPendingEnable {
					mut timer,
					open,
					timer_deadline
				} => {
					if let Poll::Pending = Pin::new(&mut timer).poll(cx) {
						*peer_state = PeerState::DisabledPendingEnable {
							timer,
							open,
							timer_deadline
						};
						continue;
					}

					debug!(target: "sub-libp2p", "Handler({:?}) <= Enable (ban expired)", peer_id);
					self.events.push(NetworkBehaviourAction::NotifyHandler {
						peer_id: peer_id.clone(),
						handler: NotifyHandler::All,
						event: NotifsHandlerIn::Enable,
					});
					*peer_state = PeerState::Enabled { open };
				}

				st @ _ => *peer_state = st,
			}
		}

		if !self.events.is_empty() {
			return Poll::Ready(self.events.remove(0))
		}

		Poll::Pending
	}
}
