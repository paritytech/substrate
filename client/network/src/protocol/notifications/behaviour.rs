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

use crate::protocol::notifications::handler::{
	self, NotificationsSink, NotifsHandlerIn, NotifsHandlerOut, NotifsHandlerProto,
};

use bytes::BytesMut;
use fnv::FnvHashMap;
use futures::prelude::*;
use libp2p::{
	core::{connection::ConnectionId, ConnectedPoint, Multiaddr, PeerId},
	swarm::{
		DialError, DialPeerCondition, IntoProtocolsHandler, NetworkBehaviour,
		NetworkBehaviourAction, NotifyHandler, PollParameters,
	},
};
use log::{error, trace, warn};
use parking_lot::RwLock;
use rand::distributions::{Distribution as _, Uniform};
use sc_peerset::DropReason;
use smallvec::SmallVec;
use std::{
	borrow::Cow,
	cmp,
	collections::{hash_map::Entry, VecDeque},
	mem,
	pin::Pin,
	str,
	sync::Arc,
	task::{Context, Poll},
	time::{Duration, Instant},
};

/// Network behaviour that handles opening substreams for custom protocols with other peers.
///
/// # How it works
///
/// The role of the `Notifications` is to synchronize the following components:
///
/// - The libp2p swarm that opens new connections and reports disconnects.
/// - The connection handler (see `group.rs`) that handles individual connections.
/// - The peerset manager (PSM) that requests links to peers to be established or broken.
/// - The external API, that requires knowledge of the links that have been established.
///
/// In the state machine below, each `PeerId` is attributed one of these states:
///
/// - [`PeerState::Requested`]: No open connection, but requested by the peerset. Currently dialing.
/// - [`PeerState::Disabled`]: Has open TCP connection(s) unbeknownst to the peerset. No substream
///   is open.
/// - [`PeerState::Enabled`]: Has open TCP connection(s), acknowledged by the peerset.
///   - Notifications substreams are open on at least one connection, and external API has been
///     notified.
///   - Notifications substreams aren't open.
/// - [`PeerState::Incoming`]: Has open TCP connection(s) and remote would like to open substreams.
///   Peerset has been asked to attribute an inbound slot.
///
/// In addition to these states, there also exists a "banning" system. If we fail to dial a peer,
/// we back-off for a few seconds. If the PSM requests connecting to a peer that is currently
/// backed-off, the next dialing attempt is delayed until after the ban expires. However, the PSM
/// will still consider the peer to be connected. This "ban" is thus not a ban in a strict sense:
/// if a backed-off peer tries to connect, the connection is accepted. A ban only delays dialing
/// attempts.
///
/// There may be multiple connections to a peer. The status of a peer on
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
///   3. The behaviour reports `NotificationsOut::CustomProtocolOpen` when the
///      first connection reports `NotifsHandlerOut::OpenResultOk`.
///   4. The behaviour reports `NotificationsOut::CustomProtocolClosed` when the
///      last connection reports `NotifsHandlerOut::ClosedResult`.
///
/// In this way, the number of actual established connections to the peer is
/// an implementation detail of this behaviour. Note that, in practice and at
/// the time of this writing, there may be at most two connections to a peer
/// and only as a result of simultaneous dialing. However, the implementation
/// accommodates for any number of connections.
pub struct Notifications {
	/// Notification protocols. Entries never change after initialization.
	notif_protocols: Vec<handler::ProtocolConfig>,

	/// Receiver for instructions about who to connect to or disconnect from.
	peerset: sc_peerset::Peerset,

	/// List of peers in our state.
	peers: FnvHashMap<(PeerId, sc_peerset::SetId), PeerState>,

	/// The elements in `peers` occasionally contain `Delay` objects that we would normally have
	/// to be polled one by one. In order to avoid doing so, as an optimization, every `Delay` is
	/// instead put inside of `delays` and reference by a [`DelayId`]. This stream
	/// yields `PeerId`s whose `DelayId` is potentially ready.
	///
	/// By design, we never remove elements from this list. Elements are removed only when the
	/// `Delay` triggers. As such, this stream may produce obsolete elements.
	delays: stream::FuturesUnordered<
		Pin<Box<dyn Future<Output = (DelayId, PeerId, sc_peerset::SetId)> + Send>>,
	>,

	/// [`DelayId`] to assign to the next delay.
	next_delay_id: DelayId,

	/// List of incoming messages we have sent to the peer set manager and that are waiting for an
	/// answer.
	incoming: SmallVec<[IncomingPeer; 6]>,

	/// We generate indices to identify incoming connections. This is the next value for the index
	/// to use when a connection is incoming.
	next_incoming_index: sc_peerset::IncomingIndex,

	/// Events to produce from `poll()`.
	events: VecDeque<NetworkBehaviourAction<NotificationsOut, NotifsHandlerProto>>,
}

/// Configuration for a notifications protocol.
#[derive(Debug, Clone)]
pub struct ProtocolConfig {
	/// Name of the protocol.
	pub name: Cow<'static, str>,
	/// Names of the protocol to use if the main one isn't available.
	pub fallback_names: Vec<Cow<'static, str>>,
	/// Handshake of the protocol.
	pub handshake: Vec<u8>,
	/// Maximum allowed size for a notification.
	pub max_notification_size: u64,
}

/// Identifier for a delay firing.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
struct DelayId(u64);

/// State of a peer we're connected to.
///
/// The variants correspond to the state of the peer w.r.t. the peerset.
#[derive(Debug)]
enum PeerState {
	/// State is poisoned. This is a temporary state for a peer and we should always switch back
	/// to it later. If it is found in the wild, that means there was either a panic or a bug in
	/// the state machine code.
	Poisoned,

	/// The peer misbehaved. If the PSM wants us to connect to this peer, we will add an artificial
	/// delay to the connection.
	Backoff {
		/// When the ban expires. For clean-up purposes. References an entry in `delays`.
		timer: DelayId,
		/// Until when the peer is backed-off.
		timer_deadline: Instant,
	},

	/// The peerset requested that we connect to this peer. We are currently not connected.
	PendingRequest {
		/// When to actually start dialing. References an entry in `delays`.
		timer: DelayId,
		/// When the `timer` will trigger.
		timer_deadline: Instant,
	},

	/// The peerset requested that we connect to this peer. We are currently dialing this peer.
	Requested,

	/// We are connected to this peer but the peerset hasn't requested it or has denied it.
	///
	/// The handler is either in the closed state, or a `Close` message has been sent to it and
	/// hasn't been answered yet.
	Disabled {
		/// If `Some`, any connection request from the peerset to this peer is delayed until the
		/// given `Instant`.
		backoff_until: Option<Instant>,

		/// List of connections with this peer, and their state.
		connections: SmallVec<[(ConnectionId, ConnectionState); crate::MAX_CONNECTIONS_PER_PEER]>,
	},

	/// We are connected to this peer. The peerset has requested a connection to this peer, but
	/// it is currently in a "backed-off" phase. The state will switch to `Enabled` once the timer
	/// expires.
	///
	/// The handler is either in the closed state, or a `Close` message has been sent to it and
	/// hasn't been answered yet.
	///
	/// The handler will be opened when `timer` fires.
	DisabledPendingEnable {
		/// When to enable this remote. References an entry in `delays`.
		timer: DelayId,
		/// When the `timer` will trigger.
		timer_deadline: Instant,

		/// List of connections with this peer, and their state.
		connections: SmallVec<[(ConnectionId, ConnectionState); crate::MAX_CONNECTIONS_PER_PEER]>,
	},

	/// We are connected to this peer and the peerset has accepted it.
	Enabled {
		/// List of connections with this peer, and their state.
		connections: SmallVec<[(ConnectionId, ConnectionState); crate::MAX_CONNECTIONS_PER_PEER]>,
	},

	/// We are connected to this peer. We have received an `OpenDesiredByRemote` from one of the
	/// handlers and forwarded that request to the peerset. The connection handlers are waiting for
	/// a response, i.e. to be opened or closed based on whether the peerset accepts or rejects
	/// the peer.
	Incoming {
		/// If `Some`, any dial attempts to this peer are delayed until the given `Instant`.
		backoff_until: Option<Instant>,

		/// List of connections with this peer, and their state.
		connections: SmallVec<[(ConnectionId, ConnectionState); crate::MAX_CONNECTIONS_PER_PEER]>,
	},
}

impl PeerState {
	/// True if there exists an established connection to the peer
	/// that is open for custom protocol traffic.
	fn is_open(&self) -> bool {
		self.get_open().is_some()
	}

	/// Returns the [`NotificationsSink`] of the first established connection
	/// that is open for custom protocol traffic.
	fn get_open(&self) -> Option<&NotificationsSink> {
		match self {
			Self::Enabled { connections, .. } => connections.iter().find_map(|(_, s)| match s {
				ConnectionState::Open(s) => Some(s),
				_ => None,
			}),
			_ => None,
		}
	}

	/// True if that node has been requested by the PSM.
	fn is_requested(&self) -> bool {
		matches!(
			self,
			Self::PendingRequest { .. } |
				Self::Requested | Self::DisabledPendingEnable { .. } |
				Self::Enabled { .. }
		)
	}
}

/// State of the handler of a single connection visible from this state machine.
#[derive(Debug)]
enum ConnectionState {
	/// Connection is in the `Closed` state, meaning that the remote hasn't requested anything.
	Closed,

	/// Connection is either in the `Open` or the `Closed` state, but a
	/// [`NotifsHandlerIn::Close`] message has been sent. Waiting for this message to be
	/// acknowledged through a [`NotifsHandlerOut::CloseResult`].
	Closing,

	/// Connection is in the `Closed` state but a [`NotifsHandlerIn::Open`] message has been sent.
	/// An `OpenResultOk`/`OpenResultErr` message is expected.
	Opening,

	/// Connection is in the `Closed` state but a [`NotifsHandlerIn::Open`] message then a
	/// [`NotifsHandlerIn::Close`] message has been sent. An `OpenResultOk`/`OpenResultErr` message
	/// followed with a `CloseResult` message are expected.
	OpeningThenClosing,

	/// Connection is in the `Closed` state, but a [`NotifsHandlerOut::OpenDesiredByRemote`]
	/// message has been received, meaning that the remote wants to open a substream.
	OpenDesiredByRemote,

	/// Connection is in the `Open` state.
	///
	/// The external API is notified of a channel with this peer if any of its connection is in
	/// this state.
	Open(NotificationsSink),
}

/// State of an "incoming" message sent to the peer set manager.
#[derive(Debug)]
struct IncomingPeer {
	/// Id of the remote peer of the incoming substream.
	peer_id: PeerId,
	/// Id of the set the incoming substream would belong to.
	set_id: sc_peerset::SetId,
	/// If true, this "incoming" still corresponds to an actual connection. If false, then the
	/// connection corresponding to it has been closed or replaced already.
	alive: bool,
	/// Id that the we sent to the peerset.
	incoming_id: sc_peerset::IncomingIndex,
}

/// Event that can be emitted by the `Notifications`.
#[derive(Debug)]
pub enum NotificationsOut {
	/// Opened a custom protocol with the remote.
	CustomProtocolOpen {
		/// Id of the peer we are connected to.
		peer_id: PeerId,
		/// Peerset set ID the substream is tied to.
		set_id: sc_peerset::SetId,
		/// If `Some`, a fallback protocol name has been used rather the main protocol name.
		/// Always matches one of the fallback names passed at initialization.
		negotiated_fallback: Option<Cow<'static, str>>,
		/// Handshake that was sent to us.
		/// This is normally a "Status" message, but this is out of the concern of this code.
		received_handshake: Vec<u8>,
		/// Object that permits sending notifications to the peer.
		notifications_sink: NotificationsSink,
	},

	/// The [`NotificationsSink`] object used to send notifications with the given peer must be
	/// replaced with a new one.
	///
	/// This event is typically emitted when a transport-level connection is closed and we fall
	/// back to a secondary connection.
	CustomProtocolReplaced {
		/// Id of the peer we are connected to.
		peer_id: PeerId,
		/// Peerset set ID the substream is tied to.
		set_id: sc_peerset::SetId,
		/// Replacement for the previous [`NotificationsSink`].
		notifications_sink: NotificationsSink,
	},

	/// Closed a custom protocol with the remote. The existing [`NotificationsSink`] should
	/// be dropped.
	CustomProtocolClosed {
		/// Id of the peer we were connected to.
		peer_id: PeerId,
		/// Peerset set ID the substream was tied to.
		set_id: sc_peerset::SetId,
	},

	/// Receives a message on a custom protocol substream.
	///
	/// Also concerns received notifications for the notifications API.
	Notification {
		/// Id of the peer the message came from.
		peer_id: PeerId,
		/// Peerset set ID the substream is tied to.
		set_id: sc_peerset::SetId,
		/// Message that has been received.
		message: BytesMut,
	},
}

impl Notifications {
	/// Creates a `CustomProtos`.
	pub fn new(
		peerset: sc_peerset::Peerset,
		notif_protocols: impl Iterator<Item = ProtocolConfig>,
	) -> Self {
		let notif_protocols = notif_protocols
			.map(|cfg| handler::ProtocolConfig {
				name: cfg.name,
				fallback_names: cfg.fallback_names,
				handshake: Arc::new(RwLock::new(cfg.handshake)),
				max_notification_size: cfg.max_notification_size,
			})
			.collect::<Vec<_>>();

		assert!(!notif_protocols.is_empty());

		Self {
			notif_protocols,
			peerset,
			peers: FnvHashMap::default(),
			delays: Default::default(),
			next_delay_id: DelayId(0),
			incoming: SmallVec::new(),
			next_incoming_index: sc_peerset::IncomingIndex(0),
			events: VecDeque::new(),
		}
	}

	/// Modifies the handshake of the given notifications protocol.
	pub fn set_notif_protocol_handshake(
		&mut self,
		set_id: sc_peerset::SetId,
		handshake_message: impl Into<Vec<u8>>,
	) {
		if let Some(p) = self.notif_protocols.get_mut(usize::from(set_id)) {
			*p.handshake.write() = handshake_message.into();
		} else {
			log::error!(target: "sub-libp2p", "Unknown handshake change set: {:?}", set_id);
			debug_assert!(false);
		}
	}

	/// Returns the number of discovered nodes that we keep in memory.
	pub fn num_discovered_peers(&self) -> usize {
		self.peerset.num_discovered_peers()
	}

	/// Returns the list of all the peers we have an open channel to.
	pub fn open_peers<'a>(&'a self) -> impl Iterator<Item = &'a PeerId> + 'a {
		self.peers.iter().filter(|(_, state)| state.is_open()).map(|((id, _), _)| id)
	}

	/// Returns true if we have an open substream to the given peer.
	pub fn is_open(&self, peer_id: &PeerId, set_id: sc_peerset::SetId) -> bool {
		self.peers.get(&(*peer_id, set_id)).map(|p| p.is_open()).unwrap_or(false)
	}

	/// Disconnects the given peer if we are connected to it.
	pub fn disconnect_peer(&mut self, peer_id: &PeerId, set_id: sc_peerset::SetId) {
		trace!(target: "sub-libp2p", "External API => Disconnect({}, {:?})", peer_id, set_id);
		self.disconnect_peer_inner(peer_id, set_id, None);
	}

	/// Inner implementation of `disconnect_peer`. If `ban` is `Some`, we ban the peer
	/// for the specific duration.
	fn disconnect_peer_inner(
		&mut self,
		peer_id: &PeerId,
		set_id: sc_peerset::SetId,
		ban: Option<Duration>,
	) {
		let mut entry = if let Entry::Occupied(entry) = self.peers.entry((*peer_id, set_id)) {
			entry
		} else {
			return
		};

		match mem::replace(entry.get_mut(), PeerState::Poisoned) {
			// We're not connected anyway.
			st @ PeerState::Disabled { .. } => *entry.into_mut() = st,
			st @ PeerState::Requested => *entry.into_mut() = st,
			st @ PeerState::PendingRequest { .. } => *entry.into_mut() = st,
			st @ PeerState::Backoff { .. } => *entry.into_mut() = st,

			// DisabledPendingEnable => Disabled.
			PeerState::DisabledPendingEnable { connections, timer_deadline, timer: _ } => {
				trace!(target: "sub-libp2p", "PSM <= Dropped({}, {:?})", peer_id, set_id);
				self.peerset.dropped(set_id, *peer_id, DropReason::Unknown);
				let backoff_until = Some(if let Some(ban) = ban {
					cmp::max(timer_deadline, Instant::now() + ban)
				} else {
					timer_deadline
				});
				*entry.into_mut() = PeerState::Disabled { connections, backoff_until }
			},

			// Enabled => Disabled.
			// All open or opening connections are sent a `Close` message.
			// If relevant, the external API is instantly notified.
			PeerState::Enabled { mut connections } => {
				trace!(target: "sub-libp2p", "PSM <= Dropped({}, {:?})", peer_id, set_id);
				self.peerset.dropped(set_id, *peer_id, DropReason::Unknown);

				if connections.iter().any(|(_, s)| matches!(s, ConnectionState::Open(_))) {
					trace!(target: "sub-libp2p", "External API <= Closed({}, {:?})", peer_id, set_id);
					let event =
						NotificationsOut::CustomProtocolClosed { peer_id: *peer_id, set_id };
					self.events.push_back(NetworkBehaviourAction::GenerateEvent(event));
				}

				for (connec_id, connec_state) in
					connections.iter_mut().filter(|(_, s)| matches!(s, ConnectionState::Open(_)))
				{
					trace!(target: "sub-libp2p", "Handler({:?}, {:?}) <= Close({:?})", peer_id, *connec_id, set_id);
					self.events.push_back(NetworkBehaviourAction::NotifyHandler {
						peer_id: *peer_id,
						handler: NotifyHandler::One(*connec_id),
						event: NotifsHandlerIn::Close { protocol_index: set_id.into() },
					});
					*connec_state = ConnectionState::Closing;
				}

				for (connec_id, connec_state) in
					connections.iter_mut().filter(|(_, s)| matches!(s, ConnectionState::Opening))
				{
					trace!(target: "sub-libp2p", "Handler({:?}, {:?}) <= Close({:?})", peer_id, *connec_id, set_id);
					self.events.push_back(NetworkBehaviourAction::NotifyHandler {
						peer_id: *peer_id,
						handler: NotifyHandler::One(*connec_id),
						event: NotifsHandlerIn::Close { protocol_index: set_id.into() },
					});
					*connec_state = ConnectionState::OpeningThenClosing;
				}

				debug_assert!(!connections
					.iter()
					.any(|(_, s)| matches!(s, ConnectionState::Open(_))));
				debug_assert!(!connections
					.iter()
					.any(|(_, s)| matches!(s, ConnectionState::Opening)));

				let backoff_until = ban.map(|dur| Instant::now() + dur);
				*entry.into_mut() = PeerState::Disabled { connections, backoff_until }
			},

			// Incoming => Disabled.
			// Ongoing opening requests from the remote are rejected.
			PeerState::Incoming { mut connections, backoff_until } => {
				let inc = if let Some(inc) = self
					.incoming
					.iter_mut()
					.find(|i| i.peer_id == entry.key().0 && i.set_id == set_id && i.alive)
				{
					inc
				} else {
					error!(
						target: "sub-libp2p",
						"State mismatch in libp2p: no entry in incoming for incoming peer"
					);
					return
				};

				inc.alive = false;

				for (connec_id, connec_state) in connections
					.iter_mut()
					.filter(|(_, s)| matches!(s, ConnectionState::OpenDesiredByRemote))
				{
					trace!(target: "sub-libp2p", "Handler({:?}, {:?}) <= Close({:?})", peer_id, *connec_id, set_id);
					self.events.push_back(NetworkBehaviourAction::NotifyHandler {
						peer_id: *peer_id,
						handler: NotifyHandler::One(*connec_id),
						event: NotifsHandlerIn::Close { protocol_index: set_id.into() },
					});
					*connec_state = ConnectionState::Closing;
				}

				let backoff_until = match (backoff_until, ban) {
					(Some(a), Some(b)) => Some(cmp::max(a, Instant::now() + b)),
					(Some(a), None) => Some(a),
					(None, Some(b)) => Some(Instant::now() + b),
					(None, None) => None,
				};

				debug_assert!(!connections
					.iter()
					.any(|(_, s)| matches!(s, ConnectionState::OpenDesiredByRemote)));
				*entry.into_mut() = PeerState::Disabled { connections, backoff_until }
			},

			PeerState::Poisoned => {
				error!(target: "sub-libp2p", "State of {:?} is poisoned", peer_id)
			},
		}
	}

	/// Returns the list of all the peers that the peerset currently requests us to be connected to.
	pub fn requested_peers<'a>(
		&'a self,
		set_id: sc_peerset::SetId,
	) -> impl Iterator<Item = &'a PeerId> + 'a {
		self.peers
			.iter()
			.filter(move |((_, set), state)| *set == set_id && state.is_requested())
			.map(|((id, _), _)| id)
	}

	/// Returns the list of reserved peers.
	pub fn reserved_peers<'a>(
		&'a self,
		set_id: sc_peerset::SetId,
	) -> impl Iterator<Item = &'a PeerId> + 'a {
		self.peerset.reserved_peers(set_id)
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
		set_id: sc_peerset::SetId,
		message: impl Into<Vec<u8>>,
	) {
		let notifs_sink = match self.peers.get(&(*target, set_id)).and_then(|p| p.get_open()) {
			None => {
				trace!(
					target: "sub-libp2p",
					"Tried to sent notification to {:?} without an open channel.",
					target,
				);
				return
			},
			Some(sink) => sink,
		};

		let message = message.into();

		trace!(
			target: "sub-libp2p",
			"External API => Notification({:?}, {:?}, {} bytes)",
			target,
			set_id,
			message.len(),
		);
		trace!(target: "sub-libp2p", "Handler({:?}) <= Sync notification", target);

		notifs_sink.send_sync_notification(message);
	}

	/// Returns the state of the peerset manager, for debugging purposes.
	pub fn peerset_debug_info(&mut self) -> serde_json::Value {
		self.peerset.debug_info()
	}

	/// Function that is called when the peerset wants us to connect to a peer.
	fn peerset_report_connect(&mut self, peer_id: PeerId, set_id: sc_peerset::SetId) {
		// If `PeerId` is unknown to us, insert an entry, start dialing, and return early.
		let handler = self.new_handler();
		let mut occ_entry = match self.peers.entry((peer_id, set_id)) {
			Entry::Occupied(entry) => entry,
			Entry::Vacant(entry) => {
				// If there's no entry in `self.peers`, start dialing.
				trace!(
					target: "sub-libp2p",
					"PSM => Connect({}, {:?}): Starting to connect",
					entry.key().0,
					set_id,
				);
				trace!(target: "sub-libp2p", "Libp2p <= Dial {}", entry.key().0);
				// The `DialPeerCondition` ensures that dial attempts are de-duplicated
				self.events.push_back(NetworkBehaviourAction::DialPeer {
					peer_id: entry.key().0.clone(),
					condition: DialPeerCondition::Disconnected,
					handler,
				});
				entry.insert(PeerState::Requested);
				return
			},
		};

		let now = Instant::now();

		match mem::replace(occ_entry.get_mut(), PeerState::Poisoned) {
			// Backoff (not expired) => PendingRequest
			PeerState::Backoff { ref timer, ref timer_deadline } if *timer_deadline > now => {
				let peer_id = occ_entry.key().0.clone();
				trace!(
					target: "sub-libp2p",
					"PSM => Connect({}, {:?}): Will start to connect at until {:?}",
					peer_id,
					set_id,
					timer_deadline,
				);
				*occ_entry.into_mut() =
					PeerState::PendingRequest { timer: *timer, timer_deadline: *timer_deadline };
			},

			// Backoff (expired) => Requested
			PeerState::Backoff { .. } => {
				trace!(
					target: "sub-libp2p",
					"PSM => Connect({}, {:?}): Starting to connect",
					occ_entry.key().0,
					set_id,
				);
				trace!(target: "sub-libp2p", "Libp2p <= Dial {:?}", occ_entry.key());
				// The `DialPeerCondition` ensures that dial attempts are de-duplicated
				self.events.push_back(NetworkBehaviourAction::DialPeer {
					peer_id: occ_entry.key().0.clone(),
					condition: DialPeerCondition::Disconnected,
					handler,
				});
				*occ_entry.into_mut() = PeerState::Requested;
			},

			// Disabled (with non-expired ban) => DisabledPendingEnable
			PeerState::Disabled { connections, backoff_until: Some(ref backoff) }
				if *backoff > now =>
			{
				let peer_id = occ_entry.key().0.clone();
				trace!(
					target: "sub-libp2p",
					"PSM => Connect({}, {:?}): But peer is backed-off until {:?}",
					peer_id,
					set_id,
					backoff,
				);

				let delay_id = self.next_delay_id;
				self.next_delay_id.0 += 1;
				let delay = futures_timer::Delay::new(*backoff - now);
				self.delays.push(
					async move {
						delay.await;
						(delay_id, peer_id, set_id)
					}
					.boxed(),
				);

				*occ_entry.into_mut() = PeerState::DisabledPendingEnable {
					connections,
					timer: delay_id,
					timer_deadline: *backoff,
				};
			},

			// Disabled => Enabled
			PeerState::Disabled { mut connections, backoff_until } => {
				debug_assert!(!connections
					.iter()
					.any(|(_, s)| { matches!(s, ConnectionState::Open(_)) }));

				// The first element of `closed` is chosen to open the notifications substream.
				if let Some((connec_id, connec_state)) =
					connections.iter_mut().find(|(_, s)| matches!(s, ConnectionState::Closed))
				{
					trace!(target: "sub-libp2p", "PSM => Connect({}, {:?}): Enabling connections.",
						occ_entry.key().0, set_id);
					trace!(target: "sub-libp2p", "Handler({:?}, {:?}) <= Open({:?})", peer_id, *connec_id, set_id);
					self.events.push_back(NetworkBehaviourAction::NotifyHandler {
						peer_id,
						handler: NotifyHandler::One(*connec_id),
						event: NotifsHandlerIn::Open { protocol_index: set_id.into() },
					});
					*connec_state = ConnectionState::Opening;
					*occ_entry.into_mut() = PeerState::Enabled { connections };
				} else {
					// If no connection is available, switch to `DisabledPendingEnable` in order
					// to try again later.
					debug_assert!(connections.iter().any(|(_, s)| {
						matches!(s, ConnectionState::OpeningThenClosing | ConnectionState::Closing)
					}));
					trace!(
						target: "sub-libp2p",
						"PSM => Connect({}, {:?}): No connection in proper state. Delaying.",
						occ_entry.key().0, set_id
					);

					let timer_deadline = {
						let base = now + Duration::from_secs(5);
						if let Some(backoff_until) = backoff_until {
							cmp::max(base, backoff_until)
						} else {
							base
						}
					};

					let delay_id = self.next_delay_id;
					self.next_delay_id.0 += 1;
					debug_assert!(timer_deadline > now);
					let delay = futures_timer::Delay::new(timer_deadline - now);
					self.delays.push(
						async move {
							delay.await;
							(delay_id, peer_id, set_id)
						}
						.boxed(),
					);

					*occ_entry.into_mut() = PeerState::DisabledPendingEnable {
						connections,
						timer: delay_id,
						timer_deadline,
					};
				}
			},

			// Incoming => Enabled
			PeerState::Incoming { mut connections, .. } => {
				trace!(target: "sub-libp2p", "PSM => Connect({}, {:?}): Enabling connections.",
					occ_entry.key().0, set_id);
				if let Some(inc) = self
					.incoming
					.iter_mut()
					.find(|i| i.peer_id == occ_entry.key().0 && i.set_id == set_id && i.alive)
				{
					inc.alive = false;
				} else {
					error!(
						target: "sub-libp2p",
						"State mismatch in libp2p: no entry in incoming for incoming peer",
					)
				}

				debug_assert!(connections
					.iter()
					.any(|(_, s)| matches!(s, ConnectionState::OpenDesiredByRemote)));
				for (connec_id, connec_state) in connections
					.iter_mut()
					.filter(|(_, s)| matches!(s, ConnectionState::OpenDesiredByRemote))
				{
					trace!(target: "sub-libp2p", "Handler({:?}, {:?}) <= Open({:?})",
						occ_entry.key(), *connec_id, set_id);
					self.events.push_back(NetworkBehaviourAction::NotifyHandler {
						peer_id: occ_entry.key().0.clone(),
						handler: NotifyHandler::One(*connec_id),
						event: NotifsHandlerIn::Open { protocol_index: set_id.into() },
					});
					*connec_state = ConnectionState::Opening;
				}

				*occ_entry.into_mut() = PeerState::Enabled { connections };
			},

			// Other states are kept as-is.
			st @ PeerState::Enabled { .. } => {
				warn!(target: "sub-libp2p",
					"PSM => Connect({}, {:?}): Already connected.",
					occ_entry.key().0, set_id);
				*occ_entry.into_mut() = st;
				debug_assert!(false);
			},
			st @ PeerState::DisabledPendingEnable { .. } => {
				warn!(target: "sub-libp2p",
					"PSM => Connect({}, {:?}): Already pending enabling.",
					occ_entry.key().0, set_id);
				*occ_entry.into_mut() = st;
				debug_assert!(false);
			},
			st @ PeerState::Requested { .. } | st @ PeerState::PendingRequest { .. } => {
				warn!(target: "sub-libp2p",
					"PSM => Connect({}, {:?}): Duplicate request.",
					occ_entry.key().0, set_id);
				*occ_entry.into_mut() = st;
				debug_assert!(false);
			},

			PeerState::Poisoned => {
				error!(target: "sub-libp2p", "State of {:?} is poisoned", occ_entry.key());
				debug_assert!(false);
			},
		}
	}

	/// Function that is called when the peerset wants us to disconnect from a peer.
	fn peerset_report_disconnect(&mut self, peer_id: PeerId, set_id: sc_peerset::SetId) {
		let mut entry = match self.peers.entry((peer_id, set_id)) {
			Entry::Occupied(entry) => entry,
			Entry::Vacant(entry) => {
				trace!(target: "sub-libp2p", "PSM => Drop({}, {:?}): Already disabled.",
					entry.key().0, set_id);
				return
			},
		};

		match mem::replace(entry.get_mut(), PeerState::Poisoned) {
			st @ PeerState::Disabled { .. } | st @ PeerState::Backoff { .. } => {
				trace!(target: "sub-libp2p", "PSM => Drop({}, {:?}): Already disabled.",
					entry.key().0, set_id);
				*entry.into_mut() = st;
			},

			// DisabledPendingEnable => Disabled
			PeerState::DisabledPendingEnable { connections, timer_deadline, timer: _ } => {
				debug_assert!(!connections.is_empty());
				trace!(target: "sub-libp2p",
					"PSM => Drop({}, {:?}): Interrupting pending enabling.",
					entry.key().0, set_id);
				*entry.into_mut() =
					PeerState::Disabled { connections, backoff_until: Some(timer_deadline) };
			},

			// Enabled => Disabled
			PeerState::Enabled { mut connections } => {
				trace!(target: "sub-libp2p", "PSM => Drop({}, {:?}): Disabling connections.",
					entry.key().0, set_id);

				debug_assert!(connections.iter().any(|(_, s)| matches!(
					s,
					ConnectionState::Opening | ConnectionState::Open(_)
				)));

				if connections.iter().any(|(_, s)| matches!(s, ConnectionState::Open(_))) {
					trace!(target: "sub-libp2p", "External API <= Closed({}, {:?})", entry.key().0, set_id);
					let event = NotificationsOut::CustomProtocolClosed {
						peer_id: entry.key().0.clone(),
						set_id,
					};
					self.events.push_back(NetworkBehaviourAction::GenerateEvent(event));
				}

				for (connec_id, connec_state) in
					connections.iter_mut().filter(|(_, s)| matches!(s, ConnectionState::Opening))
				{
					trace!(target: "sub-libp2p", "Handler({:?}, {:?}) <= Close({:?})",
						entry.key(), *connec_id, set_id);
					self.events.push_back(NetworkBehaviourAction::NotifyHandler {
						peer_id: entry.key().0.clone(),
						handler: NotifyHandler::One(*connec_id),
						event: NotifsHandlerIn::Close { protocol_index: set_id.into() },
					});
					*connec_state = ConnectionState::OpeningThenClosing;
				}

				for (connec_id, connec_state) in
					connections.iter_mut().filter(|(_, s)| matches!(s, ConnectionState::Open(_)))
				{
					trace!(target: "sub-libp2p", "Handler({:?}, {:?}) <= Close({:?})",
						entry.key(), *connec_id, set_id);
					self.events.push_back(NetworkBehaviourAction::NotifyHandler {
						peer_id: entry.key().0.clone(),
						handler: NotifyHandler::One(*connec_id),
						event: NotifsHandlerIn::Close { protocol_index: set_id.into() },
					});
					*connec_state = ConnectionState::Closing;
				}

				*entry.into_mut() = PeerState::Disabled { connections, backoff_until: None }
			},

			// Requested => Ø
			PeerState::Requested => {
				// We don't cancel dialing. Libp2p doesn't expose that on purpose, as other
				// sub-systems (such as the discovery mechanism) may require dialing this peer as
				// well at the same time.
				trace!(target: "sub-libp2p", "PSM => Drop({}, {:?}): Not yet connected.",
					entry.key().0, set_id);
				entry.remove();
			},

			// PendingRequest => Backoff
			PeerState::PendingRequest { timer, timer_deadline } => {
				trace!(target: "sub-libp2p", "PSM => Drop({}, {:?}): Not yet connected",
					entry.key().0, set_id);
				*entry.into_mut() = PeerState::Backoff { timer, timer_deadline }
			},

			// Invalid state transitions.
			st @ PeerState::Incoming { .. } => {
				error!(target: "sub-libp2p", "PSM => Drop({}, {:?}): Not enabled (Incoming).",
					entry.key().0, set_id);
				*entry.into_mut() = st;
				debug_assert!(false);
			},
			PeerState::Poisoned => {
				error!(target: "sub-libp2p", "State of {:?} is poisoned", entry.key());
				debug_assert!(false);
			},
		}
	}

	/// Function that is called when the peerset wants us to accept a connection
	/// request from a peer.
	fn peerset_report_accept(&mut self, index: sc_peerset::IncomingIndex) {
		let incoming = if let Some(pos) = self.incoming.iter().position(|i| i.incoming_id == index)
		{
			self.incoming.remove(pos)
		} else {
			error!(target: "sub-libp2p", "PSM => Accept({:?}): Invalid index", index);
			return
		};

		if !incoming.alive {
			trace!(target: "sub-libp2p", "PSM => Accept({:?}, {}, {:?}): Obsolete incoming",
				index, incoming.peer_id, incoming.set_id);
			match self.peers.get_mut(&(incoming.peer_id, incoming.set_id)) {
				Some(PeerState::DisabledPendingEnable { .. }) | Some(PeerState::Enabled { .. }) => {
				},
				_ => {
					trace!(target: "sub-libp2p", "PSM <= Dropped({}, {:?})",
						incoming.peer_id, incoming.set_id);
					self.peerset.dropped(incoming.set_id, incoming.peer_id, DropReason::Unknown);
				},
			}
			return
		}

		let state = match self.peers.get_mut(&(incoming.peer_id, incoming.set_id)) {
			Some(s) => s,
			None => {
				debug_assert!(false);
				return
			},
		};

		match mem::replace(state, PeerState::Poisoned) {
			// Incoming => Enabled
			PeerState::Incoming { mut connections, .. } => {
				trace!(target: "sub-libp2p", "PSM => Accept({:?}, {}, {:?}): Enabling connections.",
					index, incoming.peer_id, incoming.set_id);

				debug_assert!(connections
					.iter()
					.any(|(_, s)| matches!(s, ConnectionState::OpenDesiredByRemote)));
				for (connec_id, connec_state) in connections
					.iter_mut()
					.filter(|(_, s)| matches!(s, ConnectionState::OpenDesiredByRemote))
				{
					trace!(target: "sub-libp2p", "Handler({:?}, {:?}) <= Open({:?})",
						incoming.peer_id, *connec_id, incoming.set_id);
					self.events.push_back(NetworkBehaviourAction::NotifyHandler {
						peer_id: incoming.peer_id,
						handler: NotifyHandler::One(*connec_id),
						event: NotifsHandlerIn::Open { protocol_index: incoming.set_id.into() },
					});
					*connec_state = ConnectionState::Opening;
				}

				*state = PeerState::Enabled { connections };
			},

			// Any state other than `Incoming` is invalid.
			peer => {
				error!(target: "sub-libp2p",
					"State mismatch in libp2p: Expected alive incoming. Got {:?}.",
					peer);
				debug_assert!(false);
			},
		}
	}

	/// Function that is called when the peerset wants us to reject an incoming peer.
	fn peerset_report_reject(&mut self, index: sc_peerset::IncomingIndex) {
		let incoming = if let Some(pos) = self.incoming.iter().position(|i| i.incoming_id == index)
		{
			self.incoming.remove(pos)
		} else {
			error!(target: "sub-libp2p", "PSM => Reject({:?}): Invalid index", index);
			return
		};

		if !incoming.alive {
			trace!(target: "sub-libp2p", "PSM => Reject({:?}, {}, {:?}): Obsolete incoming, \
				ignoring", index, incoming.peer_id, incoming.set_id);
			return
		}

		let state = match self.peers.get_mut(&(incoming.peer_id, incoming.set_id)) {
			Some(s) => s,
			None => {
				debug_assert!(false);
				return
			},
		};

		match mem::replace(state, PeerState::Poisoned) {
			// Incoming => Disabled
			PeerState::Incoming { mut connections, backoff_until } => {
				trace!(target: "sub-libp2p", "PSM => Reject({:?}, {}, {:?}): Rejecting connections.",
					index, incoming.peer_id, incoming.set_id);

				debug_assert!(connections
					.iter()
					.any(|(_, s)| matches!(s, ConnectionState::OpenDesiredByRemote)));
				for (connec_id, connec_state) in connections
					.iter_mut()
					.filter(|(_, s)| matches!(s, ConnectionState::OpenDesiredByRemote))
				{
					trace!(target: "sub-libp2p", "Handler({:?}, {:?}) <= Close({:?})",
						incoming.peer_id, connec_id, incoming.set_id);
					self.events.push_back(NetworkBehaviourAction::NotifyHandler {
						peer_id: incoming.peer_id,
						handler: NotifyHandler::One(*connec_id),
						event: NotifsHandlerIn::Close { protocol_index: incoming.set_id.into() },
					});
					*connec_state = ConnectionState::Closing;
				}

				*state = PeerState::Disabled { connections, backoff_until };
			},
			peer => error!(target: "sub-libp2p",
				"State mismatch in libp2p: Expected alive incoming. Got {:?}.",
				peer),
		}
	}
}

impl NetworkBehaviour for Notifications {
	type ProtocolsHandler = NotifsHandlerProto;
	type OutEvent = NotificationsOut;

	fn new_handler(&mut self) -> Self::ProtocolsHandler {
		NotifsHandlerProto::new(self.notif_protocols.clone())
	}

	fn addresses_of_peer(&mut self, _: &PeerId) -> Vec<Multiaddr> {
		Vec::new()
	}

	fn inject_connected(&mut self, _: &PeerId) {}

	fn inject_connection_established(
		&mut self,
		peer_id: &PeerId,
		conn: &ConnectionId,
		endpoint: &ConnectedPoint,
		_failed_addresses: Option<&Vec<Multiaddr>>,
	) {
		for set_id in (0..self.notif_protocols.len()).map(sc_peerset::SetId::from) {
			match self.peers.entry((*peer_id, set_id)).or_insert(PeerState::Poisoned) {
				// Requested | PendingRequest => Enabled
				st @ &mut PeerState::Requested | st @ &mut PeerState::PendingRequest { .. } => {
					trace!(target: "sub-libp2p",
						"Libp2p => Connected({}, {:?}, {:?}): Connection was requested by PSM.",
						peer_id, set_id, endpoint
					);
					trace!(target: "sub-libp2p", "Handler({:?}, {:?}) <= Open({:?})", peer_id, *conn, set_id);
					self.events.push_back(NetworkBehaviourAction::NotifyHandler {
						peer_id: *peer_id,
						handler: NotifyHandler::One(*conn),
						event: NotifsHandlerIn::Open { protocol_index: set_id.into() },
					});

					let mut connections = SmallVec::new();
					connections.push((*conn, ConnectionState::Opening));
					*st = PeerState::Enabled { connections };
				},

				// Poisoned gets inserted above if the entry was missing.
				// Ø | Backoff => Disabled
				st @ &mut PeerState::Poisoned | st @ &mut PeerState::Backoff { .. } => {
					let backoff_until = if let PeerState::Backoff { timer_deadline, .. } = st {
						Some(*timer_deadline)
					} else {
						None
					};
					trace!(target: "sub-libp2p",
						"Libp2p => Connected({}, {:?}, {:?}, {:?}): Not requested by PSM, disabling.",
						peer_id, set_id, endpoint, *conn);

					let mut connections = SmallVec::new();
					connections.push((*conn, ConnectionState::Closed));
					*st = PeerState::Disabled { connections, backoff_until };
				},

				// In all other states, add this new connection to the list of closed inactive
				// connections.
				PeerState::Incoming { connections, .. } |
				PeerState::Disabled { connections, .. } |
				PeerState::DisabledPendingEnable { connections, .. } |
				PeerState::Enabled { connections, .. } => {
					trace!(target: "sub-libp2p",
						"Libp2p => Connected({}, {:?}, {:?}, {:?}): Secondary connection. Leaving closed.",
						peer_id, set_id, endpoint, *conn);
					connections.push((*conn, ConnectionState::Closed));
				},
			}
		}
	}

	fn inject_connection_closed(
		&mut self,
		peer_id: &PeerId,
		conn: &ConnectionId,
		_endpoint: &ConnectedPoint,
		_handler: <Self::ProtocolsHandler as IntoProtocolsHandler>::Handler,
	) {
		for set_id in (0..self.notif_protocols.len()).map(sc_peerset::SetId::from) {
			let mut entry = if let Entry::Occupied(entry) = self.peers.entry((*peer_id, set_id)) {
				entry
			} else {
				error!(target: "sub-libp2p", "inject_connection_closed: State mismatch in the custom protos handler");
				debug_assert!(false);
				return
			};

			match mem::replace(entry.get_mut(), PeerState::Poisoned) {
				// Disabled => Disabled | Backoff | Ø
				PeerState::Disabled { mut connections, backoff_until } => {
					trace!(target: "sub-libp2p", "Libp2p => Disconnected({}, {:?}, {:?}): Disabled.",
						peer_id, set_id, *conn);

					if let Some(pos) = connections.iter().position(|(c, _)| *c == *conn) {
						connections.remove(pos);
					} else {
						debug_assert!(false);
						error!(target: "sub-libp2p",
							"inject_connection_closed: State mismatch in the custom protos handler");
					}

					if connections.is_empty() {
						if let Some(until) = backoff_until {
							let now = Instant::now();
							if until > now {
								let delay_id = self.next_delay_id;
								self.next_delay_id.0 += 1;
								let delay = futures_timer::Delay::new(until - now);
								let peer_id = *peer_id;
								self.delays.push(
									async move {
										delay.await;
										(delay_id, peer_id, set_id)
									}
									.boxed(),
								);

								*entry.get_mut() =
									PeerState::Backoff { timer: delay_id, timer_deadline: until };
							} else {
								entry.remove();
							}
						} else {
							entry.remove();
						}
					} else {
						*entry.get_mut() = PeerState::Disabled { connections, backoff_until };
					}
				},

				// DisabledPendingEnable => DisabledPendingEnable | Backoff
				PeerState::DisabledPendingEnable { mut connections, timer_deadline, timer } => {
					trace!(
						target: "sub-libp2p",
						"Libp2p => Disconnected({}, {:?}, {:?}): Disabled but pending enable.",
						peer_id, set_id, *conn
					);

					if let Some(pos) = connections.iter().position(|(c, _)| *c == *conn) {
						connections.remove(pos);
					} else {
						error!(target: "sub-libp2p",
							"inject_connection_closed: State mismatch in the custom protos handler");
						debug_assert!(false);
					}

					if connections.is_empty() {
						trace!(target: "sub-libp2p", "PSM <= Dropped({}, {:?})", peer_id, set_id);
						self.peerset.dropped(set_id, *peer_id, DropReason::Unknown);
						*entry.get_mut() = PeerState::Backoff { timer, timer_deadline };
					} else {
						*entry.get_mut() =
							PeerState::DisabledPendingEnable { connections, timer_deadline, timer };
					}
				},

				// Incoming => Incoming | Disabled | Backoff | Ø
				PeerState::Incoming { mut connections, backoff_until } => {
					trace!(
						target: "sub-libp2p",
						"Libp2p => Disconnected({}, {:?}, {:?}): OpenDesiredByRemote.",
						peer_id, set_id, *conn
					);

					debug_assert!(connections
						.iter()
						.any(|(_, s)| matches!(s, ConnectionState::OpenDesiredByRemote)));

					if let Some(pos) = connections.iter().position(|(c, _)| *c == *conn) {
						connections.remove(pos);
					} else {
						error!(target: "sub-libp2p",
							"inject_connection_closed: State mismatch in the custom protos handler");
						debug_assert!(false);
					}

					let no_desired_left = !connections
						.iter()
						.any(|(_, s)| matches!(s, ConnectionState::OpenDesiredByRemote));

					// If no connection is `OpenDesiredByRemote` anymore, clean up the peerset
					// incoming request.
					if no_desired_left {
						// In the incoming state, we don't report "Dropped". Instead we will just
						// ignore the corresponding Accept/Reject.
						if let Some(state) = self
							.incoming
							.iter_mut()
							.find(|i| i.alive && i.set_id == set_id && i.peer_id == *peer_id)
						{
							state.alive = false;
						} else {
							error!(target: "sub-libp2p", "State mismatch in libp2p: no entry in \
								incoming corresponding to an incoming state in peers");
							debug_assert!(false);
						}
					}

					if connections.is_empty() {
						if let Some(until) = backoff_until {
							let now = Instant::now();
							if until > now {
								let delay_id = self.next_delay_id;
								self.next_delay_id.0 += 1;
								let delay = futures_timer::Delay::new(until - now);
								let peer_id = *peer_id;
								self.delays.push(
									async move {
										delay.await;
										(delay_id, peer_id, set_id)
									}
									.boxed(),
								);

								*entry.get_mut() =
									PeerState::Backoff { timer: delay_id, timer_deadline: until };
							} else {
								entry.remove();
							}
						} else {
							entry.remove();
						}
					} else if no_desired_left {
						// If no connection is `OpenDesiredByRemote` anymore, switch to `Disabled`.
						*entry.get_mut() = PeerState::Disabled { connections, backoff_until };
					} else {
						*entry.get_mut() = PeerState::Incoming { connections, backoff_until };
					}
				},

				// Enabled => Enabled | Backoff
				// Peers are always backed-off when disconnecting while Enabled.
				PeerState::Enabled { mut connections } => {
					trace!(
						target: "sub-libp2p",
						"Libp2p => Disconnected({}, {:?}, {:?}): Enabled.",
						peer_id, set_id, *conn
					);

					debug_assert!(connections.iter().any(|(_, s)| matches!(
						s,
						ConnectionState::Opening | ConnectionState::Open(_)
					)));

					if let Some(pos) = connections.iter().position(|(c, _)| *c == *conn) {
						let (_, state) = connections.remove(pos);
						if let ConnectionState::Open(_) = state {
							if let Some((replacement_pos, replacement_sink)) =
								connections.iter().enumerate().find_map(|(num, (_, s))| match s {
									ConnectionState::Open(s) => Some((num, s.clone())),
									_ => None,
								}) {
								if pos <= replacement_pos {
									trace!(
										target: "sub-libp2p",
										"External API <= Sink replaced({}, {:?})",
										peer_id, set_id
									);
									let event = NotificationsOut::CustomProtocolReplaced {
										peer_id: *peer_id,
										set_id,
										notifications_sink: replacement_sink,
									};
									self.events
										.push_back(NetworkBehaviourAction::GenerateEvent(event));
								}
							} else {
								trace!(
									target: "sub-libp2p", "External API <= Closed({}, {:?})",
									peer_id, set_id
								);
								let event = NotificationsOut::CustomProtocolClosed {
									peer_id: *peer_id,
									set_id,
								};
								self.events.push_back(NetworkBehaviourAction::GenerateEvent(event));
							}
						}
					} else {
						error!(target: "sub-libp2p",
							"inject_connection_closed: State mismatch in the custom protos handler");
						debug_assert!(false);
					}

					if connections.is_empty() {
						trace!(target: "sub-libp2p", "PSM <= Dropped({}, {:?})", peer_id, set_id);
						self.peerset.dropped(set_id, *peer_id, DropReason::Unknown);
						let ban_dur = Uniform::new(5, 10).sample(&mut rand::thread_rng());

						let delay_id = self.next_delay_id;
						self.next_delay_id.0 += 1;
						let delay = futures_timer::Delay::new(Duration::from_secs(ban_dur));
						let peer_id = *peer_id;
						self.delays.push(
							async move {
								delay.await;
								(delay_id, peer_id, set_id)
							}
							.boxed(),
						);

						*entry.get_mut() = PeerState::Backoff {
							timer: delay_id,
							timer_deadline: Instant::now() + Duration::from_secs(ban_dur),
						};
					} else if !connections.iter().any(|(_, s)| {
						matches!(s, ConnectionState::Opening | ConnectionState::Open(_))
					}) {
						trace!(target: "sub-libp2p", "PSM <= Dropped({}, {:?})", peer_id, set_id);
						self.peerset.dropped(set_id, *peer_id, DropReason::Unknown);

						*entry.get_mut() = PeerState::Disabled { connections, backoff_until: None };
					} else {
						*entry.get_mut() = PeerState::Enabled { connections };
					}
				},

				PeerState::Requested |
				PeerState::PendingRequest { .. } |
				PeerState::Backoff { .. } => {
					// This is a serious bug either in this state machine or in libp2p.
					error!(target: "sub-libp2p",
						"`inject_connection_closed` called for unknown peer {}",
						peer_id);
					debug_assert!(false);
				},
				PeerState::Poisoned => {
					error!(target: "sub-libp2p", "State of peer {} is poisoned", peer_id);
					debug_assert!(false);
				},
			}
		}
	}

	fn inject_disconnected(&mut self, _peer_id: &PeerId) {}

	fn inject_dial_failure(
		&mut self,
		peer_id: Option<PeerId>,
		_: Self::ProtocolsHandler,
		error: &DialError,
	) {
		if let DialError::Transport(errors) = error {
			for (addr, error) in errors.iter() {
				trace!(target: "sub-libp2p", "Libp2p => Reach failure for {:?} through {:?}: {:?}", peer_id, addr, error);
			}
		}

		if let Some(peer_id) = peer_id {
			trace!(target: "sub-libp2p", "Libp2p => Dial failure for {:?}", peer_id);

			for set_id in (0..self.notif_protocols.len()).map(sc_peerset::SetId::from) {
				if let Entry::Occupied(mut entry) = self.peers.entry((peer_id.clone(), set_id)) {
					match mem::replace(entry.get_mut(), PeerState::Poisoned) {
						// The peer is not in our list.
						st @ PeerState::Backoff { .. } => {
							*entry.into_mut() = st;
						},

						// "Basic" situation: we failed to reach a peer that the peerset requested.
						st @ PeerState::Requested | st @ PeerState::PendingRequest { .. } => {
							trace!(target: "sub-libp2p", "PSM <= Dropped({}, {:?})", peer_id, set_id);
							self.peerset.dropped(set_id, peer_id, DropReason::Unknown);

							let now = Instant::now();
							let ban_duration = match st {
								PeerState::PendingRequest { timer_deadline, .. }
									if timer_deadline > now =>
									cmp::max(timer_deadline - now, Duration::from_secs(5)),
								_ => Duration::from_secs(5),
							};

							let delay_id = self.next_delay_id;
							self.next_delay_id.0 += 1;
							let delay = futures_timer::Delay::new(ban_duration);
							let peer_id = peer_id;
							self.delays.push(
								async move {
									delay.await;
									(delay_id, peer_id, set_id)
								}
								.boxed(),
							);

							*entry.into_mut() = PeerState::Backoff {
								timer: delay_id,
								timer_deadline: now + ban_duration,
							};
						},

						// We can still get dial failures even if we are already connected to the
						// peer, as an extra diagnostic for an earlier attempt.
						st @ PeerState::Disabled { .. } |
						st @ PeerState::Enabled { .. } |
						st @ PeerState::DisabledPendingEnable { .. } |
						st @ PeerState::Incoming { .. } => {
							*entry.into_mut() = st;
						},

						PeerState::Poisoned => {
							error!(target: "sub-libp2p", "State of {:?} is poisoned", peer_id);
							debug_assert!(false);
						},
					}
				}
			}
		}
	}

	fn inject_event(&mut self, source: PeerId, connection: ConnectionId, event: NotifsHandlerOut) {
		match event {
			NotifsHandlerOut::OpenDesiredByRemote { protocol_index } => {
				let set_id = sc_peerset::SetId::from(protocol_index);

				trace!(target: "sub-libp2p",
					"Handler({:?}, {:?}]) => OpenDesiredByRemote({:?})",
					source, connection, set_id);

				let mut entry = if let Entry::Occupied(entry) = self.peers.entry((source, set_id)) {
					entry
				} else {
					error!(
						target: "sub-libp2p",
						"OpenDesiredByRemote: State mismatch in the custom protos handler"
					);
					debug_assert!(false);
					return
				};

				match mem::replace(entry.get_mut(), PeerState::Poisoned) {
					// Incoming => Incoming
					PeerState::Incoming { mut connections, backoff_until } => {
						debug_assert!(connections
							.iter()
							.any(|(_, s)| matches!(s, ConnectionState::OpenDesiredByRemote)));
						if let Some((_, connec_state)) =
							connections.iter_mut().find(|(c, _)| *c == connection)
						{
							if let ConnectionState::Closed = *connec_state {
								*connec_state = ConnectionState::OpenDesiredByRemote;
							} else {
								// Connections in `OpeningThenClosing` and `Closing` state can be
								// in a Closed phase, and as such can emit `OpenDesiredByRemote`
								// messages.
								// Since an `Open` and/or a `Close` message have already been sent,
								// there is nothing much that can be done about this anyway.
								debug_assert!(matches!(
									connec_state,
									ConnectionState::OpeningThenClosing | ConnectionState::Closing
								));
							}
						} else {
							error!(
								target: "sub-libp2p",
								"OpenDesiredByRemote: State mismatch in the custom protos handler"
							);
							debug_assert!(false);
						}

						*entry.into_mut() = PeerState::Incoming { connections, backoff_until };
					},

					PeerState::Enabled { mut connections } => {
						debug_assert!(connections.iter().any(|(_, s)| matches!(
							s,
							ConnectionState::Opening | ConnectionState::Open(_)
						)));

						if let Some((_, connec_state)) =
							connections.iter_mut().find(|(c, _)| *c == connection)
						{
							if let ConnectionState::Closed = *connec_state {
								trace!(target: "sub-libp2p", "Handler({:?}, {:?}) <= Open({:?})",
									source, connection, set_id);
								self.events.push_back(NetworkBehaviourAction::NotifyHandler {
									peer_id: source,
									handler: NotifyHandler::One(connection),
									event: NotifsHandlerIn::Open { protocol_index: set_id.into() },
								});
								*connec_state = ConnectionState::Opening;
							} else {
								// Connections in `OpeningThenClosing`, `Opening`, and `Closing`
								// state can be in a Closed phase, and as such can emit
								// `OpenDesiredByRemote` messages.
								// Since an `Open` message haS already been sent, there is nothing
								// more to do.
								debug_assert!(matches!(
									connec_state,
									ConnectionState::OpenDesiredByRemote |
										ConnectionState::Closing | ConnectionState::Opening
								));
							}
						} else {
							error!(
								target: "sub-libp2p",
								"OpenDesiredByRemote: State mismatch in the custom protos handler"
							);
							debug_assert!(false);
						}

						*entry.into_mut() = PeerState::Enabled { connections };
					},

					// Disabled => Disabled | Incoming
					PeerState::Disabled { mut connections, backoff_until } => {
						if let Some((_, connec_state)) =
							connections.iter_mut().find(|(c, _)| *c == connection)
						{
							if let ConnectionState::Closed = *connec_state {
								*connec_state = ConnectionState::OpenDesiredByRemote;

								let incoming_id = self.next_incoming_index;
								self.next_incoming_index.0 += 1;

								trace!(target: "sub-libp2p", "PSM <= Incoming({}, {:?}).",
									source, incoming_id);
								self.peerset.incoming(set_id, source, incoming_id);
								self.incoming.push(IncomingPeer {
									peer_id: source,
									set_id,
									alive: true,
									incoming_id,
								});

								*entry.into_mut() =
									PeerState::Incoming { connections, backoff_until };
							} else {
								// Connections in `OpeningThenClosing` and `Closing` state can be
								// in a Closed phase, and as such can emit `OpenDesiredByRemote`
								// messages.
								// We ignore them.
								debug_assert!(matches!(
									connec_state,
									ConnectionState::OpeningThenClosing | ConnectionState::Closing
								));
								*entry.into_mut() =
									PeerState::Disabled { connections, backoff_until };
							}
						} else {
							error!(
								target: "sub-libp2p",
								"OpenDesiredByRemote: State mismatch in the custom protos handler"
							);
							debug_assert!(false);
						}
					},

					// DisabledPendingEnable => Enabled | DisabledPendingEnable
					PeerState::DisabledPendingEnable { mut connections, timer, timer_deadline } => {
						if let Some((_, connec_state)) =
							connections.iter_mut().find(|(c, _)| *c == connection)
						{
							if let ConnectionState::Closed = *connec_state {
								trace!(target: "sub-libp2p", "Handler({:?}, {:?}) <= Open({:?})",
									source, connection, set_id);
								self.events.push_back(NetworkBehaviourAction::NotifyHandler {
									peer_id: source,
									handler: NotifyHandler::One(connection),
									event: NotifsHandlerIn::Open { protocol_index: set_id.into() },
								});
								*connec_state = ConnectionState::Opening;

								*entry.into_mut() = PeerState::Enabled { connections };
							} else {
								// Connections in `OpeningThenClosing` and `Closing` state can be
								// in a Closed phase, and as such can emit `OpenDesiredByRemote`
								// messages.
								// We ignore them.
								debug_assert!(matches!(
									connec_state,
									ConnectionState::OpeningThenClosing | ConnectionState::Closing
								));
								*entry.into_mut() = PeerState::DisabledPendingEnable {
									connections,
									timer,
									timer_deadline,
								};
							}
						} else {
							error!(
								target: "sub-libp2p",
								"OpenDesiredByRemote: State mismatch in the custom protos handler"
							);
							debug_assert!(false);
						}
					},

					state => {
						error!(target: "sub-libp2p",
							   "OpenDesiredByRemote: Unexpected state in the custom protos handler: {:?}",
							   state);
						debug_assert!(false);
						return
					},
				};
			},

			NotifsHandlerOut::CloseDesired { protocol_index } => {
				let set_id = sc_peerset::SetId::from(protocol_index);

				trace!(target: "sub-libp2p",
					"Handler({}, {:?}) => CloseDesired({:?})",
					source, connection, set_id);

				let mut entry = if let Entry::Occupied(entry) = self.peers.entry((source, set_id)) {
					entry
				} else {
					error!(target: "sub-libp2p", "CloseDesired: State mismatch in the custom protos handler");
					debug_assert!(false);
					return
				};

				match mem::replace(entry.get_mut(), PeerState::Poisoned) {
					// Enabled => Enabled | Disabled
					PeerState::Enabled { mut connections } => {
						debug_assert!(connections.iter().any(|(_, s)| matches!(
							s,
							ConnectionState::Opening | ConnectionState::Open(_)
						)));

						let pos = if let Some(pos) =
							connections.iter().position(|(c, _)| *c == connection)
						{
							pos
						} else {
							error!(target: "sub-libp2p",
								"CloseDesired: State mismatch in the custom protos handler");
							debug_assert!(false);
							return
						};

						if matches!(connections[pos].1, ConnectionState::Closing) {
							*entry.into_mut() = PeerState::Enabled { connections };
							return
						}

						debug_assert!(matches!(connections[pos].1, ConnectionState::Open(_)));
						connections[pos].1 = ConnectionState::Closing;

						trace!(target: "sub-libp2p", "Handler({}, {:?}) <= Close({:?})", source, connection, set_id);
						self.events.push_back(NetworkBehaviourAction::NotifyHandler {
							peer_id: source,
							handler: NotifyHandler::One(connection),
							event: NotifsHandlerIn::Close { protocol_index: set_id.into() },
						});

						if let Some((replacement_pos, replacement_sink)) =
							connections.iter().enumerate().find_map(|(num, (_, s))| match s {
								ConnectionState::Open(s) => Some((num, s.clone())),
								_ => None,
							}) {
							if pos <= replacement_pos {
								trace!(target: "sub-libp2p", "External API <= Sink replaced({:?})", source);
								let event = NotificationsOut::CustomProtocolReplaced {
									peer_id: source,
									set_id,
									notifications_sink: replacement_sink,
								};
								self.events.push_back(NetworkBehaviourAction::GenerateEvent(event));
							}

							*entry.into_mut() = PeerState::Enabled { connections };
						} else {
							// List of open connections wasn't empty before but now it is.
							if !connections
								.iter()
								.any(|(_, s)| matches!(s, ConnectionState::Opening))
							{
								trace!(target: "sub-libp2p", "PSM <= Dropped({}, {:?})", source, set_id);
								self.peerset.dropped(set_id, source, DropReason::Refused);
								*entry.into_mut() =
									PeerState::Disabled { connections, backoff_until: None };
							} else {
								*entry.into_mut() = PeerState::Enabled { connections };
							}

							trace!(target: "sub-libp2p", "External API <= Closed({}, {:?})", source, set_id);
							let event =
								NotificationsOut::CustomProtocolClosed { peer_id: source, set_id };
							self.events.push_back(NetworkBehaviourAction::GenerateEvent(event));
						}
					},

					// All connections in `Disabled` and `DisabledPendingEnable` have been sent a
					// `Close` message already, and as such ignore any `CloseDesired` message.
					state @ PeerState::Disabled { .. } |
					state @ PeerState::DisabledPendingEnable { .. } => {
						*entry.into_mut() = state;
						return
					},
					state => {
						error!(target: "sub-libp2p",
							"Unexpected state in the custom protos handler: {:?}",
							state);
						return
					},
				}
			},

			NotifsHandlerOut::CloseResult { protocol_index } => {
				let set_id = sc_peerset::SetId::from(protocol_index);

				trace!(target: "sub-libp2p",
					"Handler({}, {:?}) => CloseResult({:?})",
					source, connection, set_id);

				match self.peers.get_mut(&(source, set_id)) {
					// Move the connection from `Closing` to `Closed`.
					Some(PeerState::Incoming { connections, .. }) |
					Some(PeerState::DisabledPendingEnable { connections, .. }) |
					Some(PeerState::Disabled { connections, .. }) |
					Some(PeerState::Enabled { connections, .. }) => {
						if let Some((_, connec_state)) = connections.iter_mut().find(|(c, s)| {
							*c == connection && matches!(s, ConnectionState::Closing)
						}) {
							*connec_state = ConnectionState::Closed;
						} else {
							error!(target: "sub-libp2p",
								"CloseResult: State mismatch in the custom protos handler");
							debug_assert!(false);
						}
					},

					state => {
						error!(target: "sub-libp2p",
							   "CloseResult: Unexpected state in the custom protos handler: {:?}",
							   state);
						debug_assert!(false);
					},
				}
			},

			NotifsHandlerOut::OpenResultOk {
				protocol_index,
				negotiated_fallback,
				received_handshake,
				notifications_sink,
				..
			} => {
				let set_id = sc_peerset::SetId::from(protocol_index);
				trace!(target: "sub-libp2p",
					"Handler({}, {:?}) => OpenResultOk({:?})",
					source, connection, set_id);

				match self.peers.get_mut(&(source, set_id)) {
					Some(PeerState::Enabled { connections, .. }) => {
						debug_assert!(connections.iter().any(|(_, s)| matches!(
							s,
							ConnectionState::Opening | ConnectionState::Open(_)
						)));
						let any_open =
							connections.iter().any(|(_, s)| matches!(s, ConnectionState::Open(_)));

						if let Some((_, connec_state)) = connections.iter_mut().find(|(c, s)| {
							*c == connection && matches!(s, ConnectionState::Opening)
						}) {
							if !any_open {
								trace!(target: "sub-libp2p", "External API <= Open({}, {:?})", source, set_id);
								let event = NotificationsOut::CustomProtocolOpen {
									peer_id: source,
									set_id,
									negotiated_fallback,
									received_handshake,
									notifications_sink: notifications_sink.clone(),
								};
								self.events.push_back(NetworkBehaviourAction::GenerateEvent(event));
							}
							*connec_state = ConnectionState::Open(notifications_sink);
						} else if let Some((_, connec_state)) =
							connections.iter_mut().find(|(c, s)| {
								*c == connection && matches!(s, ConnectionState::OpeningThenClosing)
							}) {
							*connec_state = ConnectionState::Closing;
						} else {
							error!(target: "sub-libp2p",
								"OpenResultOk State mismatch in the custom protos handler");
							debug_assert!(false);
						}
					},

					Some(PeerState::Incoming { connections, .. }) |
					Some(PeerState::DisabledPendingEnable { connections, .. }) |
					Some(PeerState::Disabled { connections, .. }) => {
						if let Some((_, connec_state)) = connections.iter_mut().find(|(c, s)| {
							*c == connection && matches!(s, ConnectionState::OpeningThenClosing)
						}) {
							*connec_state = ConnectionState::Closing;
						} else {
							error!(target: "sub-libp2p",
								"OpenResultOk State mismatch in the custom protos handler");
							debug_assert!(false);
						}
					},

					state => {
						error!(target: "sub-libp2p",
							   "OpenResultOk: Unexpected state in the custom protos handler: {:?}",
							   state);
						debug_assert!(false);
						return
					},
				}
			},

			NotifsHandlerOut::OpenResultErr { protocol_index } => {
				let set_id = sc_peerset::SetId::from(protocol_index);
				trace!(target: "sub-libp2p",
					"Handler({:?}, {:?}) => OpenResultErr({:?})",
					source, connection, set_id);

				let mut entry = if let Entry::Occupied(entry) = self.peers.entry((source, set_id)) {
					entry
				} else {
					error!(target: "sub-libp2p", "OpenResultErr: State mismatch in the custom protos handler");
					debug_assert!(false);
					return
				};

				match mem::replace(entry.get_mut(), PeerState::Poisoned) {
					PeerState::Enabled { mut connections } => {
						debug_assert!(connections.iter().any(|(_, s)| matches!(
							s,
							ConnectionState::Opening | ConnectionState::Open(_)
						)));

						if let Some((_, connec_state)) = connections.iter_mut().find(|(c, s)| {
							*c == connection && matches!(s, ConnectionState::Opening)
						}) {
							*connec_state = ConnectionState::Closed;
						} else if let Some((_, connec_state)) =
							connections.iter_mut().find(|(c, s)| {
								*c == connection && matches!(s, ConnectionState::OpeningThenClosing)
							}) {
							*connec_state = ConnectionState::Closing;
						} else {
							error!(target: "sub-libp2p",
								"OpenResultErr: State mismatch in the custom protos handler");
							debug_assert!(false);
						}

						if !connections.iter().any(|(_, s)| {
							matches!(s, ConnectionState::Opening | ConnectionState::Open(_))
						}) {
							trace!(target: "sub-libp2p", "PSM <= Dropped({:?})", source);
							self.peerset.dropped(set_id, source, DropReason::Refused);

							let ban_dur = Uniform::new(5, 10).sample(&mut rand::thread_rng());
							*entry.into_mut() = PeerState::Disabled {
								connections,
								backoff_until: Some(Instant::now() + Duration::from_secs(ban_dur)),
							};
						} else {
							*entry.into_mut() = PeerState::Enabled { connections };
						}
					},
					mut state @ PeerState::Incoming { .. } |
					mut state @ PeerState::DisabledPendingEnable { .. } |
					mut state @ PeerState::Disabled { .. } => {
						match &mut state {
							PeerState::Incoming { connections, .. } |
							PeerState::Disabled { connections, .. } |
							PeerState::DisabledPendingEnable { connections, .. } => {
								if let Some((_, connec_state)) =
									connections.iter_mut().find(|(c, s)| {
										*c == connection &&
											matches!(s, ConnectionState::OpeningThenClosing)
									}) {
									*connec_state = ConnectionState::Closing;
								} else {
									error!(target: "sub-libp2p",
										"OpenResultErr: State mismatch in the custom protos handler");
									debug_assert!(false);
								}
							},
							_ => unreachable!(
								"Match branches are the same as the one on which we
							enter this block; qed"
							),
						};

						*entry.into_mut() = state;
					},
					state => {
						error!(target: "sub-libp2p",
							"Unexpected state in the custom protos handler: {:?}",
							state);
						debug_assert!(false);
					},
				};
			},

			NotifsHandlerOut::Notification { protocol_index, message } => {
				let set_id = sc_peerset::SetId::from(protocol_index);
				if self.is_open(&source, set_id) {
					trace!(
						target: "sub-libp2p",
						"Handler({:?}) => Notification({}, {:?}, {} bytes)",
						connection,
						source,
						set_id,
						message.len()
					);
					trace!(
						target: "sub-libp2p",
						"External API <= Message({}, {:?})",
						source,
						set_id,
					);
					let event = NotificationsOut::Notification { peer_id: source, set_id, message };

					self.events.push_back(NetworkBehaviourAction::GenerateEvent(event));
				} else {
					trace!(
						target: "sub-libp2p",
						"Handler({:?}) => Post-close notification({}, {:?}, {} bytes)",
						connection,
						source,
						set_id,
						message.len()
					);
				}
			},
		}
	}

	fn poll(
		&mut self,
		cx: &mut Context,
		_params: &mut impl PollParameters,
	) -> Poll<NetworkBehaviourAction<Self::OutEvent, Self::ProtocolsHandler>> {
		if let Some(event) = self.events.pop_front() {
			return Poll::Ready(event)
		}

		// Poll for instructions from the peerset.
		// Note that the peerset is a *best effort* crate, and we have to use defensive programming.
		loop {
			match futures::Stream::poll_next(Pin::new(&mut self.peerset), cx) {
				Poll::Ready(Some(sc_peerset::Message::Accept(index))) => {
					self.peerset_report_accept(index);
				},
				Poll::Ready(Some(sc_peerset::Message::Reject(index))) => {
					self.peerset_report_reject(index);
				},
				Poll::Ready(Some(sc_peerset::Message::Connect { peer_id, set_id, .. })) => {
					self.peerset_report_connect(peer_id, set_id);
				},
				Poll::Ready(Some(sc_peerset::Message::Drop { peer_id, set_id, .. })) => {
					self.peerset_report_disconnect(peer_id, set_id);
				},
				Poll::Ready(None) => {
					error!(target: "sub-libp2p", "Peerset receiver stream has returned None");
					break
				},
				Poll::Pending => break,
			}
		}

		while let Poll::Ready(Some((delay_id, peer_id, set_id))) =
			Pin::new(&mut self.delays).poll_next(cx)
		{
			let handler = self.new_handler();

			let peer_state = match self.peers.get_mut(&(peer_id, set_id)) {
				Some(s) => s,
				// We intentionally never remove elements from `delays`, and it may
				// thus contain peers which are now gone. This is a normal situation.
				None => continue,
			};

			match peer_state {
				PeerState::Backoff { timer, .. } if *timer == delay_id => {
					trace!(target: "sub-libp2p", "Libp2p <= Clean up ban of {:?} from the state", peer_id);
					self.peers.remove(&(peer_id, set_id));
				},

				PeerState::PendingRequest { timer, .. } if *timer == delay_id => {
					trace!(target: "sub-libp2p", "Libp2p <= Dial {:?} now that ban has expired", peer_id);
					// The `DialPeerCondition` ensures that dial attempts are de-duplicated
					self.events.push_back(NetworkBehaviourAction::DialPeer {
						peer_id,
						condition: DialPeerCondition::Disconnected,
						handler,
					});
					*peer_state = PeerState::Requested;
				},

				PeerState::DisabledPendingEnable { connections, timer, timer_deadline }
					if *timer == delay_id =>
				{
					// The first element of `closed` is chosen to open the notifications substream.
					if let Some((connec_id, connec_state)) =
						connections.iter_mut().find(|(_, s)| matches!(s, ConnectionState::Closed))
					{
						trace!(target: "sub-libp2p", "Handler({}, {:?}) <= Open({:?}) (ban expired)",
							peer_id, *connec_id, set_id);
						self.events.push_back(NetworkBehaviourAction::NotifyHandler {
							peer_id,
							handler: NotifyHandler::One(*connec_id),
							event: NotifsHandlerIn::Open { protocol_index: set_id.into() },
						});
						*connec_state = ConnectionState::Opening;
						*peer_state = PeerState::Enabled {
							connections: mem::replace(connections, Default::default()),
						};
					} else {
						*timer_deadline = Instant::now() + Duration::from_secs(5);
						let delay = futures_timer::Delay::new(Duration::from_secs(5));
						let timer = *timer;
						self.delays.push(
							async move {
								delay.await;
								(timer, peer_id, set_id)
							}
							.boxed(),
						);
					}
				},

				// We intentionally never remove elements from `delays`, and it may
				// thus contain obsolete entries. This is a normal situation.
				_ => {},
			}
		}

		if let Some(event) = self.events.pop_front() {
			return Poll::Ready(event)
		}

		Poll::Pending
	}
}
