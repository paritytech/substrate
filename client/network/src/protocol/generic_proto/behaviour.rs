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

use crate::{DiscoveryNetBehaviour, config::ProtocolId};
use crate::protocol::message::generic::{Message as GenericMessage, ConsensusMessage};
use crate::protocol::generic_proto::handler::{NotifsHandlerProto, NotifsHandlerOut, NotifsHandlerIn};
use crate::protocol::generic_proto::upgrade::RegisteredProtocol;

use bytes::BytesMut;
use codec::Encode as _;
use fnv::FnvHashMap;
use futures::prelude::*;
use libp2p::core::{ConnectedPoint, Multiaddr, PeerId};
use libp2p::swarm::{NetworkBehaviour, NetworkBehaviourAction, PollParameters};
use log::{debug, error, trace, warn};
use rand::distributions::{Distribution as _, Uniform};
use smallvec::SmallVec;
use sp_runtime::ConsensusEngineId;
use std::{borrow::Cow, collections::hash_map::Entry, cmp};
use std::{error, mem, pin::Pin, str, time::Duration};
use std::task::{Context, Poll};
use wasm_timer::Instant;

/// Network behaviour that handles opening substreams for custom protocols with other nodes.
///
/// ## Legacy vs new protocol
///
/// The `GenericProto` behaves as following:
///
/// - Whenever a connection is established, we open a single substream (called "legay protocol" in
/// the source code). This substream name depends on the `protocol_id` and `versions` passed at
/// initialization. If the remote refuses this substream, we close the connection.
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
/// - The peerset manager (PSM) that requests links to nodes to be established or broken.
/// - The external API, that requires knowledge of the links that have been established.
///
/// Each connection handler can be in four different states: Enabled+Open, Enabled+Closed,
/// Disabled+Open, or Disabled+Closed. The Enabled/Disabled component must be in sync with the
/// peerset manager. For example, if the peerset manager requires a disconnection, we disable the
/// existing handler. The Open/Closed component must be in sync with the external API.
///
/// However a connection handler only exists if we are actually connected to a node. What this
/// means is that there are six possible states for each node: Disconnected, Dialing (trying to
/// reach it), Enabled+Open, Enabled+Closed, Disabled+open, Disabled+Closed. Most notably, the
/// Dialing state must correspond to a "link established" state in the peerset manager. In other
/// words, the peerset manager doesn't differentiate whether we are dialing a node or connected
/// to it.
///
/// Additionally, there also exists a "banning" system. If we fail to dial a node, we "ban" it for
/// a few seconds. If the PSM requests a node that is in the "banned" state, then we delay the
/// actual dialing attempt until after the ban expires, but the PSM will still consider the link
/// to be established.
/// Note that this "banning" system is not an actual ban. If a "banned" node tries to connect to
/// us, we accept the connection. The "banning" system is only about delaying dialing attempts.
///
pub struct GenericProto {
	/// Legacy protocol to open with peers. Never modified.
	legacy_protocol: RegisteredProtocol,

	/// Notification protocols. Entries are only ever added and not removed.
	notif_protocols: Vec<(Cow<'static, [u8]>, ConsensusEngineId, Vec<u8>)>,

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
}

/// State of a peer we're connected to.
#[derive(Debug)]
enum PeerState {
	/// State is poisoned. This is a temporary state for a peer and we should always switch back
	/// to it later. If it is found in the wild, that means there was either a panic or a bug in
	/// the state machine code.
	Poisoned,

	/// The peer misbehaved. If the PSM wants us to connect to this node, we will add an artificial
	/// delay to the connection.
	Banned {
		/// Until when the node is banned.
		until: Instant,
	},

	/// The peerset requested that we connect to this peer. We are not connected to this node.
	PendingRequest {
		/// When to actually start dialing.
		timer: futures_timer::Delay,
		/// When the `timer` will trigger.
		timer_deadline: Instant,
	},

	/// The peerset requested that we connect to this peer. We are currently dialing this peer.
	Requested,

	/// We are connected to this peer but the peerset refused it. This peer can still perform
	/// Kademlia queries and such, but should get disconnected in a few seconds.
	Disabled {
		/// How we are connected to this peer.
		connected_point: ConnectedPoint,
		/// If true, we still have a custom protocol open with it. It will likely get closed in
		/// a short amount of time, but we need to keep the information in order to not have a
		/// state mismatch.
		open: bool,
		/// If `Some`, the node is banned until the given `Instant`.
		banned_until: Option<Instant>,
	},

	/// We are connected to this peer but we are not opening any Substrate substream. The handler
	/// will be enabled when `timer` fires. This peer can still perform Kademlia queries and such,
	/// but should get disconnected in a few seconds.
	DisabledPendingEnable {
		/// How we are connected to this peer.
		connected_point: ConnectedPoint,
		/// If true, we still have a custom protocol open with it. It will likely get closed in
		/// a short amount of time, but we need to keep the information in order to not have a
		/// state mismatch.
		open: bool,
		/// When to enable this remote.
		timer: futures_timer::Delay,
		/// When the `timer` will trigger.
		timer_deadline: Instant,
	},

	/// We are connected to this peer and the peerset has accepted it. The handler is in the
	/// enabled state.
	Enabled {
		/// How we are connected to this peer.
		connected_point: ConnectedPoint,
		/// If true, we have a custom protocol open with this peer.
		open: bool,
	},

	/// We are connected to this peer, and we sent an incoming message to the peerset. The handler
	/// is in initialization mode. We are waiting for the Accept or Reject from the peerset. There
	/// is a corresponding entry in `incoming`.
	Incoming {
		/// How we are connected to this peer.
		connected_point: ConnectedPoint,
	},
}

impl PeerState {
	/// True if we have an open channel with that node.
	fn is_open(&self) -> bool {
		match self {
			PeerState::Poisoned => false,
			PeerState::Banned { .. } => false,
			PeerState::PendingRequest { .. } => false,
			PeerState::Requested => false,
			PeerState::Disabled { open, .. } => *open,
			PeerState::DisabledPendingEnable { open, .. } => *open,
			PeerState::Enabled { open, .. } => *open,
			PeerState::Incoming { .. } => false,
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
	/// Id of the node that is concerned.
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
		/// Id of the node we have opened a connection with.
		peer_id: PeerId,
		/// Endpoint used for this custom protocol.
		endpoint: ConnectedPoint,
	},

	/// Closed a custom protocol with the remote.
	CustomProtocolClosed {
		/// Id of the peer we were connected to.
		peer_id: PeerId,
		/// Reason why the substream closed, for debugging purposes.
		reason: Cow<'static, str>,
	},

	/// Receives a message on a custom protocol substream.
	///
	/// Also concerns received notifications for the notifications API.
	CustomMessage {
		/// Id of the peer the message came from.
		peer_id: PeerId,
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
	pub fn new(
		protocol: impl Into<ProtocolId>,
		versions: &[u8],
		peerset: sc_peerset::Peerset,
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
		}
	}

	/// Registers a new notifications protocol.
	///
	/// You are very strongly encouraged to call this method very early on. Any open connection
	/// will retain the protocols that were registered then, and not any new one.
	pub fn register_notif_protocol(
		&mut self,
		protocol_name: impl Into<Cow<'static, [u8]>>,
		engine_id: ConsensusEngineId,
		handshake_msg: impl Into<Vec<u8>>
	) {
		self.notif_protocols.push((protocol_name.into(), engine_id, handshake_msg.into()));
	}

	/// Returns the number of discovered nodes that we keep in memory.
	pub fn num_discovered_peers(&self) -> usize {
		self.peerset.num_discovered_peers()
	}

	/// Returns the list of all the peers we have an open channel to.
	pub fn open_peers<'a>(&'a self) -> impl Iterator<Item = &'a PeerId> + 'a {
		self.peers.iter().filter(|(_, state)| state.is_open()).map(|(id, _)| id)
	}

	/// Returns true if we have a channel open with this node.
	pub fn is_open(&self, peer_id: &PeerId) -> bool {
		self.peers.get(peer_id).map(|p| p.is_open()).unwrap_or(false)
	}

	/// Disconnects the given peer if we are connected to it.
	pub fn disconnect_peer(&mut self, peer_id: &PeerId) {
		debug!(target: "sub-libp2p", "External API => Disconnect {:?}", peer_id);
		self.disconnect_peer_inner(peer_id, None);
	}

	/// Inner implementation of `disconnect_peer`. If `ban` is `Some`, we ban the node for the
	/// specific duration.
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
			PeerState::DisabledPendingEnable { open, connected_point, timer_deadline, .. } => {
				debug!(target: "sub-libp2p", "PSM <= Dropped({:?})", peer_id);
				self.peerset.dropped(peer_id.clone());
				let banned_until = Some(if let Some(ban) = ban {
					cmp::max(timer_deadline, Instant::now() + ban)
				} else {
					timer_deadline
				});
				*entry.into_mut() = PeerState::Disabled { open, connected_point, banned_until }
			},

			// Enabled => Disabled.
			PeerState::Enabled { open, connected_point } => {
				debug!(target: "sub-libp2p", "PSM <= Dropped({:?})", peer_id);
				self.peerset.dropped(peer_id.clone());
				debug!(target: "sub-libp2p", "Handler({:?}) <= Disable", peer_id);
				self.events.push(NetworkBehaviourAction::SendEvent {
					peer_id: peer_id.clone(),
					event: NotifsHandlerIn::Disable,
				});
				let banned_until = ban.map(|dur| Instant::now() + dur);
				*entry.into_mut() = PeerState::Disabled { open, connected_point, banned_until }
			},

			// Incoming => Disabled.
			PeerState::Incoming { connected_point, .. } => {
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
				self.events.push(NetworkBehaviourAction::SendEvent {
					peer_id: peer_id.clone(),
					event: NotifsHandlerIn::Disable,
				});
				let banned_until = ban.map(|dur| Instant::now() + dur);
				*entry.into_mut() = PeerState::Disabled { open: false, connected_point, banned_until }
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

	/// Sends a notification to a peer.
	///
	/// Has no effect if the custom protocol is not open with the given peer.
	///
	/// Also note that even if we have a valid open substream, it may in fact be already closed
	/// without us knowing, in which case the packet will not be received.
	///
	/// > **Note**: Ideally the `engine_id` parameter wouldn't be necessary. See the documentation
	/// >			of [`NotifsHandlerIn`] for more information.
	pub fn write_notification(
		&mut self,
		target: &PeerId,
		engine_id: ConsensusEngineId,
		protocol_name: Cow<'static, [u8]>,
		message: impl Into<Vec<u8>>,
	) {
		if !self.is_open(target) {
			return;
		}

		trace!(
			target: "sub-libp2p",
			"External API => Notification for {:?} with protocol {:?}",
			target,
			str::from_utf8(&protocol_name)
		);
		trace!(target: "sub-libp2p", "Handler({:?}) <= Packet", target);

		self.events.push(NetworkBehaviourAction::SendEvent {
			peer_id: target.clone(),
			event: NotifsHandlerIn::SendNotification {
				message: message.into(),
				engine_id,
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
		if !self.is_open(target) {
			return;
		}

		trace!(target: "sub-libp2p", "External API => Packet for {:?}", target);
		trace!(target: "sub-libp2p", "Handler({:?}) <= Packet", target);
		self.events.push(NetworkBehaviourAction::SendEvent {
			peer_id: target.clone(),
			event: NotifsHandlerIn::SendLegacy {
				message,
			}
		});
	}

	/// Returns the state of the peerset manager, for debugging purposes.
	pub fn peerset_debug_info(&mut self) -> serde_json::Value {
		self.peerset.debug_info()
	}

	/// Function that is called when the peerset wants us to connect to a node.
	fn peerset_report_connect(&mut self, peer_id: PeerId) {
		let mut occ_entry = match self.peers.entry(peer_id) {
			Entry::Occupied(entry) => entry,
			Entry::Vacant(entry) => {
				// If there's no entry in `self.peers`, start dialing.
				debug!(target: "sub-libp2p", "PSM => Connect({:?}): Starting to connect", entry.key());
				debug!(target: "sub-libp2p", "Libp2p <= Dial {:?}", entry.key());
				self.events.push(NetworkBehaviourAction::DialPeer { peer_id: entry.key().clone() });
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
				self.events.push(NetworkBehaviourAction::DialPeer { peer_id: occ_entry.key().clone() });
				*occ_entry.into_mut() = PeerState::Requested;
			},

			PeerState::Disabled { open, ref connected_point, banned_until: Some(ref banned) }
				if *banned > now => {
				debug!(target: "sub-libp2p", "PSM => Connect({:?}): Has idle connection through \
					{:?} but node is banned until {:?}", occ_entry.key(), connected_point, banned);
				*occ_entry.into_mut() = PeerState::DisabledPendingEnable {
					connected_point: connected_point.clone(),
					open,
					timer: futures_timer::Delay::new(banned.clone() - now),
					timer_deadline: banned.clone(),
				};
			},

			PeerState::Disabled { open, connected_point, banned_until: _ } => {
				debug!(target: "sub-libp2p", "PSM => Connect({:?}): Enabling previously-idle \
					connection through {:?}", occ_entry.key(), connected_point);
				debug!(target: "sub-libp2p", "Handler({:?}) <= Enable", occ_entry.key());
				self.events.push(NetworkBehaviourAction::SendEvent {
					peer_id: occ_entry.key().clone(),
					event: NotifsHandlerIn::Enable,
				});
				*occ_entry.into_mut() = PeerState::Enabled { connected_point, open };
			},

			PeerState::Incoming { connected_point, .. } => {
				debug!(target: "sub-libp2p", "PSM => Connect({:?}): Enabling incoming \
					connection through {:?}", occ_entry.key(), connected_point);
				if let Some(inc) = self.incoming.iter_mut()
					.find(|i| i.peer_id == *occ_entry.key() && i.alive) {
					inc.alive = false;
				} else {
					error!(target: "sub-libp2p", "State mismatch in libp2p: no entry in \
						incoming for incoming peer")
				}
				debug!(target: "sub-libp2p", "Handler({:?}) <= Enable", occ_entry.key());
				self.events.push(NetworkBehaviourAction::SendEvent {
					peer_id: occ_entry.key().clone(),
					event: NotifsHandlerIn::Enable,
				});
				*occ_entry.into_mut() = PeerState::Enabled { connected_point, open: false };
			},

			st @ PeerState::Enabled { .. } => {
				warn!(target: "sub-libp2p", "PSM => Connect({:?}): Already connected to this \
					peer", occ_entry.key());
				*occ_entry.into_mut() = st;
			},
			st @ PeerState::DisabledPendingEnable { .. } => {
				warn!(target: "sub-libp2p", "PSM => Connect({:?}): Already have an idle \
					connection to this peer and waiting to enable it", occ_entry.key());
				*occ_entry.into_mut() = st;
			},
			st @ PeerState::Requested { .. } | st @ PeerState::PendingRequest { .. } => {
				warn!(target: "sub-libp2p", "PSM => Connect({:?}): Received a previous \
					request for that peer", occ_entry.key());
				*occ_entry.into_mut() = st;
			},

			PeerState::Poisoned =>
				error!(target: "sub-libp2p", "State of {:?} is poisoned", occ_entry.key()),
		}
	}

	/// Function that is called when the peerset wants us to disconnect from a node.
	fn peerset_report_disconnect(&mut self, peer_id: PeerId) {
		let mut entry = match self.peers.entry(peer_id) {
			Entry::Occupied(entry) => entry,
			Entry::Vacant(entry) => {
				debug!(target: "sub-libp2p", "PSM => Drop({:?}): Node already disabled", entry.key());
				return
			}
		};

		match mem::replace(entry.get_mut(), PeerState::Poisoned) {
			st @ PeerState::Disabled { .. } | st @ PeerState::Banned { .. } => {
				debug!(target: "sub-libp2p", "PSM => Drop({:?}): Node already disabled", entry.key());
				*entry.into_mut() = st;
			},

			PeerState::DisabledPendingEnable { open, connected_point, timer_deadline, .. } => {
				debug!(target: "sub-libp2p", "PSM => Drop({:?}): Interrupting pending \
					enable", entry.key());
				*entry.into_mut() = PeerState::Disabled {
					open,
					connected_point,
					banned_until: Some(timer_deadline),
				};
			},

			PeerState::Enabled { open, connected_point } => {
				debug!(target: "sub-libp2p", "PSM => Drop({:?}): Disabling connection", entry.key());
				debug!(target: "sub-libp2p", "Handler({:?}) <= Disable", entry.key());
				self.events.push(NetworkBehaviourAction::SendEvent {
					peer_id: entry.key().clone(),
					event: NotifsHandlerIn::Disable,
				});
				*entry.into_mut() = PeerState::Disabled { open, connected_point, banned_until: None }
			},
			st @ PeerState::Incoming { .. } => {
				error!(target: "sub-libp2p", "PSM => Drop({:?}): Was in incoming mode",
					entry.key());
				*entry.into_mut() = st;
			},
			PeerState::Requested => {
				// We don't cancel dialing. Libp2p doesn't expose that on purpose, as other
				// sub-systems (such as the discovery mechanism) may require dialing this node as
				// well at the same time.
				debug!(target: "sub-libp2p", "PSM => Drop({:?}): Was not yet connected", entry.key());
				entry.remove();
			},
			PeerState::PendingRequest { timer_deadline, .. } => {
				debug!(target: "sub-libp2p", "PSM => Drop({:?}): Was not yet connected", entry.key());
				*entry.into_mut() = PeerState::Banned { until: timer_deadline }
			},

			PeerState::Poisoned =>
				error!(target: "sub-libp2p", "State of {:?} is poisoned", entry.key()),
		}
	}

	/// Function that is called when the peerset wants us to accept an incoming node.
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

		let state = if let Some(state) = self.peers.get_mut(&incoming.peer_id) {
			state
		} else {
			error!(target: "sub-libp2p", "State mismatch in libp2p: no entry in peers \
				corresponding to an alive incoming");
			return
		};

		let connected_point = if let PeerState::Incoming { connected_point } = state {
			connected_point.clone()
		} else {
			error!(target: "sub-libp2p", "State mismatch in libp2p: entry in peers corresponding \
				to an alive incoming is not in incoming state");
			return
		};

		debug!(target: "sub-libp2p", "PSM => Accept({:?}, {:?}): Enabling connection \
			through {:?}", index, incoming.peer_id, connected_point);
		debug!(target: "sub-libp2p", "Handler({:?}) <= Enable", incoming.peer_id);
		self.events.push(NetworkBehaviourAction::SendEvent {
			peer_id: incoming.peer_id,
			event: NotifsHandlerIn::Enable,
		});

		*state = PeerState::Enabled { open: false, connected_point };
	}

	/// Function that is called when the peerset wants us to reject an incoming node.
	fn peerset_report_reject(&mut self, index: sc_peerset::IncomingIndex) {
		let incoming = if let Some(pos) = self.incoming.iter().position(|i| i.incoming_id == index) {
			self.incoming.remove(pos)
		} else {
			error!(target: "sub-libp2p", "PSM => Reject({:?}): Invalid index", index);
			return
		};

		if !incoming.alive {
			error!(target: "sub-libp2p", "PSM => Reject({:?}, {:?}): Obsolete incoming, \
				ignoring", index, incoming.peer_id);
			return
		}

		let state = if let Some(state) = self.peers.get_mut(&incoming.peer_id) {
			state
		} else {
			error!(target: "sub-libp2p", "State mismatch in libp2p: no entry in peers \
				corresponding to an alive incoming");
			return
		};

		let connected_point = if let PeerState::Incoming { connected_point } = state {
			connected_point.clone()
		} else {
			error!(target: "sub-libp2p", "State mismatch in libp2p: entry in peers corresponding \
				to an alive incoming is not in incoming state");
			return
		};

		debug!(target: "sub-libp2p", "PSM => Reject({:?}, {:?}): Rejecting connection through \
			{:?}", index, incoming.peer_id, connected_point);
		debug!(target: "sub-libp2p", "Handler({:?}) <= Disable", incoming.peer_id);
		self.events.push(NetworkBehaviourAction::SendEvent {
			peer_id: incoming.peer_id,
			event: NotifsHandlerIn::Disable,
		});
		*state = PeerState::Disabled { open: false, connected_point, banned_until: None };
	}
}

impl DiscoveryNetBehaviour for GenericProto {
	fn add_discovered_nodes(&mut self, peer_ids: impl Iterator<Item = PeerId>) {
		self.peerset.discovered(peer_ids.into_iter().map(|peer_id| {
			debug!(target: "sub-libp2p", "PSM <= Discovered({:?})", peer_id);
			peer_id
		}));
	}
}

impl NetworkBehaviour for GenericProto {
	type ProtocolsHandler = NotifsHandlerProto;
	type OutEvent = GenericProtoOut;

	fn new_handler(&mut self) -> Self::ProtocolsHandler {
		NotifsHandlerProto::new(self.legacy_protocol.clone(), self.notif_protocols.clone())
	}

	fn addresses_of_peer(&mut self, _: &PeerId) -> Vec<Multiaddr> {
		Vec::new()
	}

	fn inject_connected(&mut self, peer_id: PeerId, connected_point: ConnectedPoint) {
		match (self.peers.entry(peer_id.clone()).or_insert(PeerState::Poisoned), connected_point) {
			(st @ &mut PeerState::Requested, connected_point) |
			(st @ &mut PeerState::PendingRequest { .. }, connected_point) => {
				debug!(target: "sub-libp2p", "Libp2p => Connected({:?}): Connection \
					requested by PSM (through {:?})", peer_id, connected_point
				);
				debug!(target: "sub-libp2p", "Handler({:?}) <= Enable", peer_id);
				self.events.push(NetworkBehaviourAction::SendEvent {
					peer_id: peer_id.clone(),
					event: NotifsHandlerIn::Enable,
				});
				*st = PeerState::Enabled { open: false, connected_point };
			}

			// Note: it may seem weird that "Banned" nodes get treated as if there were absent.
			// This is because the word "Banned" means "temporarily prevent outgoing connections to
			// this node", and not "banned" in the sense that we would refuse the node altogether.
			(st @ &mut PeerState::Poisoned, connected_point @ ConnectedPoint::Listener { .. }) |
			(st @ &mut PeerState::Banned { .. }, connected_point @ ConnectedPoint::Listener { .. }) => {
				let incoming_id = self.next_incoming_index.clone();
				self.next_incoming_index.0 = match self.next_incoming_index.0.checked_add(1) {
					Some(v) => v,
					None => {
						error!(target: "sub-libp2p", "Overflow in next_incoming_index");
						return
					}
				};
				debug!(target: "sub-libp2p", "Libp2p => Connected({:?}): Incoming connection",
					peer_id);
				debug!(target: "sub-libp2p", "PSM <= Incoming({:?}, {:?}): Through {:?}",
					incoming_id, peer_id, connected_point);
				self.peerset.incoming(peer_id.clone(), incoming_id);
				self.incoming.push(IncomingPeer {
					peer_id: peer_id.clone(),
					alive: true,
					incoming_id,
				});
				*st = PeerState::Incoming { connected_point };
			}

			(st @ &mut PeerState::Poisoned, connected_point) |
			(st @ &mut PeerState::Banned { .. }, connected_point) => {
				let banned_until = if let PeerState::Banned { until } = st {
					Some(*until)
				} else {
					None
				};
				debug!(target: "sub-libp2p", "Libp2p => Connected({:?}): Requested by something \
					else than PSM, disabling", peer_id);
				debug!(target: "sub-libp2p", "Handler({:?}) <= Disable", peer_id);
				self.events.push(NetworkBehaviourAction::SendEvent {
					peer_id: peer_id.clone(),
					event: NotifsHandlerIn::Disable,
				});
				*st = PeerState::Disabled { open: false, connected_point, banned_until };
			}

			st => {
				// This is a serious bug either in this state machine or in libp2p.
				error!(target: "sub-libp2p", "Received inject_connected for \
					already-connected node; state is {:?}", st
				);
			}
		}
	}

	fn inject_disconnected(&mut self, peer_id: &PeerId, endpoint: ConnectedPoint) {
		match self.peers.remove(peer_id) {
			None | Some(PeerState::Requested) | Some(PeerState::PendingRequest { .. }) |
			Some(PeerState::Banned { .. }) =>
				// This is a serious bug either in this state machine or in libp2p.
				error!(target: "sub-libp2p", "Received inject_disconnected for non-connected \
					node {:?}", peer_id),

			Some(PeerState::Disabled { open, banned_until, .. }) => {
				debug!(target: "sub-libp2p", "Libp2p => Disconnected({:?}): Was disabled \
					(through {:?})", peer_id, endpoint);
				if let Some(until) = banned_until {
					self.peers.insert(peer_id.clone(), PeerState::Banned { until });
				}
				if open {
					debug!(target: "sub-libp2p", "External API <= Closed({:?})", peer_id);
					let event = GenericProtoOut::CustomProtocolClosed {
						peer_id: peer_id.clone(),
						reason: "Disconnected by libp2p".into(),
					};

					self.events.push(NetworkBehaviourAction::GenerateEvent(event));
				}
			}

			Some(PeerState::DisabledPendingEnable { open, timer_deadline, .. }) => {
				debug!(target: "sub-libp2p", "Libp2p => Disconnected({:?}): Was disabled \
					(through {:?}) but pending enable", peer_id, endpoint);
				debug!(target: "sub-libp2p", "PSM <= Dropped({:?})", peer_id);
				self.peerset.dropped(peer_id.clone());
				self.peers.insert(peer_id.clone(), PeerState::Banned { until: timer_deadline });
				if open {
					debug!(target: "sub-libp2p", "External API <= Closed({:?})", peer_id);
					let event = GenericProtoOut::CustomProtocolClosed {
						peer_id: peer_id.clone(),
						reason: "Disconnected by libp2p".into(),
					};

					self.events.push(NetworkBehaviourAction::GenerateEvent(event));
				}
			}

			Some(PeerState::Enabled { open, .. }) => {
				debug!(target: "sub-libp2p", "Libp2p => Disconnected({:?}): Was enabled \
					(through {:?})", peer_id, endpoint);
				debug!(target: "sub-libp2p", "PSM <= Dropped({:?})", peer_id);
				self.peerset.dropped(peer_id.clone());

				let ban_dur = Uniform::new(5, 10).sample(&mut rand::thread_rng());
				self.peers.insert(peer_id.clone(), PeerState::Banned {
					until: Instant::now() + Duration::from_secs(ban_dur)
				});

				if open {
					debug!(target: "sub-libp2p", "External API <= Closed({:?})", peer_id);
					let event = GenericProtoOut::CustomProtocolClosed {
						peer_id: peer_id.clone(),
						reason: "Disconnected by libp2p".into(),
					};

					self.events.push(NetworkBehaviourAction::GenerateEvent(event));
				}
			}

			// In the incoming state, we don't report "Dropped". Instead we will just ignore the
			// corresponding Accept/Reject.
			Some(PeerState::Incoming { .. }) => {
				if let Some(state) = self.incoming.iter_mut().find(|i| i.peer_id == *peer_id) {
					debug!(target: "sub-libp2p", "Libp2p => Disconnected({:?}): Was in incoming \
						mode (id {:?}, through {:?})", peer_id, state.incoming_id, endpoint);
					state.alive = false;
				} else {
					error!(target: "sub-libp2p", "State mismatch in libp2p: no entry in incoming \
						corresponding to an incoming state in peers")
				}
			}

			Some(PeerState::Poisoned) =>
				error!(target: "sub-libp2p", "State of {:?} is poisoned", peer_id),
		}
	}

	fn inject_addr_reach_failure(&mut self, peer_id: Option<&PeerId>, addr: &Multiaddr, error: &dyn error::Error) {
		trace!(target: "sub-libp2p", "Libp2p => Reach failure for {:?} through {:?}: {:?}", peer_id, addr, error);
	}

	fn inject_dial_failure(&mut self, peer_id: &PeerId) {
		if let Entry::Occupied(mut entry) = self.peers.entry(peer_id.clone()) {
			match mem::replace(entry.get_mut(), PeerState::Poisoned) {
				// The node is not in our list.
				st @ PeerState::Banned { .. } => {
					trace!(target: "sub-libp2p", "Libp2p => Dial failure for {:?}", peer_id);
					*entry.into_mut() = st;
				},

				// "Basic" situation: we failed to reach a node that the peerset requested.
				PeerState::Requested | PeerState::PendingRequest { .. } => {
					debug!(target: "sub-libp2p", "Libp2p => Dial failure for {:?}", peer_id);
					*entry.into_mut() = PeerState::Banned {
						until: Instant::now() + Duration::from_secs(5)
					};
					debug!(target: "sub-libp2p", "PSM <= Dropped({:?})", peer_id);
					self.peerset.dropped(peer_id.clone())
				},

				// We can still get dial failures even if we are already connected to the node,
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
			// The node is not in our list.
			trace!(target: "sub-libp2p", "Libp2p => Dial failure for {:?}", peer_id);
		}
	}

	fn inject_node_event(
		&mut self,
		source: PeerId,
		event: NotifsHandlerOut,
	) {
		match event {
			NotifsHandlerOut::Closed { reason } => {
				debug!(target: "sub-libp2p", "Handler({:?}) => Closed: {}", source, reason);

				let mut entry = if let Entry::Occupied(entry) = self.peers.entry(source.clone()) {
					entry
				} else {
					error!(target: "sub-libp2p", "State mismatch in the custom protos handler");
					return
				};

				debug!(target: "sub-libp2p", "External API <= Closed({:?})", source);
				let event = GenericProtoOut::CustomProtocolClosed {
					reason,
					peer_id: source.clone(),
				};
				self.events.push(NetworkBehaviourAction::GenerateEvent(event));

				match mem::replace(entry.get_mut(), PeerState::Poisoned) {
					PeerState::Enabled { open, connected_point } => {
						debug_assert!(open);

						debug!(target: "sub-libp2p", "PSM <= Dropped({:?})", source);
						self.peerset.dropped(source.clone());

						debug!(target: "sub-libp2p", "Handler({:?}) <= Disable", source);
						self.events.push(NetworkBehaviourAction::SendEvent {
							peer_id: source.clone(),
							event: NotifsHandlerIn::Disable,
						});

						*entry.into_mut() = PeerState::Disabled {
							open: false,
							connected_point,
							banned_until: None
						};
					},
					PeerState::Disabled { open, connected_point, banned_until } => {
						debug_assert!(open);
						*entry.into_mut() = PeerState::Disabled { open: false, connected_point, banned_until };
					},
					PeerState::DisabledPendingEnable { open, connected_point, timer, timer_deadline } => {
						debug_assert!(open);
						*entry.into_mut() = PeerState::DisabledPendingEnable {
							open: false,
							connected_point,
							timer,
							timer_deadline
						};
					},
					_ => error!(target: "sub-libp2p", "State mismatch in the custom protos handler"),
				}
			}

			NotifsHandlerOut::Open => {
				debug!(target: "sub-libp2p", "Handler({:?}) => Open", source);
				let endpoint = match self.peers.get_mut(&source) {
					Some(PeerState::Enabled { ref mut open, ref connected_point }) |
					Some(PeerState::DisabledPendingEnable { ref mut open, ref connected_point, .. }) |
					Some(PeerState::Disabled { ref mut open, ref connected_point, .. }) if !*open => {
						*open = true;
						connected_point.clone()
					}
					_ => {
						error!(target: "sub-libp2p", "State mismatch in the custom protos handler");
						return
					}
				};

				debug!(target: "sub-libp2p", "External API <= Open({:?})", source);
				let event = GenericProtoOut::CustomProtocolOpen {
					peer_id: source,
					endpoint,
				};

				self.events.push(NetworkBehaviourAction::GenerateEvent(event));
			}

			NotifsHandlerOut::CustomMessage { message } => {
				debug_assert!(self.is_open(&source));
				trace!(target: "sub-libp2p", "Handler({:?}) => Message", source);
				trace!(target: "sub-libp2p", "External API <= Message({:?})", source);
				let event = GenericProtoOut::CustomMessage {
					peer_id: source,
					message,
				};

				self.events.push(NetworkBehaviourAction::GenerateEvent(event));
			}

			NotifsHandlerOut::Notification { protocol_name, engine_id, message } => {
				debug_assert!(self.is_open(&source));
				trace!(
					target: "sub-libp2p",
					"Handler({:?}) => Notification({:?})",
					source,
					str::from_utf8(&protocol_name)
				);
				trace!(target: "sub-libp2p", "External API <= Message({:?})", source);
				let event = GenericProtoOut::CustomMessage {
					peer_id: source,
					message: {
						let message = GenericMessage::<(), (), (), ()>::Consensus(ConsensusMessage {
							engine_id,
							data: message.to_vec(),
						});

						// Note that we clone `message` here.
						From::from(&message.encode()[..])
					},
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
				debug!(target: "sub-libp2p", "Handler({:?}) => Severe protocol error: {:?}",
					source, error);
				// A severe protocol error happens when we detect a "bad" node, such as a node on
				// a different chain, or a node that doesn't speak the same protocol(s). We
				// decrease the node's reputation, hence lowering the chances we try this node
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
					self.events.push(NetworkBehaviourAction::DialPeer { peer_id: peer_id.clone() });
					*peer_state = PeerState::Requested;
				}

				PeerState::DisabledPendingEnable { mut timer, connected_point, open, timer_deadline } => {
					if let Poll::Pending = Pin::new(&mut timer).poll(cx) {
						*peer_state = PeerState::DisabledPendingEnable {
							timer,
							connected_point,
							open,
							timer_deadline
						};
						continue;
					}

					debug!(target: "sub-libp2p", "Handler({:?}) <= Enable now that ban has expired", peer_id);
					self.events.push(NetworkBehaviourAction::SendEvent {
						peer_id: peer_id.clone(),
						event: NotifsHandlerIn::Enable,
					});
					*peer_state = PeerState::Enabled { connected_point, open };
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
