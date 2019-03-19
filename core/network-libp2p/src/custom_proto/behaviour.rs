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

use crate::custom_proto::handler::{CustomProtoHandler, CustomProtoHandlerOut, CustomProtoHandlerIn};
use crate::custom_proto::upgrade::{CustomMessage, RegisteredProtocol};
use fnv::FnvHashMap;
use futures::prelude::*;
use libp2p::core::swarm::{ConnectedPoint, NetworkBehaviour, NetworkBehaviourAction, PollParameters};
use libp2p::core::{protocols_handler::ProtocolsHandler, Multiaddr, PeerId};
use log::{debug, error, trace, warn};
use smallvec::SmallVec;
use std::{collections::hash_map::Entry, error, io, marker::PhantomData};
use tokio_io::{AsyncRead, AsyncWrite};

/// Network behaviour that handles opening substreams for custom protocols with other nodes.
pub struct CustomProto<TMessage, TSubstream> {
	/// List of protocols to open with peers. Never modified.
	protocol: RegisteredProtocol<TMessage>,

	/// Receiver for instructions about who to connect to or disconnect from.
	peerset: substrate_peerset::PeersetMut,

	/// List of peers in our state.
	peers: FnvHashMap<PeerId, PeerState>,

	/// List of incoming messages we have sent to the peer set manager and that are waiting for an
	/// answer.
	incoming: SmallVec<[IncomingPeer; 6]>,

	/// We generate indices to identify incoming connections. This is the next value for the index
	/// to use when a connection is incoming.
	next_incoming_index: substrate_peerset::IncomingIndex,

	/// Events to produce from `poll()`.
	events: SmallVec<[NetworkBehaviourAction<CustomProtoHandlerIn<TMessage>, CustomProtoOut<TMessage>>; 4]>,

	/// Marker to pin the generics.
	marker: PhantomData<TSubstream>,
}

/// State of a peer we're connected to.
#[derive(Debug, Clone)]
enum PeerState {
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

/// State of an "incoming" message sent to the peer set manager.
#[derive(Debug)]
struct IncomingPeer {
	/// Id of the node that is concerned.
	peer_id: PeerId,
	/// If true, this "incoming" still corresponds to an actual connection. If false, then the
	/// connection corresponding to it has been closed or replaced already.
	alive: bool,
	/// Id that the we sent to the peerset.
	incoming_id: substrate_peerset::IncomingIndex,
}

/// Event that can be emitted by the `CustomProto`.
#[derive(Debug)]
pub enum CustomProtoOut<TMessage> {
	/// Opened a custom protocol with the remote.
	CustomProtocolOpen {
		/// Version of the protocol that has been opened.
		version: u8,
		/// Id of the node we have opened a connection with.
		peer_id: PeerId,
		/// Endpoint used for this custom protocol.
		endpoint: ConnectedPoint,
	},

	/// Closed a custom protocol with the remote.
	CustomProtocolClosed {
		/// Id of the peer we were connected to.
		peer_id: PeerId,
		/// Reason why the substream closed. If `Ok`, then it's a graceful exit (EOF).
		result: io::Result<()>,
	},

	/// Receives a message on a custom protocol substream.
	CustomMessage {
		/// Id of the peer the message came from.
		peer_id: PeerId,
		/// Message that has been received.
		message: TMessage,
	},

	/// The substream used by the protocol is pretty large. We should print avoid sending more
	/// messages on it if possible.
	Clogged {
		/// Id of the peer which is clogged.
		peer_id: PeerId,
		/// Copy of the messages that are within the buffer, for further diagnostic.
		messages: Vec<TMessage>,
	},
}

impl<TMessage, TSubstream> CustomProto<TMessage, TSubstream> {
	/// Creates a `CustomProtos`.
	pub fn new(
		protocol: RegisteredProtocol<TMessage>,
		peerset: substrate_peerset::PeersetMut,
	) -> Self {
		CustomProto {
			protocol,
			peerset,
			peers: FnvHashMap::default(),
			incoming: SmallVec::new(),
			next_incoming_index: substrate_peerset::IncomingIndex(0),
			events: SmallVec::new(),
			marker: PhantomData,
		}
	}

	/// Disconnects the given peer if we are connected to it.
	pub fn disconnect_peer(&mut self, peer_id: &PeerId) {
		debug!(target: "sub-libp2p", "Disconnecting {:?} by request from the external API", peer_id);
		self.disconnect_peer_inner(peer_id);
	}

	fn disconnect_peer_inner(&mut self, peer_id: &PeerId) {
		let entry = if let Entry::Occupied(entry) = self.peers.entry(peer_id.clone()) {
			entry
		} else {
			return
		};

		match entry.get().clone() {
			// We're not connected anyway.
			PeerState::Disabled { .. } | PeerState::Requested => {},

			// Enabled => Disabled.
			PeerState::Enabled { open, connected_point } => {
				debug!(target: "sub-libp2p", "PSM <= Dropped({:?})", peer_id);
				self.peerset.dropped(peer_id);
				debug!(target: "sub-libp2p", "Handler({:?}) <= Disable", peer_id);
				self.events.push(NetworkBehaviourAction::SendEvent {
					peer_id: peer_id.clone(),
					event: CustomProtoHandlerIn::Disable,
				});
				*entry.into_mut() = PeerState::Disabled { open, connected_point }
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
					event: CustomProtoHandlerIn::Disable,
				});
				*entry.into_mut() = PeerState::Disabled { open: false, connected_point }
			},
		}
	}

	/// Returns true if we try to open protocols with the given peer.
	pub fn is_enabled(&self, peer_id: &PeerId) -> bool {
		match self.peers.get(peer_id) {
			None => false,
			Some(PeerState::Disabled { .. }) => false,
			Some(PeerState::Enabled { .. }) => true,
			Some(PeerState::Incoming { .. }) => false,
			Some(PeerState::Requested) => false,
		}
	}

	/// Returns true if we have opened a protocol with the given peer.
	pub fn is_open(&self, peer_id: &PeerId) -> bool {
		match self.peers.get(peer_id) {
			None => false,
			Some(PeerState::Disabled { open, .. }) => *open,
			Some(PeerState::Enabled { open, .. }) => *open,
			Some(PeerState::Incoming { .. }) => false,
			Some(PeerState::Requested) => false,
		}
	}

	/// Sends a message to a peer.
	///
	/// Has no effect if the custom protocol is not open with the given peer.
	///
	/// Also note that even we have a valid open substream, it may in fact be already closed
	/// without us knowing, in which case the packet will not be received.
	pub fn send_packet(&mut self, target: &PeerId, message: TMessage) {
		if !self.is_open(target) {
			return;
		}

		trace!(target: "sub-libp2p", "Handler({:?}) <= Packet", target);
		self.events.push(NetworkBehaviourAction::SendEvent {
			peer_id: target.clone(),
			event: CustomProtoHandlerIn::SendCustomMessage {
				message,
			}
		});
	}

	/// Indicates to the peerset that we have discovered new addresses for a given node.
	pub fn add_discovered_node(&mut self, peer_id: &PeerId) {
		trace!(target: "sub-libp2p", "PSM <= Discovered({:?})", peer_id);
		self.peerset.discovered(peer_id.clone())
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

		match occ_entry.get_mut().clone() {
			PeerState::Disabled { open, connected_point } => {
				debug!(target: "sub-libp2p", "PSM => Connect({:?}): Enabling previously-idle \
					connection through {:?}", occ_entry.key(), connected_point);
				debug!(target: "sub-libp2p", "Handler({:?}) <= Enable", occ_entry.key());
				self.events.push(NetworkBehaviourAction::SendEvent {
					peer_id: occ_entry.key().clone(),
					event: CustomProtoHandlerIn::Enable(connected_point.clone().into()),
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
					event: CustomProtoHandlerIn::Enable(connected_point.clone().into()),
				});
				*occ_entry.into_mut() = PeerState::Enabled { connected_point, open: false };
			},

			PeerState::Enabled { .. } =>
				warn!(target: "sub-libp2p", "PSM => Connect({:?}): Already connected to this \
					peer", occ_entry.key()),

			PeerState::Requested { .. } =>
				warn!(target: "sub-libp2p", "PSM => Connect({:?}): Received a previous \
					request for that peer", occ_entry.key()),
		}
	}

	/// Function that is called when the peerset wants us to disconnect from a node.
	fn peerset_report_disconnect(&mut self, peer_id: PeerId) {
		let entry = match self.peers.entry(peer_id) {
			Entry::Occupied(entry) => entry,
			Entry::Vacant(entry) => {
				debug!(target: "sub-libp2p", "PSM => Drop({:?}): Node already disabled", entry.key());
				return
			}
		};

		match entry.get().clone() {
			PeerState::Disabled { .. } =>
				debug!(target: "sub-libp2p", "PSM => Drop({:?}): Node already disabled", entry.key()),
			PeerState::Enabled { open, connected_point } => {
				debug!(target: "sub-libp2p", "PSM => Drop({:?}): Disabling connection", entry.key());
				debug!(target: "sub-libp2p", "Handler({:?}) <= Disable", entry.key());
				self.events.push(NetworkBehaviourAction::SendEvent {
					peer_id: entry.key().clone(),
					event: CustomProtoHandlerIn::Disable,
				});
				*entry.into_mut() = PeerState::Disabled { open, connected_point }
			},
			PeerState::Incoming { .. } =>
				error!(target: "sub-libp2p", "PSM => Drop({:?}): Was in incoming mode",
					entry.key()),
			PeerState::Requested => {
				// We don't cancel dialing. Libp2p doesn't expose that on purpose, as other
				// sub-systems (such as the discovery mechanism) may require dialing this node as
				// well at the same time.
				debug!(target: "sub-libp2p", "PSM => Drop({:?}): Was not yet connected", entry.key());
				entry.remove();
			},
		}
	}

	/// Function that is called when the peerset wants us to accept an incoming node.
	fn peerset_report_accept(&mut self, index: substrate_peerset::IncomingIndex) {
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
			self.peerset.dropped(&incoming.peer_id);
			return
		}

		let state = if let Some(state) = self.peers.get_mut(&incoming.peer_id) {
			state
		} else {
			error!(target: "sub-libp2p", "State mismatch in libp2p: no entry in peers \
				corresponding to an alive incoming");
			return
		};

		let connected_point = if let PeerState::Incoming { connected_point, .. } = state {
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
			event: CustomProtoHandlerIn::Enable(connected_point.clone().into()),
		});

		*state = PeerState::Enabled { open: false, connected_point };
	}

	/// Function that is called when the peerset wants us to reject an incoming node.
	fn peerset_report_reject(&mut self, index: substrate_peerset::IncomingIndex) {
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

		let connected_point = if let PeerState::Incoming { connected_point, .. } = state {
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
			event: CustomProtoHandlerIn::Disable,
		});
		*state = PeerState::Disabled { open: false, connected_point };
	}
}

impl<TMessage, TSubstream> NetworkBehaviour for CustomProto<TMessage, TSubstream>
where
	TSubstream: AsyncRead + AsyncWrite,
	TMessage: CustomMessage,
{
	type ProtocolsHandler = CustomProtoHandler<TMessage, TSubstream>;
	type OutEvent = CustomProtoOut<TMessage>;

	fn new_handler(&mut self) -> Self::ProtocolsHandler {
		CustomProtoHandler::new(self.protocol.clone())
	}

	fn addresses_of_peer(&mut self, _: &PeerId) -> Vec<Multiaddr> {
		Vec::new()
	}

	fn inject_connected(&mut self, peer_id: PeerId, connected_point: ConnectedPoint) {
		match (self.peers.entry(peer_id), connected_point) {
			(Entry::Occupied(mut entry), connected_point) => {
				match entry.get_mut().clone() {
					PeerState::Requested => {
						debug!(target: "sub-libp2p", "Libp2p => Connected({:?}): Connection \
							requested by PSM (through {:?})", entry.key(), connected_point);
						debug!(target: "sub-libp2p", "Handler({:?}) <= Enable", entry.key());
						self.events.push(NetworkBehaviourAction::SendEvent {
							peer_id: entry.key().clone(),
							event: CustomProtoHandlerIn::Enable(connected_point.clone().into()),
						});
						*entry.into_mut() = PeerState::Enabled { open: false, connected_point };
					}
					_ => {
						// This is a serious bug either in this state machine or in libp2p.
						error!(target: "sub-libp2p", "Received inject_connected for \
							already-connected node");
						return
					}
				}
			}

			(Entry::Vacant(entry), connected_point @ ConnectedPoint::Listener { .. }) => {
				let incoming_id = self.next_incoming_index.clone();
				self.next_incoming_index.0 = match self.next_incoming_index.0.checked_add(1) {
					Some(v) => v,
					None => {
						error!(target: "sub-libp2p", "Overflow in next_incoming_index");
						return
					}
				};
				debug!(target: "sub-libp2p", "Libp2p => Connected({:?}): Incoming connection",
					entry.key());
				debug!(target: "sub-libp2p", "PSM <= Incoming({:?}, {:?}): Through {:?}",
					incoming_id, entry.key(), connected_point);
				self.peerset.incoming(entry.key().clone(), incoming_id);
				self.incoming.push(IncomingPeer {
					peer_id: entry.key().clone(),
					alive: true,
					incoming_id,
				});
				entry.insert(PeerState::Incoming { connected_point });
			}

			(Entry::Vacant(entry), connected_point) => {
				debug!(target: "sub-libp2p", "Libp2p => Connected({:?}): Requested by something \
					else than PSM, disabling", entry.key());
				debug!(target: "sub-libp2p", "Handler({:?}) <= Disable", entry.key());
				self.events.push(NetworkBehaviourAction::SendEvent {
					peer_id: entry.key().clone(),
					event: CustomProtoHandlerIn::Disable,
				});
				entry.insert(PeerState::Disabled { open: false, connected_point });
			}
		}
	}

	fn inject_disconnected(&mut self, peer_id: &PeerId, endpoint: ConnectedPoint) {
		match self.peers.remove(peer_id) {
			None | Some(PeerState::Requested) =>
				// This is a serious bug either in this state machine or in libp2p.
				error!(target: "sub-libp2p", "Received inject_disconnected for non-connected \
					node {:?}", peer_id),

			Some(PeerState::Disabled { open, .. }) => {
				debug!(target: "sub-libp2p", "Libp2p => Disconnected({:?}): Was disabled \
					(through {:?})", peer_id, endpoint);
				if open {
					debug!(target: "sub-libp2p", "External API <= Closed({:?})", peer_id);
					let event = CustomProtoOut::CustomProtocolClosed {
						peer_id: peer_id.clone(),
						result: Ok(()),
					};

					self.events.push(NetworkBehaviourAction::GenerateEvent(event));
				}
			}

			Some(PeerState::Enabled { open, .. }) => {
				debug!(target: "sub-libp2p", "Libp2p => Disconnected({:?}): Was enabled \
					(through {:?})", peer_id, endpoint);
				debug!(target: "sub-libp2p", "PSM <= Dropped({:?})", peer_id);
				self.peerset.dropped(peer_id);

				if open {
					debug!(target: "sub-libp2p", "External API <= Closed({:?})", peer_id);
					let event = CustomProtoOut::CustomProtocolClosed {
						peer_id: peer_id.clone(),
						result: Ok(()),
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
		}
	}

	fn inject_addr_reach_failure(&mut self, peer_id: Option<&PeerId>, addr: &Multiaddr, error: &dyn error::Error) {
		debug!(target: "sub-libp2p", "Libp2p => Reach failure for {:?} through {:?}: {:?}", peer_id, addr, error);
	}

	fn inject_dial_failure(&mut self, peer_id: &PeerId) {
		if let Entry::Occupied(entry) = self.peers.entry(peer_id.clone()) {
			match entry.get() {
				// "Basic" situation: we failed to reach a node that the peerset requested.
				PeerState::Requested => {
					debug!(target: "sub-libp2p", "Libp2p => Dial failure for {:?}", peer_id);
					debug!(target: "sub-libp2p", "PSM <= Dropped({:?})", peer_id);
					entry.remove();
					self.peerset.dropped(peer_id)
				},

				// We can still get dial failures even if we are already connected to the node,
				// as an extra diagnostic for an earlier attempt.
				PeerState::Disabled { .. } | PeerState::Enabled { .. } |
					PeerState::Incoming { .. } =>
					debug!(target: "sub-libp2p", "Libp2p => Dial failure for {:?}", peer_id),
			}

		} else {
			// The node is not in our list.
			trace!(target: "sub-libp2p", "Libp2p => Dial failure for {:?}", peer_id);
		}
	}

	fn inject_node_event(
		&mut self,
		source: PeerId,
		event: <Self::ProtocolsHandler as ProtocolsHandler>::OutEvent,
	) {
		match event {
			CustomProtoHandlerOut::CustomProtocolClosed { result } => {
				debug!(target: "sub-libp2p", "Handler({:?}) => Closed({:?})", source, result);
				match self.peers.get_mut(&source) {
					Some(PeerState::Enabled { ref mut open, .. }) if *open =>
						*open = false,
					Some(PeerState::Disabled { ref mut open, .. }) if *open =>
						*open = false,
					_ => error!(target: "sub-libp2p", "State mismatch in the custom protos handler"),
				}

				debug!(target: "sub-libp2p", "External API <= Closed({:?})", source);
				let event = CustomProtoOut::CustomProtocolClosed {
					result,
					peer_id: source,
				};

				self.events.push(NetworkBehaviourAction::GenerateEvent(event));
			}

			CustomProtoHandlerOut::CustomProtocolOpen { version } => {
				debug!(target: "sub-libp2p", "Handler({:?}) => Open: version {:?}", source, version);
				let endpoint = match self.peers.get_mut(&source) {
					Some(PeerState::Enabled { ref mut open, ref connected_point }) |
					Some(PeerState::Disabled { ref mut open, ref connected_point }) if !*open => {
						*open = true;
						connected_point.clone()
					}
					_ => {
						error!(target: "sub-libp2p", "State mismatch in the custom protos handler");
						return
					}
				};

				debug!(target: "sub-libp2p", "External API <= Open({:?})", source);
				let event = CustomProtoOut::CustomProtocolOpen {
					version,
					peer_id: source,
					endpoint,
				};

				self.events.push(NetworkBehaviourAction::GenerateEvent(event));
			}

			CustomProtoHandlerOut::CustomMessage { message } => {
				debug_assert!(self.is_open(&source));
				trace!(target: "sub-libp2p", "Handler({:?}) => Message", source);
				trace!(target: "sub-libp2p", "External API <= Message({:?})", source);
				let event = CustomProtoOut::CustomMessage {
					peer_id: source,
					message,
				};

				self.events.push(NetworkBehaviourAction::GenerateEvent(event));
			}

			CustomProtoHandlerOut::Clogged { messages } => {
				debug_assert!(self.is_open(&source));
				trace!(target: "sub-libp2p", "Handler({:?}) => Clogged", source);
				trace!(target: "sub-libp2p", "External API <= Clogged({:?})", source);
				warn!(target: "sub-libp2p", "Queue of packets to send to {:?} is \
					pretty large", source);
				self.events.push(NetworkBehaviourAction::GenerateEvent(CustomProtoOut::Clogged {
					peer_id: source,
					messages,
				}));
			}

			// Don't do anything for non-severe errors except report them.
			CustomProtoHandlerOut::ProtocolError { is_severe, ref error } if !is_severe => {
				debug!(target: "sub-libp2p", "Handler({:?}) => Benign protocol error: {:?}",
					source, error)
			}

			CustomProtoHandlerOut::ProtocolError { error, .. } => {
				debug!(target: "sub-libp2p", "Handler({:?}) => Severe protocol error: {:?}",
					source, error);
				self.disconnect_peer_inner(&source);
			}
		}
	}

	fn poll(
		&mut self,
		_params: &mut PollParameters,
	) -> Async<
		NetworkBehaviourAction<
			<Self::ProtocolsHandler as ProtocolsHandler>::InEvent,
			Self::OutEvent,
		>,
	> {
		// Poll for instructions from the peerset.
		// Note that the peerset is a *best effort* crate, and we have to use defensive programming.
		loop {
			match self.peerset.poll() {
				Ok(Async::Ready(Some(substrate_peerset::Message::Accept(index)))) => {
					self.peerset_report_accept(index);
				}
				Ok(Async::Ready(Some(substrate_peerset::Message::Reject(index)))) => {
					self.peerset_report_reject(index);
				}
				Ok(Async::Ready(Some(substrate_peerset::Message::Connect(id)))) => {
					self.peerset_report_connect(id);
				}
				Ok(Async::Ready(Some(substrate_peerset::Message::Drop(id)))) => {
					self.peerset_report_disconnect(id);
				}
				Ok(Async::Ready(None)) => {
					error!(target: "sub-libp2p", "Peerset receiver stream has returned None");
					break;
				}
				Ok(Async::NotReady) => break,
				Err(err) => {
					error!(target: "sub-libp2p", "Peerset receiver stream has errored: {:?}", err);
					break
				}
			}
		}

		if !self.events.is_empty() {
			return Async::Ready(self.events.remove(0))
		}

		Async::NotReady
	}
}
