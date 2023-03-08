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

use crate::config;

use bytes::Bytes;
use codec::{DecodeAll, Encode};
use libp2p::{
	core::connection::ConnectionId,
	swarm::{
		behaviour::FromSwarm, ConnectionHandler, IntoConnectionHandler, NetworkBehaviour,
		NetworkBehaviourAction, PollParameters,
	},
	Multiaddr, PeerId,
};
use log::{debug, error, warn};
use message::{generic::Message as GenericMessage, Message};
use notifications::{Notifications, NotificationsOut};
use sc_network_common::{
	config::NonReservedPeerMode,
	error,
	protocol::{role::Roles, ProtocolName},
	sync::message::BlockAnnouncesHandshake,
};
use sp_runtime::traits::Block as BlockT;
use std::{
	collections::{HashMap, HashSet, VecDeque},
	iter,
	task::Poll,
};

mod notifications;

pub mod message;

pub use notifications::{NotificationsSink, NotifsHandlerError, Ready};

/// Maximum size used for notifications in the block announce and transaction protocols.
// Must be equal to `max(MAX_BLOCK_ANNOUNCE_SIZE, MAX_TRANSACTIONS_SIZE)`.
pub(crate) const BLOCK_ANNOUNCES_TRANSACTIONS_SUBSTREAM_SIZE: u64 = 16 * 1024 * 1024;

/// Identifier of the peerset for the block announces protocol.
const HARDCODED_PEERSETS_SYNC: sc_peerset::SetId = sc_peerset::SetId::from(0);
/// Number of hardcoded peersets (the constants right above). Any set whose identifier is equal or
/// superior to this value corresponds to a user-defined protocol.
const NUM_HARDCODED_PEERSETS: usize = 1;

mod rep {
	use sc_peerset::ReputationChange as Rep;
	/// We received a message that failed to decode.
	pub const BAD_MESSAGE: Rep = Rep::new(-(1 << 12), "Bad message");
}

// Lock must always be taken in order declared here.
pub struct Protocol<B: BlockT> {
	/// Pending list of messages to return from `poll` as a priority.
	pending_messages: VecDeque<CustomMessageOutcome>,
	/// Used to report reputation changes.
	peerset_handle: sc_peerset::PeersetHandle,
	/// Handles opening the unique substream and sending and receiving raw messages.
	behaviour: Notifications,
	/// List of notifications protocols that have been registered.
	notification_protocols: Vec<ProtocolName>,
	/// If we receive a new "substream open" event that contains an invalid handshake, we ask the
	/// inner layer to force-close the substream. Force-closing the substream will generate a
	/// "substream closed" event. This is a problem: since we can't propagate the "substream open"
	/// event to the outer layers, we also shouldn't propagate this "substream closed" event. To
	/// solve this, an entry is added to this map whenever an invalid handshake is received.
	/// Entries are removed when the corresponding "substream closed" is later received.
	bad_handshake_substreams: HashSet<(PeerId, sc_peerset::SetId)>,
	/// Connected peers.
	peers: HashMap<PeerId, Roles>,
	_marker: std::marker::PhantomData<B>,
}

impl<B: BlockT> Protocol<B> {
	/// Create a new instance.
	pub fn new(
		roles: Roles,
		network_config: &config::NetworkConfiguration,
		block_announces_protocol: sc_network_common::config::NonDefaultSetConfig,
	) -> error::Result<(Self, sc_peerset::PeersetHandle, Vec<(PeerId, Multiaddr)>)> {
		let mut known_addresses = Vec::new();

		let (peerset, peerset_handle) = {
			let mut sets =
				Vec::with_capacity(NUM_HARDCODED_PEERSETS + network_config.extra_sets.len());

			let mut default_sets_reserved = HashSet::new();
			for reserved in network_config.default_peers_set.reserved_nodes.iter() {
				default_sets_reserved.insert(reserved.peer_id);

				if !reserved.multiaddr.is_empty() {
					known_addresses.push((reserved.peer_id, reserved.multiaddr.clone()));
				}
			}

			let mut bootnodes = Vec::with_capacity(network_config.boot_nodes.len());
			for bootnode in network_config.boot_nodes.iter() {
				bootnodes.push(bootnode.peer_id);
			}

			// Set number 0 is used for block announces.
			sets.push(sc_peerset::SetConfig {
				in_peers: network_config.default_peers_set.in_peers,
				out_peers: network_config.default_peers_set.out_peers,
				bootnodes,
				reserved_nodes: default_sets_reserved.clone(),
				reserved_only: network_config.default_peers_set.non_reserved_mode ==
					NonReservedPeerMode::Deny,
			});

			for set_cfg in &network_config.extra_sets {
				let mut reserved_nodes = HashSet::new();
				for reserved in set_cfg.set_config.reserved_nodes.iter() {
					reserved_nodes.insert(reserved.peer_id);
					known_addresses.push((reserved.peer_id, reserved.multiaddr.clone()));
				}

				let reserved_only =
					set_cfg.set_config.non_reserved_mode == NonReservedPeerMode::Deny;

				sets.push(sc_peerset::SetConfig {
					in_peers: set_cfg.set_config.in_peers,
					out_peers: set_cfg.set_config.out_peers,
					bootnodes: Vec::new(),
					reserved_nodes,
					reserved_only,
				});
			}

			sc_peerset::Peerset::from_config(sc_peerset::PeersetConfig { sets })
		};

		let behaviour = {
			Notifications::new(
				peerset,
				// NOTE: Block announcement protocol is still very much hardcoded into `Protocol`.
				// 	This protocol must be the first notification protocol given to
				// `Notifications`
				iter::once(notifications::ProtocolConfig {
					name: block_announces_protocol.notifications_protocol.clone(),
					fallback_names: block_announces_protocol.fallback_names.clone(),
					handshake: block_announces_protocol.handshake.as_ref().unwrap().to_vec(),
					max_notification_size: block_announces_protocol.max_notification_size,
				})
				.chain(network_config.extra_sets.iter().map(|s| notifications::ProtocolConfig {
					name: s.notifications_protocol.clone(),
					fallback_names: s.fallback_names.clone(),
					handshake: s.handshake.as_ref().map_or(roles.encode(), |h| (*h).to_vec()),
					max_notification_size: s.max_notification_size,
				})),
			)
		};

		let protocol = Self {
			pending_messages: VecDeque::new(),
			peerset_handle: peerset_handle.clone(),
			behaviour,
			notification_protocols: iter::once(block_announces_protocol.notifications_protocol)
				.chain(network_config.extra_sets.iter().map(|s| s.notifications_protocol.clone()))
				.collect(),
			bad_handshake_substreams: Default::default(),
			peers: HashMap::new(),
			// TODO: remove when `BlockAnnouncesHandshake` is moved away from `Protocol`
			_marker: Default::default(),
		};

		Ok((protocol, peerset_handle, known_addresses))
	}

	/// Returns the list of all the peers we have an open channel to.
	pub fn open_peers(&self) -> impl Iterator<Item = &PeerId> {
		self.behaviour.open_peers()
	}

	/// Returns the number of discovered nodes that we keep in memory.
	pub fn num_discovered_peers(&self) -> usize {
		self.behaviour.num_discovered_peers()
	}

	/// Disconnects the given peer if we are connected to it.
	pub fn disconnect_peer(&mut self, peer_id: &PeerId, protocol_name: ProtocolName) {
		if let Some(position) = self.notification_protocols.iter().position(|p| *p == protocol_name)
		{
			self.behaviour.disconnect_peer(peer_id, sc_peerset::SetId::from(position));
			self.peers.remove(peer_id);
		} else {
			warn!(target: "sub-libp2p", "disconnect_peer() with invalid protocol name")
		}
	}

	/// Returns the state of the peerset manager, for debugging purposes.
	pub fn peerset_debug_info(&mut self) -> serde_json::Value {
		self.behaviour.peerset_debug_info()
	}

	/// Returns the number of peers we're connected to.
	pub fn num_connected_peers(&self) -> usize {
		self.peers.len()
	}

	/// Adjusts the reputation of a node.
	pub fn report_peer(&self, who: PeerId, reputation: sc_peerset::ReputationChange) {
		self.peerset_handle.report_peer(who, reputation)
	}

	/// Set handshake for the notification protocol.
	pub fn set_notification_handshake(&mut self, protocol: ProtocolName, handshake: Vec<u8>) {
		if let Some(index) = self.notification_protocols.iter().position(|p| *p == protocol) {
			self.behaviour
				.set_notif_protocol_handshake(sc_peerset::SetId::from(index), handshake);
		} else {
			error!(
				target: "sub-libp2p",
				"set_notification_handshake with unknown protocol: {}",
				protocol
			);
		}
	}

	/// Set whether the syncing peers set is in reserved-only mode.
	pub fn set_reserved_only(&self, reserved_only: bool) {
		self.peerset_handle.set_reserved_only(HARDCODED_PEERSETS_SYNC, reserved_only);
	}

	/// Removes a `PeerId` from the list of reserved peers for syncing purposes.
	pub fn remove_reserved_peer(&self, peer: PeerId) {
		self.peerset_handle.remove_reserved_peer(HARDCODED_PEERSETS_SYNC, peer);
	}

	/// Returns the list of reserved peers.
	pub fn reserved_peers(&self) -> impl Iterator<Item = &PeerId> {
		self.behaviour.reserved_peers(HARDCODED_PEERSETS_SYNC)
	}

	/// Adds a `PeerId` to the list of reserved peers for syncing purposes.
	pub fn add_reserved_peer(&self, peer: PeerId) {
		self.peerset_handle.add_reserved_peer(HARDCODED_PEERSETS_SYNC, peer);
	}

	/// Sets the list of reserved peers for syncing purposes.
	pub fn set_reserved_peers(&self, peers: HashSet<PeerId>) {
		self.peerset_handle.set_reserved_peers(HARDCODED_PEERSETS_SYNC, peers);
	}

	/// Sets the list of reserved peers for the given protocol/peerset.
	pub fn set_reserved_peerset_peers(&self, protocol: ProtocolName, peers: HashSet<PeerId>) {
		if let Some(index) = self.notification_protocols.iter().position(|p| *p == protocol) {
			self.peerset_handle.set_reserved_peers(sc_peerset::SetId::from(index), peers);
		} else {
			error!(
				target: "sub-libp2p",
				"set_reserved_peerset_peers with unknown protocol: {}",
				protocol
			);
		}
	}

	/// Removes a `PeerId` from the list of reserved peers.
	pub fn remove_set_reserved_peer(&self, protocol: ProtocolName, peer: PeerId) {
		if let Some(index) = self.notification_protocols.iter().position(|p| *p == protocol) {
			self.peerset_handle.remove_reserved_peer(sc_peerset::SetId::from(index), peer);
		} else {
			error!(
				target: "sub-libp2p",
				"remove_set_reserved_peer with unknown protocol: {}",
				protocol
			);
		}
	}

	/// Adds a `PeerId` to the list of reserved peers.
	pub fn add_set_reserved_peer(&self, protocol: ProtocolName, peer: PeerId) {
		if let Some(index) = self.notification_protocols.iter().position(|p| *p == protocol) {
			self.peerset_handle.add_reserved_peer(sc_peerset::SetId::from(index), peer);
		} else {
			error!(
				target: "sub-libp2p",
				"add_set_reserved_peer with unknown protocol: {}",
				protocol
			);
		}
	}

	/// Notify the protocol that we have learned about the existence of nodes on the default set.
	///
	/// Can be called multiple times with the same `PeerId`s.
	pub fn add_default_set_discovered_nodes(&mut self, peer_ids: impl Iterator<Item = PeerId>) {
		for peer_id in peer_ids {
			self.peerset_handle.add_to_peers_set(HARDCODED_PEERSETS_SYNC, peer_id);
		}
	}

	/// Add a peer to a peers set.
	pub fn add_to_peers_set(&self, protocol: ProtocolName, peer: PeerId) {
		if let Some(index) = self.notification_protocols.iter().position(|p| *p == protocol) {
			self.peerset_handle.add_to_peers_set(sc_peerset::SetId::from(index), peer);
		} else {
			error!(
				target: "sub-libp2p",
				"add_to_peers_set with unknown protocol: {}",
				protocol
			);
		}
	}

	/// Remove a peer from a peers set.
	pub fn remove_from_peers_set(&self, protocol: ProtocolName, peer: PeerId) {
		if let Some(index) = self.notification_protocols.iter().position(|p| *p == protocol) {
			self.peerset_handle.remove_from_peers_set(sc_peerset::SetId::from(index), peer);
		} else {
			error!(
				target: "sub-libp2p",
				"remove_from_peers_set with unknown protocol: {}",
				protocol
			);
		}
	}
}

/// Outcome of an incoming custom message.
#[derive(Debug)]
#[must_use]
pub enum CustomMessageOutcome {
	/// Notification protocols have been opened with a remote.
	NotificationStreamOpened {
		remote: PeerId,
		protocol: ProtocolName,
		/// See [`crate::Event::NotificationStreamOpened::negotiated_fallback`].
		negotiated_fallback: Option<ProtocolName>,
		roles: Roles,
		received_handshake: Vec<u8>,
		notifications_sink: NotificationsSink,
	},
	/// The [`NotificationsSink`] of some notification protocols need an update.
	NotificationStreamReplaced {
		remote: PeerId,
		protocol: ProtocolName,
		notifications_sink: NotificationsSink,
	},
	/// Notification protocols have been closed with a remote.
	NotificationStreamClosed { remote: PeerId, protocol: ProtocolName },
	/// Messages have been received on one or more notifications protocols.
	NotificationsReceived { remote: PeerId, messages: Vec<(ProtocolName, Bytes)> },
	/// Now connected to a new peer for syncing purposes.
	None,
}

impl<B: BlockT> NetworkBehaviour for Protocol<B> {
	type ConnectionHandler = <Notifications as NetworkBehaviour>::ConnectionHandler;
	type OutEvent = CustomMessageOutcome;

	fn new_handler(&mut self) -> Self::ConnectionHandler {
		self.behaviour.new_handler()
	}

	fn addresses_of_peer(&mut self, _: &PeerId) -> Vec<Multiaddr> {
		// Only `Discovery::addresses_of_peer` must be returning addresses to ensure that we
		// don't return unwanted addresses.
		Vec::new()
	}

	fn on_swarm_event(&mut self, event: FromSwarm<Self::ConnectionHandler>) {
		self.behaviour.on_swarm_event(event);
	}

	fn on_connection_handler_event(
		&mut self,
		peer_id: PeerId,
		connection_id: ConnectionId,
		event: <<Self::ConnectionHandler as IntoConnectionHandler>::Handler as
		ConnectionHandler>::OutEvent,
	) {
		self.behaviour.on_connection_handler_event(peer_id, connection_id, event);
	}

	fn poll(
		&mut self,
		cx: &mut std::task::Context,
		params: &mut impl PollParameters,
	) -> Poll<NetworkBehaviourAction<Self::OutEvent, Self::ConnectionHandler>> {
		if let Some(message) = self.pending_messages.pop_front() {
			return Poll::Ready(NetworkBehaviourAction::GenerateEvent(message))
		}

		let event = match self.behaviour.poll(cx, params) {
			Poll::Pending => return Poll::Pending,
			Poll::Ready(NetworkBehaviourAction::GenerateEvent(ev)) => ev,
			Poll::Ready(NetworkBehaviourAction::Dial { opts, handler }) =>
				return Poll::Ready(NetworkBehaviourAction::Dial { opts, handler }),
			Poll::Ready(NetworkBehaviourAction::NotifyHandler { peer_id, handler, event }) =>
				return Poll::Ready(NetworkBehaviourAction::NotifyHandler {
					peer_id,
					handler,
					event,
				}),
			Poll::Ready(NetworkBehaviourAction::ReportObservedAddr { address, score }) =>
				return Poll::Ready(NetworkBehaviourAction::ReportObservedAddr { address, score }),
			Poll::Ready(NetworkBehaviourAction::CloseConnection { peer_id, connection }) =>
				return Poll::Ready(NetworkBehaviourAction::CloseConnection { peer_id, connection }),
		};

		let outcome = match event {
			NotificationsOut::CustomProtocolOpen {
				peer_id,
				set_id,
				received_handshake,
				notifications_sink,
				negotiated_fallback,
			} => {
				// Set number 0 is hardcoded the default set of peers we sync from.
				if set_id == HARDCODED_PEERSETS_SYNC {
					// `received_handshake` can be either a `Status` message if received from the
					// legacy substream ,or a `BlockAnnouncesHandshake` if received from the block
					// announces substream.
					match <Message<B> as DecodeAll>::decode_all(&mut &received_handshake[..]) {
						Ok(GenericMessage::Status(handshake)) => {
							let roles = handshake.roles;
							let handshake = BlockAnnouncesHandshake::<B> {
								roles: handshake.roles,
								best_number: handshake.best_number,
								best_hash: handshake.best_hash,
								genesis_hash: handshake.genesis_hash,
							};
							self.peers.insert(peer_id, roles);

							CustomMessageOutcome::NotificationStreamOpened {
								remote: peer_id,
								protocol: self.notification_protocols[usize::from(set_id)].clone(),
								negotiated_fallback,
								received_handshake: handshake.encode(),
								roles,
								notifications_sink,
							}
						},
						Ok(msg) => {
							debug!(
								target: "sync",
								"Expected Status message from {}, but got {:?}",
								peer_id,
								msg,
							);
							self.peerset_handle.report_peer(peer_id, rep::BAD_MESSAGE);
							CustomMessageOutcome::None
						},
						Err(err) => {
							match <BlockAnnouncesHandshake<B> as DecodeAll>::decode_all(
								&mut &received_handshake[..],
							) {
								Ok(handshake) => {
									let roles = handshake.roles;
									self.peers.insert(peer_id, roles);

									CustomMessageOutcome::NotificationStreamOpened {
										remote: peer_id,
										protocol: self.notification_protocols[usize::from(set_id)]
											.clone(),
										negotiated_fallback,
										received_handshake,
										roles,
										notifications_sink,
									}
								},
								Err(err2) => {
									log::debug!(
										target: "sync",
										"Couldn't decode handshake sent by {}: {:?}: {} & {}",
										peer_id,
										received_handshake,
										err,
										err2,
									);
									self.peerset_handle.report_peer(peer_id, rep::BAD_MESSAGE);
									CustomMessageOutcome::None
								},
							}
						},
					}
				} else {
					match (
						Roles::decode_all(&mut &received_handshake[..]),
						self.peers.get(&peer_id),
					) {
						(Ok(roles), _) => CustomMessageOutcome::NotificationStreamOpened {
							remote: peer_id,
							protocol: self.notification_protocols[usize::from(set_id)].clone(),
							negotiated_fallback,
							roles,
							received_handshake,
							notifications_sink,
						},
						(Err(_), Some(roles)) if received_handshake.is_empty() => {
							// As a convenience, we allow opening substreams for "external"
							// notification protocols with an empty handshake. This fetches the
							// roles from the locally-known roles.
							// TODO: remove this after https://github.com/paritytech/substrate/issues/5685
							CustomMessageOutcome::NotificationStreamOpened {
								remote: peer_id,
								protocol: self.notification_protocols[usize::from(set_id)].clone(),
								negotiated_fallback,
								roles: *roles,
								received_handshake,
								notifications_sink,
							}
						},
						(Err(err), _) => {
							debug!(target: "sync", "Failed to parse remote handshake: {}", err);
							self.bad_handshake_substreams.insert((peer_id, set_id));
							self.behaviour.disconnect_peer(&peer_id, set_id);
							self.peerset_handle.report_peer(peer_id, rep::BAD_MESSAGE);
							self.peers.remove(&peer_id);
							CustomMessageOutcome::None
						},
					}
				}
			},
			NotificationsOut::CustomProtocolReplaced { peer_id, notifications_sink, set_id } =>
				if self.bad_handshake_substreams.contains(&(peer_id, set_id)) {
					CustomMessageOutcome::None
				} else {
					CustomMessageOutcome::NotificationStreamReplaced {
						remote: peer_id,
						protocol: self.notification_protocols[usize::from(set_id)].clone(),
						notifications_sink,
					}
				},
			NotificationsOut::CustomProtocolClosed { peer_id, set_id } => {
				if self.bad_handshake_substreams.remove(&(peer_id, set_id)) {
					// The substream that has just been closed had been opened with a bad
					// handshake. The outer layers have never received an opening event about this
					// substream, and consequently shouldn't receive a closing event either.
					CustomMessageOutcome::None
				} else {
					CustomMessageOutcome::NotificationStreamClosed {
						remote: peer_id,
						protocol: self.notification_protocols[usize::from(set_id)].clone(),
					}
				}
			},
			NotificationsOut::Notification { peer_id, set_id, message } => {
				if self.bad_handshake_substreams.contains(&(peer_id, set_id)) {
					CustomMessageOutcome::None
				} else {
					let protocol_name = self.notification_protocols[usize::from(set_id)].clone();
					CustomMessageOutcome::NotificationsReceived {
						remote: peer_id,
						messages: vec![(protocol_name, message.freeze())],
					}
				}
			},
		};

		if !matches!(outcome, CustomMessageOutcome::None) {
			return Poll::Ready(NetworkBehaviourAction::GenerateEvent(outcome))
		}

		if let Some(message) = self.pending_messages.pop_front() {
			return Poll::Ready(NetworkBehaviourAction::GenerateEvent(message))
		}

		// This block can only be reached if an event was pulled from the behaviour and that
		// resulted in `CustomMessageOutcome::None`. Since there might be another pending
		// message from the behaviour, the task is scheduled again.
		cx.waker().wake_by_ref();
		Poll::Pending
	}
}
