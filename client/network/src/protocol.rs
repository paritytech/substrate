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

use crate::{
	config, error,
	peer_store::{PeerStoreHandle, PeerStoreProvider},
	protocol_controller::{self, SetId},
	types::ProtocolName,
};

use bytes::Bytes;
use codec::{DecodeAll, Encode};
use futures::{channel::oneshot, stream::FuturesUnordered, StreamExt};
use libp2p::{
	core::Endpoint,
	swarm::{
		behaviour::FromSwarm, ConnectionDenied, ConnectionId, NetworkBehaviour, PollParameters,
		THandler, THandlerInEvent, THandlerOutEvent, ToSwarm,
	},
	Multiaddr, PeerId,
};
use log::{debug, error, warn};

use sc_network_common::{role::Roles, sync::message::BlockAnnouncesHandshake};
use sc_utils::mpsc::{TracingUnboundedReceiver, TracingUnboundedSender};
use sp_runtime::traits::Block as BlockT;

use std::{
	collections::{HashMap, HashSet},
	future::Future,
	iter,
	pin::Pin,
	task::Poll,
};

use message::{generic::Message as GenericMessage, Message};
use notifications::{Notifications, NotificationsOut};

pub use notifications::{NotificationsSink, NotifsHandlerError, Ready};

mod notifications;

pub mod message;

/// Maximum size used for notifications in the block announce and transaction protocols.
// Must be equal to `max(MAX_BLOCK_ANNOUNCE_SIZE, MAX_TRANSACTIONS_SIZE)`.
pub(crate) const BLOCK_ANNOUNCES_TRANSACTIONS_SUBSTREAM_SIZE: u64 = 16 * 1024 * 1024;

/// Identifier of the peerset for the block announces protocol.
const HARDCODED_PEERSETS_SYNC: SetId = SetId::from(0);

mod rep {
	use crate::ReputationChange as Rep;
	/// We received a message that failed to decode.
	pub const BAD_MESSAGE: Rep = Rep::new(-(1 << 12), "Bad message");
}

type PendingSyncSubstreamValidation =
	Pin<Box<dyn Future<Output = Result<(PeerId, Roles), PeerId>> + Send>>;

// Lock must always be taken in order declared here.
pub struct Protocol<B: BlockT> {
	/// Used to report reputation changes.
	peer_store_handle: PeerStoreHandle,
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
	bad_handshake_substreams: HashSet<(PeerId, SetId)>,
	/// Connected peers on sync protocol.
	peers: HashMap<PeerId, Roles>,
	sync_substream_validations: FuturesUnordered<PendingSyncSubstreamValidation>,
	tx: TracingUnboundedSender<crate::event::SyncEvent<B>>,
	_marker: std::marker::PhantomData<B>,
}

impl<B: BlockT> Protocol<B> {
	/// Create a new instance.
	pub fn new(
		roles: Roles,
		notification_protocols: Vec<config::NonDefaultSetConfig>,
		block_announces_protocol: config::NonDefaultSetConfig,
		peer_store_handle: PeerStoreHandle,
		protocol_controller_handles: Vec<protocol_controller::ProtocolHandle>,
		from_protocol_controllers: TracingUnboundedReceiver<protocol_controller::Message>,
		tx: TracingUnboundedSender<crate::event::SyncEvent<B>>,
	) -> error::Result<Self> {
		let behaviour = {
			Notifications::new(
				protocol_controller_handles,
				from_protocol_controllers,
				// NOTE: Block announcement protocol is still very much hardcoded into `Protocol`.
				// 	This protocol must be the first notification protocol given to
				// `Notifications`
				iter::once(notifications::ProtocolConfig {
					name: block_announces_protocol.notifications_protocol.clone(),
					fallback_names: block_announces_protocol.fallback_names.clone(),
					handshake: block_announces_protocol.handshake.as_ref().unwrap().to_vec(),
					max_notification_size: block_announces_protocol.max_notification_size,
				})
				.chain(notification_protocols.iter().map(|s| notifications::ProtocolConfig {
					name: s.notifications_protocol.clone(),
					fallback_names: s.fallback_names.clone(),
					handshake: s.handshake.as_ref().map_or(roles.encode(), |h| (*h).to_vec()),
					max_notification_size: s.max_notification_size,
				})),
			)
		};

		let protocol = Self {
			peer_store_handle,
			behaviour,
			notification_protocols: iter::once(block_announces_protocol.notifications_protocol)
				.chain(notification_protocols.iter().map(|s| s.notifications_protocol.clone()))
				.collect(),
			bad_handshake_substreams: Default::default(),
			peers: HashMap::new(),
			sync_substream_validations: FuturesUnordered::new(),
			tx,
			// TODO: remove when `BlockAnnouncesHandshake` is moved away from `Protocol`
			_marker: Default::default(),
		};

		Ok(protocol)
	}

	/// Returns the list of all the peers we have an open channel to.
	pub fn open_peers(&self) -> impl Iterator<Item = &PeerId> {
		self.behaviour.open_peers()
	}

	/// Disconnects the given peer if we are connected to it.
	pub fn disconnect_peer(&mut self, peer_id: &PeerId, protocol_name: ProtocolName) {
		if let Some(position) = self.notification_protocols.iter().position(|p| *p == protocol_name)
		{
			// Note: no need to remove a peer from `self.peers` if we are dealing with sync
			// protocol, because it will be done when handling
			// `NotificationsOut::CustomProtocolClosed`.
			self.behaviour.disconnect_peer(peer_id, SetId::from(position));
		} else {
			warn!(target: "sub-libp2p", "disconnect_peer() with invalid protocol name")
		}
	}

	/// Returns the number of peers we're connected to on sync protocol.
	pub fn num_connected_peers(&self) -> usize {
		self.peers.len()
	}

	/// Set handshake for the notification protocol.
	pub fn set_notification_handshake(&mut self, protocol: ProtocolName, handshake: Vec<u8>) {
		if let Some(index) = self.notification_protocols.iter().position(|p| *p == protocol) {
			self.behaviour.set_notif_protocol_handshake(SetId::from(index), handshake);
		} else {
			error!(
				target: "sub-libp2p",
				"set_notification_handshake with unknown protocol: {}",
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

	fn handle_established_inbound_connection(
		&mut self,
		connection_id: ConnectionId,
		peer: PeerId,
		local_addr: &Multiaddr,
		remote_addr: &Multiaddr,
	) -> Result<THandler<Self>, ConnectionDenied> {
		self.behaviour.handle_established_inbound_connection(
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
		self.behaviour.handle_established_outbound_connection(
			connection_id,
			peer,
			addr,
			role_override,
		)
	}

	fn handle_pending_outbound_connection(
		&mut self,
		_connection_id: ConnectionId,
		_maybe_peer: Option<PeerId>,
		_addresses: &[Multiaddr],
		_effective_role: Endpoint,
	) -> Result<Vec<Multiaddr>, ConnectionDenied> {
		// Only `Discovery::handle_pending_outbound_connection` must be returning addresses to
		// ensure that we don't return unwanted addresses.
		Ok(Vec::new())
	}

	fn on_swarm_event(&mut self, event: FromSwarm<Self::ConnectionHandler>) {
		self.behaviour.on_swarm_event(event);
	}

	fn on_connection_handler_event(
		&mut self,
		peer_id: PeerId,
		connection_id: ConnectionId,
		event: THandlerOutEvent<Self>,
	) {
		self.behaviour.on_connection_handler_event(peer_id, connection_id, event);
	}

	fn poll(
		&mut self,
		cx: &mut std::task::Context,
		params: &mut impl PollParameters,
	) -> Poll<ToSwarm<Self::OutEvent, THandlerInEvent<Self>>> {
		while let Poll::Ready(Some(validation_result)) =
			self.sync_substream_validations.poll_next_unpin(cx)
		{
			match validation_result {
				Ok((peer, roles)) => {
					self.peers.insert(peer, roles);
				},
				Err(peer) => {
					log::debug!(
						target: "sub-libp2p",
						"`SyncingEngine` rejected stream"
					);
					self.behaviour.disconnect_peer(&peer, HARDCODED_PEERSETS_SYNC);
				},
			}
		}

		let event = match self.behaviour.poll(cx, params) {
			Poll::Pending => return Poll::Pending,
			Poll::Ready(ToSwarm::GenerateEvent(ev)) => ev,
			Poll::Ready(ToSwarm::Dial { opts }) => return Poll::Ready(ToSwarm::Dial { opts }),
			Poll::Ready(ToSwarm::NotifyHandler { peer_id, handler, event }) =>
				return Poll::Ready(ToSwarm::NotifyHandler { peer_id, handler, event }),
			Poll::Ready(ToSwarm::ReportObservedAddr { address, score }) =>
				return Poll::Ready(ToSwarm::ReportObservedAddr { address, score }),
			Poll::Ready(ToSwarm::CloseConnection { peer_id, connection }) =>
				return Poll::Ready(ToSwarm::CloseConnection { peer_id, connection }),
		};

		let outcome = match event {
			NotificationsOut::CustomProtocolOpen {
				peer_id,
				set_id,
				received_handshake,
				notifications_sink,
				negotiated_fallback,
				inbound,
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

							let (tx, rx) = oneshot::channel();
							let _ = self.tx.unbounded_send(
								crate::SyncEvent::NotificationStreamOpened {
									inbound,
									remote: peer_id,
									received_handshake: handshake,
									sink: notifications_sink,
									tx,
								},
							);
							self.sync_substream_validations.push(Box::pin(async move {
								match rx.await {
									Ok(accepted) =>
										if accepted {
											Ok((peer_id, roles))
										} else {
											Err(peer_id)
										},
									Err(_) => Err(peer_id),
								}
							}));

							CustomMessageOutcome::None
						},
						Ok(msg) => {
							debug!(
								target: "sync",
								"Expected Status message from {}, but got {:?}",
								peer_id,
								msg,
							);
							self.peer_store_handle.report_peer(peer_id, rep::BAD_MESSAGE);
							CustomMessageOutcome::None
						},
						Err(err) => {
							match <BlockAnnouncesHandshake<B> as DecodeAll>::decode_all(
								&mut &received_handshake[..],
							) {
								Ok(handshake) => {
									let roles = handshake.roles;

									let (tx, rx) = oneshot::channel();
									let _ = self.tx.unbounded_send(
										crate::SyncEvent::NotificationStreamOpened {
											inbound,
											remote: peer_id,
											received_handshake: handshake,
											sink: notifications_sink,
											tx,
										},
									);
									self.sync_substream_validations.push(Box::pin(async move {
										match rx.await {
											Ok(accepted) =>
												if accepted {
													Ok((peer_id, roles))
												} else {
													Err(peer_id)
												},
											Err(_) => Err(peer_id),
										}
									}));
									CustomMessageOutcome::None
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
									self.peer_store_handle.report_peer(peer_id, rep::BAD_MESSAGE);
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
							self.peer_store_handle.report_peer(peer_id, rep::BAD_MESSAGE);
							CustomMessageOutcome::None
						},
					}
				}
			},
			NotificationsOut::CustomProtocolReplaced { peer_id, notifications_sink, set_id } =>
				if self.bad_handshake_substreams.contains(&(peer_id, set_id)) {
					CustomMessageOutcome::None
				} else if set_id == HARDCODED_PEERSETS_SYNC {
					let _ = self.tx.unbounded_send(crate::SyncEvent::NotificationSinkReplaced {
						remote: peer_id,
						sink: notifications_sink,
					});
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
				} else if set_id == HARDCODED_PEERSETS_SYNC {
					let _ = self.tx.unbounded_send(crate::SyncEvent::NotificationStreamClosed {
						remote: peer_id,
					});
					self.peers.remove(&peer_id);
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
				} else if set_id == HARDCODED_PEERSETS_SYNC {
					let _ = self.tx.unbounded_send(crate::SyncEvent::NotificationsReceived {
						remote: peer_id,
						messages: vec![message.freeze()],
					});
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
			return Poll::Ready(ToSwarm::GenerateEvent(outcome))
		}

		// This block can only be reached if an event was pulled from the behaviour and that
		// resulted in `CustomMessageOutcome::None`. Since there might be another pending
		// message from the behaviour, the task is scheduled again.
		cx.waker().wake_by_ref();
		Poll::Pending
	}
}
