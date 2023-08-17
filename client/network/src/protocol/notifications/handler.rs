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

//! Implementations of the `IntoConnectionHandler` and `ConnectionHandler` traits for both incoming
//! and outgoing substreams for all gossiping protocols.
//!
//! This is the main implementation of `ConnectionHandler` in this crate, that handles all the
//! gossiping protocols that are Substrate-related and outside of the scope of libp2p.
//!
//! # Usage
//!
//! From an API perspective, for each of its protocols, the [`NotifsHandler`] is always in one of
//! the following state (see [`State`]):
//!
//! - Closed substream. This is the initial state.
//! - Closed substream, but remote desires them to be open.
//! - Open substream.
//! - Open substream, but remote desires them to be closed.
//!
//! Each protocol in the [`NotifsHandler`] can spontaneously switch between these states:
//!
//! - "Closed substream" to "Closed substream but open desired". When that happens, a
//! [`NotifsHandlerOut::OpenDesiredByRemote`] is emitted.
//! - "Closed substream but open desired" to "Closed substream" (i.e. the remote has cancelled
//! their request). When that happens, a [`NotifsHandlerOut::CloseDesired`] is emitted.
//! - "Open substream" to "Open substream but close desired". When that happens, a
//! [`NotifsHandlerOut::CloseDesired`] is emitted.
//!
//! The user can instruct a protocol in the `NotifsHandler` to switch from "closed" to "open" or
//! vice-versa by sending either a [`NotifsHandlerIn::Open`] or a [`NotifsHandlerIn::Close`]. The
//! `NotifsHandler` must answer with [`NotifsHandlerOut::OpenResultOk`] or
//! [`NotifsHandlerOut::OpenResultErr`], or with [`NotifsHandlerOut::CloseResult`].
//!
//! When a [`NotifsHandlerOut::OpenResultOk`] is emitted, the substream is now in the open state.
//! When a [`NotifsHandlerOut::OpenResultErr`] or [`NotifsHandlerOut::CloseResult`] is emitted,
//! the `NotifsHandler` is now (or remains) in the closed state.
//!
//! When a [`NotifsHandlerOut::OpenDesiredByRemote`] is emitted, the user should always send back
//! either a [`NotifsHandlerIn::Open`] or a [`NotifsHandlerIn::Close`].If this isn't done, the
//! remote will be left in a pending state.
//!
//! It is illegal to send a [`NotifsHandlerIn::Open`] before a previously-emitted
//! [`NotifsHandlerIn::Open`] has gotten an answer.

use crate::{
	protocol::notifications::upgrade::{
		NotificationsIn, NotificationsInSubstream, NotificationsOut, NotificationsOutSubstream,
		UpgradeCollec,
	},
	types::ProtocolName,
};

use bytes::BytesMut;
use futures::{
	channel::mpsc,
	lock::{Mutex as FuturesMutex, MutexGuard as FuturesMutexGuard},
	prelude::*,
};
use libp2p::{
	core::ConnectedPoint,
	swarm::{
		handler::ConnectionEvent, ConnectionHandler, ConnectionHandlerEvent, KeepAlive,
		NegotiatedSubstream, SubstreamProtocol,
	},
	PeerId,
};
use log::error;
use parking_lot::{Mutex, RwLock};
use std::{
	collections::VecDeque,
	mem,
	pin::Pin,
	sync::Arc,
	task::{Context, Poll},
	time::{Duration, Instant},
};

/// Number of pending notifications in asynchronous contexts.
/// See [`NotificationsSink::reserve_notification`] for context.
const ASYNC_NOTIFICATIONS_BUFFER_SIZE: usize = 8;

/// Number of pending notifications in synchronous contexts.
const SYNC_NOTIFICATIONS_BUFFER_SIZE: usize = 2048;

/// Maximum duration to open a substream and receive the handshake message. After that, we
/// consider that we failed to open the substream.
const OPEN_TIMEOUT: Duration = Duration::from_secs(10);

/// After successfully establishing a connection with the remote, we keep the connection open for
/// at least this amount of time in order to give the rest of the code the chance to notify us to
/// open substreams.
const INITIAL_KEEPALIVE_TIME: Duration = Duration::from_secs(5);

/// The actual handler once the connection has been established.
///
/// See the documentation at the module level for more information.
pub struct NotifsHandler {
	/// List of notification protocols, specified by the user at initialization.
	protocols: Vec<Protocol>,

	/// When the connection with the remote has been successfully established.
	when_connection_open: Instant,

	/// Whether we are the connection dialer or listener.
	endpoint: ConnectedPoint,

	/// Remote we are connected to.
	peer_id: PeerId,

	/// Events to return in priority from `poll`.
	events_queue: VecDeque<
		ConnectionHandlerEvent<NotificationsOut, usize, NotifsHandlerOut, NotifsHandlerError>,
	>,
}

impl NotifsHandler {
	/// Creates new [`NotifsHandler`].
	pub fn new(peer_id: PeerId, endpoint: ConnectedPoint, protocols: Vec<ProtocolConfig>) -> Self {
		Self {
			protocols: protocols
				.into_iter()
				.map(|config| {
					let in_upgrade = NotificationsIn::new(
						config.name.clone(),
						config.fallback_names.clone(),
						config.max_notification_size,
					);

					Protocol { config, in_upgrade, state: State::Closed { pending_opening: false } }
				})
				.collect(),
			peer_id,
			endpoint,
			when_connection_open: Instant::now(),
			events_queue: VecDeque::with_capacity(16),
		}
	}
}

/// Configuration for a notifications protocol.
#[derive(Debug, Clone)]
pub struct ProtocolConfig {
	/// Name of the protocol.
	pub name: ProtocolName,
	/// Names of the protocol to use if the main one isn't available.
	pub fallback_names: Vec<ProtocolName>,
	/// Handshake of the protocol. The `RwLock` is locked every time a new substream is opened.
	pub handshake: Arc<RwLock<Vec<u8>>>,
	/// Maximum allowed size for a notification.
	pub max_notification_size: u64,
}

/// Fields specific for each individual protocol.
struct Protocol {
	/// Other fields.
	config: ProtocolConfig,

	/// Prototype for the inbound upgrade.
	in_upgrade: NotificationsIn,

	/// Current state of the substreams for this protocol.
	state: State,
}

/// See the module-level documentation to learn about the meaning of these variants.
enum State {
	/// Protocol is in the "Closed" state.
	Closed {
		/// True if an outgoing substream is still in the process of being opened.
		pending_opening: bool,
	},

	/// Protocol is in the "Closed" state. A [`NotifsHandlerOut::OpenDesiredByRemote`] has been
	/// emitted.
	OpenDesiredByRemote {
		/// Substream opened by the remote and that hasn't been accepted/rejected yet.
		in_substream: NotificationsInSubstream<NegotiatedSubstream>,

		/// See [`State::Closed::pending_opening`].
		pending_opening: bool,
	},

	/// Protocol is in the "Closed" state, but has received a [`NotifsHandlerIn::Open`] and is
	/// consequently trying to open the various notifications substreams.
	///
	/// A [`NotifsHandlerOut::OpenResultOk`] or a [`NotifsHandlerOut::OpenResultErr`] event must
	/// be emitted when transitionning to respectively [`State::Open`] or [`State::Closed`].
	Opening {
		/// Substream opened by the remote. If `Some`, has been accepted.
		in_substream: Option<NotificationsInSubstream<NegotiatedSubstream>>,
		/// Is the connection inbound.
		inbound: bool,
	},

	/// Protocol is in the "Open" state.
	Open {
		/// Contains the two `Receiver`s connected to the [`NotificationsSink`] that has been
		/// sent out. The notifications to send out can be pulled from this receivers.
		/// We use two different channels in order to have two different channel sizes, but from
		/// the receiving point of view, the two channels are the same.
		/// The receivers are fused in case the user drops the [`NotificationsSink`] entirely.
		notifications_sink_rx: stream::Peekable<
			stream::Select<
				stream::Fuse<mpsc::Receiver<NotificationsSinkMessage>>,
				stream::Fuse<mpsc::Receiver<NotificationsSinkMessage>>,
			>,
		>,

		/// Outbound substream that has been accepted by the remote.
		///
		/// Always `Some` on transition to [`State::Open`]. Switched to `None` only if the remote
		/// closed the substream. If `None`, a [`NotifsHandlerOut::CloseDesired`] event has been
		/// emitted.
		out_substream: Option<NotificationsOutSubstream<NegotiatedSubstream>>,

		/// Substream opened by the remote.
		///
		/// Contrary to the `out_substream` field, operations continue as normal even if the
		/// substream has been closed by the remote. A `None` is treated the same way as if there
		/// was an idle substream.
		in_substream: Option<NotificationsInSubstream<NegotiatedSubstream>>,
	},
}

/// Event that can be received by a `NotifsHandler`.
#[derive(Debug, Clone)]
pub enum NotifsHandlerIn {
	/// Instruct the handler to open the notification substreams.
	///
	/// Must always be answered by a [`NotifsHandlerOut::OpenResultOk`] or a
	/// [`NotifsHandlerOut::OpenResultErr`] event.
	///
	/// Importantly, it is forbidden to send a [`NotifsHandlerIn::Open`] while a previous one is
	/// already in the fly. It is however possible if a `Close` is still in the fly.
	Open {
		/// Index of the protocol in the list of protocols passed at initialization.
		protocol_index: usize,
	},

	/// Instruct the handler to close the notification substreams, or reject any pending incoming
	/// substream request.
	///
	/// Must always be answered by a [`NotifsHandlerOut::CloseResult`] event.
	Close {
		/// Index of the protocol in the list of protocols passed at initialization.
		protocol_index: usize,
	},
}

/// Event that can be emitted by a `NotifsHandler`.
#[derive(Debug)]
pub enum NotifsHandlerOut {
	/// Acknowledges a [`NotifsHandlerIn::Open`].
	OpenResultOk {
		/// Index of the protocol in the list of protocols passed at initialization.
		protocol_index: usize,
		/// Name of the protocol that was actually negotiated, if the default one wasn't available.
		negotiated_fallback: Option<ProtocolName>,
		/// The endpoint of the connection that is open for custom protocols.
		endpoint: ConnectedPoint,
		/// Handshake that was sent to us.
		/// This is normally a "Status" message, but this out of the concern of this code.
		received_handshake: Vec<u8>,
		/// How notifications can be sent to this node.
		notifications_sink: NotificationsSink,
		/// Is the connection inbound.
		inbound: bool,
	},

	/// Acknowledges a [`NotifsHandlerIn::Open`]. The remote has refused the attempt to open
	/// notification substreams.
	OpenResultErr {
		/// Index of the protocol in the list of protocols passed at initialization.
		protocol_index: usize,
	},

	/// Acknowledges a [`NotifsHandlerIn::Close`].
	CloseResult {
		/// Index of the protocol in the list of protocols passed at initialization.
		protocol_index: usize,
	},

	/// The remote would like the substreams to be open. Send a [`NotifsHandlerIn::Open`] or a
	/// [`NotifsHandlerIn::Close`] in order to either accept or deny this request. If a
	/// [`NotifsHandlerIn::Open`] or [`NotifsHandlerIn::Close`] has been sent before and has not
	/// yet been acknowledged by a matching [`NotifsHandlerOut`], then you don't need to a send
	/// another [`NotifsHandlerIn`].
	OpenDesiredByRemote {
		/// Index of the protocol in the list of protocols passed at initialization.
		protocol_index: usize,
	},

	/// The remote would like the substreams to be closed. Send a [`NotifsHandlerIn::Close`] in
	/// order to close them. If a [`NotifsHandlerIn::Close`] has been sent before and has not yet
	/// been acknowledged by a [`NotifsHandlerOut::CloseResult`], then you don't need to a send
	/// another one.
	CloseDesired {
		/// Index of the protocol in the list of protocols passed at initialization.
		protocol_index: usize,
	},

	/// Received a message on a custom protocol substream.
	///
	/// Can only happen when the handler is in the open state.
	Notification {
		/// Index of the protocol in the list of protocols passed at initialization.
		protocol_index: usize,
		/// Message that has been received.
		message: BytesMut,
	},
}

/// Sink connected directly to the node background task. Allows sending notifications to the peer.
///
/// Can be cloned in order to obtain multiple references to the substream of the same peer.
#[derive(Debug, Clone)]
pub struct NotificationsSink {
	inner: Arc<NotificationsSinkInner>,
}

#[derive(Debug)]
struct NotificationsSinkInner {
	/// Target of the sink.
	peer_id: PeerId,
	/// Sender to use in asynchronous contexts. Uses an asynchronous mutex.
	async_channel: FuturesMutex<mpsc::Sender<NotificationsSinkMessage>>,
	/// Sender to use in synchronous contexts. Uses a synchronous mutex.
	/// Contains `None` if the channel was full at some point, in which case the channel will
	/// be closed in the near future anyway.
	/// This channel has a large capacity and is meant to be used in contexts where
	/// back-pressure cannot be properly exerted.
	/// It will be removed in a future version.
	sync_channel: Mutex<Option<mpsc::Sender<NotificationsSinkMessage>>>,
}

/// Message emitted through the [`NotificationsSink`] and processed by the background task
/// dedicated to the peer.
#[derive(Debug)]
enum NotificationsSinkMessage {
	/// Message emitted by [`NotificationsSink::reserve_notification`] and
	/// [`NotificationsSink::write_notification_now`].
	Notification { message: Vec<u8> },

	/// Must close the connection.
	ForceClose,
}

impl NotificationsSink {
	/// Returns the [`PeerId`] the sink is connected to.
	pub fn peer_id(&self) -> &PeerId {
		&self.inner.peer_id
	}

	/// Sends a notification to the peer.
	///
	/// If too many messages are already buffered, the notification is silently discarded and the
	/// connection to the peer will be closed shortly after.
	///
	/// The protocol name is expected to be checked ahead of calling this method. It is a logic
	/// error to send a notification using an unknown protocol.
	///
	/// This method will be removed in a future version.
	pub fn send_sync_notification(&self, message: impl Into<Vec<u8>>) {
		let mut lock = self.inner.sync_channel.lock();

		if let Some(tx) = lock.as_mut() {
			let result =
				tx.try_send(NotificationsSinkMessage::Notification { message: message.into() });

			if result.is_err() {
				// Cloning the `mpsc::Sender` guarantees the allocation of an extra spot in the
				// buffer, and therefore `try_send` will succeed.
				let _result2 = tx.clone().try_send(NotificationsSinkMessage::ForceClose);
				debug_assert!(_result2.map(|()| true).unwrap_or_else(|err| err.is_disconnected()));

				// Destroy the sender in order to not send more `ForceClose` messages.
				*lock = None;
			}
		}
	}

	/// Wait until the remote is ready to accept a notification.
	///
	/// Returns an error in the case where the connection is closed.
	///
	/// The protocol name is expected to be checked ahead of calling this method. It is a logic
	/// error to send a notification using an unknown protocol.
	pub async fn reserve_notification(&self) -> Result<Ready<'_>, ()> {
		let mut lock = self.inner.async_channel.lock().await;

		let poll_ready = future::poll_fn(|cx| lock.poll_ready(cx)).await;
		if poll_ready.is_ok() {
			Ok(Ready { lock })
		} else {
			Err(())
		}
	}
}

/// Notification slot is reserved and the notification can actually be sent.
#[must_use]
#[derive(Debug)]
pub struct Ready<'a> {
	/// Guarded channel. The channel inside is guaranteed to not be full.
	lock: FuturesMutexGuard<'a, mpsc::Sender<NotificationsSinkMessage>>,
}

impl<'a> Ready<'a> {
	/// Consumes this slots reservation and actually queues the notification.
	///
	/// Returns an error if the substream has been closed.
	pub fn send(mut self, notification: impl Into<Vec<u8>>) -> Result<(), ()> {
		self.lock
			.start_send(NotificationsSinkMessage::Notification { message: notification.into() })
			.map_err(|_| ())
	}
}

/// Error specific to the collection of protocols.
#[derive(Debug, thiserror::Error)]
pub enum NotifsHandlerError {
	#[error("Channel of synchronous notifications is full.")]
	SyncNotificationsClogged,
}

impl ConnectionHandler for NotifsHandler {
	type InEvent = NotifsHandlerIn;
	type OutEvent = NotifsHandlerOut;
	type Error = NotifsHandlerError;
	type InboundProtocol = UpgradeCollec<NotificationsIn>;
	type OutboundProtocol = NotificationsOut;
	// Index within the `out_protocols`.
	type OutboundOpenInfo = usize;
	type InboundOpenInfo = ();

	fn listen_protocol(&self) -> SubstreamProtocol<Self::InboundProtocol, ()> {
		let protocols = self
			.protocols
			.iter()
			.map(|p| p.in_upgrade.clone())
			.collect::<UpgradeCollec<_>>();

		SubstreamProtocol::new(protocols, ())
	}

	fn on_connection_event(
		&mut self,
		event: ConnectionEvent<
			'_,
			Self::InboundProtocol,
			Self::OutboundProtocol,
			Self::InboundOpenInfo,
			Self::OutboundOpenInfo,
		>,
	) {
		match event {
			ConnectionEvent::FullyNegotiatedInbound(inbound) => {
				let (mut in_substream_open, protocol_index) = inbound.protocol;
				let protocol_info = &mut self.protocols[protocol_index];

				match protocol_info.state {
					State::Closed { pending_opening } => {
						self.events_queue.push_back(ConnectionHandlerEvent::Custom(
							NotifsHandlerOut::OpenDesiredByRemote { protocol_index },
						));

						protocol_info.state = State::OpenDesiredByRemote {
							in_substream: in_substream_open.substream,
							pending_opening,
						};
					},
					State::OpenDesiredByRemote { .. } => {
						// If a substream already exists, silently drop the new one.
						// Note that we drop the substream, which will send an equivalent to a
						// TCP "RST" to the remote and force-close the substream. It might
						// seem like an unclean way to get rid of a substream. However, keep
						// in mind that it is invalid for the remote to open multiple such
						// substreams, and therefore sending a "RST" is the most correct thing
						// to do.
						return
					},
					State::Opening { ref mut in_substream, .. } |
					State::Open { ref mut in_substream, .. } => {
						if in_substream.is_some() {
							// Same remark as above.
							return
						}

						// Create `handshake_message` on a separate line to be sure that the
						// lock is released as soon as possible.
						let handshake_message = protocol_info.config.handshake.read().clone();
						in_substream_open.substream.send_handshake(handshake_message);
						*in_substream = Some(in_substream_open.substream);
					},
				}
			},
			ConnectionEvent::FullyNegotiatedOutbound(outbound) => {
				let (new_open, protocol_index) = (outbound.protocol, outbound.info);

				match self.protocols[protocol_index].state {
					State::Closed { ref mut pending_opening } |
					State::OpenDesiredByRemote { ref mut pending_opening, .. } => {
						debug_assert!(*pending_opening);
						*pending_opening = false;
					},
					State::Open { .. } => {
						error!(target: "sub-libp2p", "☎️ State mismatch in notifications handler");
						debug_assert!(false);
					},
					State::Opening { ref mut in_substream, inbound } => {
						let (async_tx, async_rx) = mpsc::channel(ASYNC_NOTIFICATIONS_BUFFER_SIZE);
						let (sync_tx, sync_rx) = mpsc::channel(SYNC_NOTIFICATIONS_BUFFER_SIZE);
						let notifications_sink = NotificationsSink {
							inner: Arc::new(NotificationsSinkInner {
								peer_id: self.peer_id,
								async_channel: FuturesMutex::new(async_tx),
								sync_channel: Mutex::new(Some(sync_tx)),
							}),
						};

						self.protocols[protocol_index].state = State::Open {
							notifications_sink_rx: stream::select(async_rx.fuse(), sync_rx.fuse())
								.peekable(),
							out_substream: Some(new_open.substream),
							in_substream: in_substream.take(),
						};

						self.events_queue.push_back(ConnectionHandlerEvent::Custom(
							NotifsHandlerOut::OpenResultOk {
								protocol_index,
								negotiated_fallback: new_open.negotiated_fallback,
								endpoint: self.endpoint.clone(),
								received_handshake: new_open.handshake,
								notifications_sink,
								inbound,
							},
						));
					},
				}
			},
			ConnectionEvent::AddressChange(_address_change) => {},
			ConnectionEvent::DialUpgradeError(dial_upgrade_error) => match self.protocols
				[dial_upgrade_error.info]
				.state
			{
				State::Closed { ref mut pending_opening } |
				State::OpenDesiredByRemote { ref mut pending_opening, .. } => {
					debug_assert!(*pending_opening);
					*pending_opening = false;
				},

				State::Opening { .. } => {
					self.protocols[dial_upgrade_error.info].state =
						State::Closed { pending_opening: false };

					self.events_queue.push_back(ConnectionHandlerEvent::Custom(
						NotifsHandlerOut::OpenResultErr { protocol_index: dial_upgrade_error.info },
					));
				},

				// No substream is being open when already `Open`.
				State::Open { .. } => debug_assert!(false),
			},
			ConnectionEvent::ListenUpgradeError(_listen_upgrade_error) => {},
		}
	}

	fn on_behaviour_event(&mut self, message: NotifsHandlerIn) {
		match message {
			NotifsHandlerIn::Open { protocol_index } => {
				let protocol_info = &mut self.protocols[protocol_index];
				match &mut protocol_info.state {
					State::Closed { pending_opening } => {
						if !*pending_opening {
							let proto = NotificationsOut::new(
								protocol_info.config.name.clone(),
								protocol_info.config.fallback_names.clone(),
								protocol_info.config.handshake.read().clone(),
								protocol_info.config.max_notification_size,
							);

							self.events_queue.push_back(
								ConnectionHandlerEvent::OutboundSubstreamRequest {
									protocol: SubstreamProtocol::new(proto, protocol_index)
										.with_timeout(OPEN_TIMEOUT),
								},
							);
						}

						protocol_info.state = State::Opening { in_substream: None, inbound: false };
					},
					State::OpenDesiredByRemote { pending_opening, in_substream } => {
						let handshake_message = protocol_info.config.handshake.read().clone();

						if !*pending_opening {
							let proto = NotificationsOut::new(
								protocol_info.config.name.clone(),
								protocol_info.config.fallback_names.clone(),
								handshake_message.clone(),
								protocol_info.config.max_notification_size,
							);

							self.events_queue.push_back(
								ConnectionHandlerEvent::OutboundSubstreamRequest {
									protocol: SubstreamProtocol::new(proto, protocol_index)
										.with_timeout(OPEN_TIMEOUT),
								},
							);
						}

						in_substream.send_handshake(handshake_message);

						// The state change is done in two steps because of borrowing issues.
						let in_substream = match mem::replace(
							&mut protocol_info.state,
							State::Opening { in_substream: None, inbound: false },
						) {
							State::OpenDesiredByRemote { in_substream, .. } => in_substream,
							_ => unreachable!(),
						};
						protocol_info.state =
							State::Opening { in_substream: Some(in_substream), inbound: true };
					},
					State::Opening { .. } | State::Open { .. } => {
						// As documented, it is forbidden to send an `Open` while there is already
						// one in the fly.
						error!(target: "sub-libp2p", "opening already-opened handler");
						debug_assert!(false);
					},
				}
			},

			NotifsHandlerIn::Close { protocol_index } => {
				match self.protocols[protocol_index].state {
					State::Open { .. } => {
						self.protocols[protocol_index].state =
							State::Closed { pending_opening: false };
					},
					State::Opening { .. } => {
						self.protocols[protocol_index].state =
							State::Closed { pending_opening: true };

						self.events_queue.push_back(ConnectionHandlerEvent::Custom(
							NotifsHandlerOut::OpenResultErr { protocol_index },
						));
					},
					State::OpenDesiredByRemote { pending_opening, .. } => {
						self.protocols[protocol_index].state = State::Closed { pending_opening };
					},
					State::Closed { .. } => {},
				}

				self.events_queue.push_back(ConnectionHandlerEvent::Custom(
					NotifsHandlerOut::CloseResult { protocol_index },
				));
			},
		}
	}

	fn connection_keep_alive(&self) -> KeepAlive {
		// `Yes` if any protocol has some activity.
		if self.protocols.iter().any(|p| !matches!(p.state, State::Closed { .. })) {
			return KeepAlive::Yes
		}

		// A grace period of `INITIAL_KEEPALIVE_TIME` must be given to leave time for the remote
		// to express desire to open substreams.
		KeepAlive::Until(self.when_connection_open + INITIAL_KEEPALIVE_TIME)
	}

	fn poll(
		&mut self,
		cx: &mut Context,
	) -> Poll<
		ConnectionHandlerEvent<
			Self::OutboundProtocol,
			Self::OutboundOpenInfo,
			Self::OutEvent,
			Self::Error,
		>,
	> {
		if let Some(ev) = self.events_queue.pop_front() {
			return Poll::Ready(ev)
		}

		// For each open substream, try send messages from `notifications_sink_rx` to the
		// substream.
		for protocol_index in 0..self.protocols.len() {
			if let State::Open {
				notifications_sink_rx, out_substream: Some(out_substream), ..
			} = &mut self.protocols[protocol_index].state
			{
				loop {
					// Only proceed with `out_substream.poll_ready_unpin` if there is an element
					// available in `notifications_sink_rx`. This avoids waking up the task when
					// a substream is ready to send if there isn't actually something to send.
					match Pin::new(&mut *notifications_sink_rx).as_mut().poll_peek(cx) {
						Poll::Ready(Some(&NotificationsSinkMessage::ForceClose)) =>
							return Poll::Ready(ConnectionHandlerEvent::Close(
								NotifsHandlerError::SyncNotificationsClogged,
							)),
						Poll::Ready(Some(&NotificationsSinkMessage::Notification { .. })) => {},
						Poll::Ready(None) | Poll::Pending => break,
					}

					// Before we extract the element from `notifications_sink_rx`, check that the
					// substream is ready to accept a message.
					match out_substream.poll_ready_unpin(cx) {
						Poll::Ready(_) => {},
						Poll::Pending => break,
					}

					// Now that the substream is ready for a message, grab what to send.
					let message = match notifications_sink_rx.poll_next_unpin(cx) {
						Poll::Ready(Some(NotificationsSinkMessage::Notification { message })) =>
							message,
						Poll::Ready(Some(NotificationsSinkMessage::ForceClose)) |
						Poll::Ready(None) |
						Poll::Pending => {
							// Should never be reached, as per `poll_peek` above.
							debug_assert!(false);
							break
						},
					};

					let _ = out_substream.start_send_unpin(message);
					// Note that flushing is performed later down this function.
				}
			}
		}

		// Flush all outbound substreams.
		// When `poll` returns `Poll::Ready`, the libp2p `Swarm` may decide to no longer call
		// `poll` again before it is ready to accept more events.
		// In order to make sure that substreams are flushed as soon as possible, the flush is
		// performed before the code paths that can produce `Ready` (with some rare exceptions).
		// Importantly, however, the flush is performed *after* notifications are queued with
		// `Sink::start_send`.
		for protocol_index in 0..self.protocols.len() {
			match &mut self.protocols[protocol_index].state {
				State::Open { out_substream: out_substream @ Some(_), .. } => {
					match Sink::poll_flush(Pin::new(out_substream.as_mut().unwrap()), cx) {
						Poll::Pending | Poll::Ready(Ok(())) => {},
						Poll::Ready(Err(_)) => {
							*out_substream = None;
							let event = NotifsHandlerOut::CloseDesired { protocol_index };
							return Poll::Ready(ConnectionHandlerEvent::Custom(event))
						},
					};
				},

				State::Closed { .. } |
				State::Opening { .. } |
				State::Open { out_substream: None, .. } |
				State::OpenDesiredByRemote { .. } => {},
			}
		}

		// Poll inbound substreams.
		for protocol_index in 0..self.protocols.len() {
			// Inbound substreams being closed is always tolerated, except for the
			// `OpenDesiredByRemote` state which might need to be switched back to `Closed`.
			match &mut self.protocols[protocol_index].state {
				State::Closed { .. } |
				State::Open { in_substream: None, .. } |
				State::Opening { in_substream: None, .. } => {},

				State::Open { in_substream: in_substream @ Some(_), .. } =>
					match Stream::poll_next(Pin::new(in_substream.as_mut().unwrap()), cx) {
						Poll::Pending => {},
						Poll::Ready(Some(Ok(message))) => {
							let event = NotifsHandlerOut::Notification { protocol_index, message };
							return Poll::Ready(ConnectionHandlerEvent::Custom(event))
						},
						Poll::Ready(None) | Poll::Ready(Some(Err(_))) => *in_substream = None,
					},

				State::OpenDesiredByRemote { in_substream, pending_opening } =>
					match NotificationsInSubstream::poll_process(Pin::new(in_substream), cx) {
						Poll::Pending => {},
						Poll::Ready(Ok(void)) => match void {},
						Poll::Ready(Err(_)) => {
							self.protocols[protocol_index].state =
								State::Closed { pending_opening: *pending_opening };
							return Poll::Ready(ConnectionHandlerEvent::Custom(
								NotifsHandlerOut::CloseDesired { protocol_index },
							))
						},
					},

				State::Opening { in_substream: in_substream @ Some(_), .. } =>
					match NotificationsInSubstream::poll_process(
						Pin::new(in_substream.as_mut().unwrap()),
						cx,
					) {
						Poll::Pending => {},
						Poll::Ready(Ok(void)) => match void {},
						Poll::Ready(Err(_)) => *in_substream = None,
					},
			}
		}

		// This is the only place in this method that can return `Pending`.
		// By putting it at the very bottom, we are guaranteed that everything has been properly
		// polled.
		Poll::Pending
	}
}

#[cfg(test)]
pub mod tests {
	use super::*;
	use crate::protocol::notifications::upgrade::{
		NotificationsInOpen, NotificationsInSubstreamHandshake, NotificationsOutOpen,
	};
	use asynchronous_codec::Framed;
	use libp2p::{
		core::muxing::SubstreamBox,
		swarm::{handler, ConnectionHandlerUpgrErr},
		Multiaddr,
	};
	use multistream_select::{dialer_select_proto, listener_select_proto, Negotiated, Version};
	use std::{
		collections::HashMap,
		io::{Error, IoSlice, IoSliceMut},
	};
	use tokio::sync::mpsc;
	use unsigned_varint::codec::UviBytes;

	struct OpenSubstream {
		notifications: stream::Peekable<
			stream::Select<
				stream::Fuse<futures::channel::mpsc::Receiver<NotificationsSinkMessage>>,
				stream::Fuse<futures::channel::mpsc::Receiver<NotificationsSinkMessage>>,
			>,
		>,
		_in_substream: MockSubstream,
		_out_substream: MockSubstream,
	}

	pub struct ConnectionYielder {
		connections: HashMap<(PeerId, usize), OpenSubstream>,
	}

	impl ConnectionYielder {
		/// Create new [`ConnectionYielder`].
		pub fn new() -> Self {
			Self { connections: HashMap::new() }
		}

		/// Open a new substream for peer.
		pub fn open_substream(
			&mut self,
			peer: PeerId,
			protocol_index: usize,
			endpoint: ConnectedPoint,
			received_handshake: Vec<u8>,
		) -> NotifsHandlerOut {
			let (async_tx, async_rx) =
				futures::channel::mpsc::channel(ASYNC_NOTIFICATIONS_BUFFER_SIZE);
			let (sync_tx, sync_rx) =
				futures::channel::mpsc::channel(SYNC_NOTIFICATIONS_BUFFER_SIZE);
			let notifications_sink = NotificationsSink {
				inner: Arc::new(NotificationsSinkInner {
					peer_id: peer,
					async_channel: FuturesMutex::new(async_tx),
					sync_channel: Mutex::new(Some(sync_tx)),
				}),
			};
			let (in_substream, out_substream) = MockSubstream::new();

			self.connections.insert(
				(peer, protocol_index),
				OpenSubstream {
					notifications: stream::select(async_rx.fuse(), sync_rx.fuse()).peekable(),
					_in_substream: in_substream,
					_out_substream: out_substream,
				},
			);

			NotifsHandlerOut::OpenResultOk {
				protocol_index,
				negotiated_fallback: None,
				endpoint,
				received_handshake,
				notifications_sink,
				inbound: false,
			}
		}

		/// Attempt to get next pending event from one of the notification sinks.
		pub async fn get_next_event(&mut self, peer: PeerId, set: usize) -> Option<Vec<u8>> {
			let substream = if let Some(info) = self.connections.get_mut(&(peer, set)) {
				info
			} else {
				return None
			};

			futures::future::poll_fn(|cx| match substream.notifications.poll_next_unpin(cx) {
				Poll::Ready(Some(NotificationsSinkMessage::Notification { message })) =>
					Poll::Ready(Some(message)),
				Poll::Pending => Poll::Ready(None),
				Poll::Ready(Some(NotificationsSinkMessage::ForceClose)) | Poll::Ready(None) => {
					panic!("sink closed")
				},
			})
			.await
		}
	}
	struct MockSubstream {
		pub rx: mpsc::Receiver<Vec<u8>>,
		pub tx: mpsc::Sender<Vec<u8>>,
		rx_buffer: BytesMut,
	}

	impl MockSubstream {
		/// Create new substream pair.
		pub fn new() -> (Self, Self) {
			let (tx1, rx1) = mpsc::channel(32);
			let (tx2, rx2) = mpsc::channel(32);

			(
				Self { rx: rx1, tx: tx2, rx_buffer: BytesMut::with_capacity(512) },
				Self { rx: rx2, tx: tx1, rx_buffer: BytesMut::with_capacity(512) },
			)
		}

		/// Create new negotiated substream pair.
		pub async fn negotiated() -> (Negotiated<SubstreamBox>, Negotiated<SubstreamBox>) {
			let (socket1, socket2) = Self::new();
			let socket1 = SubstreamBox::new(socket1);
			let socket2 = SubstreamBox::new(socket2);

			let protos = vec![b"/echo/1.0.0", b"/echo/2.5.0"];
			let (res1, res2) = tokio::join!(
				dialer_select_proto(socket1, protos.clone(), Version::V1),
				listener_select_proto(socket2, protos),
			);

			(res1.unwrap().1, res2.unwrap().1)
		}
	}

	impl AsyncWrite for MockSubstream {
		fn poll_write<'a>(
			self: Pin<&mut Self>,
			_cx: &mut Context<'a>,
			buf: &[u8],
		) -> Poll<Result<usize, Error>> {
			match self.tx.try_send(buf.to_vec()) {
				Ok(_) => Poll::Ready(Ok(buf.len())),
				Err(_) => Poll::Ready(Err(std::io::ErrorKind::UnexpectedEof.into())),
			}
		}

		fn poll_flush<'a>(self: Pin<&mut Self>, _cx: &mut Context<'a>) -> Poll<Result<(), Error>> {
			Poll::Ready(Ok(()))
		}

		fn poll_close<'a>(self: Pin<&mut Self>, _cx: &mut Context<'a>) -> Poll<Result<(), Error>> {
			Poll::Ready(Ok(()))
		}

		fn poll_write_vectored<'a, 'b>(
			self: Pin<&mut Self>,
			_cx: &mut Context<'a>,
			_bufs: &[IoSlice<'b>],
		) -> Poll<Result<usize, Error>> {
			unimplemented!();
		}
	}

	impl AsyncRead for MockSubstream {
		fn poll_read<'a>(
			mut self: Pin<&mut Self>,
			cx: &mut Context<'a>,
			buf: &mut [u8],
		) -> Poll<Result<usize, Error>> {
			match self.rx.poll_recv(cx) {
				Poll::Ready(Some(data)) => self.rx_buffer.extend_from_slice(&data),
				Poll::Ready(None) =>
					return Poll::Ready(Err(std::io::ErrorKind::UnexpectedEof.into())),
				_ => {},
			}

			let nsize = std::cmp::min(self.rx_buffer.len(), buf.len());
			let data = self.rx_buffer.split_to(nsize);
			buf[..nsize].copy_from_slice(&data[..]);

			if nsize > 0 {
				return Poll::Ready(Ok(nsize))
			}

			Poll::Pending
		}

		fn poll_read_vectored<'a, 'b>(
			self: Pin<&mut Self>,
			_cx: &mut Context<'a>,
			_bufs: &mut [IoSliceMut<'b>],
		) -> Poll<Result<usize, Error>> {
			unimplemented!();
		}
	}

	/// Create new [`NotifsHandler`].
	fn notifs_handler() -> NotifsHandler {
		let proto = Protocol {
			config: ProtocolConfig {
				name: "/foo".into(),
				fallback_names: vec![],
				handshake: Arc::new(RwLock::new(b"hello, world".to_vec())),
				max_notification_size: u64::MAX,
			},
			in_upgrade: NotificationsIn::new("/foo", Vec::new(), u64::MAX),
			state: State::Closed { pending_opening: false },
		};

		NotifsHandler {
			protocols: vec![proto],
			when_connection_open: Instant::now(),
			endpoint: ConnectedPoint::Listener {
				local_addr: Multiaddr::empty(),
				send_back_addr: Multiaddr::empty(),
			},
			peer_id: PeerId::random(),
			events_queue: VecDeque::new(),
		}
	}

	// verify that if another substream is attempted to be opened by remote while an inbound
	// substream already exists, the new inbound stream is rejected and closed by the local node.
	#[tokio::test]
	async fn second_open_desired_by_remote_rejected() {
		let mut handler = notifs_handler();
		let (io, mut io2) = MockSubstream::negotiated().await;
		let mut codec = UviBytes::default();
		codec.set_max_len(usize::MAX);

		let notif_in = NotificationsInOpen {
			handshake: b"hello, world".to_vec(),
			negotiated_fallback: None,
			substream: NotificationsInSubstream::new(
				Framed::new(io, codec),
				NotificationsInSubstreamHandshake::NotSent,
			),
		};

		handler.on_connection_event(handler::ConnectionEvent::FullyNegotiatedInbound(
			handler::FullyNegotiatedInbound { protocol: (notif_in, 0), info: () },
		));

		// verify that the substream is in (partly) opened state
		assert!(std::matches!(handler.protocols[0].state, State::OpenDesiredByRemote { .. }));
		futures::future::poll_fn(|cx| {
			let mut buf = Vec::with_capacity(512);
			assert!(std::matches!(Pin::new(&mut io2).poll_read(cx, &mut buf), Poll::Pending));
			Poll::Ready(())
		})
		.await;

		// attempt to open another inbound substream and verify that it is rejected
		let (io, mut io2) = MockSubstream::negotiated().await;
		let mut codec = UviBytes::default();
		codec.set_max_len(usize::MAX);

		let notif_in = NotificationsInOpen {
			handshake: b"hello, world".to_vec(),
			negotiated_fallback: None,
			substream: NotificationsInSubstream::new(
				Framed::new(io, codec),
				NotificationsInSubstreamHandshake::NotSent,
			),
		};

		handler.on_connection_event(handler::ConnectionEvent::FullyNegotiatedInbound(
			handler::FullyNegotiatedInbound { protocol: (notif_in, 0), info: () },
		));

		// verify that the new substream is rejected and closed
		futures::future::poll_fn(|cx| {
			let mut buf = Vec::with_capacity(512);

			if let Poll::Ready(Err(err)) = Pin::new(&mut io2).poll_read(cx, &mut buf) {
				assert_eq!(err.kind(), std::io::ErrorKind::UnexpectedEof,);
			}

			Poll::Ready(())
		})
		.await;
	}

	#[tokio::test]
	async fn open_rejected_if_substream_is_opening() {
		let mut handler = notifs_handler();
		let (io, mut io2) = MockSubstream::negotiated().await;
		let mut codec = UviBytes::default();
		codec.set_max_len(usize::MAX);

		let notif_in = NotificationsInOpen {
			handshake: b"hello, world".to_vec(),
			negotiated_fallback: None,
			substream: NotificationsInSubstream::new(
				Framed::new(io, codec),
				NotificationsInSubstreamHandshake::NotSent,
			),
		};

		handler.on_connection_event(handler::ConnectionEvent::FullyNegotiatedInbound(
			handler::FullyNegotiatedInbound { protocol: (notif_in, 0), info: () },
		));

		// verify that the substream is in (partly) opened state
		assert!(std::matches!(handler.protocols[0].state, State::OpenDesiredByRemote { .. }));
		futures::future::poll_fn(|cx| {
			let mut buf = Vec::with_capacity(512);
			assert!(std::matches!(Pin::new(&mut io2).poll_read(cx, &mut buf), Poll::Pending));
			Poll::Ready(())
		})
		.await;

		// move the handler state to 'Opening'
		handler.on_behaviour_event(NotifsHandlerIn::Open { protocol_index: 0 });
		assert!(std::matches!(
			handler.protocols[0].state,
			State::Opening { in_substream: Some(_), .. }
		));

		// remote now tries to open another substream, verify that it is rejected and closed
		let (io, mut io2) = MockSubstream::negotiated().await;
		let mut codec = UviBytes::default();
		codec.set_max_len(usize::MAX);

		let notif_in = NotificationsInOpen {
			handshake: b"hello, world".to_vec(),
			negotiated_fallback: None,
			substream: NotificationsInSubstream::new(
				Framed::new(io, codec),
				NotificationsInSubstreamHandshake::NotSent,
			),
		};

		handler.on_connection_event(handler::ConnectionEvent::FullyNegotiatedInbound(
			handler::FullyNegotiatedInbound { protocol: (notif_in, 0), info: () },
		));

		// verify that the new substream is rejected and closed but that the first substream is
		// still in correct state
		futures::future::poll_fn(|cx| {
			let mut buf = Vec::with_capacity(512);

			if let Poll::Ready(Err(err)) = Pin::new(&mut io2).poll_read(cx, &mut buf) {
				assert_eq!(err.kind(), std::io::ErrorKind::UnexpectedEof,);
			} else {
				panic!("unexpected result");
			}

			Poll::Ready(())
		})
		.await;
		assert!(std::matches!(
			handler.protocols[0].state,
			State::Opening { in_substream: Some(_), .. }
		));
	}

	#[tokio::test]
	async fn open_rejected_if_substream_already_open() {
		let mut handler = notifs_handler();
		let (io, mut io2) = MockSubstream::negotiated().await;
		let mut codec = UviBytes::default();
		codec.set_max_len(usize::MAX);

		let notif_in = NotificationsInOpen {
			handshake: b"hello, world".to_vec(),
			negotiated_fallback: None,
			substream: NotificationsInSubstream::new(
				Framed::new(io, codec),
				NotificationsInSubstreamHandshake::NotSent,
			),
		};
		handler.on_connection_event(handler::ConnectionEvent::FullyNegotiatedInbound(
			handler::FullyNegotiatedInbound { protocol: (notif_in, 0), info: () },
		));

		// verify that the substream is in (partly) opened state
		assert!(std::matches!(handler.protocols[0].state, State::OpenDesiredByRemote { .. }));
		futures::future::poll_fn(|cx| {
			let mut buf = Vec::with_capacity(512);
			assert!(std::matches!(Pin::new(&mut io2).poll_read(cx, &mut buf), Poll::Pending));
			Poll::Ready(())
		})
		.await;

		// move the handler state to 'Opening'
		handler.on_behaviour_event(NotifsHandlerIn::Open { protocol_index: 0 });
		assert!(std::matches!(
			handler.protocols[0].state,
			State::Opening { in_substream: Some(_), .. }
		));

		// accept the substream and move its state to `Open`
		let (io, _io2) = MockSubstream::negotiated().await;
		let mut codec = UviBytes::default();
		codec.set_max_len(usize::MAX);

		let notif_out = NotificationsOutOpen {
			handshake: b"hello, world".to_vec(),
			negotiated_fallback: None,
			substream: NotificationsOutSubstream::new(Framed::new(io, codec)),
		};
		handler.on_connection_event(handler::ConnectionEvent::FullyNegotiatedOutbound(
			handler::FullyNegotiatedOutbound { protocol: notif_out, info: 0 },
		));

		assert!(std::matches!(
			handler.protocols[0].state,
			State::Open { in_substream: Some(_), .. }
		));

		// remote now tries to open another substream, verify that it is rejected and closed
		let (io, mut io2) = MockSubstream::negotiated().await;
		let mut codec = UviBytes::default();
		codec.set_max_len(usize::MAX);
		let notif_in = NotificationsInOpen {
			handshake: b"hello, world".to_vec(),
			negotiated_fallback: None,
			substream: NotificationsInSubstream::new(
				Framed::new(io, codec),
				NotificationsInSubstreamHandshake::NotSent,
			),
		};
		handler.on_connection_event(handler::ConnectionEvent::FullyNegotiatedInbound(
			handler::FullyNegotiatedInbound { protocol: (notif_in, 0), info: () },
		));

		// verify that the new substream is rejected and closed but that the first substream is
		// still in correct state
		futures::future::poll_fn(|cx| {
			let mut buf = Vec::with_capacity(512);

			if let Poll::Ready(Err(err)) = Pin::new(&mut io2).poll_read(cx, &mut buf) {
				assert_eq!(err.kind(), std::io::ErrorKind::UnexpectedEof);
			} else {
				panic!("unexpected result");
			}

			Poll::Ready(())
		})
		.await;
		assert!(std::matches!(
			handler.protocols[0].state,
			State::Open { in_substream: Some(_), .. }
		));
	}

	#[tokio::test]
	async fn fully_negotiated_resets_state_for_closed_substream() {
		let mut handler = notifs_handler();
		let (io, mut io2) = MockSubstream::negotiated().await;
		let mut codec = UviBytes::default();
		codec.set_max_len(usize::MAX);

		let notif_in = NotificationsInOpen {
			handshake: b"hello, world".to_vec(),
			negotiated_fallback: None,
			substream: NotificationsInSubstream::new(
				Framed::new(io, codec),
				NotificationsInSubstreamHandshake::NotSent,
			),
		};
		handler.on_connection_event(handler::ConnectionEvent::FullyNegotiatedInbound(
			handler::FullyNegotiatedInbound { protocol: (notif_in, 0), info: () },
		));

		// verify that the substream is in (partly) opened state
		assert!(std::matches!(handler.protocols[0].state, State::OpenDesiredByRemote { .. }));
		futures::future::poll_fn(|cx| {
			let mut buf = Vec::with_capacity(512);
			assert!(std::matches!(Pin::new(&mut io2).poll_read(cx, &mut buf), Poll::Pending));
			Poll::Ready(())
		})
		.await;

		// first instruct the handler to open a connection and then close it right after
		// so the handler is in state `Closed { pending_opening: true }`
		handler.on_behaviour_event(NotifsHandlerIn::Open { protocol_index: 0 });
		assert!(std::matches!(
			handler.protocols[0].state,
			State::Opening { in_substream: Some(_), .. }
		));

		handler.on_behaviour_event(NotifsHandlerIn::Close { protocol_index: 0 });
		assert!(std::matches!(handler.protocols[0].state, State::Closed { pending_opening: true }));

		// verify that if the the outbound substream is successfully negotiated, the state is not
		// changed as the substream was commanded to be closed by the handler.
		let (io, _io2) = MockSubstream::negotiated().await;
		let mut codec = UviBytes::default();
		codec.set_max_len(usize::MAX);

		let notif_out = NotificationsOutOpen {
			handshake: b"hello, world".to_vec(),
			negotiated_fallback: None,
			substream: NotificationsOutSubstream::new(Framed::new(io, codec)),
		};
		handler.on_connection_event(handler::ConnectionEvent::FullyNegotiatedOutbound(
			handler::FullyNegotiatedOutbound { protocol: notif_out, info: 0 },
		));

		assert!(std::matches!(
			handler.protocols[0].state,
			State::Closed { pending_opening: false }
		));
	}

	#[tokio::test]
	async fn fully_negotiated_resets_state_for_open_desired_substream() {
		let mut handler = notifs_handler();
		let (io, mut io2) = MockSubstream::negotiated().await;
		let mut codec = UviBytes::default();
		codec.set_max_len(usize::MAX);

		let notif_in = NotificationsInOpen {
			handshake: b"hello, world".to_vec(),
			negotiated_fallback: None,
			substream: NotificationsInSubstream::new(
				Framed::new(io, codec),
				NotificationsInSubstreamHandshake::NotSent,
			),
		};
		handler.on_connection_event(handler::ConnectionEvent::FullyNegotiatedInbound(
			handler::FullyNegotiatedInbound { protocol: (notif_in, 0), info: () },
		));

		// verify that the substream is in (partly) opened state
		assert!(std::matches!(handler.protocols[0].state, State::OpenDesiredByRemote { .. }));
		futures::future::poll_fn(|cx| {
			let mut buf = Vec::with_capacity(512);
			assert!(std::matches!(Pin::new(&mut io2).poll_read(cx, &mut buf), Poll::Pending));
			Poll::Ready(())
		})
		.await;

		// first instruct the handler to open a connection and then close it right after
		// so the handler is in state `Closed { pending_opening: true }`
		handler.on_behaviour_event(NotifsHandlerIn::Open { protocol_index: 0 });
		assert!(std::matches!(
			handler.protocols[0].state,
			State::Opening { in_substream: Some(_), .. }
		));

		handler.on_behaviour_event(NotifsHandlerIn::Close { protocol_index: 0 });
		assert!(std::matches!(handler.protocols[0].state, State::Closed { pending_opening: true }));

		// attempt to open another inbound substream and verify that it is rejected
		let (io, _io2) = MockSubstream::negotiated().await;
		let mut codec = UviBytes::default();
		codec.set_max_len(usize::MAX);

		let notif_in = NotificationsInOpen {
			handshake: b"hello, world".to_vec(),
			negotiated_fallback: None,
			substream: NotificationsInSubstream::new(
				Framed::new(io, codec),
				NotificationsInSubstreamHandshake::NotSent,
			),
		};
		handler.on_connection_event(handler::ConnectionEvent::FullyNegotiatedInbound(
			handler::FullyNegotiatedInbound { protocol: (notif_in, 0), info: () },
		));

		assert!(std::matches!(
			handler.protocols[0].state,
			State::OpenDesiredByRemote { pending_opening: true, .. }
		));

		// verify that if the the outbound substream is successfully negotiated, the state is not
		// changed as the substream was commanded to be closed by the handler.
		let (io, _io2) = MockSubstream::negotiated().await;
		let mut codec = UviBytes::default();
		codec.set_max_len(usize::MAX);

		let notif_out = NotificationsOutOpen {
			handshake: b"hello, world".to_vec(),
			negotiated_fallback: None,
			substream: NotificationsOutSubstream::new(Framed::new(io, codec)),
		};

		handler.on_connection_event(handler::ConnectionEvent::FullyNegotiatedOutbound(
			handler::FullyNegotiatedOutbound { protocol: notif_out, info: 0 },
		));

		assert!(std::matches!(
			handler.protocols[0].state,
			State::OpenDesiredByRemote { pending_opening: false, .. }
		));
	}

	#[tokio::test]
	async fn dial_upgrade_error_resets_closed_outbound_state() {
		let mut handler = notifs_handler();
		let (io, mut io2) = MockSubstream::negotiated().await;
		let mut codec = UviBytes::default();
		codec.set_max_len(usize::MAX);

		let notif_in = NotificationsInOpen {
			handshake: b"hello, world".to_vec(),
			negotiated_fallback: None,
			substream: NotificationsInSubstream::new(
				Framed::new(io, codec),
				NotificationsInSubstreamHandshake::NotSent,
			),
		};
		handler.on_connection_event(handler::ConnectionEvent::FullyNegotiatedInbound(
			handler::FullyNegotiatedInbound { protocol: (notif_in, 0), info: () },
		));

		// verify that the substream is in (partly) opened state
		assert!(std::matches!(handler.protocols[0].state, State::OpenDesiredByRemote { .. }));
		futures::future::poll_fn(|cx| {
			let mut buf = Vec::with_capacity(512);
			assert!(std::matches!(Pin::new(&mut io2).poll_read(cx, &mut buf), Poll::Pending));
			Poll::Ready(())
		})
		.await;

		// first instruct the handler to open a connection and then close it right after
		// so the handler is in state `Closed { pending_opening: true }`
		handler.on_behaviour_event(NotifsHandlerIn::Open { protocol_index: 0 });
		assert!(std::matches!(
			handler.protocols[0].state,
			State::Opening { in_substream: Some(_), .. }
		));

		handler.on_behaviour_event(NotifsHandlerIn::Close { protocol_index: 0 });
		assert!(std::matches!(handler.protocols[0].state, State::Closed { pending_opening: true }));

		// inject dial failure to an already closed substream and verify outbound state is reset
		handler.on_connection_event(handler::ConnectionEvent::DialUpgradeError(
			handler::DialUpgradeError { info: 0, error: ConnectionHandlerUpgrErr::Timeout },
		));
		assert!(std::matches!(
			handler.protocols[0].state,
			State::Closed { pending_opening: false }
		));
	}

	#[tokio::test]
	async fn dial_upgrade_error_resets_open_desired_state() {
		let mut handler = notifs_handler();
		let (io, mut io2) = MockSubstream::negotiated().await;
		let mut codec = UviBytes::default();
		codec.set_max_len(usize::MAX);

		let notif_in = NotificationsInOpen {
			handshake: b"hello, world".to_vec(),
			negotiated_fallback: None,
			substream: NotificationsInSubstream::new(
				Framed::new(io, codec),
				NotificationsInSubstreamHandshake::NotSent,
			),
		};
		handler.on_connection_event(handler::ConnectionEvent::FullyNegotiatedInbound(
			handler::FullyNegotiatedInbound { protocol: (notif_in, 0), info: () },
		));

		// verify that the substream is in (partly) opened state
		assert!(std::matches!(handler.protocols[0].state, State::OpenDesiredByRemote { .. }));
		futures::future::poll_fn(|cx| {
			let mut buf = Vec::with_capacity(512);
			assert!(std::matches!(Pin::new(&mut io2).poll_read(cx, &mut buf), Poll::Pending));
			Poll::Ready(())
		})
		.await;

		// first instruct the handler to open a connection and then close it right after
		// so the handler is in state `Closed { pending_opening: true }`
		handler.on_behaviour_event(NotifsHandlerIn::Open { protocol_index: 0 });
		assert!(std::matches!(
			handler.protocols[0].state,
			State::Opening { in_substream: Some(_), .. }
		));

		handler.on_behaviour_event(NotifsHandlerIn::Close { protocol_index: 0 });
		assert!(std::matches!(handler.protocols[0].state, State::Closed { pending_opening: true }));

		let (io, _io2) = MockSubstream::negotiated().await;
		let mut codec = UviBytes::default();
		codec.set_max_len(usize::MAX);

		let notif_in = NotificationsInOpen {
			handshake: b"hello, world".to_vec(),
			negotiated_fallback: None,
			substream: NotificationsInSubstream::new(
				Framed::new(io, codec),
				NotificationsInSubstreamHandshake::NotSent,
			),
		};
		handler.on_connection_event(handler::ConnectionEvent::FullyNegotiatedInbound(
			handler::FullyNegotiatedInbound { protocol: (notif_in, 0), info: () },
		));

		assert!(std::matches!(
			handler.protocols[0].state,
			State::OpenDesiredByRemote { pending_opening: true, .. }
		));

		// inject dial failure to an already closed substream and verify outbound state is reset
		handler.on_connection_event(handler::ConnectionEvent::DialUpgradeError(
			handler::DialUpgradeError { info: 0, error: ConnectionHandlerUpgrErr::Timeout },
		));
		assert!(std::matches!(
			handler.protocols[0].state,
			State::OpenDesiredByRemote { pending_opening: false, .. }
		));
	}

	#[tokio::test]
	async fn sync_notifications_clogged() {
		let mut handler = notifs_handler();
		let (io, _) = MockSubstream::negotiated().await;
		let codec = UviBytes::default();

		let (async_tx, async_rx) = futures::channel::mpsc::channel(ASYNC_NOTIFICATIONS_BUFFER_SIZE);
		let (sync_tx, sync_rx) = futures::channel::mpsc::channel(1);
		let notifications_sink = NotificationsSink {
			inner: Arc::new(NotificationsSinkInner {
				peer_id: PeerId::random(),
				async_channel: FuturesMutex::new(async_tx),
				sync_channel: Mutex::new(Some(sync_tx)),
			}),
		};

		handler.protocols[0].state = State::Open {
			notifications_sink_rx: stream::select(async_rx.fuse(), sync_rx.fuse()).peekable(),
			out_substream: Some(NotificationsOutSubstream::new(Framed::new(io, codec))),
			in_substream: None,
		};

		notifications_sink.send_sync_notification(vec![1, 3, 3, 7]);
		notifications_sink.send_sync_notification(vec![1, 3, 3, 8]);
		notifications_sink.send_sync_notification(vec![1, 3, 3, 9]);
		notifications_sink.send_sync_notification(vec![1, 3, 4, 0]);

		futures::future::poll_fn(|cx| {
			assert!(std::matches!(
				handler.poll(cx),
				Poll::Ready(ConnectionHandlerEvent::Close(
					NotifsHandlerError::SyncNotificationsClogged,
				))
			));
			Poll::Ready(())
		})
		.await;
	}

	#[tokio::test]
	async fn close_desired_by_remote() {
		let mut handler = notifs_handler();
		let (io, io2) = MockSubstream::negotiated().await;
		let mut codec = UviBytes::default();
		codec.set_max_len(usize::MAX);

		let notif_in = NotificationsInOpen {
			handshake: b"hello, world".to_vec(),
			negotiated_fallback: None,
			substream: NotificationsInSubstream::new(
				Framed::new(io, codec),
				NotificationsInSubstreamHandshake::PendingSend(vec![1, 2, 3, 4]),
			),
		};

		// add new inbound substream but close it immediately and verify that correct events are
		// emitted
		handler.on_connection_event(handler::ConnectionEvent::FullyNegotiatedInbound(
			handler::FullyNegotiatedInbound { protocol: (notif_in, 0), info: () },
		));
		drop(io2);

		futures::future::poll_fn(|cx| {
			assert!(std::matches!(
				handler.poll(cx),
				Poll::Ready(ConnectionHandlerEvent::Custom(
					NotifsHandlerOut::OpenDesiredByRemote { protocol_index: 0 },
				))
			));
			assert!(std::matches!(
				handler.poll(cx),
				Poll::Ready(ConnectionHandlerEvent::Custom(NotifsHandlerOut::CloseDesired {
					protocol_index: 0
				},))
			));
			Poll::Ready(())
		})
		.await;
	}
}
