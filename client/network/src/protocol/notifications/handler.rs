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

//! Implementations of the `IntoProtocolsHandler` and `ProtocolsHandler` traits for both incoming
//! and outgoing substreams for all gossiping protocols.
//!
//! This is the main implementation of `ProtocolsHandler` in this crate, that handles all the
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

use crate::protocol::notifications::upgrade::{
	NotificationsHandshakeError, NotificationsIn, NotificationsInSubstream, NotificationsOut,
	NotificationsOutSubstream, UpgradeCollec,
};

use bytes::BytesMut;
use futures::{
	channel::mpsc,
	lock::{Mutex as FuturesMutex, MutexGuard as FuturesMutexGuard},
	prelude::*,
};
use libp2p::{
	core::{
		upgrade::{InboundUpgrade, OutboundUpgrade},
		ConnectedPoint, PeerId,
	},
	swarm::{
		IntoProtocolsHandler, KeepAlive, NegotiatedSubstream, ProtocolsHandler,
		ProtocolsHandlerEvent, ProtocolsHandlerUpgrErr, SubstreamProtocol,
	},
};
use log::error;
use parking_lot::{Mutex, RwLock};
use std::{
	borrow::Cow,
	collections::VecDeque,
	mem,
	pin::Pin,
	str,
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

/// Implements the `IntoProtocolsHandler` trait of libp2p.
///
/// Every time a connection with a remote starts, an instance of this struct is created and
/// sent to a background task dedicated to this connection. Once the connection is established,
/// it is turned into a [`NotifsHandler`].
///
/// See the documentation at the module level for more information.
pub struct NotifsHandlerProto {
	/// Name of protocols, prototypes for upgrades for inbound substreams, and the message we
	/// send or respond with in the handshake.
	protocols: Vec<ProtocolConfig>,
}

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
		ProtocolsHandlerEvent<NotificationsOut, usize, NotifsHandlerOut, NotifsHandlerError>,
	>,
}

/// Configuration for a notifications protocol.
#[derive(Debug, Clone)]
pub struct ProtocolConfig {
	/// Name of the protocol.
	pub name: Cow<'static, str>,
	/// Names of the protocol to use if the main one isn't available.
	pub fallback_names: Vec<Cow<'static, str>>,
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

impl IntoProtocolsHandler for NotifsHandlerProto {
	type Handler = NotifsHandler;

	fn inbound_protocol(&self) -> UpgradeCollec<NotificationsIn> {
		self.protocols
			.iter()
			.map(|cfg| {
				NotificationsIn::new(
					cfg.name.clone(),
					cfg.fallback_names.clone(),
					cfg.max_notification_size,
				)
			})
			.collect::<UpgradeCollec<_>>()
	}

	fn into_handler(self, peer_id: &PeerId, connected_point: &ConnectedPoint) -> Self::Handler {
		NotifsHandler {
			protocols: self
				.protocols
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
			peer_id: *peer_id,
			endpoint: connected_point.clone(),
			when_connection_open: Instant::now(),
			events_queue: VecDeque::with_capacity(16),
		}
	}
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
		negotiated_fallback: Option<Cow<'static, str>>,
		/// The endpoint of the connection that is open for custom protocols.
		endpoint: ConnectedPoint,
		/// Handshake that was sent to us.
		/// This is normally a "Status" message, but this out of the concern of this code.
		received_handshake: Vec<u8>,
		/// How notifications can be sent to this node.
		notifications_sink: NotificationsSink,
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
	pub fn send_sync_notification<'a>(&'a self, message: impl Into<Vec<u8>>) {
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
	pub async fn reserve_notification<'a>(&'a self) -> Result<Ready<'a>, ()> {
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

impl NotifsHandlerProto {
	/// Builds a new handler.
	///
	/// `list` is a list of notification protocols names, the message to send as part of the
	/// handshake, and the maximum allowed size of a notification. At the moment, the message
	/// is always the same whether we open a substream ourselves or respond to handshake from
	/// the remote.
	pub fn new(list: impl Into<Vec<ProtocolConfig>>) -> Self {
		Self { protocols: list.into() }
	}
}

impl ProtocolsHandler for NotifsHandler {
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

	fn inject_fully_negotiated_inbound(
		&mut self,
		(mut in_substream_open, protocol_index): <Self::InboundProtocol as InboundUpgrade<
			NegotiatedSubstream,
		>>::Output,
		(): (),
	) {
		let mut protocol_info = &mut self.protocols[protocol_index];
		match protocol_info.state {
			State::Closed { pending_opening } => {
				self.events_queue.push_back(ProtocolsHandlerEvent::Custom(
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
	}

	fn inject_fully_negotiated_outbound(
		&mut self,
		new_open: <Self::OutboundProtocol as OutboundUpgrade<NegotiatedSubstream>>::Output,
		protocol_index: Self::OutboundOpenInfo,
	) {
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
			State::Opening { ref mut in_substream } => {
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

				self.events_queue.push_back(ProtocolsHandlerEvent::Custom(
					NotifsHandlerOut::OpenResultOk {
						protocol_index,
						negotiated_fallback: new_open.negotiated_fallback,
						endpoint: self.endpoint.clone(),
						received_handshake: new_open.handshake,
						notifications_sink,
					},
				));
			},
		}
	}

	fn inject_event(&mut self, message: NotifsHandlerIn) {
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
								ProtocolsHandlerEvent::OutboundSubstreamRequest {
									protocol: SubstreamProtocol::new(proto, protocol_index)
										.with_timeout(OPEN_TIMEOUT),
								},
							);
						}

						protocol_info.state = State::Opening { in_substream: None };
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
								ProtocolsHandlerEvent::OutboundSubstreamRequest {
									protocol: SubstreamProtocol::new(proto, protocol_index)
										.with_timeout(OPEN_TIMEOUT),
								},
							);
						}

						in_substream.send_handshake(handshake_message);

						// The state change is done in two steps because of borrowing issues.
						let in_substream = match mem::replace(
							&mut protocol_info.state,
							State::Opening { in_substream: None },
						) {
							State::OpenDesiredByRemote { in_substream, .. } => in_substream,
							_ => unreachable!(),
						};
						protocol_info.state = State::Opening { in_substream: Some(in_substream) };
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

						self.events_queue.push_back(ProtocolsHandlerEvent::Custom(
							NotifsHandlerOut::OpenResultErr { protocol_index },
						));
					},
					State::OpenDesiredByRemote { pending_opening, .. } => {
						self.protocols[protocol_index].state = State::Closed { pending_opening };
					},
					State::Closed { .. } => {},
				}

				self.events_queue.push_back(ProtocolsHandlerEvent::Custom(
					NotifsHandlerOut::CloseResult { protocol_index },
				));
			},
		}
	}

	fn inject_dial_upgrade_error(
		&mut self,
		num: usize,
		_: ProtocolsHandlerUpgrErr<NotificationsHandshakeError>,
	) {
		match self.protocols[num].state {
			State::Closed { ref mut pending_opening } |
			State::OpenDesiredByRemote { ref mut pending_opening, .. } => {
				debug_assert!(*pending_opening);
				*pending_opening = false;
			},

			State::Opening { .. } => {
				self.protocols[num].state = State::Closed { pending_opening: false };

				self.events_queue.push_back(ProtocolsHandlerEvent::Custom(
					NotifsHandlerOut::OpenResultErr { protocol_index: num },
				));
			},

			// No substream is being open when already `Open`.
			State::Open { .. } => debug_assert!(false),
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
		ProtocolsHandlerEvent<
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
							return Poll::Ready(ProtocolsHandlerEvent::Close(
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
							return Poll::Ready(ProtocolsHandlerEvent::Custom(event))
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
				State::Opening { in_substream: None } => {},

				State::Open { in_substream: in_substream @ Some(_), .. } =>
					match Stream::poll_next(Pin::new(in_substream.as_mut().unwrap()), cx) {
						Poll::Pending => {},
						Poll::Ready(Some(Ok(message))) => {
							let event = NotifsHandlerOut::Notification { protocol_index, message };
							return Poll::Ready(ProtocolsHandlerEvent::Custom(event))
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
							return Poll::Ready(ProtocolsHandlerEvent::Custom(
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
