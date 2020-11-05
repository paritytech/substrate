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

//! Implementations of the `IntoProtocolsHandler` and `ProtocolsHandler` traits for both incoming
//! and outgoing substreams for all gossiping protocols together.
//!
//! This is the main implementation of `ProtocolsHandler` in this crate, that handles all the
//! protocols that are Substrate-related and outside of the scope of libp2p.
//!
//! # Usage
//!
//! From an API perspective, the [`NotifsHandler`] is always in one of the following state:
//!
//! - Closed substreams. This is the initial state.
//! - Closed substreams, but remote desires them to be open.
//! - Open substreams.
//! - Open substreams, but remote desires them to be closed.
//!
//! The [`NotifsHandler`] can spontaneously switch between these states:
//!
//! - "Closed substreams" to "Closed substreams but open desired". When that happens, a
//! [`NotifsHandlerOut::OpenDesired`] is emitted.
//! - "Closed substreams but open desired" to "Closed substreams" (i.e. the remote has cancelled
//! their request). When that happens, a [`NotifsHandlerOut::CloseDesired`] is emitted.
//! - "Open substreams" to "Open substreams but close desired". When that happens, a
//! [`NotifsHandlerOut::CloseDesired`] is emitted.
//!
//! The user can instruct the `NotifsHandler` to switch from "closed" to "open" or vice-versa by
//! sending either a [`NotifsHandlerIn::Open`] or a [`NotifsHandlerIn::Close`]. The `NotifsHandler`
//! must answer with [`NotifsHandlerOut::OpenResultOk`] or [`NotifsHandlerOut::OpenResultErr`], or
//! with [`NotifsHandlerOut::CloseResult`].
//!
//! When a [`NotifsHandlerOut::OpenResultOk`] is emitted, the `NotifsHandler` is now in the open
//! state. When a [`NotifsHandlerOut::OpenResultErr`] or [`NotifsHandlerOut::CloseResult`] is
//! emitted, the `NotifsHandler` is now (or remains) in the closed state.
//!
//! When a [`NotifsHandlerOut::OpenDesired`] is emitted, the user should always send back either a
//! [`NotifsHandlerIn::Open`] or a [`NotifsHandlerIn::Close`].If this isn't done, the remote will
//! be left in a pending state.

use crate::protocol::generic_proto::{
	handler::legacy::{LegacyProtoHandler, LegacyProtoHandlerProto, LegacyProtoHandlerIn, LegacyProtoHandlerOut},
	handler::notif_in::{NotifsInHandlerProto, NotifsInHandler, NotifsInHandlerIn, NotifsInHandlerOut},
	handler::notif_out::{NotifsOutHandlerProto, NotifsOutHandler, NotifsOutHandlerIn, NotifsOutHandlerOut},
	upgrade::{NotificationsIn, NotificationsOut, NotificationsHandshakeError, RegisteredProtocol, UpgradeCollec},
};

use bytes::BytesMut;
use libp2p::core::{either::EitherOutput, ConnectedPoint, PeerId};
use libp2p::core::upgrade::{UpgradeError, SelectUpgrade, InboundUpgrade, OutboundUpgrade};
use libp2p::swarm::{
	ProtocolsHandler, ProtocolsHandlerEvent,
	IntoProtocolsHandler,
	KeepAlive,
	ProtocolsHandlerUpgrErr,
	SubstreamProtocol,
	NegotiatedSubstream,
};
use futures::{
	channel::mpsc,
	lock::{Mutex as FuturesMutex, MutexGuard as FuturesMutexGuard},
	prelude::*
};
use log::error;
use parking_lot::{Mutex, RwLock};
use std::{borrow::Cow, collections::VecDeque, mem, str, sync::Arc, task::{Context, Poll}};

/// Number of pending notifications in asynchronous contexts.
/// See [`NotificationsSink::reserve_notification`] for context.
const ASYNC_NOTIFICATIONS_BUFFER_SIZE: usize = 8;
/// Number of pending notifications in synchronous contexts.
const SYNC_NOTIFICATIONS_BUFFER_SIZE: usize = 2048;

/// Implements the `IntoProtocolsHandler` trait of libp2p.
///
/// Every time a connection with a remote starts, an instance of this struct is created and
/// sent to a background task dedicated to this connection. Once the connection is established,
/// it is turned into a [`NotifsHandler`].
///
/// See the documentation at the module level for more information.
pub struct NotifsHandlerProto {
	/// Prototypes for handlers for inbound substreams, and the message we respond with in the
	/// handshake.
	in_handlers: Vec<(NotifsInHandlerProto, Arc<RwLock<Vec<u8>>>)>,

	/// Prototypes for handlers for outbound substreams, and the initial handshake message we send.
	out_handlers: Vec<(NotifsOutHandlerProto, Arc<RwLock<Vec<u8>>>)>,

	/// Prototype for handler for backwards-compatibility.
	legacy: LegacyProtoHandlerProto,
}

/// The actual handler once the connection has been established.
///
/// See the documentation at the module level for more information.
pub struct NotifsHandler {
	/// Handlers for inbound substreams, and the message we respond with in the handshake.
	in_handlers: Vec<(NotifsInHandler, Arc<RwLock<Vec<u8>>>)>,

	/// Handlers for outbound substreams, and the initial handshake message we send.
	out_handlers: Vec<(NotifsOutHandler, Arc<RwLock<Vec<u8>>>)>,

	/// Whether we are the connection dialer or listener.
	endpoint: ConnectedPoint,

	/// Handler for backwards-compatibility.
	legacy: LegacyProtoHandler,

	/// State of this handler.
	state: State,

	/// Events to return in priority from `poll`.
	events_queue: VecDeque<
		ProtocolsHandlerEvent<NotificationsOut, usize, NotifsHandlerOut, NotifsHandlerError>
	>,
}

/// See the module-level documentation to learn about the meaning of these variants.
#[derive(Debug)]
enum State {
	/// Handler is in the "Closed" state.
	Closed {
		/// When we receive inbound substream requests, we push here the index within
		/// [`NotisHandler::in_handlers`], and process them when an `Open` or `Close` request is
		/// received.
		///
		/// If this is non-empty, a [`NotifsHandlerOut::OpenDesired`] has been emitted. If this
		/// transitions from non-empty to empty, a [`NotisHandlerOut::CloseDesired`] or a
		/// [`NotisHandlerOut::CloseResult`] is emitted.
		pending_in: Vec<usize>,
	},

	/// Handler is in the "Closed" state, but has received a [`NotifsHandlerIn::Open`] and is
	/// consequently trying to open the various notifications substreams.
	///
	/// A [`NotifsHandlerOut::OpenResultOk`] or a [`NotifsHandlerOut::OpenResultErr`] event must
	/// be emitted when transitionning to respectively [`State::Open`] or [`State::Closed`].
	Opening {
		/// In the situation where either the legacy substream has been opened or the
		/// handshake-bearing notifications protocol is open, but we haven't sent out any
		/// [`NotifsHandlerOut::Open`] event yet, this contains the received handshake waiting to
		/// be reported through the external API.
		pending_handshake: Option<Vec<u8>>,
	},

	/// Handler is in the "Open" state.
	Open {
		/// Contains the two `Receiver`s connected to the [`NotificationsSink`] that has been
		/// sent out. The notifications to send out can be pulled from this receivers.
		/// We use two different channels in order to have two different channel sizes, but from
		/// the receiving point of view, the two channels are the same.
		/// The receivers are fused in case the user drops the [`NotificationsSink`] entirely.
		notifications_sink_rx: stream::Select<
			stream::Fuse<mpsc::Receiver<NotificationsSinkMessage>>,
			stream::Fuse<mpsc::Receiver<NotificationsSinkMessage>>
		>,

		/// If true, at least one substream has been closed and a
		/// [`NotifsHandlerOut::CloseDesired`] message has been sent out.
		want_closed: bool,
	},
}

impl IntoProtocolsHandler for NotifsHandlerProto {
	type Handler = NotifsHandler;

	fn inbound_protocol(&self) -> SelectUpgrade<UpgradeCollec<NotificationsIn>, RegisteredProtocol> {
		let in_handlers = self.in_handlers.iter()
			.map(|(h, _)| h.inbound_protocol())
			.collect::<UpgradeCollec<_>>();

		SelectUpgrade::new(in_handlers, self.legacy.inbound_protocol())
	}

	fn into_handler(self, remote_peer_id: &PeerId, connected_point: &ConnectedPoint) -> Self::Handler {
		NotifsHandler {
			in_handlers: self.in_handlers
				.into_iter()
				.map(|(proto, msg)| (proto.into_handler(remote_peer_id, connected_point), msg))
				.collect(),
			out_handlers: self.out_handlers
				.into_iter()
				.map(|(proto, msg)| (proto.into_handler(remote_peer_id, connected_point), msg))
				.collect(),
			endpoint: connected_point.clone(),
			legacy: self.legacy.into_handler(remote_peer_id, connected_point),
			state: State::Closed {
				pending_in: Vec::new(),
			},
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
	Open,

	/// Instruct the handler to close the notification substreams, or reject any pending incoming
	/// substream request.
	///
	/// Must always be answered by a [`NotifsHandlerOut::CloseResult`] event.
	Close,
}

/// Event that can be emitted by a `NotifsHandler`.
#[derive(Debug)]
pub enum NotifsHandlerOut {
	/// Acknowledges a [`NotifsHandlerIn::Open`].
	OpenResultOk {
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
	OpenResultErr,

	/// Acknowledges a [`NotifsHandlerIn::Close`].
	CloseResult,

	/// The remote would like the substreams to be open. Send a [`NotifsHandlerIn::Open`] or a
	/// [`NotifsHandlerIn::Close`] in order to either accept or deny this request. If a
	/// [`NotifsHandlerIn::Open`] or [`NotifsHandlerIn::Close`] has been sent before and has not
	/// yet been acknowledged by a matching [`NotifsHandlerOut`], then you don't need to a send
	/// another [`NotifsHandlerIn`].
	OpenDesired,

	/// The remote would like the substreams to be closed. Send a [`NotifsHandlerIn::Close`] in
	/// order to close them. If a [`NotifsHandlerIn::Close`] has been sent before and has not yet
	/// been acknowledged by a [`NotifsHandlerOut::CloseResult`], then you don't need to a send
	/// another one.
	CloseDesired,

	/// Received a non-gossiping message on the legacy substream.
	///
	/// Can only happen when the handler is in the open state.
	CustomMessage {
		/// Message that has been received.
		///
		/// Keep in mind that this can be a `ConsensusMessage` message, which then contains a
		/// notification.
		message: BytesMut,
	},

	/// Received a message on a custom protocol substream.
	///
	/// Can only happen when the handler is in the open state.
	Notification {
		/// Name of the protocol of the message.
		protocol_name: Cow<'static, str>,

		/// Message that has been received.
		message: BytesMut,
	},
}

/// Sink connected directly to the node background task. Allows sending notifications to the peer.
///
/// Can be cloned in order to obtain multiple references to the same peer.
#[derive(Debug, Clone)]
pub struct NotificationsSink {
	inner: Arc<NotificationsSinkInner>,
}

#[derive(Debug)]
struct NotificationsSinkInner {
	/// Sender to use in asynchronous contexts. Uses an asynchronous mutex.
	async_channel: FuturesMutex<mpsc::Sender<NotificationsSinkMessage>>,
	/// Sender to use in synchronous contexts. Uses a synchronous mutex.
	/// This channel has a large capacity and is meant to be used in contexts where
	/// back-pressure cannot be properly exerted.
	/// It will be removed in a future version.
	sync_channel: Mutex<mpsc::Sender<NotificationsSinkMessage>>,
}

/// Message emitted through the [`NotificationsSink`] and processed by the background task
/// dedicated to the peer.
#[derive(Debug)]
enum NotificationsSinkMessage {
	/// Message emitted by [`NotificationsSink::reserve_notification`] and
	/// [`NotificationsSink::write_notification_now`].
	Notification {
		protocol_name: Cow<'static, str>,
		message: Vec<u8>,
	},

	/// Must close the connection.
	ForceClose,
}

impl NotificationsSink {
	/// Sends a notification to the peer.
	///
	/// If too many messages are already buffered, the notification is silently discarded and the
	/// connection to the peer will be closed shortly after.
	///
	/// The protocol name is expected to be checked ahead of calling this method. It is a logic
	/// error to send a notification using an unknown protocol.
	///
	/// This method will be removed in a future version.
	pub fn send_sync_notification<'a>(
		&'a self,
		protocol_name: Cow<'static, str>,
		message: impl Into<Vec<u8>>
	) {
		let mut lock = self.inner.sync_channel.lock();
		let result = lock.try_send(NotificationsSinkMessage::Notification {
			protocol_name,
			message: message.into()
		});

		if result.is_err() {
			// Cloning the `mpsc::Sender` guarantees the allocation of an extra spot in the
			// buffer, and therefore that `try_send` will succeed.
			let _result2 = lock.clone().try_send(NotificationsSinkMessage::ForceClose);
			debug_assert!(_result2.map(|()| true).unwrap_or_else(|err| err.is_disconnected()));
		}
	}

	/// Wait until the remote is ready to accept a notification.
	///
	/// Returns an error in the case where the connection is closed.
	///
	/// The protocol name is expected to be checked ahead of calling this method. It is a logic
	/// error to send a notification using an unknown protocol.
	pub async fn reserve_notification<'a>(&'a self, protocol_name: Cow<'static, str>) -> Result<Ready<'a>, ()> {
		let mut lock = self.inner.async_channel.lock().await;

		let poll_ready = future::poll_fn(|cx| lock.poll_ready(cx)).await;
		if poll_ready.is_ok() {
			Ok(Ready { protocol_name: protocol_name, lock })
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
	/// Name of the protocol. Should match one of the protocols passed at initialization.
	protocol_name: Cow<'static, str>,
}

impl<'a> Ready<'a> {
	/// Consumes this slots reservation and actually queues the notification.
	///
	/// Returns an error if the substream has been closed.
	pub fn send(
		mut self,
		notification: impl Into<Vec<u8>>
	) -> Result<(), ()> {
		self.lock.start_send(NotificationsSinkMessage::Notification {
			protocol_name: self.protocol_name,
			message: notification.into(),
		}).map_err(|_| ())
	}
}

/// Error specific to the collection of protocols.
#[derive(Debug, derive_more::Display, derive_more::Error)]
pub enum NotifsHandlerError {
	/// Channel of synchronous notifications is full.
	SyncNotificationsClogged,
	/// Error in legacy protocol.
	Legacy(<LegacyProtoHandler as ProtocolsHandler>::Error),
}

impl NotifsHandlerProto {
	/// Builds a new handler.
	///
	/// `list` is a list of notification protocols names, and the message to send as part of the
	/// handshake. At the moment, the message is always the same whether we open a substream
	/// ourselves or respond to handshake from the remote.
	///
	/// The first protocol in `list` is special-cased as the protocol that contains the handshake
	/// to report through the [`NotifsHandlerOut::Open`] event.
	///
	/// # Panic
	///
	/// - Panics if `list` is empty.
	///
	pub fn new(
		legacy: RegisteredProtocol,
		list: impl Into<Vec<(Cow<'static, str>, Arc<RwLock<Vec<u8>>>)>>,
	) -> Self {
		let list = list.into();
		assert!(!list.is_empty());

		let out_handlers = list
			.clone()
			.into_iter()
			.map(|(proto_name, initial_message)| {
				(NotifsOutHandlerProto::new(proto_name), initial_message)
			}).collect();

		let in_handlers = list.clone()
			.into_iter()
			.map(|(proto_name, msg)| (NotifsInHandlerProto::new(proto_name), msg))
			.collect();

		NotifsHandlerProto {
			in_handlers,
			out_handlers,
			legacy: LegacyProtoHandlerProto::new(legacy),
		}
	}
}

impl ProtocolsHandler for NotifsHandler {
	type InEvent = NotifsHandlerIn;
	type OutEvent = NotifsHandlerOut;
	type Error = NotifsHandlerError;
	type InboundProtocol = SelectUpgrade<UpgradeCollec<NotificationsIn>, RegisteredProtocol>;
	type OutboundProtocol = NotificationsOut;
	// Index within the `out_handlers`
	type OutboundOpenInfo = usize;
	type InboundOpenInfo = ();

	fn listen_protocol(&self) -> SubstreamProtocol<Self::InboundProtocol, ()> {
		let in_handlers = self.in_handlers.iter()
			.map(|(h, _)| h.listen_protocol().into_upgrade().1)
			.collect::<UpgradeCollec<_>>();

		let proto = SelectUpgrade::new(in_handlers, self.legacy.listen_protocol().into_upgrade().1);
		SubstreamProtocol::new(proto, ())
	}

	fn inject_fully_negotiated_inbound(
		&mut self,
		out: <Self::InboundProtocol as InboundUpgrade<NegotiatedSubstream>>::Output,
		(): ()
	) {
		match out {
			EitherOutput::First((out, num)) =>
				self.in_handlers[num].0.inject_fully_negotiated_inbound(out, ()),
			EitherOutput::Second(out) =>
				self.legacy.inject_fully_negotiated_inbound(out, ()),
		}
	}

	fn inject_fully_negotiated_outbound(
		&mut self,
		out: <Self::OutboundProtocol as OutboundUpgrade<NegotiatedSubstream>>::Output,
		num: Self::OutboundOpenInfo
	) {
		self.out_handlers[num].0.inject_fully_negotiated_outbound(out, ())
	}

	fn inject_event(&mut self, message: NotifsHandlerIn) {
		match message {
			NotifsHandlerIn::Open => {
				match &mut self.state {
					State::Closed { pending_in } => {
						for (handler, initial_message) in &mut self.out_handlers {
							// We create `initial_message` on a separate line to be sure that the
							// lock is released as soon as possible.
							let initial_message = initial_message.read().clone();
							handler.inject_event(NotifsOutHandlerIn::Enable {
								initial_message,
							});
						}

						for num in pending_in.drain(..) {
							// We create `handshake_message` on a separate line to be sure
							// that the lock is released as soon as possible.
							let handshake_message = self.in_handlers[num].1.read().clone();
							self.in_handlers[num].0
								.inject_event(NotifsInHandlerIn::Accept(handshake_message));
						}

						self.state = State::Opening {
							pending_handshake: None,
						};
					},
					State::Opening { .. } |
					State::Open { .. } => {
						// As documented, it is forbidden to send an `Open` while there is already
						// one in the fly.
						error!(target: "sub-libp2p", "opening already-opened handler");
					},
				}
			},

			NotifsHandlerIn::Close => {
				match &mut self.state {
					State::Open { .. } |
					State::Opening { .. } => {
						self.legacy.inject_event(LegacyProtoHandlerIn::Close);
						for (handler, _) in &mut self.out_handlers {
							handler.inject_event(NotifsOutHandlerIn::Disable);
						}

						self.state = State::Closed {
							pending_in: Vec::new(),
						};

						if matches!(self.state, State::Opening { .. }) {
							self.events_queue.push_back(
								ProtocolsHandlerEvent::Custom(NotifsHandlerOut::OpenResultErr)
							);
						}
					},
					State::Closed { pending_in } => {
						for num in pending_in.drain(..) {
							self.in_handlers[num].0.inject_event(NotifsInHandlerIn::Refuse);
						}
					},
				}

				self.events_queue.push_back(
					ProtocolsHandlerEvent::Custom(NotifsHandlerOut::CloseResult)
				);
			},
		}
	}

	fn inject_dial_upgrade_error(
		&mut self,
		num: usize,
		err: ProtocolsHandlerUpgrErr<NotificationsHandshakeError>
	) {
		match err {
			ProtocolsHandlerUpgrErr::Timeout =>
				self.out_handlers[num].0.inject_dial_upgrade_error(
					(),
					ProtocolsHandlerUpgrErr::Timeout
				),
			ProtocolsHandlerUpgrErr::Timer =>
				self.out_handlers[num].0.inject_dial_upgrade_error(
					(),
					ProtocolsHandlerUpgrErr::Timer
				),
			ProtocolsHandlerUpgrErr::Upgrade(UpgradeError::Select(err)) =>
				self.out_handlers[num].0.inject_dial_upgrade_error(
					(),
					ProtocolsHandlerUpgrErr::Upgrade(UpgradeError::Select(err))
				),
			ProtocolsHandlerUpgrErr::Upgrade(UpgradeError::Apply(err)) =>
				self.out_handlers[num].0.inject_dial_upgrade_error(
					(),
					ProtocolsHandlerUpgrErr::Upgrade(UpgradeError::Apply(err))
				),
		}
	}

	fn connection_keep_alive(&self) -> KeepAlive {
		// Iterate over each handler and return the maximum value.

		let mut ret = self.legacy.connection_keep_alive();
		if ret.is_yes() {
			return KeepAlive::Yes;
		}

		for (handler, _) in &self.in_handlers {
			let val = handler.connection_keep_alive();
			if val.is_yes() {
				return KeepAlive::Yes;
			}
			if ret < val { ret = val; }
		}

		for (handler, _) in &self.out_handlers {
			let val = handler.connection_keep_alive();
			if val.is_yes() {
				return KeepAlive::Yes;
			}
			if ret < val { ret = val; }
		}

		ret
	}

	fn poll(
		&mut self,
		cx: &mut Context,
	) -> Poll<
		ProtocolsHandlerEvent<Self::OutboundProtocol, Self::OutboundOpenInfo, Self::OutEvent, Self::Error>
	> {
		if let Some(ev) = self.events_queue.pop_front() {
			return Poll::Ready(ev);
		}

		if let State::Open { notifications_sink_rx, .. } = &mut self.state {
			'poll_notifs_sink: loop {
				// Before we poll the notifications sink receiver, check that all the notification
				// channels are ready to send a message.
				// TODO: it is planned that in the future we switch to one `NotificationsSink` per
				// protocol, in which case each sink should wait only for its corresponding handler
				// to be ready, and not all handlers
				// see https://github.com/paritytech/substrate/issues/5670
				for (out_handler, _) in &mut self.out_handlers {
					match out_handler.poll_ready(cx) {
						Poll::Ready(_) => {},
						Poll::Pending => break 'poll_notifs_sink,
					}
				}

				let message = match notifications_sink_rx.poll_next_unpin(cx) {
					Poll::Ready(Some(msg)) => msg,
					Poll::Ready(None) | Poll::Pending => break,
				};

				match message {
					NotificationsSinkMessage::Notification {
						protocol_name,
						message
					} => {
						let mut found_any_with_name = false;

						for (handler, _) in &mut self.out_handlers {
							if *handler.protocol_name() == protocol_name {
								found_any_with_name = true;
								if handler.is_open() {
									handler.send_or_discard(message);
									continue 'poll_notifs_sink;
								}
							}
						}

						// This code can be reached via the following scenarios:
						//
						// - User tried to send a notification on a non-existing protocol. This
						// most likely relates to https://github.com/paritytech/substrate/issues/6827
						// - User tried to send a notification to a peer we're not or no longer
						// connected to. This happens in a normal scenario due to the racy nature
						// of connections and disconnections, and is benign.
						//
						// We print a warning in the former condition.
						if !found_any_with_name {
							log::warn!(
								target: "sub-libp2p",
								"Tried to send a notification on non-registered protocol: {:?}",
								protocol_name
							);
						}
					}
					NotificationsSinkMessage::ForceClose => {
						return Poll::Ready(
							ProtocolsHandlerEvent::Close(NotifsHandlerError::SyncNotificationsClogged)
						);
					}
				}
			}
		}

		// If `self.pending_handshake` is `Some`, we are in a state where the handshake-bearing
		// substream (either the legacy substream or the one special-cased as providing the
		// handshake) is open but the user isn't aware yet of the substreams being open.
		// When that is the case, neither the legacy substream nor the incoming notifications
		// substreams should be polled, otherwise there is a risk of receiving messages from them.
		if !matches!(self.state, State::Opening { pending_handshake: Some(_) }) {
			while let Poll::Ready(ev) = self.legacy.poll(cx) {
				match ev {
					ProtocolsHandlerEvent::OutboundSubstreamRequest { protocol, .. } =>
						match *protocol.info() {},
					ProtocolsHandlerEvent::Custom(LegacyProtoHandlerOut::CustomProtocolOpen {
						received_handshake,
						..
					}) => {
						match &mut self.state {
							State::Opening { pending_handshake } => {
								debug_assert!(pending_handshake.is_none());
								*pending_handshake = Some(received_handshake);
							}
							_ => debug_assert!(false),
						}

						cx.waker().wake_by_ref();
						return Poll::Pending;
					},
					ProtocolsHandlerEvent::Custom(LegacyProtoHandlerOut::CustomProtocolClosed { .. }) => {
						match &mut self.state {
							State::Open { want_closed, .. } if *want_closed == false => {
								*want_closed = true;
								return Poll::Ready(ProtocolsHandlerEvent::Custom(
									NotifsHandlerOut::CloseDesired
								));
							}
							State::Open { .. } => {}
							State::Opening { .. } => {}
							State::Closed { .. } => debug_assert!(false),
						}
					},
					ProtocolsHandlerEvent::Custom(LegacyProtoHandlerOut::CustomMessage { message }) => {
						debug_assert!(!matches!(self.state, State::Open { .. }));
						return Poll::Ready(ProtocolsHandlerEvent::Custom(
							NotifsHandlerOut::CustomMessage { message }
						))
					},
					ProtocolsHandlerEvent::Close(err) =>
						return Poll::Ready(ProtocolsHandlerEvent::Close(NotifsHandlerError::Legacy(err))),
				}
			}
		}

		for (handler_num, (handler, handshake_message)) in self.in_handlers.iter_mut().enumerate() {
			loop {
				let poll = if matches!(self.state, State::Open { .. }) {
					handler.poll(cx)
				} else {
					handler.poll_process(cx)
				};

				let ev = match poll {
					Poll::Ready(e) => e,
					Poll::Pending => break,
				};

				match ev {
					ProtocolsHandlerEvent::OutboundSubstreamRequest { .. } =>
						error!("Incoming substream handler tried to open a substream"),
					ProtocolsHandlerEvent::Close(err) => void::unreachable(err),
					ProtocolsHandlerEvent::Custom(NotifsInHandlerOut::OpenRequest(_)) =>
						match &mut self.state {
							State::Closed { pending_in } => {
								let was_empty = pending_in.is_empty();
								pending_in.push(handler_num);
								if was_empty {
									return Poll::Ready(ProtocolsHandlerEvent::Custom(
										NotifsHandlerOut::OpenDesired
									));
								}
							},
							State::Opening { .. } | State::Open { .. } => {
								// We create `handshake_message` on a separate line to be sure
								// that the lock is released as soon as possible.
								let handshake_message = handshake_message.read().clone();
								handler.inject_event(NotifsInHandlerIn::Accept(handshake_message))
							},
						},
					ProtocolsHandlerEvent::Custom(NotifsInHandlerOut::Closed) => {
						match &mut self.state {
							State::Open { want_closed, .. } if *want_closed == false => {
								*want_closed = true;
								return Poll::Ready(ProtocolsHandlerEvent::Custom(
									NotifsHandlerOut::CloseDesired
								));
							}
							State::Open { .. } => {}
							State::Opening { .. } => {}
							State::Closed { .. } => debug_assert!(false),
						}
					},
					ProtocolsHandlerEvent::Custom(NotifsInHandlerOut::Notif(message)) => {
						if matches!(self.state, State::Open { .. }) {
							let msg = NotifsHandlerOut::Notification {
								message,
								protocol_name: handler.protocol_name().clone(),
							};
							return Poll::Ready(ProtocolsHandlerEvent::Custom(msg));
						} else {
							debug_assert!(false);
						}
					},
				}
			}
		}

		for (handler_num, (handler, _)) in self.out_handlers.iter_mut().enumerate() {
			while let Poll::Ready(ev) = handler.poll(cx) {
				match (ev, &mut self.state) {
					(ProtocolsHandlerEvent::OutboundSubstreamRequest { protocol }, _) =>
						return Poll::Ready(ProtocolsHandlerEvent::OutboundSubstreamRequest {
							protocol: protocol
								.map_info(|()| handler_num),
						}),
					(ProtocolsHandlerEvent::Close(err), _) => void::unreachable(err),

					// Opened substream on the handshake-bearing notification protocol.
					(
						ProtocolsHandlerEvent::Custom(NotifsOutHandlerOut::Open { handshake }),
						State::Opening { pending_handshake }
					) if handler_num == 0 && pending_handshake.is_none() =>
					{
						*pending_handshake = Some(handshake);
					},

					(ProtocolsHandlerEvent::Custom(NotifsOutHandlerOut::Open { .. }), _)
						if handler_num == 0 => debug_assert!(false),
					(ProtocolsHandlerEvent::Custom(NotifsOutHandlerOut::Open { .. }), _) => {},

					(
						ProtocolsHandlerEvent::Custom(NotifsOutHandlerOut::Closed),
						State::Open { want_closed, .. }
					) => {
						if *want_closed == false {
							*want_closed = true;
							return Poll::Ready(ProtocolsHandlerEvent::Custom(
								NotifsHandlerOut::CloseDesired
							));
						}
					},

					// Remote has denied an opening attempt for this notifications protocol.
					// This fails the entire opening attempt.
					(ProtocolsHandlerEvent::Custom(NotifsOutHandlerOut::Refused), State::Opening { .. }) |
					(ProtocolsHandlerEvent::Custom(NotifsOutHandlerOut::Closed), State::Opening { .. }) => {
						self.legacy.inject_event(LegacyProtoHandlerIn::Close);
						for (handler, _) in &mut self.out_handlers {
							handler.inject_event(NotifsOutHandlerIn::Disable);
						}

						self.state = State::Closed {
							pending_in: Vec::new(),
						};

						return Poll::Ready(ProtocolsHandlerEvent::Custom(
							NotifsHandlerOut::OpenResultErr
						));
					},


					(ProtocolsHandlerEvent::Custom(NotifsOutHandlerOut::Refused), _) |
					(ProtocolsHandlerEvent::Custom(NotifsOutHandlerOut::Closed), _) =>
						debug_assert!(false),
				}
			}
		}

		if let State::Opening { pending_handshake: Some(pending_handshake), .. } = &mut self.state {
			if self.out_handlers.iter().all(|(h, _)| h.is_open() || h.is_refused()) {
				let (async_tx, async_rx) = mpsc::channel(ASYNC_NOTIFICATIONS_BUFFER_SIZE);
				let (sync_tx, sync_rx) = mpsc::channel(SYNC_NOTIFICATIONS_BUFFER_SIZE);
				let notifications_sink = NotificationsSink {
					inner: Arc::new(NotificationsSinkInner {
						async_channel: FuturesMutex::new(async_tx),
						sync_channel: Mutex::new(sync_tx),
					}),
				};

				let pending_handshake = mem::replace(pending_handshake, Vec::new());
				self.state = State::Open {
					notifications_sink_rx: stream::select(async_rx.fuse(), sync_rx.fuse()),
					want_closed: false,
				};

				return Poll::Ready(ProtocolsHandlerEvent::Custom(
					NotifsHandlerOut::OpenResultOk {
						endpoint: self.endpoint.clone(),
						received_handshake: pending_handshake,
						notifications_sink
					}
				))
			}
		}

		Poll::Pending
	}
}
