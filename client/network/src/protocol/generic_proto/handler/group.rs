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
//! The handler can be in one of the following states: `Initial`, `Enabled`, `Disabled`.
//!
//! The `Initial` state is the state that the handler initially is in. It is a temporary state
//! during which the user must either enable or disable the handler. After that, the handler stays
//! either enabled or disabled.
//!
//! On the wire, we try to open the following substreams:
//!
//! - One substream for each notification protocol passed as parameter to the
//!   `NotifsHandlerProto::new` function.
//! - One "legacy" substream used for anything non-related to gossiping, and used as a fallback
//!   in case the notification protocol can't be opened.
//!
//! When the handler is in the `Enabled` state, we immediately open and try to maintain all the
//! aforementioned substreams. When the handler is in the `Disabled` state, we immediately close
//! (or abort opening) all these substreams. It is intended that in the future we allow states in
//! which some protocols are open and not others. Symmetrically, we allow incoming
//! Substrate-related substreams if and only if we are in the `Enabled` state.
//!
//! The user has the choice between sending a message with `SendNotification`, to send a
//! notification, and `SendLegacy`, to send any other kind of message.
//!

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
use log::{debug, error};
use parking_lot::{Mutex, RwLock};
use std::{borrow::Cow, str, sync::Arc, task::{Context, Poll}};

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

	/// In the situation where either the legacy substream has been opened or the handshake-bearing
	/// notifications protocol is open, but we haven't sent out any [`NotifsHandlerOut::Open`]
	/// event yet, this contains the received handshake waiting to be reported through the
	/// external API.
	pending_handshake: Option<Vec<u8>>,

	/// State of this handler.
	enabled: EnabledState,

	/// If we receive inbound substream requests while in initialization mode,
	/// we push the corresponding index here and process them when the handler
	/// gets enabled/disabled.
	pending_in: Vec<usize>,

	/// If `Some`, contains the two `Receiver`s connected to the [`NotificationsSink`] that has
	/// been sent out. The notifications to send out can be pulled from this receivers.
	/// We use two different channels in order to have two different channel sizes, but from the
	/// receiving point of view, the two channels are the same.
	/// The receivers are fused in case the user drops the [`NotificationsSink`] entirely.
	///
	/// Contains `Some` if and only if it has been reported to the user that the substreams are
	/// open.
	notifications_sink_rx: Option<
		stream::Select<
			stream::Fuse<mpsc::Receiver<NotificationsSinkMessage>>,
			stream::Fuse<mpsc::Receiver<NotificationsSinkMessage>>
		>
	>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum EnabledState {
	Initial,
	Enabled,
	Disabled,
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
			pending_handshake: None,
			enabled: EnabledState::Initial,
			pending_in: Vec::new(),
			notifications_sink_rx: None,
		}
	}
}

/// Event that can be received by a `NotifsHandler`.
#[derive(Debug, Clone)]
pub enum NotifsHandlerIn {
	/// The node should start using custom protocols.
	Enable,

	/// The node should stop using custom protocols.
	Disable,
}

/// Event that can be emitted by a `NotifsHandler`.
#[derive(Debug)]
pub enum NotifsHandlerOut {
	/// The connection is open for custom protocols.
	Open {
		/// The endpoint of the connection that is open for custom protocols.
		endpoint: ConnectedPoint,
		/// Handshake that was sent to us.
		/// This is normally a "Status" message, but this out of the concern of this code.
		received_handshake: Vec<u8>,
		/// How notifications can be sent to this node.
		notifications_sink: NotificationsSink,
	},

	/// The connection is closed for custom protocols.
	Closed {
		/// The reason for closing, for diagnostic purposes.
		reason: Cow<'static, str>,
		/// The endpoint of the connection that closed for custom protocols.
		endpoint: ConnectedPoint,
	},

	/// Received a non-gossiping message on the legacy substream.
	CustomMessage {
		/// Message that has been received.
		///
		/// Keep in mind that this can be a `ConsensusMessage` message, which then contains a
		/// notification.
		message: BytesMut,
	},

	/// Received a message on a custom protocol substream.
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
			NotifsHandlerIn::Enable => {
				if let EnabledState::Enabled = self.enabled {
					debug!("enabling already-enabled handler");
				}
				self.enabled = EnabledState::Enabled;
				self.legacy.inject_event(LegacyProtoHandlerIn::Enable);
				for (handler, initial_message) in &mut self.out_handlers {
					// We create `initial_message` on a separate line to be sure that the lock
					// is released as soon as possible.
					let initial_message = initial_message.read().clone();
					handler.inject_event(NotifsOutHandlerIn::Enable {
						initial_message,
					});
				}
				for num in self.pending_in.drain(..) {
					// We create `handshake_message` on a separate line to be sure
					// that the lock is released as soon as possible.
					let handshake_message = self.in_handlers[num].1.read().clone();
					self.in_handlers[num].0
						.inject_event(NotifsInHandlerIn::Accept(handshake_message));
				}
			},
			NotifsHandlerIn::Disable => {
				if let EnabledState::Disabled = self.enabled {
					debug!("disabling already-disabled handler");
				}
				self.legacy.inject_event(LegacyProtoHandlerIn::Disable);
				// The notifications protocols start in the disabled state. If we were in the
				// "Initial" state, then we shouldn't disable the notifications protocols again.
				if self.enabled != EnabledState::Initial {
					for (handler, _) in &mut self.out_handlers {
						handler.inject_event(NotifsOutHandlerIn::Disable);
					}
				}
				self.enabled = EnabledState::Disabled;
				for num in self.pending_in.drain(..) {
					self.in_handlers[num].0.inject_event(NotifsInHandlerIn::Refuse);
				}
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
		if let Some(notifications_sink_rx) = &mut self.notifications_sink_rx {
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
						return Poll::Ready(ProtocolsHandlerEvent::Close(NotifsHandlerError::SyncNotificationsClogged));
					}
				}
			}
		}

		// If `self.pending_handshake` is `Some`, we are in a state where the handshake-bearing
		// substream (either the legacy substream or the one special-cased as providing the
		// handshake) is open but the user isn't aware yet of the substreams being open.
		// When that is the case, neither the legacy substream nor the incoming notifications
		// substreams should be polled, otherwise there is a risk of receiving messages from them.
		if self.pending_handshake.is_none() {
			while let Poll::Ready(ev) = self.legacy.poll(cx) {
				match ev {
					ProtocolsHandlerEvent::OutboundSubstreamRequest { protocol, .. } =>
						match *protocol.info() {},
					ProtocolsHandlerEvent::Custom(LegacyProtoHandlerOut::CustomProtocolOpen {
						received_handshake,
						..
					}) => {
						if self.notifications_sink_rx.is_none() {
							debug_assert!(self.pending_handshake.is_none());
							self.pending_handshake = Some(received_handshake);
						}
						cx.waker().wake_by_ref();
						return Poll::Pending;
					},
					ProtocolsHandlerEvent::Custom(LegacyProtoHandlerOut::CustomProtocolClosed { reason, .. }) => {
						// We consciously drop the receivers despite notifications being potentially
						// still buffered up.
						self.notifications_sink_rx = None;

						return Poll::Ready(ProtocolsHandlerEvent::Custom(
							NotifsHandlerOut::Closed { endpoint: self.endpoint.clone(), reason }
						))
					},
					ProtocolsHandlerEvent::Custom(LegacyProtoHandlerOut::CustomMessage { message }) => {
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
				let poll = if self.notifications_sink_rx.is_some() {
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
						match self.enabled {
							EnabledState::Initial => self.pending_in.push(handler_num),
							EnabledState::Enabled => {
								// We create `handshake_message` on a separate line to be sure
								// that the lock is released as soon as possible.
								let handshake_message = handshake_message.read().clone();
								handler.inject_event(NotifsInHandlerIn::Accept(handshake_message))
							},
							EnabledState::Disabled =>
								handler.inject_event(NotifsInHandlerIn::Refuse),
						},
					ProtocolsHandlerEvent::Custom(NotifsInHandlerOut::Closed) => {},
					ProtocolsHandlerEvent::Custom(NotifsInHandlerOut::Notif(message)) => {
						debug_assert!(self.pending_handshake.is_none());
						if self.notifications_sink_rx.is_some() {
							let msg = NotifsHandlerOut::Notification {
								message,
								protocol_name: handler.protocol_name().clone(),
							};
							return Poll::Ready(ProtocolsHandlerEvent::Custom(msg));
						}
					},
				}
			}
		}

		for (handler_num, (handler, _)) in self.out_handlers.iter_mut().enumerate() {
			while let Poll::Ready(ev) = handler.poll(cx) {
				match ev {
					ProtocolsHandlerEvent::OutboundSubstreamRequest { protocol } =>
						return Poll::Ready(ProtocolsHandlerEvent::OutboundSubstreamRequest {
							protocol: protocol
								.map_info(|()| handler_num),
						}),
					ProtocolsHandlerEvent::Close(err) => void::unreachable(err),

					// Opened substream on the handshake-bearing notification protocol.
					ProtocolsHandlerEvent::Custom(NotifsOutHandlerOut::Open { handshake })
						if handler_num == 0 =>
					{
						if self.notifications_sink_rx.is_none() && self.pending_handshake.is_none() {
							self.pending_handshake = Some(handshake);
						}
					},

					// Nothing to do in response to other notification substreams being opened
					// or closed.
					ProtocolsHandlerEvent::Custom(NotifsOutHandlerOut::Open { .. }) => {},
					ProtocolsHandlerEvent::Custom(NotifsOutHandlerOut::Closed) => {},
					ProtocolsHandlerEvent::Custom(NotifsOutHandlerOut::Refused) => {},
				}
			}
		}

		if self.out_handlers.iter().all(|(h, _)| h.is_open() || h.is_refused()) {
			if let Some(handshake) = self.pending_handshake.take() {
				let (async_tx, async_rx) = mpsc::channel(ASYNC_NOTIFICATIONS_BUFFER_SIZE);
				let (sync_tx, sync_rx) = mpsc::channel(SYNC_NOTIFICATIONS_BUFFER_SIZE);
				let notifications_sink = NotificationsSink {
					inner: Arc::new(NotificationsSinkInner {
						async_channel: FuturesMutex::new(async_tx),
						sync_channel: Mutex::new(sync_tx),
					}),
				};

				debug_assert!(self.notifications_sink_rx.is_none());
				self.notifications_sink_rx = Some(stream::select(async_rx.fuse(), sync_rx.fuse()));

				return Poll::Ready(ProtocolsHandlerEvent::Custom(
					NotifsHandlerOut::Open {
						endpoint: self.endpoint.clone(),
						received_handshake: handshake,
						notifications_sink
					}
				))
			}
		}

		Poll::Pending
	}
}
