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
//! From an API perspective, the [`NotifsHandler`] is always in one of the following state (see [`State`]):
//!
//! - Closed substreams. This is the initial state.
//! - Closed substreams, but remote desires them to be open.
//! - Open substreams.
//! - Open substreams, but remote desires them to be closed.
//!
//! The [`NotifsHandler`] can spontaneously switch between these states:
//!
//! - "Closed substreams" to "Closed substreams but open desired". When that happens, a
//! [`NotifsHandlerOut::OpenDesiredByRemote`] is emitted.
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
//! When a [`NotifsHandlerOut::OpenDesiredByRemote`] is emitted, the user should always send back either a
//! [`NotifsHandlerIn::Open`] or a [`NotifsHandlerIn::Close`].If this isn't done, the remote will
//! be left in a pending state.
//!
//! It is illegal to send a [`NotifsHandlerIn::Open`] before a previously-emitted
//! [`NotifsHandlerIn::Open`] has gotten an answer.

use crate::protocol::generic_proto::{
	upgrade::{
		NotificationsIn, NotificationsOut, NotificationsInSubstream, NotificationsOutSubstream,
		NotificationsHandshakeError, RegisteredProtocol, RegisteredProtocolSubstream,
		RegisteredProtocolEvent, UpgradeCollec
	},
};

use bytes::BytesMut;
use libp2p::core::{either::EitherOutput, ConnectedPoint, PeerId};
use libp2p::core::upgrade::{SelectUpgrade, InboundUpgrade, OutboundUpgrade};
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
use smallvec::SmallVec;
use std::{borrow::Cow, collections::VecDeque, mem, pin::Pin, str, sync::Arc, task::{Context, Poll}, time::Duration};
use wasm_timer::Instant;

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
	/// Prototypes for upgrades for inbound substreams, and the message we respond with in the
	/// handshake.
	in_protocols: Vec<(NotificationsIn, Arc<RwLock<Vec<u8>>>)>,

	/// Name of protocols available for outbound substreams, and the initial handshake message we
	/// send.
	out_protocols: Vec<(Cow<'static, str>, Arc<RwLock<Vec<u8>>>)>,

	/// Configuration for the legacy protocol upgrade.
	legacy_protocol: RegisteredProtocol,
}

/// The actual handler once the connection has been established.
///
/// See the documentation at the module level for more information.
pub struct NotifsHandler {
	/// Prototypes for upgrades for inbound substreams, and the message we respond with in the
	/// handshake.
	in_protocols: Vec<(NotificationsIn, Arc<RwLock<Vec<u8>>>)>,

	/// Name of protocols available for outbound substreams, and the initial handshake message we
	/// send.
	out_protocols: Vec<(Cow<'static, str>, Arc<RwLock<Vec<u8>>>)>,

	/// When the connection with the remote has been successfully established.
	when_connection_open: Instant,

	/// Whether we are the connection dialer or listener.
	endpoint: ConnectedPoint,

	/// Remote we are connected to.
	peer_id: PeerId,

	/// State of this handler.
	state: State,

	/// Configuration for the legacy protocol upgrade.
	legacy_protocol: RegisteredProtocol,

	/// The substreams where bidirectional communications happen.
	legacy_substreams: SmallVec<[RegisteredProtocolSubstream<NegotiatedSubstream>; 4]>,

	/// Contains substreams which are being shut down.
	legacy_shutdown: SmallVec<[RegisteredProtocolSubstream<NegotiatedSubstream>; 4]>,

	/// Events to return in priority from `poll`.
	events_queue: VecDeque<
		ProtocolsHandlerEvent<NotificationsOut, usize, NotifsHandlerOut, NotifsHandlerError>
	>,
}

/// See the module-level documentation to learn about the meaning of these variants.
enum State {
	/// Handler is in the "Closed" state.
	Closed {
		/// Vec of the same length as [`NotifsHandler::out_protocols`]. For each protocol, contains
		/// a boolean indicating whether an outgoing substream is still in the process of being
		/// opened.
		pending_opening: Vec<bool>,
	},

	/// Handler is in the "Closed" state. A [`NotifsHandlerOut::OpenDesiredByRemote`] has been emitted.
	OpenDesiredByRemote {
		/// Vec of the same length as [`NotifsHandler::in_protocols`]. For each protocol, contains
		/// a substream opened by the remote and that hasn't been accepted/rejected yet.
		///
		/// Must always contain at least one `Some`.
		in_substreams: Vec<Option<NotificationsInSubstream<NegotiatedSubstream>>>,

		/// See [`State::Closed::pending_opening`].
		pending_opening: Vec<bool>,
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

		/// Vec of the same length as [`NotifsHandler::in_protocols`]. For each protocol, contains
		/// a substream opened by the remote and that has been accepted.
		///
		/// Contrary to [`State::OpenDesiredByRemote::in_substreams`], it is possible for this to
		/// contain only `None`s.
		in_substreams: Vec<Option<NotificationsInSubstream<NegotiatedSubstream>>>,

		/// Vec of the same length as [`NotifsHandler::out_protocols`]. For each protocol, contains
		/// an outbound substream that has been accepted by the remote.
		///
		/// Items that contain `None` mean that a substream is still being opened or has been
		/// rejected by the remote. In other words, this `Vec` is kind of a mirror version of
		/// [`State::Closed::pending_opening`].
		///
		/// Items that contain `Some(None)` have been rejected by the remote, most likely because
		/// they don't support this protocol. At the time of writing, the external API doesn't
		/// distinguish between the different protocols. From the external API's point of view,
		/// either all protocols are open or none are open. In reality, light clients in particular
		/// don't support for example the GrandPa protocol, and as such will refuse our outgoing
		/// attempts. This is problematic in theory, but in practice this is handled properly at a
		/// higher level. This flaw will fixed once the outer layers know to differentiate the
		/// multiple protocols.
		out_substreams: Vec<Option<Option<NotificationsOutSubstream<NegotiatedSubstream>>>>,
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

		/// Vec of the same length as [`NotifsHandler::out_protocols`]. For each protocol, contains
		/// an outbound substream that has been accepted by the remote.
		///
		/// On transition to [`State::Open`], all the elements must be `Some`. Elements are
		/// switched to `None` only if the remote closes substreams, in which case `want_closed`
		/// must be true.
		out_substreams: Vec<Option<NotificationsOutSubstream<NegotiatedSubstream>>>,

		/// Vec of the same length as [`NotifsHandler::in_protocols`]. For each protocol, contains
		/// a substream opened by the remote and that has been accepted.
		///
		/// Contrary to [`State::OpenDesiredByRemote::in_substreams`], it is possible for this to
		/// contain only `None`s.
		in_substreams: Vec<Option<NotificationsInSubstream<NegotiatedSubstream>>>,

		/// If true, at least one substream in [`State::Open::out_substreams`] has been closed or
		/// reset by the remote and a [`NotifsHandlerOut::CloseDesired`] message has been sent
		/// out.
		want_closed: bool,
	},
}

impl IntoProtocolsHandler for NotifsHandlerProto {
	type Handler = NotifsHandler;

	fn inbound_protocol(&self) -> SelectUpgrade<UpgradeCollec<NotificationsIn>, RegisteredProtocol> {
		let in_protocols = self.in_protocols.iter()
			.map(|(h, _)| h.clone())
			.collect::<UpgradeCollec<_>>();

		SelectUpgrade::new(in_protocols, self.legacy_protocol.clone())
	}

	fn into_handler(self, peer_id: &PeerId, connected_point: &ConnectedPoint) -> Self::Handler {
		let num_out_proto = self.out_protocols.len();

		NotifsHandler {
			in_protocols: self.in_protocols,
			out_protocols: self.out_protocols,
			peer_id: peer_id.clone(),
			endpoint: connected_point.clone(),
			when_connection_open: Instant::now(),
			state: State::Closed {
				pending_opening: (0..num_out_proto).map(|_| false).collect(),
			},
			legacy_protocol: self.legacy_protocol,
			legacy_substreams: SmallVec::new(),
			legacy_shutdown: SmallVec::new(),
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
	OpenDesiredByRemote,

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
	/// Target of the sink.
	peer_id: PeerId,
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
			// buffer, and therefore `try_send` will succeed.
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
	/// Returns the name of the protocol. Matches the one passed to
	/// [`NotificationsSink::reserve_notification`].
	pub fn protocol_name(&self) -> &Cow<'static, str> {
		&self.protocol_name
	}

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
		legacy_protocol: RegisteredProtocol,
		list: impl Into<Vec<(Cow<'static, str>, Arc<RwLock<Vec<u8>>>)>>,
	) -> Self {
		let list = list.into();
		assert!(!list.is_empty());

		let out_protocols = list
			.clone()
			.into_iter()
			.collect();

		let in_protocols = list.clone()
			.into_iter()
			.map(|(proto_name, msg)| (NotificationsIn::new(proto_name), msg))
			.collect();

		NotifsHandlerProto {
			in_protocols,
			out_protocols,
			legacy_protocol,
		}
	}
}

impl ProtocolsHandler for NotifsHandler {
	type InEvent = NotifsHandlerIn;
	type OutEvent = NotifsHandlerOut;
	type Error = NotifsHandlerError;
	type InboundProtocol = SelectUpgrade<UpgradeCollec<NotificationsIn>, RegisteredProtocol>;
	type OutboundProtocol = NotificationsOut;
	// Index within the `out_protocols`.
	type OutboundOpenInfo = usize;
	type InboundOpenInfo = ();

	fn listen_protocol(&self) -> SubstreamProtocol<Self::InboundProtocol, ()> {
		let in_protocols = self.in_protocols.iter()
			.map(|(h, _)| h.clone())
			.collect::<UpgradeCollec<_>>();

		let proto = SelectUpgrade::new(in_protocols, self.legacy_protocol.clone());
		SubstreamProtocol::new(proto, ())
	}

	fn inject_fully_negotiated_inbound(
		&mut self,
		out: <Self::InboundProtocol as InboundUpgrade<NegotiatedSubstream>>::Output,
		(): ()
	) {
		match out {
			// Received notifications substream.
			EitherOutput::First(((_remote_handshake, mut proto), num)) => {
				match &mut self.state {
					State::Closed { pending_opening } => {
						self.events_queue.push_back(ProtocolsHandlerEvent::Custom(
							NotifsHandlerOut::OpenDesiredByRemote
						));

						let mut in_substreams = (0..self.in_protocols.len())
							.map(|_| None)
							.collect::<Vec<_>>();
						in_substreams[num] = Some(proto);
						self.state = State::OpenDesiredByRemote {
							in_substreams,
							pending_opening: mem::replace(pending_opening, Vec::new()),
						};
					},
					State::OpenDesiredByRemote { in_substreams, .. } => {
						if in_substreams[num].is_some() {
							// If a substream already exists, silently drop the new one.
							// Note that we drop the substream, which will send an equivalent to a
							// TCP "RST" to the remote and force-close the substream. It might
							// seem like an unclean way to get rid of a substream. However, keep
							// in mind that it is invalid for the remote to open multiple such
							// substreams, and therefore sending a "RST" is the most correct thing
							// to do.
							return;
						}
						in_substreams[num] = Some(proto);
					},
					State::Opening { in_substreams, .. } |
					State::Open { in_substreams, .. } => {
						if in_substreams[num].is_some() {
							// Same remark as above.
							return;
						}

						// We create `handshake_message` on a separate line to be sure
						// that the lock is released as soon as possible.
						let handshake_message = self.in_protocols[num].1.read().clone();
						proto.send_handshake(handshake_message);
						in_substreams[num] = Some(proto);
					},
				};
			}

			// Received legacy substream.
			EitherOutput::Second((substream, _handshake)) => {
				// Note: while we awknowledge legacy substreams and handle incoming messages,
				// it doesn't trigger any `OpenDesiredByRemote` event as a way to simplify the
				// logic of this code.
				// Since mid-2019, legacy substreams are supposed to be used at the same time as
				// notifications substreams, and not in isolation. Nodes that open legacy
				// substreams in isolation are considered deprecated.
				if self.legacy_substreams.len() <= 4 {
					self.legacy_substreams.push(substream);
				}
			},
		}
	}

	fn inject_fully_negotiated_outbound(
		&mut self,
		(handshake, substream): <Self::OutboundProtocol as OutboundUpgrade<NegotiatedSubstream>>::Output,
		num: Self::OutboundOpenInfo
	) {
		match &mut self.state {
			State::Closed { pending_opening } |
			State::OpenDesiredByRemote { pending_opening, .. } => {
				debug_assert!(pending_opening[num]);
				pending_opening[num] = false;
			}
			State::Open { .. } => {
				error!(target: "sub-libp2p", "☎️ State mismatch in notifications handler");
				debug_assert!(false);
			}
			State::Opening { pending_handshake, in_substreams, out_substreams } => {
				debug_assert!(out_substreams[num].is_none());
				out_substreams[num] = Some(Some(substream));

				if num == 0 {
					debug_assert!(pending_handshake.is_none());
					*pending_handshake = Some(handshake);
				}

				if !out_substreams.iter().any(|s| s.is_none()) {
					let (async_tx, async_rx) = mpsc::channel(ASYNC_NOTIFICATIONS_BUFFER_SIZE);
					let (sync_tx, sync_rx) = mpsc::channel(SYNC_NOTIFICATIONS_BUFFER_SIZE);
					let notifications_sink = NotificationsSink {
						inner: Arc::new(NotificationsSinkInner {
							peer_id: self.peer_id.clone(),
							async_channel: FuturesMutex::new(async_tx),
							sync_channel: Mutex::new(sync_tx),
						}),
					};

					debug_assert!(pending_handshake.is_some());
					let pending_handshake = pending_handshake.take().unwrap_or_default();

					let out_substreams = out_substreams
						.drain(..)
						.map(|s| s.expect("checked by the if above; qed"))
						.collect();

					self.state = State::Open {
						notifications_sink_rx: stream::select(async_rx.fuse(), sync_rx.fuse()),
						out_substreams,
						in_substreams: mem::replace(in_substreams, Vec::new()),
						want_closed: false,
					};

					self.events_queue.push_back(ProtocolsHandlerEvent::Custom(
						NotifsHandlerOut::OpenResultOk {
							endpoint: self.endpoint.clone(),
							received_handshake: pending_handshake,
							notifications_sink
						}
					));
				}
			}
		}
	}

	fn inject_event(&mut self, message: NotifsHandlerIn) {
		match message {
			NotifsHandlerIn::Open => {
				match &mut self.state {
					State::Closed { .. } | State::OpenDesiredByRemote { .. } => {
						let (pending_opening, mut in_substreams) = match &mut self.state {
							State::Closed { pending_opening } => (pending_opening, None),
							State::OpenDesiredByRemote { pending_opening, in_substreams } =>
								(pending_opening, Some(mem::replace(in_substreams, Vec::new()))),
							_ => unreachable!()
						};

						debug_assert_eq!(pending_opening.len(), self.out_protocols.len());
						for (n, is_pending) in pending_opening.iter().enumerate() {
							if *is_pending {
								continue;
							}

							let proto = NotificationsOut::new(
								self.out_protocols[n].0.clone(),
								self.out_protocols[n].1.read().clone()
							);

							self.events_queue.push_back(ProtocolsHandlerEvent::OutboundSubstreamRequest {
								protocol: SubstreamProtocol::new(proto, n)
									.with_timeout(OPEN_TIMEOUT),
							});
						}

						if let Some(in_substreams) = in_substreams.as_mut() {
							for (num, substream) in in_substreams.iter_mut().enumerate() {
								let substream = match substream.as_mut() {
									Some(s) => s,
									None => continue,
								};

								let handshake_message = self.in_protocols[num].1.read().clone();
								substream.send_handshake(handshake_message);
							}
						}

						self.state = State::Opening {
							pending_handshake: None,
							in_substreams: if let Some(in_substreams) = in_substreams {
								in_substreams
							} else {
								(0..self.in_protocols.len()).map(|_| None).collect()
							},
							out_substreams: (0..self.out_protocols.len()).map(|_| None).collect(),
						};
					},
					State::Opening { .. } |
					State::Open { .. } => {
						// As documented, it is forbidden to send an `Open` while there is already
						// one in the fly.
						error!(target: "sub-libp2p", "opening already-opened handler");
						debug_assert!(false);
					},
				}
			},

			NotifsHandlerIn::Close => {
				for mut substream in self.legacy_substreams.drain(..) {
					substream.shutdown();
					self.legacy_shutdown.push(substream);
				}

				match &mut self.state {
					State::Open { .. } => {
						let pending_opening = self.out_protocols.iter().map(|_| false).collect();
						self.state = State::Closed {
							pending_opening,
						};
					},
					State::Opening { out_substreams, .. } => {
						let pending_opening = out_substreams.iter().map(|s| s.is_none()).collect();
						self.state = State::Closed {
							pending_opening,
						};

						self.events_queue.push_back(ProtocolsHandlerEvent::Custom(
							NotifsHandlerOut::OpenResultErr
						));
					},
					State::OpenDesiredByRemote { pending_opening, .. } => {
						self.state = State::Closed {
							pending_opening: mem::replace(pending_opening, Vec::new()),
						};
					}
					State::Closed { .. } => {},
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
		_: ProtocolsHandlerUpgrErr<NotificationsHandshakeError>
	) {
		match &mut self.state {
			State::Closed { pending_opening } | State::OpenDesiredByRemote { pending_opening, .. } => {
				debug_assert!(pending_opening[num]);
				pending_opening[num] = false;
			}

			State::Opening { in_substreams, pending_handshake, out_substreams } => {
				// Failing to open a substream isn't considered a failure. Instead, it is marked
				// as `Some(None)` and the opening continues.

				out_substreams[num] = Some(None);

				// Some substreams are still being opened. Nothing more to do.
				if out_substreams.iter().any(|s| s.is_none()) {
					return;
				}

				// All substreams have finished being open.
				// If the handshake has been received, proceed and report the opening.

				if let Some(pending_handshake) = pending_handshake.take() {
					// Open!
					let (async_tx, async_rx) = mpsc::channel(ASYNC_NOTIFICATIONS_BUFFER_SIZE);
					let (sync_tx, sync_rx) = mpsc::channel(SYNC_NOTIFICATIONS_BUFFER_SIZE);
					let notifications_sink = NotificationsSink {
						inner: Arc::new(NotificationsSinkInner {
							peer_id: self.peer_id.clone(),
							async_channel: FuturesMutex::new(async_tx),
							sync_channel: Mutex::new(sync_tx),
						}),
					};

					let out_substreams = out_substreams
						.drain(..)
						.map(|s| s.expect("checked by the if above; qed"))
						.collect();

					self.state = State::Open {
						notifications_sink_rx: stream::select(async_rx.fuse(), sync_rx.fuse()),
						out_substreams,
						in_substreams: mem::replace(in_substreams, Vec::new()),
						want_closed: false,
					};

					self.events_queue.push_back(ProtocolsHandlerEvent::Custom(
						NotifsHandlerOut::OpenResultOk {
							endpoint: self.endpoint.clone(),
							received_handshake: pending_handshake,
							notifications_sink
						}
					));

				} else {
					// Open failure!
					self.state = State::Closed {
						pending_opening: (0..self.out_protocols.len()).map(|_| false).collect(),
					};

					self.events_queue.push_back(ProtocolsHandlerEvent::Custom(
						NotifsHandlerOut::OpenResultErr
					));
				}
			}

			// No substream is being open when already `Open`.
			State::Open { .. } => debug_assert!(false),
		}
	}

	fn connection_keep_alive(&self) -> KeepAlive {
		if !self.legacy_substreams.is_empty() {
			return KeepAlive::Yes;
		}

		match self.state {
			State::Closed { .. } => KeepAlive::Until(self.when_connection_open + INITIAL_KEEPALIVE_TIME),
			State::OpenDesiredByRemote { .. } | State::Opening { .. } | State::Open { .. } =>
				KeepAlive::Yes,
		}
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

		// Poll inbound substreams.
		// Inbound substreams being closed is always tolerated, except for the
		// `OpenDesiredByRemote` state which might need to be switched back to `Closed`.
		match &mut self.state {
			State::Closed { .. } => {}
			State::Open { in_substreams, .. } => {
				for (num, substream) in in_substreams.iter_mut().enumerate() {
					match substream.as_mut().map(|s| Stream::poll_next(Pin::new(s), cx)) {
						None | Some(Poll::Pending) => continue,
						Some(Poll::Ready(Some(Ok(message)))) => {
							let event = NotifsHandlerOut::Notification {
								message,
								protocol_name: self.in_protocols[num].0.protocol_name().clone(),
							};
							return Poll::Ready(ProtocolsHandlerEvent::Custom(event))
						},
						Some(Poll::Ready(None)) | Some(Poll::Ready(Some(Err(_)))) =>
							*substream = None,
					}
				}
			}

			State::OpenDesiredByRemote { in_substreams, .. } |
			State::Opening { in_substreams, .. } => {
				for substream in in_substreams {
					match substream.as_mut().map(|s| NotificationsInSubstream::poll_process(Pin::new(s), cx)) {
						None | Some(Poll::Pending) => continue,
						Some(Poll::Ready(Ok(void))) => match void {},
						Some(Poll::Ready(Err(_))) => *substream = None,
					}
				}
			}
		}

		// Since the previous block might have closed inbound substreams, make sure that we can
		// stay in `OpenDesiredByRemote` state.
		if let State::OpenDesiredByRemote { in_substreams, pending_opening } = &mut self.state {
			if !in_substreams.iter().any(|s| s.is_some()) {
				self.state = State::Closed {
					pending_opening: mem::replace(pending_opening, Vec::new()),
				};
				return Poll::Ready(ProtocolsHandlerEvent::Custom(
					NotifsHandlerOut::CloseDesired
				))
			}
		}

		// Poll outbound substreams.
		match &mut self.state {
			State::Open { out_substreams, want_closed, .. } => {
				let mut any_closed = false;

				for substream in out_substreams.iter_mut() {
					match substream.as_mut().map(|s| Sink::poll_flush(Pin::new(s), cx)) {
						None | Some(Poll::Pending) | Some(Poll::Ready(Ok(()))) => continue,
						Some(Poll::Ready(Err(_))) => {}
					};

					// Reached if the substream has been closed.
					*substream = None;
					any_closed = true;
				}

				if any_closed {
					if !*want_closed {
						*want_closed = true;
						return Poll::Ready(ProtocolsHandlerEvent::Custom(NotifsHandlerOut::CloseDesired));
					}
				}
			}

			State::Opening { out_substreams, pending_handshake, .. } => {
				debug_assert!(out_substreams.iter().any(|s| s.is_none()));

				for (num, substream) in out_substreams.iter_mut().enumerate() {
					match substream {
						None | Some(None) => continue,
						Some(Some(substream)) => match Sink::poll_flush(Pin::new(substream), cx) {
							Poll::Pending | Poll::Ready(Ok(())) => continue,
							Poll::Ready(Err(_)) => {}
						}
					}

					// Reached if the substream has been closed.
					*substream = Some(None);
					if num == 0 {
						// Cancel the handshake.
						*pending_handshake = None;
					}
				}
			}

			State::Closed { .. } |
			State::OpenDesiredByRemote { .. } => {}
		}

		if let State::Open { notifications_sink_rx, out_substreams, .. } = &mut self.state {
			'poll_notifs_sink: loop {
				// Before we poll the notifications sink receiver, check that all the notification
				// channels are ready to send a message.
				// TODO: it is planned that in the future we switch to one `NotificationsSink` per
				// protocol, in which case each sink should wait only for its corresponding handler
				// to be ready, and not all handlers
				// see https://github.com/paritytech/substrate/issues/5670
				for substream in out_substreams.iter_mut() {
					match substream.as_mut().map(|s| s.poll_ready_unpin(cx)) {
						None | Some(Poll::Ready(_)) => {},
						Some(Poll::Pending) => break 'poll_notifs_sink
					}
				}

				// Now that all substreams are ready for a message, grab what to send.
				let message = match notifications_sink_rx.poll_next_unpin(cx) {
					Poll::Ready(Some(msg)) => msg,
					Poll::Ready(None) | Poll::Pending => break,
				};

				match message {
					NotificationsSinkMessage::Notification {
						protocol_name,
						message
					} => {
						if let Some(pos) = self.out_protocols.iter().position(|(n, _)| *n == protocol_name) {
							if let Some(substream) = out_substreams[pos].as_mut() {
								let _ = substream.start_send_unpin(message);
								// Calling `start_send_unpin` only queues the message. Actually
								// emitting the message is done with `poll_flush`. In order to
								// not introduce too much complexity, this flushing is done earlier
								// in the body of this `poll()` method. As such, we schedule a task
								// wake-up now in order to guarantee that `poll()` will be called
								// again and the flush happening.
								// At the time of the writing of this comment, a rewrite of this
								// code is being planned. If you find this comment in the wild and
								// the rewrite didn't happen, please consider a refactor.
								cx.waker().wake_by_ref();
								continue 'poll_notifs_sink;
							}

						} else {
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

		// The legacy substreams are polled only if the state is `Open`. Otherwise, it would be
		// possible to receive notifications that would need to get silently discarded.
		if matches!(self.state, State::Open { .. }) {
			for n in (0..self.legacy_substreams.len()).rev() {
				let mut substream = self.legacy_substreams.swap_remove(n);
				let poll_outcome = Pin::new(&mut substream).poll_next(cx);
				match poll_outcome {
					Poll::Pending => self.legacy_substreams.push(substream),
					Poll::Ready(Some(Ok(RegisteredProtocolEvent::Message(message)))) => {
						self.legacy_substreams.push(substream);
						return Poll::Ready(ProtocolsHandlerEvent::Custom(
							NotifsHandlerOut::CustomMessage { message }
						))
					},
					Poll::Ready(Some(Ok(RegisteredProtocolEvent::Clogged))) => {
						return Poll::Ready(ProtocolsHandlerEvent::Close(
							NotifsHandlerError::SyncNotificationsClogged
						))
					}
					Poll::Ready(None) | Poll::Ready(Some(Err(_))) => {
						if matches!(poll_outcome, Poll::Ready(None)) {
							self.legacy_shutdown.push(substream);
						}

						if let State::Open { want_closed, .. } = &mut self.state {
							if !*want_closed {
								*want_closed = true;
								return Poll::Ready(ProtocolsHandlerEvent::Custom(
									NotifsHandlerOut::CloseDesired
								))
							}
						}
					}
				}
			}
		}

		shutdown_list(&mut self.legacy_shutdown, cx);

		Poll::Pending
	}
}

/// Given a list of substreams, tries to shut them down. The substreams that have been successfully
/// shut down are removed from the list.
fn shutdown_list
	(list: &mut SmallVec<impl smallvec::Array<Item = RegisteredProtocolSubstream<NegotiatedSubstream>>>,
	cx: &mut Context)
{
	'outer: for n in (0..list.len()).rev() {
		let mut substream = list.swap_remove(n);
		loop {
			match substream.poll_next_unpin(cx) {
				Poll::Ready(Some(Ok(_))) => {}
				Poll::Pending => break,
				Poll::Ready(Some(Err(_))) | Poll::Ready(None) => continue 'outer,
			}
		}
		list.push(substream);
	}
}
